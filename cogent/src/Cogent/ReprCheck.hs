--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

-- {-# LANGUAGE ExplicitForAll #-}
-- {-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE ImplicitParams #-}
-- {-# LANGUAGE LambdaCase #-}
-- {-# LANGUAGE TupleSections #-}
-- {-# LANGUAGE ViewPatterns #-}

module Cogent.ReprCheck where

import Cogent.Common.Repr as R
import Cogent.Common.Syntax
import Cogent.Surface as S
import Cogent.Util (mapAccumLM)

import qualified Data.Map as M
import Text.Parsec.Pos

data RepContext = InField FieldName SourcePos RepContext
                | InTag RepContext
                | InAlt TagName SourcePos RepContext
                | InDecl RepDecl
                deriving (Eq, Show, Ord)

data RepError = OverlappingBlocks Block Block
              | UnknownRepr RepName RepContext
              | TagMustBeSingleBlock RepContext
              deriving (Eq, Show, Ord)

type Allocation = [[Block]] -- disjunction of conjunctions

data Block = Block { blockSize :: Int, blockOffset :: Int, blockContext :: RepContext }
           deriving (Eq, Show, Ord)

(\/) :: Allocation -> Allocation -> Either RepError Allocation 
a \/ b = Right (a ++ b)

(/\) :: Allocation -> Allocation -> Either RepError Allocation
(x:xs) /\ b = (++) <$> helper x b <*> (xs /\ b)
  where helper :: [Block] -> [[Block]] -> Either RepError Allocation
        helper bs (y:ys) = let os = [(b1,b2) | b1 <- bs, b2 <- y, overlaps b1 b2]
                            in case os of 
                                [] -> ((bs ++ y):) <$> helper bs ys 
                                (b1,b2):_ -> Left $ OverlappingBlocks b1 b2
        helper bs [] = Right []

        overlaps (Block s1 o1 _) (Block s2 o2 _) = o1 >= o2 && o1 < (o2 + s2)
                                                || o2 >= o1 && o2 < (o1 + s1)
[] /\ b = pure b


offsetAllocation :: Int -> Allocation -> Allocation 
offsetAllocation off = map (map (\(Block s o c) -> Block s (o + off) c))

offsetRep :: Int -> Representation -> Representation
offsetRep off (R.Bits    s o   ) = R.Bits s (o + off)
offsetRep off (R.Variant s o vs) = R.Variant s (o + off) (fmap (fmap (offsetRep off)) vs)
offsetRep off (R.Record      fs) = R.Record (fmap (offsetRep off) fs)


compile :: M.Map RepName (Allocation, RepData) -> RepDecl -> Either RepError (Allocation, RepData)
compile env d@(RepDecl p n a) = fmap (Rep d n) <$> evalAlloc (InDecl d) a
  where evalSize (S.Bytes b) = b * 8
        evalSize (S.Bits b) = b
        evalSize (S.Add a b) = evalSize a + evalSize b

        evalAlloc ctx (S.RepRef n) = do 
            case M.lookup n env of 
                Just (a,Rep _ _ r) -> Right (a,r)
                Nothing    -> Left $ UnknownRepr n ctx
        evalAlloc ctx (S.Prim s) = Right ([[Block (evalSize s) 0 ctx]], R.Bits (evalSize s) 0)
        evalAlloc ctx (S.Offset e off) = do
            (a', r') <- evalAlloc ctx e
            return (offsetAllocation (evalSize off) a', offsetRep (evalSize off) r')
        evalAlloc ctx (S.Record fs) = do
            let step alloc (f,pos,r) = do
                  (a, r') <- evalAlloc (InField f pos ctx) r 
                  a' <- a /\ alloc 
                  return (a', (f, r'))
            (a, fs') <- mapAccumLM step [[]] fs 
            pure (a, R.Record $ M.fromList fs')
        evalAlloc ctx (S.Variant e vs) = do
            (a, td) <- evalAlloc (InTag ctx) e
            case a of 
                [[Block ts to _]] -> do
                    let step alloc (f,pos,i,r) = do 
                            (a, r') <- evalAlloc (InAlt f pos ctx) r
                            a' <- a \/ alloc
                            return (a', (f,(i,r')))
                    (a', vs') <- mapAccumLM step a vs
                    pure (a', R.Variant ts to $ M.fromList vs')
                _ -> Left $ TagMustBeSingleBlock (InTag ctx)

