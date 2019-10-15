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

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
module CogentTests.Dargent.TypeCheck where

import Data.Set (Set, union, empty, intersection)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

import Control.Monad (guard)

import Test.QuickCheck
import Test.QuickCheck.All
import Text.Parsec.Pos (SourcePos)

import Cogent.Dargent.Surface
import Cogent.Dargent.Core
import Cogent.Dargent.TypeCheck
import CogentTests.Dargent.Core
import Cogent.Common.Syntax (DataLayoutName, Size)

{- PROPERTIES -}

prop_allocationConj :: Allocation -> Allocation -> Bool
prop_allocationConj a b = case a /\ b of
  ([], c)  ->
    (toSet a) `disjoint` (toSet b) &&
    (toSet a) `union`    (toSet b) == toSet c 
  _ -> not (toSet a `disjoint` toSet b)
    
prop_overlaps :: BitRange -> BitRange -> Bool
prop_overlaps a b = overlaps a b == not (toSet a `disjoint` toSet b)

prop_typeCheckValidGivesNoErrors :: Property
prop_typeCheckValidGivesNoErrors =
  forAll (genDataLayout size) $ \(layout, alloc) ->
    case typeCheckDataLayoutExpr M.empty (undesugarDataLayout layout) of
      ([], alloc')  -> toSet alloc == toSet alloc'
      _             -> False
  where size = 30

{-+ INVERSE FUNCTIONS
  |
  | Convert core DataLayout values back to surface DataLayoutExprs for round trip testing.
  +-}
  
bitSizeToDataLayoutSize :: Size -> DataLayoutSize
bitSizeToDataLayoutSize size =
  if bytes == 0
    then Bits bits
  else if bits == 0
    then Bytes bytes
    else Add (Bytes bytes) (Bits bits)
  where
    bytes = size `div` 8
    bits  = size `mod` 8
    
undesugarBitRange :: BitRange -> DataLayoutExpr
undesugarBitRange (BitRange size offset) =
  Offset (Prim (bitSizeToDataLayoutSize size)) (bitSizeToDataLayoutSize offset)
    
undesugarDataLayout  :: DataLayout BitRange -> DataLayoutExpr
undesugarDataLayout UnitLayout = Prim (Bits 0)
undesugarDataLayout (PrimLayout bitRange) = undesugarBitRange bitRange
undesugarDataLayout (RecordLayout fields) =
  Record $ fmap (\(name, (layout, pos)) -> (name, pos, (undesugarDataLayout  layout))) (M.toList fields)
undesugarDataLayout (SumLayout tagBitRange alternatives) =
  Variant
    (undesugarBitRange tagBitRange)
    (fmap (\(tagName, (tagValue, altLayout, altPos)) -> (tagName, altPos, tagValue, (undesugarDataLayout  altLayout))) (M.toList alternatives))
    
{- ARBITRARY INSTANCES -}
instance Arbitrary DataLayoutPath where
  arbitrary = InDecl <$> arbitrary <*> arbitrary
    

{- SET UTIL FUNCTIONS -}
disjoint :: Ord a => Set a -> Set a -> Bool
disjoint a b = a `intersection` b == empty

class SetLike a where
  toSet :: a -> Set Size

instance SetLike BitRange where
  toSet (BitRange size offset) = S.fromList [offset..offset + size - 1]

instance SetLike Allocation where
  toSet = foldr union empty . fmap (toSet . fst)
    
return []
testAll = $quickCheckAll
