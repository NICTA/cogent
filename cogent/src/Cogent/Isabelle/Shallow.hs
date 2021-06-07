--
-- Copyright 2017, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-
 - Shallow.hs: shallow Isabelle embedding, SCorres proof and shallow-tuples proof.
 -}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ExistentialQuantification #-}

module Cogent.Isabelle.Shallow
--   ( shallow
--   , shallowConsts
--   , shallowTuplesProof
--   , MapTypeName
--   )
  where

import Cogent.Common.Syntax as CS
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Core as CC
import Cogent.Desugar as D (freshVarPrefix)
import Cogent.Isabelle.Compound (takeFlatCase)
import Cogent.Isabelle.IsabelleName
import Cogent.Isabelle.ShallowTable (TypeStr(..), st, getStrlType, toTypeStr)

import Cogent.Normal as N (freshVarPrefix)
import Cogent.Util (NameMod, Stage(..), Warning)
import Data.Fin
import Data.Nat (Nat(..))
import Data.Vec as Vec

import Isabelle.ExprTH
import Isabelle.InnerAST as I
import Isabelle.OuterAST as O

import Control.Applicative
import Control.Arrow ((***))
import Control.Monad.RWS hiding (Product, Sum, mapM)
import Control.Monad.State
import Control.Monad.Writer (Writer, runWriter)
import Data.Char (ord, chr, intToDigit, isDigit)
import Data.Either (lefts, rights)
import Data.Function (on)
import Data.List (isPrefixOf, isSuffixOf, stripPrefix, partition, sortBy, sortOn, minimumBy, groupBy, unzip5, intercalate, nub, replicate, dropWhileEnd)
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Numeric
import Prelude as P
import System.FilePath ((</>))
import Text.PrettyPrint.ANSI.Leijen (Doc, pretty, string)
import qualified Text.PrettyPrint.ANSI.Leijen as L ((<$$>))
import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Mtl
import Debug.Trace

_fixHighlighting = x where x = ()

type MapTypeName = M.Map TypeStr TypeName

data SGTables = SGTables { typeStrs      :: [TypeStr]
                         , typeNameMap   :: MapTypeName
                         , typeVars      :: [String]     -- ^ @Cogent var &#x21A6; Isabelle var@
                         , recoverTuples :: Bool         -- ^ not a table, but convenient to be included here
                         }

type MapConcTypeSyn = M.Map String TypeName
data PolyTypeSyn = forall t b. PTS TypeName [TyVarName] (CC.Type t b)

data StateGen = StateGen {
    _varNameGen   :: Int,            -- ^ counter for fresh variables
    _concTypeSyns :: MapConcTypeSyn, -- ^ @type structure hash &#x21A6; Cogent type synonym name@
    _polyTypeSyns :: [PolyTypeSyn]   -- ^ polymorphic type synonyms
}

makeLenses ''StateGen

newtype SG a = SG { runSG :: RWS SGTables [Warning] StateGen a }
               deriving (Functor, Applicative, Monad,
                         MonadReader SGTables,
                         MonadWriter [Warning],
                         MonadState  StateGen)

isaReservedNames = ["o", "value", "from"]

shallowTVar :: Int -> String
shallowTVar v = [chr $ ord 'a' + fromIntegral v]

shallowTypeWithName :: (Show b,Eq b) => CC.Type t b -> SG I.Type
shallowTypeWithName t = shallowType =<< findShortType True t

shallowRecTupleType :: (Show b,Eq b) => [(FieldName, (CC.Type t b, Bool))] -> SG I.Type
shallowRecTupleType fs = shallowTupleType <$> mapM shallowType (map (fst . snd) fs)

shallowType :: forall t b. (Show b,Eq b) => CC.Type t b -> SG I.Type
shallowType (TVar v) = I.TyVar <$> ((!!) <$> asks typeVars <*> pure (finInt v))
shallowType (TVarBang v) = shallowType (TVar v :: CC.Type t b)
shallowType (TCon tn ts _) = I.TyDatatype tn <$> mapM shallowType ts
shallowType t@(TFun t1 t2) = 
    if __cogent_ffold_poly_types
       then do
              st <- findShortType False t
              case st of
                   (TCon _ _ _) -> shallowType st
                   _ -> I.TyArrow <$> shallowType t1 <*> shallowType t2
       else I.TyArrow <$> shallowType t1 <*> shallowType t2
shallowType (TPrim pt) = pure $ shallowPrimType pt
shallowType (TString) = pure $ I.AntiType "string"
shallowType (TSum alts) = shallowTypeWithName (TSum alts)
shallowType (TProduct t1 t2) = I.TyTuple <$> shallowType t1 <*> shallowType t2
shallowType t@(TRecord rp fs s) = do
  tuples <- asks recoverTuples
  if tuples && isRecTuple (map fst fs) 
     then
       if __cogent_ffold_poly_types
          then do
                st <- findShortType False t
                case st of
                     (TCon _ _ _) -> shallowType st
                     _ -> shallowRecTupleType fs
            else shallowRecTupleType fs
  else
    shallowTypeWithName (TRecord rp fs s)
shallowType (TUnit) = return $ I.AntiType "unit"
#ifdef BUILTIN_ARRAYS
shallowType t@(TArray el _ _ _) = 
    if __cogent_ffold_poly_types
       then do
             st <- findShortType False t
             case st of
                  (TCon _ _ _) -> shallowType st
                  _ -> I.TyDatatype "list" <$> mapM shallowType [el]
       else I.TyDatatype "list" <$> mapM shallowType [el]
#endif

shallowPrimType :: PrimInt -> I.Type
shallowPrimType U8  = I.TyDatatype "word" [I.AntiType "8"]
shallowPrimType U16 = I.TyDatatype "word" [I.AntiType "16"]
shallowPrimType U32 = I.TyDatatype "word" [I.AntiType "32"]
shallowPrimType U64 = I.TyDatatype "word" [I.AntiType "64"]
shallowPrimType Boolean = I.TyPrim I.BoolT

-- The `(foo)` syntax makes an infix operator prefix after Isabelle2018. There
-- is a special case on `(*)`, which doesn't work because comments start with
-- `(*`, which is why it's non-trivial to abstract making prefix ops here.
shallowPrimOp :: Op -> [Term] -> Term
shallowPrimOp CS.Plus   es = mkApp (mkId "(+)") es
shallowPrimOp CS.Minus  es = mkApp (mkId "(-)") es
shallowPrimOp CS.Times  es = mkApp (mkId "(*)") es
shallowPrimOp CS.Divide es = mkApp (mkId "checked_div") es
shallowPrimOp CS.Mod    es = mkApp (mkId "checked_mod") es
shallowPrimOp CS.Not    es = mkApp (mkId "HOL.Not") es
shallowPrimOp CS.And    es = TermBinOp Conj (es!!0) (es!!1)
shallowPrimOp CS.Or     es = TermBinOp Disj (es!!0) (es!!1)
shallowPrimOp CS.Gt     es = mkApp (mkId "(>)") es
shallowPrimOp CS.Lt     es = mkApp (mkId "(<)") es
shallowPrimOp CS.Le     es = mkApp (mkId "(<=)") es
shallowPrimOp CS.Ge     es = mkApp (mkId "(>=)") es
shallowPrimOp CS.Eq     es = mkApp (mkId "(=)") es
shallowPrimOp CS.NEq    es = mkApp (mkId "(~=)") es
shallowPrimOp CS.BitAnd es = mkApp (mkId "(AND)") es
shallowPrimOp CS.BitOr  es = mkApp (mkId "(OR)") es
shallowPrimOp CS.BitXor es = mkApp (mkId "(XOR)") es
shallowPrimOp CS.LShift [e1,e2] = mkApp (mkId "checked_shift") [mkId "shiftl", e1, e2]
shallowPrimOp CS.RShift [e1,e2] = mkApp (mkId "checked_shift") [mkId "shiftr", e1, e2]
shallowPrimOp CS.LShift _ = __impossible "shallowPrimOp"
shallowPrimOp CS.RShift _ = __impossible "shallowPrimOp"
shallowPrimOp CS.Complement [e] = mkApp (mkId "NOT") [e]
shallowPrimOp CS.Complement _ = __impossible "shallowPrimOp"

snm :: NameMod
-- TODO: Ideally this is how we'd manipulate isabelle names
-- snm = unIsabelleName . mkIsabelleName
snm nm = case nm `elem` isaReservedNames of
  True -> nm ++ I.subSym ++ "r"
  _ -> case stripPrefix D.freshVarPrefix nm of
    Just nb -> "ds" ++ subSymStr nb
    Nothing -> case stripPrefix N.freshVarPrefix nm of
      Just nb -> "an" ++ subSymStr nb
      -- Add debug note
      Nothing -> case "_" `isPrefixOf` nm of
        True  -> dropWhile (== '_') nm ++ subSymStr "d"
        False -> case "_" `isSuffixOf` nm of
          True  -> nm ++ subSymStr "x"
          False -> nm

list2 a b = [a,b]

shallowILit :: Integer -> PrimInt -> Term
shallowILit n Boolean = if n > 0 then mkTru else mkFls
shallowILit n v = TermWithType (mkId $ show n) (shallowPrimType v)

findType :: CC.Type t b -> SG (CC.Type t b)
findType t = getStrlType <$> asks typeNameMap <*> asks typeStrs <*> pure t

-- | Reverse engineer the type synonym of a algebraic data type
--   First argument must be True for Records and Variants so that
--   the record/datatype is returned when no type synonym is found.
findShortType :: (Show b,Eq b) => Bool -> CC.Type t b -> SG (CC.Type t b)
findShortType rv t = do
  map <- use concTypeSyns
  case M.lookup (hashType t) map of
   Nothing -> 
     if __cogent_ffold_poly_types
        then do
               polys <- use polyTypeSyns
               case lookupPolySyn t polys of
                    Nothing -> if rv then findType t else pure t
                    Just (tn,args) -> pure $ TCon tn args (__impossible "findShortType")
        else findType t 
   Just tn -> pure $ TCon tn [] (__impossible "findShortType")

lookupPolySyn :: (Show b,Eq b) => CC.Type t b -> [PolyTypeSyn] -> Maybe (TypeName, [CC.Type t b])
lookupPolySyn t polys =
    if (null matches)
       then Nothing
       else -- FIXME: simple strategy using only the first match found
            Just $ P.head matches
    where matches = catMaybes $ map (matchPolySyn t) polys

matchPolySyn :: (Show b,Eq b) => CC.Type t b -> PolyTypeSyn -> Maybe (TypeName, [CC.Type t b])
matchPolySyn t (PTS sn svs r) =
    case matchType svs t r of
         Nothing -> Nothing
         Just binds ->
            let
                mbinds = nub binds
            in if (P.length svs) /= (P.length mbinds)
                  then Nothing
                  else let
                           mapbinds = M.fromList mbinds
                       in if (P.length svs) /= (M.size mapbinds)
                             then Nothing
                             else Just (sn, map (\v -> M.findWithDefault TUnit v mapbinds) svs)

-- | Match a type to a polymorphic type.
-- The first argument is the list of type variables which may occur in the polymorphic type.
-- The second argument is the type to be matched, the third argument is the polymorphic type.
-- The result is Nothing, if there is no structural match.
-- Otherwise it is an association list of bindings for the type variables.
-- The same variable may have several entries in result list, for a match they must all bind the same type.
-- FIXME: recursive record parameters and refinement types are not handled yet.
matchType :: [TyVarName] -> CC.Type t1 b1 -> CC.Type t2 b2 -> Maybe [(TyVarName, CC.Type t1 b1)]
matchType vs (TCon tn targs _) (TCon rn rargs _) | tn == rn && (P.length targs) == (P.length rargs) =
    matchTypes vs targs rargs
matchType vs (TRecord tr tfs _) (TRecord rr rfs _) | tr == rr && (P.length tfs) == (P.length rfs) =
    if (map fst tfs) /= (map fst rfs)
       then Nothing
       else matchTypes vs (map (fst . snd) tfs) (map (fst . snd) rfs)
matchType vs (TSum tts) (TSum rts) | (P.length tts) == (P.length rts) =
    if (map fst tts) /= (map fst rts)
       then Nothing
       else matchTypes vs (map (fst . snd) tts) (map (fst . snd) rts)
matchType vs (TProduct t1 t2) (TProduct r1 r2) = matchTypes vs [t1,t2] [r1,r2]
matchType vs (TFun tf1 tf2) (TFun rf1 rf2) = matchTypes vs [tf1,tf2] [rf1,rf2]
matchType _ (TPrim tp) (TPrim rp) | tp == rp = Just []
matchType _ TUnit TUnit = Just []
matchType _ TString TString = Just []
matchType vs t (TVar n) = matchTypeVar vs t n
matchType vs t (TVarBang n) = matchTypeVar vs t n
matchType vs t (TVarUnboxed n) = matchTypeVar vs t n
#ifdef BUILTIN_ARRAYS
-- FIXME: array size is ignored upon matching
matchType vs (TArray te _ _ _) (TArray re _ _ _) = matchType vs te re
#endif
matchType _ _ _ = Nothing

matchTypeVar :: [TyVarName] -> CC.Type t1 b -> Fin t2 -> Maybe [(TyVarName, CC.Type t1 b)]
matchTypeVar vs t n =
    if i >= P.length vs
       then Nothing
       else Just [(vs!!i,t)]
    where i = finInt n

-- | Pairwise match two type lists of the same length and concatenate the results.
matchTypes :: [TyVarName] -> [CC.Type t1 b1] -> [CC.Type t2 b2] -> Maybe [(TyVarName, CC.Type t1 b1)]
matchTypes vs ts rs =
    if any isNothing pmatch
       then Nothing
       else Just $ concat $ catMaybes pmatch
    where pmatch = map (\(t,r) -> matchType vs t r) $ P.zip ts rs

findTypeSyn :: CC.Type t b -> SG String
findTypeSyn t = findType t >>= \(TCon nm _ _) -> pure nm

shallowExpr :: (Show b,Eq b) => TypedExpr t v VarName b -> SG Term
shallowExpr (TE _ (Variable (_,v))) = pure $ mkId (snm v)
shallowExpr (TE t (Fun fn ts ls _)) =
    if null ts
       then pure $ mkId $ snm $ unCoreFunName fn
       else -- for polymorphic functions add its type
            TermWithType (mkId $ snm $ unCoreFunName fn) <$> shallowType t
shallowExpr (TE _ (Op opr es)) = shallowPrimOp <$> pure opr <*> (mapM shallowExpr es)
shallowExpr (TE _ (App f arg)) = mkApp <$> shallowExpr f <*> (mapM shallowExpr [arg])
shallowExpr (TE t (Con cn e _))  = do
  tn <- findTypeSyn t
  econ <- mkApp <$> pure (mkStr [tn,".",cn]) <*> (mapM shallowExpr [e])
  TermWithType econ <$> shallowType t
shallowExpr (TE _ (Unit)) = pure $ mkId "()"
shallowExpr (TE _ (ILit n pt)) = pure $ shallowILit n pt
shallowExpr (TE _ (SLit s)) = pure $ mkString s
#ifdef BUILTIN_ARRAYS
shallowExpr (TE _ (ALit es)) = mkList <$> mapM shallowExpr es
shallowExpr (TE _ (ArrayIndex arr idx)) = do
  arr' <- shallowExpr arr
  idx' <- mkApp (mkId "unat") <$> mapM shallowExpr [idx]
  return $ mkApp (mkId "nth") [arr', idx']
shallowExpr (TE _ (Pop _ arr e)) = __todo "shallowExpr: pop"
shallowExpr (TE _ (Singleton e)) = __todo "shallowExpr: singleton"
shallowExpr (TE _ (ArrayMap2 ((v1, v2), fbody) (arr1,arr2))) = do
  fbody' <- shallowExpr fbody
  let f = mkLambda [snm v1, snm v2] fbody'
  arr1' <- shallowExpr arr1
  arr2' <- shallowExpr arr2
  tuples <- asks recoverTuples
  if tuples then return $ mkApp (mkId "map2") [f, mkPair arr1' arr2']
            else shallowMaker (exprType fbody)
                              [("p1" ++ subSymStr "f", arr1), ("p2" ++ subSymStr "f", arr2)]
shallowExpr (TE _ (ArrayTake _ arr idx e)) = __todo "shallowExpr: array take"
shallowExpr (TE _ (ArrayPut arr idx val)) = __todo "shallowExpr: array put"
#endif
shallowExpr (TE _ (Let nm e1 e2)) = shallowLet nm e1 e2
shallowExpr (TE _ (LetBang vs nm e1 e2)) = shallowLet nm e1 e2
shallowExpr (TE _ (Tuple e1 e2)) = mkApp <$> (pure $ mkId "Pair") <*> (mapM shallowExpr [e1, e2])
shallowExpr (TE t (Struct fs)) = shallowMaker t fs
shallowExpr (TE _ (If c th el)) = mkApp <$> (pure $ mkId "HOL.If") <*> mapM shallowExpr [c, th, el]

shallowExpr e
 | Just (escrut,ealts) <- takeFlatCase e
 , tscrut              <- exprType escrut
 , TSum talts          <- tscrut
 = do
  tuples <- asks recoverTuples
  escrut' <- shallowExpr escrut
  if tuples 
     then do
         -- in tuples form use the case-of representation
         let es   = flip map talts $ \(tag,_) ->
              case M.lookup tag ealts of
               Just (n,e) -> (tag,n,e) 
               Nothing -> __impossible ("shallowExpr: takeFlatCase succeeded but returned map missing tag " ++ show tag)
         es' <- mapM shallowAlt es
         pure $ CaseOf escrut' es'
     else do
         -- otherwise use case_x application since the Let\^<sub>d\^<sub>s will interfere with case-of syntax
         tn      <- findTypeSyn tscrut
         ealts'  <- traverse (\(n,e) -> mkLambdaE [snm n] e) ealts
         let es   = flip map talts $ \(tag',(t',b')) ->
              case M.lookup tag' ealts' of
               Just e' -> e'
               Nothing -> __impossible ("shallowExpr: takeFlatCase succeeded but returned map missing tag " ++ show tag')
         pure $ mkApp (mkStr ["case_",tn]) $ es ++ [escrut']

shallowExpr (TE t (Case e tag (_,n1,e1) (_,n2,e2))) = do
  e' <- shallowExpr e
  let te@(TSum alts) = exprType e
  tn  <- findTypeSyn te
  te' <- shallowType te
  e1' <- mkLambdaE [snm n1] e1
  e2' <- mkLambdaE [snm n2] e2
  vn <- varNameGen <<%= (+1)
  vn2 <- varNameGen <<%= (+1)
  let vgn = "v" ++ (subSymStr $ "G" ++ show vn)
      vgn2 = "ccase" ++ (subSymStr $ "G" ++ show vn2)  -- This is the continuation @e2@
      es = flip map alts $ \(tag',(t',b')) ->
             if | tag == tag' -> e1'
                | otherwise ->
                    let cons = mkApp (mkStr [tn,".",tag']) [mkId vgn]
                        typedCons = TermWithType cons te'
                     in mkLambda [vgn] $ mkApp (mkId vgn2) [typedCons]
      rcase = mkApp (mkStr ["case_",tn]) $ es ++ [e']
  pure $ mkLet vgn2 e2' rcase
-- \ ^^^ NOTE: We can't use the @case _ of@ syntax as our @case@s are binary (and nested).
-- It seems that Isabelle spends exponential time on processing the @case _ of@ syntax depending
-- on the level of nestings. / zilinc
shallowExpr (TE t (Esac e)) = do
  tn <- findTypeSyn $ exprType e
  e' <- shallowExpr e
  let TSum alts = exprType e
      es = flip map alts $ \(tag',(t',b')) ->
             if | b' -> mkId "undefined"
                | otherwise -> mkId "Fun.id"
  pure $ mkApp (mkStr ["case_",tn]) $ es ++ [e']
shallowExpr (TE _ (Split (n1,n2) e1 e2)) = mkApp <$> mkLambdaE [mkPrettyPair n1 n2] e2 <*> mapM shallowExpr [e1]
shallowExpr (TE _ (Member rec fld)) = shallowExpr rec >>= \e -> shallowGetter rec fld e
shallowExpr (TE _ (Take (n1,n2) rec fld e)) = do
  erec <- shallowExpr rec
  efield <- mkId <$> getRecordFieldName (exprType rec) fld
  let take = mkApp (mkId $ "take" ++ subSymStr "cogent") [erec, efield]
      pp = mkPrettyPair n1 n2
  mkLet pp take <$> shallowExpr e
shallowExpr (TE _ (Put rec fld e)) = shallowSetter rec fld e
shallowExpr (TE _ (Promote ty e)) = shallowExpr e
shallowExpr (TE _ (Cast    (TPrim pt) (TE _ (ILit n _)))) = pure $ shallowILit n pt
shallowExpr (TE _ (Cast    (TPrim pt) e)) =
  TermWithType <$> (mkApp (mkId "ucast") <$> ((:[]) <$> shallowExpr e)) <*> pure (shallowPrimType pt)

shallowAlt :: (Show b,Eq b) => (TagName,VarName,TypedExpr t v VarName b) -> SG (Term,Term)
shallowAlt (tag,n,e) = do
    e' <- shallowExpr e
    pure (TermApp (mkId tag) (mkId n),e')

-- | @'mkL' nm t1 t2@:
--
--   It generates term @(&#x03bb; nm. t2) t1@
mkL :: VarName -> Term -> Term -> Term
mkL nm t1 t2 = mkApp (mkLambda [snm nm] t2) [t1]

mkLetds :: VarName -> Term -> Term -> Term
mkLetds nm t1 t2 = mkApp (mkId $ "Let" ++ subSymStr "ds") [t1, mkLambda [snm nm] t2]

mkLet :: VarName -> Term -> Term -> Term
mkLet nm t1 t2 =
 if D.freshVarPrefix `isPrefixOf` nm then
    --mkApp (mkLambda [snm nm] t2) [t1]
    mkLetds nm t1 t2
 else
    mkApp (mkId "HOL.Let") [t1, mkLambda [snm nm] t2]

shallowLet :: (Show b,Eq b) => VarName -> TypedExpr t v VarName b -> TypedExpr t ('Suc v) VarName b -> SG Term
shallowLet nm e1 e2 = do
    mkLet nm <$> shallowExpr e1 <*> shallowExpr e2

mkStr :: [String] -> Term
mkStr = mkId . concat

mkPrettyPair :: VarName -> VarName -> String
mkPrettyPair n1 n2 = "(" ++ snm n1 ++ "," ++ snm n2 ++ ")"

mkLambdaE :: (Show b,Eq b) => [VarName] -> TypedExpr t v VarName b -> SG Term
mkLambdaE vs e = mkLambda vs <$> shallowExpr e

-- | Reverse engineer whether a record type was a tuple by looking at the field names.
--   This is __hacky__.
isRecTuple :: [FieldName] -> Bool
isRecTuple fs =
  P.length fs > 1 &&
  filter (\xs -> xs!!0 == 'p' && let ys = drop 1 xs in filter isDigit ys == ys) fs == fs

shallowMaker :: (Show b,Eq b) => CC.Type t b -> [(FieldName, TypedExpr t v VarName b)] -> SG Term
shallowMaker t fs = do
  tn <- findTypeSyn t
  let fnms = map fst fs
  tuples <- asks recoverTuples
  if tuples && isRecTuple fnms
  then mkTuple <$> mapM (shallowExpr . snd) fs
  else if tuples
       then mkRecord tn fs
       else mkApp <$> pure (mkStr [tn, ".make"]) <*> (mapM (shallowExpr . snd) fs)

mkRecord :: (Show b,Eq b) => String -> [(FieldName, TypedExpr t v VarName b)] -> SG Term
mkRecord tn fs = do
    fts <- mapM (shallowExpr . snd) fs
    pure $ ListTerm "\\<lparr>" (map (\(fn,t) -> (TermBinOp I.Eq (mkId fn) t)) $ P.zip ffs fts) "\\<rparr>"
    where ffs = addtn $ map (\(f,t) -> f ++ subSymStr "f") fs
          addtn (f1:ffs) = (tn++ "." ++ f1) : ffs

shallowSetter :: (Show b,Eq b) => TypedExpr t v VarName b -> Int -> TypedExpr t v VarName b -> SG Term
shallowSetter rec idx e = do
  tn <- getRecordFieldName (exprType rec) idx
  let setter = tn ++ "_update"
  mkApp (mkId setter) <$> (list2 <$> mkLambdaE ["_"] e <*> shallowExpr rec)

shallowGetter :: TypedExpr t v VarName b -> Int -> Term -> SG Term
shallowGetter rec idx rect = mkApp <$> (mkId <$> getRecordFieldName (exprType rec) idx) <*> pure [rect]

getRecordFieldName :: CC.Type t b -> Int -> SG FieldName
getRecordFieldName t@(TRecord _ fs _) ind = do
  tn <- findTypeSyn t
  let fnms = map fst fs
  tuples <- asks recoverTuples
  let prefix = if tuples && isRecTuple fnms then recTupleName fnms ++ "_" else tn ++ "."
  pure $ prefix ++ (map fst fs !! ind) ++ subSymStr "f"
getRecordFieldName _ _ = __impossible "getRecordFieldName"

-- Simplify generated terms for better readability:
-- - eliminate take_cogent: let (a,b) = take_cogent rec sel in e --> let b = rec; a = sel b in e
-- - eliminate Let_ds: replace by HOL.Let
-- - eliminate bindings of variables not used in the body 
-- - eliminate chain bindings of variables by variable substitution
-- - eliminate tuple accessor functions by using tuple bindings
-- This is only applied to the recoverTuples form and must be respected in the TuplesProof.
simplifyTerm :: Term -> Term
simplifyTerm = useTupleBindings . simplifyLets

simplifyLets :: Term -> Term
simplifyLets (TermApp t t') =
    case t of
         TermApp hl@(TermIdent (Id s)) bnd 
           | s == "HOL.Let" -> 
             let (QuantifiedTerm Lambda [w@(Id ws)] bdy) = t'
             in case bnd of
                 TermApp (TermApp (TermIdent (Id tk)) rec) sel | tk == "take" ++ subSymStr "cogent" ->
                   let (v1,v2) = parsePrettyPair ws
                   in simplifyLets $ mkHOLLet (Id v2) rec $ mkHOLLet (Id v1) (mkApp sel [(mkId v2)]) bdy
                 TermIdent v -> 
                   let sbdy = simplifyLets bdy
                   in if v == w || (not $ isFreeInTerm w sbdy) then sbdy else substVarInTerm v w $ sbdy
                 _ -> let sbdy = simplifyLets bdy in if not $ isFreeInTerm w sbdy then sbdy else recurse
           | s == ("Let" ++ subSymStr "ds") -> simplifyLets $ TermApp (TermApp (mkId "HOL.Let") bnd) t'
         _ -> recurse
    where recurse = (TermApp (simplifyLets t) (simplifyLets t'))
simplifyLets (TermWithType t tp) = TermWithType (simplifyLets t) tp
simplifyLets (QuantifiedTerm qnt ids t) = QuantifiedTerm qnt ids $ simplifyLets t
simplifyLets (TermUnOp op t) = TermUnOp op $ simplifyLets t
simplifyLets (TermBinOp op t t') = TermBinOp op (simplifyLets t) (simplifyLets t')
simplifyLets (ListTerm opn ts cls) = ListTerm opn (map simplifyLets ts) cls
simplifyLets (CaseOf t alts) = CaseOf (simplifyLets t) $ map (\(p,t) -> (p,simplifyLets t)) alts
simplifyLets t = t

useTupleBindings :: Term -> Term
useTupleBindings (TermApp (TermApp (TermIdent (Id s)) (TermApp (TermIdent (Id tacc)) tup)) (QuantifiedTerm Lambda [(Id ws)] bdy))
    | (Just acc) <- parseTupleAcc tacc, s == "HOL.Let" = mkTupleBinding [(acc,ws)] tup bdy
useTupleBindings (TermApp t t') = TermApp (useTupleBindings t) (useTupleBindings t')
useTupleBindings (TermWithType t tp) = TermWithType (useTupleBindings t) tp
useTupleBindings (QuantifiedTerm qnt ids t) = QuantifiedTerm qnt ids $ useTupleBindings t
useTupleBindings (TermUnOp op t) = TermUnOp op $ useTupleBindings t
useTupleBindings (TermBinOp op t t') = TermBinOp op (useTupleBindings t) (useTupleBindings t')
useTupleBindings (ListTerm opn ts cls) = ListTerm opn (map useTupleBindings ts) cls
useTupleBindings (CaseOf t alts) = CaseOf (useTupleBindings t) $ map (\(p,t) -> (p,useTupleBindings t)) alts
useTupleBindings t = t

substVarInTerm :: Ident -> Ident -> Term -> Term
substVarInTerm v w (TermIdent x) | x == w = (TermIdent v)
-- [v/w] let v = bnd in bdy --> let w = v; v = bnd in bdy
-- [v/w] let w = bnd in bdy --> let w = [v/w] bnd in bdy
-- [v/w] let x = bnd in bdy --> let x = [v/w] bnd in [v/w] bdy
substVarInTerm v w t@(TermApp (TermApp hl@(TermIdent (Id s)) bnd) (QuantifiedTerm Lambda [x] bdy)) | s == "HOL.Let" = 
    if w == x || (not $ isFreeInTerm w bdy)
       then mkHOLLet x (substVarInTerm v w bnd) bdy
       else if v == x then mkHOLLet w (TermIdent v) t
                      else mkHOLLet x (substVarInTerm v w bnd) (substVarInTerm v w bdy)
substVarInTerm v w (TermApp t t') = TermApp (substVarInTerm v w t) (substVarInTerm v w t')
substVarInTerm v w (TermWithType t tp) = TermWithType (substVarInTerm v w t) tp
substVarInTerm v w t@(QuantifiedTerm qnt ids bdy) = 
    if elem v ids
       then mkHOLLet w (TermIdent v) t
       else if elem w ids then t else QuantifiedTerm qnt ids $ substVarInTerm v w bdy
substVarInTerm v w (TermUnOp op t) = TermUnOp op (substVarInTerm v w t)
substVarInTerm v w (TermBinOp op t t') = TermBinOp op (substVarInTerm v w t) (substVarInTerm v w t')
substVarInTerm v w (ListTerm opn ts cls) = ListTerm opn (map (substVarInTerm v w) ts) cls
substVarInTerm v w t@(CaseOf splt alts) = 
    if any (isBoundInAlt v) alts then mkHOLLet w (TermIdent v) t 
                                 else CaseOf (substVarInTerm v w splt) $ map (substVarInAlt v w) alts
substVarInTerm v w t = t

isBoundInAlt :: Ident -> (Term,Term) -> Bool
isBoundInAlt v (TermApp _ (TermIdent x),_) = v == x

substVarInAlt :: Ident -> Ident -> (Term,Term) -> (Term,Term)
substVarInAlt v w (p@(TermApp _ (TermIdent x)),t) = 
    if w == x then (p,t) else (p,substVarInTerm v w t)

isFreeInTerm :: Ident -> Term -> Bool
isFreeInTerm v (TermIdent x) | x == v = True
isFreeInTerm v (TermApp t t') = (isFreeInTerm v t) || (isFreeInTerm v t')
isFreeInTerm v (TermWithType t tp) = isFreeInTerm v t
isFreeInTerm v (QuantifiedTerm qnt ids t) = if elem v ids then False else isFreeInTerm v t
isFreeInTerm v (TermUnOp op t) = isFreeInTerm v t
isFreeInTerm v (TermBinOp op t t') = (isFreeInTerm v t) || (isFreeInTerm v t')
isFreeInTerm v (ListTerm opn ts cls) = any (isFreeInTerm v) ts
isFreeInTerm v (CaseOf t alts) = (isFreeInTerm v t) || any (isFreeInAlt v) alts
isFreeInTerm v _ = False

isFreeInAlt :: Ident -> (Term,Term) -> Bool
isFreeInAlt v (TermApp _ (TermIdent x),t) = if v == x then False else isFreeInTerm v t

mkTupleBinding :: [((Int,Int),VarName)] -> Term -> Term -> Term
mkTupleBinding cmps tup bdy = 
    case bdy of
         (TermApp (TermApp hl@(TermIdent (Id s)) (TermApp (TermIdent (Id tacc)) tup')) (QuantifiedTerm Lambda [(Id w)] bdy'))
             | (Just acc) <- parseTupleAcc tacc, s == "HOL.Let" && tup == tup' -> mkTupleBinding ((acc,w):cmps) tup bdy'
         _ -> mkHOLLet (Id bndtup) (useTupleBindings tup) $ useTupleBindings bdy
    where bndtup = mkPrettyTuple $ fillFrom 1 $ sortOn (snd . fst) cmps

fillFrom :: Int -> [((Int,Int),VarName)] -> [VarName]
fillFrom i cmps@(((siz,el),v):cmps') =
    if i < el then "_" : fillFrom (i+1) cmps
              else v : (if null cmps' then replicate (siz-el) "_" else fillFrom (i+1) cmps')

parseTupleAcc :: String -> Maybe (Int,Int)
parseTupleAcc s = if upp=="P" && p=="_p" && subf=="\\<^sub>f" then Just (read siz, read el) else Nothing
    where (upp,r1) = break isDigit s
          (siz,r2) = span isDigit r1
          (p,r3) = break isDigit r2
          (el,subf) = span isDigit r3

parsePrettyPair :: String -> (String,String)
parsePrettyPair vpr = (h1, dropWhileEnd (== ')') $ drop 1 h2)
    where (h1,h2) = break (== ',') $ drop 1 vpr

mkHOLLet :: Ident -> Term -> Term -> Term
mkHOLLet v bnd bdy = mkApp (TermIdent (Id "HOL.Let")) [bnd, lamTerm [v] bdy]

typarUpd typar v = v {typeVars = typar}

-- Clear out all taken annotations and mark all sigil as unboxed.
sanitizeType :: CC.Type t b -> CC.Type t b
sanitizeType (TSum ts) = TSum (map (\(tn,(t,_)) -> (tn,(sanitizeType t,False))) ts)
sanitizeType (TRecord rp ts _) = TRecord rp (map (\(tn, (t,_)) -> (tn, (sanitizeType t, False))) ts) Unboxed
sanitizeType (TCon tn ts _) = TCon tn (map sanitizeType ts) Unboxed
sanitizeType (TFun ti to) = TFun (sanitizeType ti) (sanitizeType to)
sanitizeType (TProduct t t') = TProduct (sanitizeType t) (sanitizeType t')
#ifdef BUILTIN_ARRAYS
sanitizeType (TArray t _ _ _) = TArray (sanitizeType t) (LSLit "") Unboxed Nothing
#endif
sanitizeType t = t

-- | Produce a hash for a record or variant type. Only the structure of the type matters;
--   taken entries or sigils do not.
hashType :: (Show b) => CC.Type t b -> String
hashType (TSum ts)      = show (sanitizeType $ TSum ts)
hashType (TRecord rp ts s) = show (sanitizeType $ TRecord rp ts s)
hashType (TFun ti to) = show (sanitizeType $ TFun ti to)
#ifdef BUILTIN_ARRAYS
hashType (TArray t sz s tk) = show (sanitizeType $ TArray t sz s tk)
#endif
hashType _              = error "hashType: should only pass Variant, Record, Array or Function types"

-- | A subscript @T@ will be added when generating type synonyms for records and variants.
--   Also adds an entry to the type synonyms table (if it's not parameterised) or the
--   polymorphic type synonyms table (if it is parameterized) so that
--   a shorter (and hence more readable) name can be retrieved when a type is used.
--   Uses hashType, so it may only be applied to Variant, Record, Array and Function types.
shallowTypeDefSaveSyn:: (Show b,Eq b) => TypeName -> [TyVarName] -> CC.Type t b -> SG [TheoryDecl I.Type I.Term]
shallowTypeDefSaveSyn tn ps r = do
  st <- shallowType r
  let syname = syName tn r
      hash = hashType r
  when (null ps) (concTypeSyns %= M.insert hash syname)
  when (not $ null ps) (polyTypeSyns %= (:) (PTS syname ps r))
  pure [TypeSynonym (TypeSyn syname st ps)]
    where syName tn (TSum _) = tn ++ subSymStr "T"
          syName tn (TRecord _ _ _) = tn ++ subSymStr "T"
          syName tn _ = tn

-- | Generates @type_synonym@ definitions for types.
shallowTypeDef :: (Show b,Eq b) => TypeName -> [TyVarName] -> CC.Type t b -> SG [TheoryDecl I.Type I.Term]
shallowTypeDef tn ps (TPrim p)      = pure [TypeSynonym (TypeSyn tn (shallowPrimType p) ps)]
shallowTypeDef tn ps t@(TRecord _ _ _)  = shallowTypeDefSaveSyn tn ps t
shallowTypeDef tn ps t@(TSum _)         = shallowTypeDefSaveSyn tn ps t
shallowTypeDef tn ps t@(TFun _ _)       = shallowTypeDefSaveSyn tn ps t
#ifdef BUILTIN_ARRAYS
shallowTypeDef tn ps t@(TArray _ _ _ _) = shallowTypeDefSaveSyn tn ps t
#endif
shallowTypeDef tn ps t = do
  st <- shallowType t
  pure [TypeSynonym (TypeSyn tn st ps)]

typeNameFromIdx :: Int -> String
typeNameFromIdx idx = 'T':show idx

simpLemma :: String -> String -> TheoryDecl I.Type I.Term
simpLemma nm tag =
  let simp = Attribute "simp" []
      valRelN = "valRel_" ++ nm
      thmN = valRelN ++ "_" ++ tag
      tytag = I.AntiTerm (nm ++ "." ++ tag)
      tagName = I.ConstTerm $ I.StringLiteral tag
      prop = [[isaTerm| valRel \<xi> ($tytag x) (VSum $tagName x') = valRel \<xi> x x'|]]
      methods = [Method "simp" ["add:", valRelN]]
   in LemmaDecl $ Lemma False (Just (TheoremDecl (Just thmN) [simp])) prop (Proof methods ProofDone)

mkPrettyTuple :: [VarName] -> String
mkPrettyTuple vn = "(" ++ intercalate "," vn ++ ")"

recTupleAccessors :: [FieldName] -> FieldName -> [(TheoryDecl I.Type I.Term, Name)]
recTupleAccessors fs fn =
  let dfnm = concat [recTupleName fs, "_", fn, subSymStr "f"]
      lhs = mkId dfnm
      rhs = mkLambda [mkPrettyTuple fs] (mkId fn)
      term = [isaTerm| $lhs \<equiv> $rhs |]
      getter = Definition (Def (Just (Sig dfnm Nothing)) term)
      f = "f" ++ subSymStr "fun"
      udfnm = dfnm ++ "_update"
      lhs2 = mkId udfnm
      tupelms = map (\nm -> if nm == fn then mkApp (mkId f) [mkId nm] else mkId fn) fs
      rhs2 = mkLambda [mkPrettyTuple fs, f] (mkTuple tupelms)
      term2 = [isaTerm| $lhs2 \<equiv> $rhs2 |]
      setter = Definition (Def (Just (Sig udfnm Nothing)) term2)
  in [(getter, dfnm ++ "_def"), (setter, udfnm ++ "_def")]

recTuplePrefix :: String
recTuplePrefix = "P"

recTupleName :: [FieldName] -> String
recTupleName fs = recTuplePrefix ++ (show $ P.length fs)

recTupleDecls :: [FieldName] -> [(TheoryDecl I.Type I.Term, Name)]
recTupleDecls fs = concatMap (recTupleAccessors fs) fs

shallowTupleType :: [I.Type] -> I.Type
shallowTupleType [] = error "Record should have at least 2 fields"  -- FIXME: does this error msg make sense? / zilinc
shallowTupleType [x] = x
shallowTupleType (x:xs) = I.TyTuple x (shallowTupleType xs)

fieldConjValRel :: [(I.Term, I.Term)] -> I.Term
fieldConjValRel [] = error "Can't have empty record"
fieldConjValRel [(var,fld)] = [isaTerm| valRel \<xi> ($fld x) $var |]
fieldConjValRel ((var,fld):r) = let rest = fieldConjValRel r in [isaTerm| valRel \<xi> ($fld x) $var \<and> $rest |]

data DeclT = RecordT | VariantT

shallowTT :: (Int, TypeStr)
          -> SG ( [TheoryDecl I.Type I.Term]
                , [(DeclT,TheoryDecl I.Type I.Term)]
                , [TheoryDecl I.Type I.Term]
                , [Name]
                , MapTypeName
                )
shallowTT (tidx, t) = do
  tnmap <- asks typeNameMap
  let mbsyn = M.lookup t tnmap
      nm = fromMaybe (typeNameFromIdx tidx) mbsyn
      newmap = M.insert t nm tnmap
  case t of
    RecordStr fs -> do
      tuples <- asks recoverTuples
      let tvars = map shallowTVar [0..P.length fs - 1]
          comb = P.zip tvars fs
          fields = map (\(tvar,fn) -> O.RecField (fn ++ subSymStr "f") $ I.TyVar tvar) comb
          evarNames = map ("f_" ++) fs
          tyNames = map ("t_" ++) fs
          (ity, (recdecls, defnames), prefix) = if tuples && isRecTuple fs
            then ( shallowTupleType (map I.TyVar tvars)
                 , ([], map snd (recTupleDecls fs)) --  P.unzip
                 , recTupleName fs ++ "_")
            else ( I.TyDatatype nm $ map I.TyVar tyNames
                 , ([O.RecordDecl (Record nm fields tvars)], [])
                 , nm ++ ".")
          evarIsaList = I.mkList $ map I.mkId evarNames
          conjs = fieldConjValRel (P.zip (map I.mkId evarNames) (map (I.mkId . (prefix ++) . (++ subSymStr "f")) fs))
          valRelBody = I.QuantifiedTerm Exists (map I.Id evarNames) [isaTerm| v = VRecord $evarIsaList \<and> $conjs |]
          valRelSpecName = "valRel_" ++ nm
          valRelDef = OverloadedDef
                        (Def (Just (Sig valRelSpecName Nothing)) [isaTerm| \<And> \<xi> x v. $(mkId valRelSpecName) \<xi> (x :: $ity) v \<equiv> $valRelBody |])
                        (Sig "valRel" Nothing)
          valRel = if tuples && isRecTuple fs then [] else [(RecordT, valRelDef)]
      return (recdecls, valRel, [], defnames, newmap)
    VariantStr fs ->
      let tvars = map shallowTVar [0..P.length fs - 1]
          comb = P.zip tvars fs
          cons = map (\(tvar,fn) -> O.DTCons fn $ [I.TyVar tvar]) comb
          ity = I.TyDatatype nm $ map I.TyVar tvars
          caseExpr = mkId $ "case_" ++ nm
          valRelBody' [] = [isaTerm| $caseExpr |]
          valRelBody' (x:xs) = let tagName = I.ConstTerm $ I.StringLiteral x
                                in I.TermApp (valRelBody' xs) [isaTerm|(\<lambda>x. \<exists>x'. v' = VSum $tagName x' \<and> valRel \<xi> x x') |]
          valRelBody = I.TermApp (valRelBody' $ reverse fs) [isaTerm| v |]
          valRelSpecName = "valRel_" ++ nm
          valRelDef = OverloadedDef
                        (Def (Just (Sig valRelSpecName Nothing)) [isaTerm| $(mkId valRelSpecName) \<xi> (v :: $ity) v' \<equiv> $valRelBody |])
                        (Sig "valRel" Nothing)
          simpLemmas = map (simpLemma nm) fs
      in pure $ ([O.DataTypeDecl (Datatype nm cons tvars)], [(VariantT, valRelDef)], simpLemmas, [], newmap)

-- | If several types share the same structure, we only keep the shortest synonym for it.
filterDuplicates :: [(TypeStr,TypeName)] -> [(TypeStr,TypeName)]
filterDuplicates xs =
  let sorted = sortBy (compare `on` fst) xs
      grouped = groupBy ((==) `on` fst) sorted
      grpdsrtd = map (sortBy (compare `on` snd)) grouped
  in map (minimumBy (compare `on` (P.length . snd))) grpdsrtd

stsyn :: [Definition TypedExpr VarName b] -> MapTypeName
stsyn decls = M.fromList . filterDuplicates . concat $ P.map synAllTypeStr decls

synAllTypeStr :: Definition TypedExpr VarName b -> [(TypeStr, TypeName)]
synAllTypeStr (TypeDef tn _ (Just (TRecord _ fs _))) = [(RecordStr $ P.map fst fs, tn)]
synAllTypeStr (TypeDef tn _ (Just (TSum alts))) = [(VariantStr $ P.map fst alts, tn)]
synAllTypeStr _ = []

shallowTypeFromTable :: SG ([TheoryDecl I.Type I.Term], [TheoryDecl I.Type I.Term], MapTypeName)
shallowTypeFromTable = do
  table <- asks typeStrs
  let itable = P.zip [0..] table
  (decls1,decls2,lemmas,defnames,maps) <- unzip5 <$> mapM shallowTT itable
  pure ( concat decls1
       , map snd (concat decls2) ++ concat lemmas ++
         lemmaBuckets (concat decls2) ++ defNameBucket (concat defnames)
       , M.unions maps )
  where
    defNameBucket [] = []
    defNameBucket ns@(_:_) = [O.LemmasDecl (O.Lemmas (O.TheoremDecl (Just "tuple_defs") [Attribute "simp" []]) $ map thmDecl ns)]
    thmDecl n = O.TheoremDecl (Just n) []

lemmaBuckets :: [(DeclT, TheoryDecl I.Type I.Term)] -> [TheoryDecl I.Type I.Term]
lemmaBuckets is =
  let (recs,variants) = P.unzip $ map lemmaBucket' is
   in lemmas "valRel_records" (concat recs) ++ lemmas "valRel_variants" (concat variants)
  where lemmaBucket' ((RecordT, O.OverloadedDef d s))
           | Just (Sig n _) <- defSig d
           , n' <- drop (P.length "valRel_") n
           = ([ O.TheoremDecl (Just n) [], O.TheoremDecl (Just ( n' ++ ".defs")) []], [])
        lemmaBucket' ((VariantT, O.OverloadedDef d s))
           | Just (Sig n _) <- defSig d
           = ([], [ O.TheoremDecl (Just n) [] ])
        lemmaBucket' _ = ([],[])

        lemmas nm [] = []
        lemmas nm thms@(_:_) = [O.LemmasDecl (O.Lemmas (O.TheoremDecl (Just nm) []) $ thms)]


mlFragment theoryNm stg = unlines
  [ "local_setup \\<open>"
  , "gen_scorres_lemmas \"" ++ theoryNm ++ __cogent_suffix_of_shallow_shared ++ "\" " ++
              "\"" ++ theoryNm ++ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage stg ++ "\" " ++
              "\"" ++ theoryNm ++ __cogent_suffix_of_deep    ++ __cogent_suffix_of_stage stg ++ "\" Cogent_abstract_functions Cogent_functions"
  , "\\<close>"
  ]


-- join the strings (type, tag or field names) in a way that is unlikely to clash with other names
mangleNames :: [String] -> String
mangleNames = intercalate "__"

defineLemmaBucket :: String -> [String] -> [TheoryDecl I.Type I.Term]
defineLemmaBucket _ [] = []
defineLemmaBucket name lems =
  [ O.LemmasDecl (O.Lemmas (O.TheoremDecl (Just name) []) $ map (\l -> O.TheoremDecl (Just l) []) lems) ]

{-
 - Generate rules for Case, Esac, Con, and Flattened case
 -}
data SCorresCaseData = SCCD { bigType :: String
                            , typeStr :: [String]
                            , tag :: String
                            }
                     | SCED { bigType :: String
                            , typeStr :: [String]
                            , tag :: String
                            }
                     | SCFD { bigType :: String
                            , typeStr :: [String]
                            }
                     | SCCN { tag :: String
                            , bigType :: String
                            }
                     deriving (Show, Eq, Ord)

scorresCaseExpr :: MapTypeName -> TypedExpr t v VarName b -> S.Set SCorresCaseData
scorresCaseExpr m = CC.foldEPre unwrap scorresCaseExpr'
  where
    scorresCaseExpr' (TE t e@(Case (TE bt _) tag (_,_,e1) (_,_,e2)))
      | (tstr@(VariantStr vs):_) <- toTypeStr bt
      , Just bt' <- M.lookup tstr m
      = S.fromList [SCCD bt' vs tag, SCFD bt' vs]
    scorresCaseExpr' (TE t e@(Esac (TE bt@(TSum alts) _)))
      | tag <- fst (P.head (filter (not . snd . snd) alts))
      , (tstr@(VariantStr vs):_) <- toTypeStr bt
      , Just bt' <- M.lookup tstr m
      = S.singleton $ SCED bt' vs tag
    scorresCaseExpr' (TE bt e'@(Con tag e _))
      | (tstr@(VariantStr vs):_) <- toTypeStr bt
      , Just bt' <- M.lookup tstr m
      = S.singleton $ SCCN tag bt'
    scorresCaseExpr' (TE t e) = S.empty
    unwrap (TE t e) = e

data CaseLemmaBuckets = CaseLemmaBuckets [String] [String] [String] [String]

#if __GLASGOW_HASKELL__ < 803
instance Monoid CaseLemmaBuckets where
  mempty = CaseLemmaBuckets [] [] [] []
  mappend (CaseLemmaBuckets as bs cs ds) (CaseLemmaBuckets as' bs' cs' ds') =
    CaseLemmaBuckets (as ++ as') (bs ++ bs') (cs ++ cs') (ds ++ ds')
#else
instance Semigroup CaseLemmaBuckets where
  CaseLemmaBuckets as bs cs ds <> CaseLemmaBuckets as' bs' cs' ds' =
    CaseLemmaBuckets (as ++ as') (bs ++ bs') (cs ++ cs') (ds ++ ds')
instance Monoid CaseLemmaBuckets where
  mempty = CaseLemmaBuckets [] [] [] []
#endif

caseLemmaBuckets :: CaseLemmaBuckets -> [TheoryDecl I.Type I.Term]
caseLemmaBuckets (CaseLemmaBuckets cases esacs flats cons) =
  concat $ P.zipWith defineLemmaBucket
    ["scorres_cases", "scorres_esacs", "scorres_flat_cases", "scorres_cons" ]
    [cases, esacs, flats, cons]

toCaseLemma :: SCorresCaseData -> Writer CaseLemmaBuckets (TheoryDecl I.Type I.Term)
toCaseLemma (SCCD {..}) = let
    thmName = "scorres_case_" ++ mangleNames [bigType, tag]
    propStr = "scorres x x' \\<gamma> \\<xi> \\<Longrightarrow> \n"++
              "(\\<And>v v'. valRel \\<xi> v v' \\<Longrightarrow> "++
                "scorres (match (shallow_tac__var v)) match' (v'#\\<gamma>) \\<xi>) \\<Longrightarrow> \n"++
              "(\\<And>v v'. valRel \\<xi> v v' \\<Longrightarrow> "++
                "scorres (rest (shallow_tac__var v)) rest' (v'#\\<gamma>) \\<xi>) \\<Longrightarrow> \n"++
              "scorres (HOL.Let rest (\\<lambda>co. case_" ++ bigType ++ " " ++ unwords (map shallowCase typeStr) ++
                " x)) (Case x' " ++ tagString ++ " match' rest') \\<gamma> \\<xi>"
    shallowCase tag' | tag == tag' = "match"
                     | otherwise   = "(\\<lambda>x. co (" ++ bigType ++ "." ++ tag' ++ " x))"
    tagString = show $ pretty $ mkString tag
    methods = [ Method "clarsimp" ["simp:", "scorres_def", "shallow_tac__var_def", "valRel_" ++ bigType]
              , Method "erule" ["v_sem_caseE"] ] ++
              (concat $ replicate 2 $
                 [ foldr1 (MethodCompound MethodSeq)
                     [Method "erule" ["allE"], Method "erule" ["impE"], Method "assumption" []]
                 , Method "cases" ["x"] ] ++
                 replicate (P.length typeStr)
                   (Method "force" ["simp:", "valRel_" ++ bigType]))
  in do tell (CaseLemmaBuckets [thmName] [] [] [])
        return $ O.LemmaDecl (O.Lemma False (Just (TheoremDecl (Just thmName) [])) [mkId propStr] $ Proof methods ProofDone)
toCaseLemma (SCED {..}) = let
  thmName = "scorres_esac_"  ++ mangleNames [bigType, tag]
  shallowEsac tag' | tag == tag' = "Fun.id"
                   | otherwise   = "undefined"
  tagString = show $ pretty $ mkString tag
  propStr = "scorres x x' \\<gamma> \\<xi> \\<Longrightarrow> "++
            "scorres (case_" ++ bigType ++ " " ++ unwords (map shallowEsac typeStr) ++
            " x) (Esac x' " ++ tagString ++ ") \\<gamma> \\<xi>"
  methods = [ Method "cases" ["x"],
              Method "auto" ["simp: scorres_def valRel_" ++ bigType ++ " elim!: v_sem_esacE"] ]
 in do tell (CaseLemmaBuckets [] [thmName] [] [])
       return $ O.LemmaDecl (O.Lemma False (Just (TheoremDecl (Just thmName) [])) [mkId propStr] $ Proof methods ProofDone)
toCaseLemma (SCFD {..}) = let
    thmName          = "scorres_flat_case_" ++ bigType

    shallow_cont tag = "shallow_" ++ tag
    tag_at       ix  = "tag_" ++ show ix
    deep_cont    ix  = "deep_" ++ show ix

    all_tags         = typeStr
    all_ixs          = [1 .. P.length all_tags]

    bound            = ["x", "x'", "\\<gamma>", "\\<xi>"] ++ map shallow_cont typeStr ++ map tag_at all_ixs ++ map deep_cont all_ixs

    deep_cont_of_tag  tag        = deep_cont_of_tag' tag all_ixs
    deep_cont_of_tag' tag []     = "undefined"
    deep_cont_of_tag' tag (i:is) = unwords ["if", tag_at i, "=", show $ pretty $ mkString tag
                                           , "then", deep_cont i
                                           , "else", deep_cont_of_tag' tag is]

    gamma_of_ix    ix v'         = "(" ++ v' ++ " # " ++ concat (replicate (ix - 1) ("VSum " ++ tag_at ix ++ " " ++ v' ++ " # ")) ++ "\\<gamma>)"

    gamma_of_tag  tag v'         = gamma_of_tag' tag v' all_ixs
    gamma_of_tag' tag v' []      = "undefined"
    gamma_of_tag' tag v' (i:is)  = unwords ["if", tag_at i, "=", show $ pretty $ mkString tag
                                           , "then", gamma_of_ix i v'
                                           , "else", gamma_of_tag' tag v' is]

    scorres_assumption tag       = "(\\<And>v v'. valRel \\<xi> v v' \\<Longrightarrow> scorres " ++
                                   unwords ["(" ++ shallow_cont tag
                                           , "(shallow_tac__var v))"
                                           , "(" ++ deep_cont_of_tag tag ++ ")"
                                           , "(" ++ gamma_of_tag tag "v'" ++ ")"
                                           , "\\<xi>"] ++
                                   ") \\<Longrightarrow>"

    deep_case scrut []           = ""
    deep_case scrut [ix]         = "(Let (Esac " ++ scrut ++ " " ++ tag_at ix ++ ") " ++ deep_cont ix ++ ")"
    deep_case scrut (ix:ixs)     = "(Case " ++ scrut ++ " " ++ tag_at ix ++ " " ++ deep_cont ix ++ " (" ++ deep_case "(Var 0)" ixs ++ "))"

    propStr = "\\<And> " ++ unwords bound ++ ".\n" ++
              "scorres x x' \\<gamma> \\<xi> \\<Longrightarrow> \n"++
              unlines (map scorres_assumption all_tags) ++
              "scorres (case_" ++ bigType ++ " " ++ unwords (map shallow_cont all_tags) ++ " x)" ++
                        deep_case "x'" all_ixs ++ " \\<gamma> \\<xi>"

    m_erule e           = Method "erule" [e]

    m_pre               = Method "clarsimp" ["simp:", "scorres_def", "shallow_tac__var_def", "valRel_" ++ bigType]
    m_elim_arg_relation = foldr1 (MethodCompound MethodSeq) [m_erule "allE", m_erule "impE", Method "assumption" []]
    m_case_shallow_arg  = Method "case_tac" ["x"]
    m_force_simps       = replicate (P.length all_tags)
                        $ Method "force" ["simp:", "valRel_" ++ bigType]

    -- TODO: it might be possible to lift out m_elim_arg_relation, m_case_shallow_arg and m_force_simps to a separate lemma statement.
    m_solve_case        = [ m_erule "v_sem_caseE", m_elim_arg_relation, m_case_shallow_arg ] ++ m_force_simps
    m_solve_esac        = [ m_erule "v_sem_letE", m_erule "v_sem_esacE", m_erule "v_sem_varE", m_elim_arg_relation, m_case_shallow_arg ] ++ m_force_simps

    methods = [m_pre] ++ concat (replicate (P.length all_tags - 1) m_solve_case) ++ m_solve_esac
  in do tell (CaseLemmaBuckets [] [] [thmName] [])
        return $ O.LemmaDecl (O.Lemma False (Just (TheoremDecl (Just thmName) [])) [mkId propStr] $ Proof methods ProofDone)
toCaseLemma (SCCN {..}) = let
  thmName = "scorres_con_" ++ mangleNames [bigType, tag]
  btTag = mkId $ bigType ++ "." ++ tag
  tagString = mkString tag
  thmProp = [isaTerm| scorres x x' \<gamma> \<xi> |]
      `imp` [isaTerm| scorres ($btTag x) (Con ts $tagString x') \<gamma> \<xi> |]
  methods = [Method "erule" ["scorres_con"], Method "simp" []]
 in do tell (CaseLemmaBuckets [] [] [] [thmName])
       return $ O.LemmaDecl (O.Lemma False (Just (TheoremDecl (Just thmName) [])) [thmProp] $ Proof methods ProofDone)

scorresCaseDef :: MapTypeName -> Definition TypedExpr VarName b -> S.Set SCorresCaseData
scorresCaseDef m (FunDef _ fn ts ls ti to e) = scorresCaseExpr m e
scorresCaseDef m (_) = S.empty


{-
 - Generate rules for Struct, and shallow_tac_rec_field (which is then used to obtain Take, Put and Member rules).
 -}

-- simply generate rules for all types and fields; we expect the program to use most of them
scorresStructLemma :: TypeName -> [FieldName] -> (String, TheoryDecl I.Type I.Term)
scorresStructLemma name fields = let
  thmName = "scorres_struct_" ++ name
  varNames prefix = [ prefix ++ "_" ++ field | field <- fields ]
  all_names = ["\\<gamma>", "\\<xi>"] ++ (varNames "s") ++ (varNames "d")
  assums = [ "scorres " ++ x ++ " " ++ y ++ " \\<gamma> \\<xi>"
           | (x, y) <- P.zip (varNames "s") (varNames "d") ]
  concl = "scorres (" ++ name ++ ".make " ++ unwords (varNames "s") ++ ") " ++
          "(Struct ns ts [" ++ intercalate ", " (varNames "d") ++ "]) \\<gamma> \\<xi>"
  prop = "\\<And>" ++ intercalate " " all_names ++ ".\n" ++ intercalate " \\<Longrightarrow>\n" (assums ++ [concl])
  method = Method "clarsimp" ["simp:", "scorres_def", "valRel_" ++ name, name ++ ".defs",
                              "elim!:", "v_sem_elims"]
  in (thmName, O.LemmaDecl (O.Lemma False (Just (TheoremDecl (Just thmName) [])) [mkId prop] $ Proof [method] ProofDone))

scorresStructFieldLemma :: TypeName -> [FieldName] -> FieldIndex -> (String, TheoryDecl I.Type I.Term)
scorresStructFieldLemma name fields n = let
  field = fields !! n
  thmName = "shallow_tac_rec_field_" ++ mangleNames [name, field]
  polyRecType = "(" ++ intercalate ", " [ "'t_" ++ fld | fld <- fields] ++ ") " ++ name
  prop = "shallow_tac_rec_field \\<xi> " ++
         "(" ++ name ++ "." ++ field ++ subSymStr "f" ++ " :: " ++ polyRecType ++ " \\<Rightarrow> 't_" ++ field ++ ") " ++
         name ++ "." ++ field ++ subSymStr "f" ++ "_update " ++ show n
  method = Method "fastforce" ["intro!:", "shallow_tac_rec_fieldI", "simp:", "valRel_" ++ name]
  in (thmName, O.LemmaDecl (O.Lemma False (Just (TheoremDecl (Just thmName) [])) [mkId prop] $ Proof [method] ProofDone))

scorresStructLemmas, scorresFieldLemmas :: [TypeStr] -> MapTypeName -> [TheoryDecl I.Type I.Term]
scorresStructLemmas types tmap =
  let (structLemmaNames, structLemmas) = P.unzip $
        [ scorresStructLemma name fields
        | rec@(RecordStr fields) <- types,
          name <- maybeToList $ M.lookup rec tmap ]
  in structLemmas ++
     defineLemmaBucket "scorres_structs" structLemmaNames

scorresFieldLemmas types tmap =
  let (fieldLemmaNames, fieldLemmas) = P.unzip $
        [ scorresStructFieldLemma name fields field
        | rec@(RecordStr fields) <- types,
          name <- maybeToList $ M.lookup rec tmap,
          field <- [0 .. P.length fields - 1] ]
  in fieldLemmas ++
     defineLemmaBucket "scorres_rec_fields" fieldLemmaNames



-- Left is concrete funs, Right is shared
shallowDefinition :: (Show b,Eq b) => Definition TypedExpr VarName b -> SG ([Either (TheoryDecl I.Type I.Term) (TheoryDecl I.Type I.Term)], Maybe FunName)
shallowDefinition (FunDef _ fn ps _ ti to e) =
    local (typarUpd typar) $ do
    e' <- shallowExpr e
    tuples <- asks recoverTuples
    let e'' = if tuples && __cogent_fsimplify_shallow_tuples then simplifyTerm e' else e'
    types <- shallowType $ TFun ti to
    let term = [isaTerm| $fn' $arg0 \<equiv> $e'' |]
    pure ([Left $ Definition (Def (Just (Sig (snm fn) (Just types))) term)], Just $ snm fn)
  where fn'   = mkId (snm fn)
        arg0  = mkId $ snm $ D.freshVarPrefix ++ "0"
        typar = map fst $ Vec.cvtToList ps
shallowDefinition (AbsDecl _ fn ps _ ti to) =
    local (typarUpd typar) $ do
      types <- shallowType $ TFun ti to
      pure ([Right $ ConstsDecl $ Consts (Sig (snm fn) (Just types))], Nothing)
  where typar = map fst $ Vec.cvtToList ps
shallowDefinition (TypeDef tn ps Nothing) =
    local (typarUpd typar) $ pure ([Right $ TypeDeclDecl $ TypeDecl tn typar], Nothing)
  where typar = Vec.cvtToList ps
shallowDefinition (TypeDef tn ps (Just t)) =
    local (typarUpd typar) $ (, Nothing) <$> (map Right <$> shallowTypeDef tn typar t)
  where typar = Vec.cvtToList ps

shallowDefinitions :: (Show b,Eq b) => [Definition TypedExpr VarName b] -> SG ([Either (TheoryDecl I.Type I.Term) (TheoryDecl I.Type I.Term)], [FunName])
shallowDefinitions = (((concat *** catMaybes) . P.unzip) <$>) . mapM ((varNameGen .= 0 >>) . shallowDefinition)

-- | Returns @(shallow, shallow_shared, scorres, type names)@
shallowFile :: (Show b, Eq b) => String -> Stage -> [Definition TypedExpr VarName b]
            -> SG (Theory I.Type I.Term, Theory I.Type I.Term, Theory I.Type I.Term, MapTypeName)
shallowFile thy stg defs = do
  t <- asks typeStrs
  tuples <- asks recoverTuples
  let (typedecls,defs') = partition isAbsTyp defs
  (isatdecls,_) <- shallowDefinitions typedecls  -- should all be Right
  (isatypes, valrels, fullTypeMap) <- shallowTypeFromTable
  (isadefs,fnames) <- shallowDefinitions defs'
  fullTypes <- asks typeStrs
  let structLemmas = scorresStructLemmas fullTypes fullTypeMap ++ scorresFieldLemmas fullTypes fullTypeMap
  let (sccds,buckets) = runWriter (mapM toCaseLemma $ S.toList $ S.unions $ map (scorresCaseDef fullTypeMap) defs')
      shthy = thy ++ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage stg ++ (if tuples then __cogent_suffix_of_recover_tuples else "")
      dpthy = thy ++ __cogent_suffix_of_deep    ++ __cogent_suffix_of_stage stg
      ssthy = thy ++ __cogent_suffix_of_shallow_shared ++ (if tuples then __cogent_suffix_of_recover_tuples else "")
      scthy = thy ++ __cogent_suffix_of_scorres ++ __cogent_suffix_of_stage stg
      shalImports = TheoryImports [ssthy]
      shrdImports = TheoryImports [ "Cogent.Util"
                                  , "CogentShallow.ShallowUtil" ]
      scorImports = TheoryImports [shthy, dpthy, "CogentShallow.Shallow_Tac"]
      strippedTypeMap = M.filterWithKey (\ts _ -> ts `S.member` S.fromList fullTypes) fullTypeMap
  return $ ( Theory shthy shalImports $ lefts isadefs
           , Theory ssthy shrdImports $ rights isatdecls ++ isatypes ++ rights isadefs
           , Theory scthy scorImports $
               valrels ++
               [ContextDecl (Context "shallow" $
                               sccds ++
                               caseLemmaBuckets buckets ++
                               structLemmas ++
                               [TheoryString (mlFragment thy stg)])]
           , strippedTypeMap
           )

-- | Returns @(shallow, shallow_shared, scorres, type names)@
shallow :: (Show b,Eq b) => Bool -> String -> Stage -> [Definition TypedExpr VarName b] -> String -> (Doc, Doc, Doc, MapTypeName)
shallow recoverTuples thy stg defs log =
  let (shal,shrd,scor,typeMap) = fst $ evalRWS (runSG (shallowFile thy stg defs))
                                               (SGTables (st defs) (stsyn defs) [] recoverTuples)
                                               (StateGen 0 M.empty [])
      header = (string ("(*\n" ++ log ++ "\n*)\n") L.<$$>)
  in (header (if recoverTuples then I.prettyPlus shal else pretty shal), header $ pretty shrd, header $ pretty scor, typeMap)

genConstDecl :: CC.CoreConst TypedExpr -> SG (TheoryDecl I.Type I.Term)
genConstDecl (vn, te@(TE ty expr)) = do
  e <- shallowExpr te
  t <- shallowType ty
  let nm = mkId (snm vn)
      term = [isaTerm| $nm \<equiv> $e |]
  pure $ Definition (Def (Just (Sig (snm vn) (Just t))) term)

shallowConsts :: Bool -> String -> Stage -> [CC.CoreConst TypedExpr] -> [Definition TypedExpr VarName b] -> String -> Doc
shallowConsts recoverTuples thy stg consts defs log =
  header $ pretty (Theory (thy ++ __cogent_suffix_of_shallow_consts ++ __cogent_suffix_of_stage stg ++
                           (if recoverTuples then __cogent_suffix_of_recover_tuples else ""))
                   (TheoryImports [thy ++ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage stg ++
                                   (if recoverTuples then __cogent_suffix_of_recover_tuples else "")])
                   (genConstTheoryDecls consts defs))
 where genConstTheoryDecls cs defs = fst $ evalRWS (runSG $ shallowConsts cs)
                                     (SGTables (st defs) (stsyn defs) [] recoverTuples)
                                     (StateGen 0 M.empty [])
       shallowConsts = mapM genConstDecl
       header = (string ("(*\n" ++ log ++ "\n*)\n") L.<$$>)



{-
  Generate ShallowTuples proof on desugared AST.

  The theory file creates two lemma buckets,
  one for the helper lemmas (ShallowTuplesRules_proofname) and
  one to store the refinement proofs (ShallowTuplesThms_proofname).

  Currently, no ML code is used; the proofs are written directly.
  FIXME: lemmas for abstract functions are currently sorried.
-}

shallowTuplesProof :: String -> String -> String -> String -> String ->
                      MapTypeName -> [Definition TypedExpr VarName b] -> String -> Doc
shallowTuplesProof baseName sharedDefThy defThy tupSharedDefThy tupDefThy typeMap defs log =
  header $ pretty (Theory (mkProofName baseName $ Just __cogent_suffix_of_shallow_tuples_proof)
                   (TheoryImports [defThy, tupDefThy,
                                   "CogentShallow.ShallowTuples"])
                   (theorySetup ++
                    dataRelations ++
                    proofs) :: Theory I.Type I.Term)
  where
    thyBase = mkProofName baseName Nothing
    ruleBucket = "ShallowTuplesRules_" ++ thyBase
    proofBucket = "ShallowTuplesThms_" ++ thyBase
    header = (string ("(*\n" ++ log ++ "\n*)\n") L.<$$>)

    -- Set up the lemma buckets.
    theorySetup =
      [ TheoryString $ setupBucket ruleBucket
      , TheoryString $ setupBucket proofBucket
      ]
    setupBucket name = unlines
      [ "ML \\<open>"
      , "structure " ++ name ++ " ="
      , "  Named_Thms ("
      , "    val name = Binding.name \"" ++ name ++ "\""
      , "    val description = \"\""
      , "  )"
      , "\\<close>"
      , "setup \\<open> " ++ name ++ ".setup \\<close>"
      ]

    {- Define shallow_tuples_rel instances and proof rules for all our types.
       We expect that typeMap contains all types, and that the tupled shallow embedding
       uses the same type names (except for tuples, which are omitted). -}
    {- The rules for record fields and the variant case are put into the proof bucket instead of the rule bucket.
       That makes them available in the main proof iteration in proofBucket ++ "[THEN shallow_tuples_rel_funD].
       This is necessary for higher order functions where an applied function can be taken from a record field
       or specified by a case expression. -}
    -- FIXME: use less TheoryString?
    dataRelations = map makeRel $ M.toList typeMap
      where makeRel (RecordStr fields, typeName) =
              if isRecTuple fields
              {- record, tuple -}
              then let
                fullName = sharedDefThy ++ "." ++ typeName
                fullType = polyType fullName "x" (P.length fields)
                tupleFullType = intercalate " \\<times> " ["'xt" ++ show n | n <- [1 .. P.length fields]]
                relName = "shallow_tuples_rel_" ++ typeName
                fieldEquivs = mapInitLast (++ " \\<and>") (++ "\"") $
                              [ "shallow_tuples_rel (" ++ fullName ++ "." ++ isaRecField field ++ " x) " ++
                                tupAccess (P.length fields) (f :: Int) "xt"
                              | (f, field) <- P.zip [1..] fields ]

                constrAssms = mapInitLast (++ ";") id $
                              [ "shallow_tuples_rel x" ++ show f ++ " xt" ++ show f
                              | f <- [1 .. P.length fields] ]
                in TheoryString $ unlines $
                   -- definition
                   [ "overloading " ++ relName ++ " \\<equiv> shallow_tuples_rel begin"
                   , "  definition \"" ++ relName ++ " (x :: " ++ fullType ++ ") (xt :: " ++ tupleFullType ++ ") \\<equiv>"
                   ] ++
                   indent 4 fieldEquivs ++
                   [ "end" ] ++

                   -- constructor
                   [ "lemma " ++ mangleNames ["shallow_tuples_rule", typeName ++ "_make"] ++ " [" ++ ruleBucket ++ "]:"
                   , "  \"\\<lbrakk>"
                   ] ++
                   indent 5 constrAssms ++
                   [ "  \\<rbrakk> \\<Longrightarrow> shallow_tuples_rel " ++
                     "(" ++ fullName ++ ".make " ++ unwords ["x" ++ show f | f <- [1 .. P.length fields]] ++ ") " ++
                     "(" ++ intercalate ", " ["xt" ++ show f | f <- [1 .. P.length fields]] ++ ")\""
                   , "  by (simp add: shallow_tuples_rel_" ++ typeName ++ "_def " ++
                     fullName ++ ".defs Px_px)"
                   ] ++

                   -- fields
                   concat [
                     [ "lemma " ++ mangleNames ["shallow_tuples_rule", typeName, field] ++ " [" ++ proofBucket ++ "]:"
                     , "  \"shallow_tuples_rel (x :: " ++ fullType ++ ") (xt :: " ++ tupleFullType ++ ") \\<Longrightarrow>"
                     , "   shallow_tuples_rel (" ++ fullName ++ "." ++ field ++ " x) " ++
                       tupAccess (P.length fields) f "xt" ++ "\""
                     , "  by (simp add: shallow_tuples_rel_" ++ typeName ++ "_def)"
                     ] | (f, field) <- P.zip [(1::Int) ..] (map isaRecField fields)
                   ]

                   -- no field updates for tuples (as they are always unboxed, hence immutable)

              {- record, record -}
              else let
                fullName = sharedDefThy ++ "." ++ typeName
                fullType = polyType fullName "x" (P.length fields)
                tupleFullName = tupSharedDefThy ++ "." ++ typeName
                tupleFullType = polyType tupleFullName "xt" (P.length fields)
                relName = "shallow_tuples_rel_" ++ typeName
                fieldEquivs = mapInitLast (++ " \\<and>") (++ "\"") $
                              [ "shallow_tuples_rel (" ++ fullName ++ "." ++ isaRecField field ++ " x) " ++
                                "(" ++ tupleFullName ++ "." ++ isaRecField field ++ " xt)"
                              | field <- fields ]

                constrAssms = mapInitLast (++ ";") id $
                              [ "shallow_tuples_rel x" ++ show f ++ " xt" ++ show f
                              | f <- [1 .. P.length fields] ]
                in TheoryString $ unlines $
                   -- definition
                   [ "overloading " ++ relName ++ " \\<equiv> shallow_tuples_rel begin"
                   , "  definition \"" ++ relName ++ " (x :: " ++ fullType ++ ") (xt :: " ++ tupleFullType ++ ") \\<equiv>"
                   ] ++
                   indent 4 fieldEquivs ++
                   [ "end" ] ++

                   -- constructor
                   [ "lemma " ++ mangleNames ["shallow_tuples_rule_make", typeName] ++ " [" ++ ruleBucket ++ "]:"
                   , "  \"\\<lbrakk>"
                   ] ++
                   indent 5 constrAssms ++
                   [ "  \\<rbrakk> \\<Longrightarrow> shallow_tuples_rel " ++
                     "(" ++ fullName ++ ".make " ++ unwords ["x" ++ show f | f <- [1 .. P.length fields]] ++ ") " ++
                     "\\<lparr>" ++ tupleFullName ++ "." ++ isaRecField (P.head fields) ++ " = xt1" ++ 
                     unwords [", " ++ field ++ " = xt" ++ show f | (f, field) <- P.zip [(2::Int) ..] (map isaRecField $ P.tail fields)] ++ "\\<rparr>\""
                   , "  by (simp add: shallow_tuples_rel_" ++ typeName ++ "_def " ++
                     fullName ++ ".defs " ++ tupleFullName ++ ".defs)"
                   ] ++

                   -- fields
                   concat [
                     [ "lemma " ++ mangleNames ["shallow_tuples_rule", typeName, field] ++ " [" ++ proofBucket ++ "]:"
                     , "  \"shallow_tuples_rel (x :: " ++ fullType ++ ") (xt :: " ++ tupleFullType ++ ") \\<Longrightarrow>"
                     , "   shallow_tuples_rel (" ++ fullName ++ "." ++ field ++ " x) (" ++ tupleFullName ++ "." ++ field ++ " xt)\""
                     , "  by (simp add: shallow_tuples_rel_" ++ typeName ++ "_def)"
                     ] | field <- map isaRecField fields
                   ] ++

                   -- field updates
                   concat [
                     [ "lemma " ++ mangleNames ["shallow_tuples_rule", typeName, field, "update"] ++ " [" ++ ruleBucket ++ "]:"
                     , "  \"\\<lbrakk> shallow_tuples_rel (x :: " ++ fullType ++ ") (xt :: " ++ tupleFullType ++ ");"
                     , "     shallow_tuples_rel v vt"
                     , "   \\<rbrakk> \\<Longrightarrow>"
                     , "   shallow_tuples_rel (" ++ fullName ++ "." ++ field ++ "_update (\\<lambda>_. v) x) " ++
                       "(" ++ tupleFullName ++ "." ++ field ++ "_update (\\<lambda>_. vt) xt)\""
                     , "  by (simp add: shallow_tuples_rel_" ++ typeName ++ "_def)"
                     ] | field <- map isaRecField fields
                   ]

            {- variant -}
            makeRel (VariantStr tags, typeName) = let
              fullName = sharedDefThy ++ "." ++ typeName
              fullType = polyType fullName "x" (P.length tags)
              tupleFullName = tupSharedDefThy ++ "." ++ typeName
              tupleFullType = polyType tupleFullName "xt" (P.length tags)
              relName = "shallow_tuples_rel_" ++ typeName
              tagEquivs = mapInitLast (++ " \\<or>") (++ "\"") $
                          [ "(\\<exists>v vt. shallow_tuples_rel v vt \\<and> " ++
                            "x = " ++ fullName ++ "." ++ tag ++ " v \\<and> " ++
                            "xt = " ++ tupleFullName ++ "." ++ tag ++ " vt)"
                          | tag <- tags ]

              handlers baseVar = [baseVar ++ show n | n <- [1 .. P.length tags]]
              caseTerm = sharedDefThy ++ ".case_" ++ typeName
              tupleCaseTerm = tupSharedDefThy ++ ".case_" ++ typeName
              caseAssms = mapInitLast (++ ";") id $
                          [ "\\<And>v vt. shallow_tuples_rel v vt \\<Longrightarrow> " ++
                            "shallow_tuples_rel (" ++ f ++ " v) (" ++ ft ++ " vt)"
                          | (f, ft) <- P.zip (handlers "f") (handlers "ft") ]
              in TheoryString $ unlines $
                 -- definition
                 [ "overloading " ++ relName ++ " \\<equiv> shallow_tuples_rel begin"
                 , "  definition \"" ++ relName ++ " (x :: " ++ fullType ++ ") (xt :: " ++ tupleFullType ++ ") \\<equiv>"
                 ] ++
                 indent 4 tagEquivs ++
                 [ "end" ] ++

                 -- case
                 [ "lemma " ++ mangleNames ["shallow_tuples_rule_case", typeName] ++ " [" ++ proofBucket ++ "]:"
                 , "  \"\\<lbrakk> shallow_tuples_rel x xt;"
                 ] ++
                 indent 5 caseAssms ++
                 [ "   \\<rbrakk> \\<Longrightarrow>"
                 , "   shallow_tuples_rel (" ++ unwords ([caseTerm] ++ handlers "f" ++ ["x"]) ++ ") " ++
                   "(" ++ unwords ([tupleCaseTerm] ++ handlers "ft" ++ ["xt"]) ++ ")\""
                 , "  by (fastforce simp: shallow_tuples_rel_" ++ typeName ++ "_def"
                 , "        split: " ++ fullName ++ ".splits " ++ tupleFullName ++ ".splits)"
                 ] ++

                 -- constructors
                 concat [
                   [ "lemma " ++ mangleNames ["shallow_tuples_rule", typeName, tag] ++ " [" ++ ruleBucket ++ "]:"
                   , "  \"shallow_tuples_rel x xt \\<Longrightarrow>"
                   , "   shallow_tuples_rel (" ++ fullName ++ "." ++ tag ++ " x) (" ++ tupleFullName ++ "." ++ tag ++ " xt)\""
                   , "  by (simp add: shallow_tuples_rel_" ++ typeName ++ "_def)"
                   ] | tag <- tags
                 ]

            isaRecField = (++ subSymStr "f") -- sync with getRecordFieldName
            
            tupAccess siz i t = 
                if __cogent_fsimplify_shallow_tuples
                   then tupAccOuter siz i ++ tupAccInner siz i ++ t ++ tupAccClose siz i
                   else "(P" ++ show siz ++ "_" ++ isaRecField ("p" ++ show i) ++ " " ++ t ++ ")"
            tupAccOuter siz i = if siz == i then tupAccSnd else tupAccFst
            tupAccInner siz i = concat $ replicate (if siz == i then i-2 else i-1) tupAccSnd
            tupAccClose siz i = concat $ replicate (if siz == i then i-1 else i) ")"
            tupAccFst = "(prod.fst "
            tupAccSnd = "(prod.snd "

            polyType name baseVar numArgs =
              "(" ++ intercalate ", " ["'" ++ baseVar ++ show n | n <- [1 .. numArgs]] ++ ") " ++ name

    indent k = map (replicate k ' ' ++)

    proofs = concatMap makeProof defs
      where makeProof (FunDef _ (snm -> funName) _ _ _ _ _) = let
              fullName = defThy ++ "." ++ funName
              funDef = snm fullName ++ "_def"
              tupleFullName = tupDefThy ++ "." ++ funName
              tupleFunDef = tupleFullName ++ "_def"
              in return $ TheoryString $ unlines $
                 [ "lemma " ++ mangleNames ["shallow_tuples", funName] ++ " [" ++ proofBucket ++ "]:"
                 , "  \"shallow_tuples_rel " ++ fullName ++ " " ++ tupleFullName ++ "\""
                 , "  apply (rule shallow_tuples_rel_funI)"
                 , "  apply (unfold " ++ unwords [funDef, tupleFunDef, "id_def" {- in Esacs -}] ++ ")"]
                 ++ (if __cogent_fsimplify_shallow_tuples 
                       -- fully substitute all bindings so that the simplified tuple terms can be compared with the core terms
                       then ["  apply ((unfold " ++ "take" ++ (subSymStr "cogent") ++ "_def " 
                           ++ "Let" ++ (subSymStr "ds") ++ "_def " ++ "Let_def split_def)?,(simp only: fst_conv snd_conv)?)"]
                       else []) ++
                   -- main iteration
                 [ "  by (assumption |"
                 , "      rule shallow_tuples_basic_bucket " ++ ruleBucket
                 , "           " ++ proofBucket ++ " " ++ proofBucket ++ "[THEN shallow_tuples_rel_funD])+"
                 ]

            makeProof (AbsDecl _ (snm -> funName) _ _ _ _) = let
              fullName = sharedDefThy ++ "." ++ funName
              tupleFullName = tupSharedDefThy ++ "." ++ funName
              in return $ TheoryString $ unlines $
                 [ "lemma " ++ mangleNames ["shallow_tuples", funName] ++ " [" ++ proofBucket ++ "]:"
                 , "  \"shallow_tuples_rel " ++ fullName ++ " " ++ tupleFullName ++ "\""
                 , "  sorry"
                 ]

            makeProof _ = []

mapInitLast :: (a -> a) -> (a -> a) -> [a] -> [a]
mapInitLast init last [] = []
mapInitLast init last [x] = [last x]
mapInitLast init last (x:xs) = init x : mapInitLast init last xs
