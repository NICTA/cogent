
--
-- Copyright 2019, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}

module Cogent.TypeCheck.SMT where

import Cogent.Compiler
import Cogent.Common.Syntax as S
import Cogent.Common.Types
import Cogent.PrettyPrint (indent')
import Cogent.TypeCheck.Base
import Cogent.Surface as S

import Control.Applicative
import Control.Monad.IO.Class
import Data.SBV as SMT
import Data.SBV.Dynamic as SMT
import Text.PrettyPrint.ANSI.Leijen (pretty)

typeToSmt :: TCType -> SMT.Kind
typeToSmt (T (TCon "Bool" [] Unboxed)) = KBool
typeToSmt (T (TCon n [] Unboxed))
  = let w = if | n == "U8"  -> 8
               | n == "U16" -> 16
               | n == "U32" -> 32
               | n == "U64" -> 64
     in KBounded False w
typeToSmt (T (TCon "String" [] Unboxed)) = KString
typeToSmt (T (TTuple ts))  = KTuple $ map typeToSmt ts
typeToSmt (T (TUnit))      = KTuple []
typeToSmt t = __impossible $ "typeToSmt: unsupported type in SMT:\n" ++ show (indent' $ pretty t)

sexprToSmt :: TCSExpr -> Symbolic SVal
sexprToSmt (SU t x) = mkSymVar ('?':show x) (typeToSmt t)
sexprToSmt (SE t (PrimOp op [e])) = liftA (uopToSmt op) (sexprToSmt e)
sexprToSmt (SE t (PrimOp op [e1,e2])) = liftA2 (bopToSmt op) (sexprToSmt e1) (sexprToSmt e2)
sexprToSmt (SE t (Var vn)) = return $ svUninterpreted (typeToSmt t) vn Nothing []  -- For now we make variables uninterpreted
sexprToSmt (SE t (IntLit i)) = return $ svInteger (typeToSmt t) i
sexprToSmt (SE t (BoolLit b)) = return $ svBool b
sexprToSmt (SE t (If e _ th el)) = svIte <$> sexprToSmt e <*> sexprToSmt th <*> sexprToSmt el
sexprToSmt (SE t (Upcast e)) = sexprToSmt e
sexprToSmt (SE t (Annot e _)) = sexprToSmt e
sexprToSmt e = __todo $ "sexprToSmt: unsupported expression in SMT:\n" ++ show (indent' $ pretty e)

-- type SmtM a = StateT (UVars, EVars) V.Symbolic a

bopToSmt :: OpName -> (SVal -> SVal -> SVal)
bopToSmt = \case
  "+"   -> svPlus
  "-"   -> svMinus
  "*"   -> svTimes
  "/"   -> svDivide
  "%"   -> svQuot  -- NOTE: the behaviour of `svDivide` and `svQuot` here. / zilinc
                   -- http://hackage.haskell.org/package/sbv-8.5/docs/Data-SBV-Dynamic.html#v:svDivide
  "&&"  -> svAnd
  "||"  -> svOr
  ".&." -> svAnd
  ".|." -> svOr
  ".^." -> svXOr
  "<<"  -> svShiftLeft
  ">>"  -> svShiftRight
  "=="  -> svEqual
  "/="  -> svNotEqual
  ">"   -> svGreaterThan
  "<"   -> svLessThan
  ">="  -> svGreaterEq
  "<="  -> svLessEq

uopToSmt :: OpName -> (SVal -> SVal)
uopToSmt = \case
  "not"        -> svNot
  "complement" -> svNot


-- ----------------------------------------------------------------------------
-- Helpers
--

mkSymVar :: String -> SMT.Kind -> Symbolic SVal
mkSymVar nm k = symbolicEnv >>= liftIO . svMkSymVar Nothing k (Just nm)

bvAnd :: [SVal] -> SVal
bvAnd = foldr (svAnd) svTrue


