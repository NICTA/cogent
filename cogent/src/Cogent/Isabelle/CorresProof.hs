--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

module Cogent.Isabelle.CorresProof where

import Cogent.Common.Syntax (CoreFunName, unCoreFunName)
import Cogent.Compiler
import Cogent.Util (toCName)

import Data.List (intercalate)
-- import Isabelle.ExprTH
import Isabelle.InnerAST as I
import Isabelle.OuterAST as O
import Cogent.Isabelle.IsabelleName
import System.FilePath ((</>))
import qualified Text.PrettyPrint.ANSI.Leijen as L

corresProof :: String -> String -> [CoreFunName] -> Maybe [CoreFunName] -> String -> L.Doc
corresProof thy cfile fns ent log =
  let fns' = map (toCName . unCoreFunName) fns
      header = (L.string ("(*\n" ++ log ++ "\n*)\n") L.<$>)
      theory = O.Theory { thyName = thy ++ __cogent_suffix_of_corres_proof
                        , thyImports = imports thy
                        , thyBody = [TheoryString . unlines $
                                     sanityCheck ++
                                     setupFunctionValRel thy ++
                                     context thy cfile fns' ent]
                        } :: O.Theory I.Type I.Term
   in header $ L.pretty theory

imports :: String -> TheoryImports
imports thy = TheoryImports
  [ thy ++ __cogent_suffix_of_corres_setup
  , "CogentCRefinement.Corres_Tac"
  , "CogentCRefinement.CogentHigherOrder"
  , "CogentCRefinement.Cogent_Corres_Sanity_Check"
  ]

sanityCheck :: [String]
sanityCheck =
  [ "ML \\<open>"
  , "Cogent_Corres_Sanity_Check.check_all Cogent_functions Cogent_abstract_functions @{context}"
  , "\\<close>"
  ]

setupFunctionValRel :: String -> [String]
setupFunctionValRel thy =
  [ "(* Generate value relation for function pointers."
  , " * We get a big disjunction of the form"
  , " *   val_rel f f' \\<equiv>"
  , " *       (f = Fun f1 \\<and> f' = FUN_ENUM_f1)"
  , " *     \\<or> (f = Fun f2 \\<and> f' = FUN_ENUM_f2)"
  , " *     \\<or> ..."
  , " *)"
  , "setup \\<open>"
  , "let fun C_to_Cogent_name f ="
  , "      if String.isSuffix \"'\" f then C_to_Cogent_name (unsuffix \"'\" f)"
  , "      else if String.isSuffix \"_prime\" f then C_to_Cogent_name (unsuffix \"_prime\" f)"
  , "      else f"
  , "in"
  , "maps (fn t => case Thm.prop_of t of"
  , "  Const (@{const_name Pure.eq}, _) $ (tag_term as Const (tag, _)) $ _ =>"
  , "    let val tag' = Long_Name.base_name tag"
  , "        val fun_name = C_to_Cogent_name (unprefix \"FUN_ENUM_\" tag')"
  , "    in if member (op=) Cogent_functions fun_name"
  , " (* XXX: dodgy hack: x_fresh_cogent and uv_fresh_cogent should both be fresh names and must be bound in the definition below."
  , "    This will fail if there is a function called x_fresh_cogent. *) "
  , "       then [@{mk_term \"x_fresh_cogent = sint (?tag :: 32 signed word) \\<and> uv_fresh_cogent = UFunction (?fun :: string expr) []\""
  , "               (tag, fun)} (tag_term, Syntax.read_term @{context} (\"" ++ thy ++ "_TypeProof.\" ^ fun_name))]"
  , "       else [@{mk_term \"x_fresh_cogent = sint (?tag :: 32 signed word) \\<and> uv_fresh_cogent = UAFunction (?fun :: string) []\""
  , "               (tag, fun)} (tag_term, HOLogic.mk_string fun_name)]"
  , "    end"
  , "  | _ => raise TERM (\"cogent_function_val_rel gen: couldn't parse FUN_ENUM def\", [Thm.prop_of t])"
  , "  ) @{thms untyped_func_enum_defs}"
  , "|> (fn xs => case xs of [] => @{term True}"
  , "                      | _  => fold (fn a => fn b => @{term disj} $ a $ b) (tl xs) (hd xs))"
  , "|> (fn def => @{mk_term \"cogent_function_val_rel uv_fresh_cogent x_fresh_cogent \\<equiv> ?def\" def} def)"
  , "|> strip_type |> Syntax.check_term @{context}"
  , "|> (fn def => Global_Theory.add_defs true [((Binding.name \"cogent_function_val_rel\", def), [])] #> snd)"
  , "end"
  , "\\<close>"
  ]

context :: String -> String -> [String] -> Maybe [CoreFunName] -> [String]
context thy cfile fns ent =
  [ "context " ++ thy ++ " begin"
  , ""
  , "declare cogent_function_val_rel[ValRelSimp]"
  , ""
  , "ML \\<open>"
  , "  fun corres_tac_local verbose ctxt"
  , "         (typing_tree : thm tree)"
  , "         (fun_defs : thm list)"
  , "         (absfun_corres : thm list)"
  , "         (fun_corres : thm list) ="
  , "      corres_tac ctxt"
  , "         (typing_tree)"
  , "         (fun_defs)"
  , "         (absfun_corres)"
  , "         (fun_corres)"
  , "         @{thm corres_if}             (* corres_if *)"
  , "         @{thms corres_esacs}         (* corres_esacs *)"
  , "         @{thms untyped_func_enum_defs}"
  , "         []"
  , "         @{thms tag_enum_defs}"
  , "         @{thm LETBANG_TRUE_def}"
  , "         @{thms list_to_map_more[where f=Var]"
  , "                list_to_map_singleton[where f=Var]}"
  , "         verbose;"
  , "\\<close>"
  ] ++
  ttMap fns ++
  categorise ++
  nameField ++
  hofHints cfile ++
  checkHofHints ++
  cogentMainTree thy ent ++
  xiN thy ++
  changeType ++
  corresThm ++
  runProof ++
  resolve ++
  [ ""
  , "end (* of context *)"
  ]

ttMap :: [String] -> [String]
ttMap fns =
  [ "ML \\<open>" ] ++
  (let eqns = [ "typing_tree_of \"" ++ fn ++ "\" = " ++ fn ++ "_typing_tree" | fn <- fns ] ++
              [ "typing_tree_of f = error (\"No typing tree for \" ^ quote f)" ]
   in map ("fun " ++) (take 1 eqns) ++ map ("  | " ++) (drop 1 eqns)) ++
  [ "\\<close>" ]

categorise :: [String]
categorise =
  [ "ML \\<open>"
  , "(* Categorise *)"
  , "val [(Cogent_functions_FO, Cogent_functions_HO), (Cogent_abstract_functions'_FO, Cogent_abstract_functions'_HO)] ="
  , "  map (partition (get_Cogent_funtype @{context} #> Thm.prop_of #> Utils.rhs_of_eq #> funtype_is_first_order))"
  , "      [Cogent_functions, Cogent_abstract_functions];"
  , "val _ = if null Cogent_functions_HO then () else"
  , "          error (\"Don't know how to handle higher-order Cogent functions: \" ^ commas_quote Cogent_functions_HO);"
  , "\\<close>"
  ]

nameField :: [String]
nameField =
  [ "ML \\<open>"
  , "(* translate Cogent Invalue pointers to C record lookup terms *)"
  , "fun name_field ctxt (nm, funcs) = let"
  , "   val nm' = case nm of Left f => f | Right f => f"
  , "   val T = case Syntax.read_term ctxt (nm' ^ \"'\") of"
  , "       Const (_, T) => T | t => raise TERM (\"name_field: \", [t])"
  , "   val sourceT = domain_type T"
  , "   fun typ_string T = dest_Type T |> fst"
  , "   val source_var = Free (\"x\", sourceT)"
  , "   fun access sourceT t [] = t"
  , "     | access sourceT t (getter::getters) = let"
  , "         val getterm = Syntax.read_term ctxt (typ_string sourceT ^ \".\" ^ getter)"
  , "         val destT = range_type (type_of getterm)"
  , "         in access destT (getterm $ t) getters end"
  , "  in (nm, map (apfst (access sourceT source_var #> lambda source_var)) funcs) end"
  , "\\<close>"
  ]

hofHints :: String -> [String]
hofHints cfile =
  [ "(* Higher-order function call annotations. *)"
  , "ML \\<open>"
  , "val HO_call_hints ="
  , "     Cogent_functions"
  , "     |> Par_List.map (fn f => case CogentHigherOrder.make_HO_call_hints @{context} \"" ++ cfile ++ "\" f of"
  , "            [] => [] | hints => [(f, map (name_field @{context}) hints)])"
  , "     |> List.concat"
  , "     |> Symtab.make"
  , "     : ((string, string) Either * (term * (string, string) Either) list) list Symtab.table"
  , "\\<close>"
  ]

checkHofHints :: [String]
checkHofHints =
  [ "ML \\<open>"
  , "(* Sanity check HO_call_hints. *)"
  , "val _ = Symtab.dest HO_call_hints |> map (fn (f, calls) => ("
  , "  (if member (op =) Cogent_functions f then () else error (\"HO_call_hints: no such function \" ^ quote f));"
  , "  map (fn af => case af of Right _ => () | Left af =>"
  , "                  if member (op =) Cogent_abstract_functions af then () else"
  , "                    error (\"HO_call_hints: no such absfun \" ^ quote af))"
  , "      (map fst calls);"
  , "  map (fn af => case af of Right _ => () | Left af =>"
  , "                  if member (op =) (Proof_Context.get_thm @{context} (f ^ \"_def\")"
  , "                                    |> Thm.prop_of |> get_simple_function_calls) af then ()"
  , "                  else error (\"HO_call_hints: absfun \" ^ quote af ^ \" not in \" ^ quote f)) (map fst calls)"
  , "  (* TODO: check funargs and completeness *)"
  , "  ))"
  , "\\<close>"
  ]

cogentMainTree :: String -> Maybe [CoreFunName] -> [String]
cogentMainTree thy ent =
  [ "ML \\<open>"
  , "(* Abstract function names in the AST don't have theory prefixes *)"
  , "fun maybe_unprefix pre str = if String.isPrefix pre str then unprefix pre str else str"
  , "fun mapBoth f = mapEither f f"
  , "(* Entry point for verification *)"
  , "val Cogent_main_tree ="
  , "  make_call_tree (Cogent_functions, Cogent_abstract_functions)"
  , "    (Symtab.map (K (map (apsnd (map (apsnd (mapBoth (maybe_unprefix \"" ++ thy ++ __cogent_suffix_of_type_proof ++ ".\"))))))) HO_call_hints) @{context}"
  , "  |> Symtab.map (K annotate_depth)"
  , ""
  ] ++ (case ent of
         Nothing ->   [ "val entry_func_names = Cogent_functions (* all functions *)" ]
         Just tlfs -> [ "val entry_func_names = [" ] ++
                      lines (intercalate ",\n" (map (\tlf -> "      \"" ++ tlf ++ "\"") 
                      (map (unIsabelleName . mkIsabelleName . unCoreFunName) tlfs))) ++
                      [ "]" ]
       ) ++
  [ "val entry_funcs = Symtab.dest Cogent_main_tree"
  , "      |> filter (fn (n, _) => member (op =) entry_func_names n) |> Symtab.make"
  , "\\<close>"
  ]

xiN :: String -> [String]
xiN thy =
  [ "(* Define \\<xi>_n. *)"
  , "ML \\<open>"
  , "(* FIXME: actually merge trees for uabsfuns *)"
  , "val (deepest_tree::_) ="
  , "  Symtab.dest Cogent_main_tree |> map snd |> filter (fn tr =>"
  , "    CogentCallTree_data tr ="
  , "    (Symtab.dest Cogent_main_tree |> map snd |> map CogentCallTree_data |> maximum))"
  , "\\<close>"
  , ""
  , "end (* of context *)"
  , ""
  , "setup \\<open> declare_uabsfuns deepest_tree \\<close>"
  , ""
  , "context " ++ thy ++ " begin"
  , ""
  ]

changeType :: [String]
changeType =
  [ "(* change the type of entry_funcs *)"
  , "ML \\<open>"
  , "   fun CogentCallOrder_map (FirstOrderCall tree) ="
  , "      FirstOrderCall (CogentCallTree_map tree)"
  , "   | CogentCallOrder_map (SecondOrderCall (tree, ttrl)) ="
  , "      SecondOrderCall (CogentCallTree_map tree, map (fn (tm,tr) => (tm, CogentCallTree_map tr)) ttrl)"
  , "   and CogentCallTree_map (CogentCallTree (a,typ, name, calls)) ="
  , "       CogentCallTree ((a,0), typ, name, map CogentCallOrder_map calls);"
  , ""
  , "   val entry_funcs' ="
  , "    Symtab.map (fn _ => fn tr => CogentCallTree_map tr) entry_funcs"
  , "\\<close>"
  ]

corresThm :: [String]
corresThm =
  [ "(* Define corres theorems for all function calls under entry_funcs *)"
  , "ML \\<open> val prop_tab = corres_tree_obligations entry_funcs' @{context} \\<close>"
  , ""
  ] ++
  if __cogent_fnormalisation == ANF then
    [ "(* Dummy definition; only used for programs in K-normal form *)"
    , "lemmas corres_nested_let = TrueI"
    ]
  else
    [ "(* Additional Let rule for programs in K-normal form *)"
    , "lemmas corres_nested_let = corres_nested_let_base[OF LET_TRUE_def]"
    ]

runProof :: [String]
runProof =
  [ "(* Run proofs for generated functions *)"
  , "(* ML\\<open>"
  , "fun all_corres_goals corres_tac typing_tree_of time_limit ctxt (tab : obligations) ="
  , "  let"
  , "    val tl = Time.fromSeconds time_limit"
  , "    fun driver nm = Timing.timing ((fn f => fn a => SOME (f a)) (TimeLimit.timeLimit tl"
  , "            (corres_tac_driver corres_tac typing_tree_of ctxt tab))) nm"
  , "        |> (fn (dur, res) => (tracing (\"Time for \" ^ nm ^ \": \" ^ Timing.message dur); res))"
  , "        |> (fn NONE => (tracing (\"Failed: \" ^ nm); (nm, NONE))"
  , "             | SOME thm => (tracing (\"Succeeded: \" ^ nm); (nm, SOME thm)))"
  , "    val res = map driver (Symtab.keys tab)"
  , "    val thm_tab = Symtab.make res"
  , "  in thm_tab end"
  , "\\<close>"
  , "*)"
  , "ML \\<open> val thm_tab = all_corres_goals (corres_tac_local false) typing_tree_of 99999 @{context} prop_tab \\<close>"
  ]

resolve :: [String]
resolve =
  [ "(* Resolve function calls recursively *)"
  , "ML \\<open>"
  , "val finalised_thms ="
  , "    Symtab.dest thm_tab"
  , "    |> Par_List.map (fn (n, maybe_thm) =>"
  , "         (n, Option.map (simp_xi @{context}) maybe_thm))"
  , "    |> Symtab.make"
  , "    |> finalise prop_tab @{context}"
  , "\\<close>"
  , ""
  , "(* Check that we have theorems for all entry_funcs *)"
  , "ML \\<open> Symtab.dest prop_tab"
  , "      (* only check entry_funcs *)"
  , "      |> filter (fn (_, p) => member (op=) (Symtab.keys entry_funcs) (#1 p))"
  , "      (* we only have proofs for non-Absfuns *)"
  , "      |> filter (fn (_, p) => #2 p = CogentFun)"
  , "      |> app (fn (thm, _) => @{trace} (thm, Symtab.lookup finalised_thms thm"
  , "                                            |> Utils.the' (\"failed lookup for \" ^ thm)"
  , "                                            |> Utils.the' (\"failed lookup for \" ^ thm))) \\<close>"
  ]
