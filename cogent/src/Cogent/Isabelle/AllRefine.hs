--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

module Cogent.Isabelle.AllRefine where

import Cogent.Common.Types (primIntSizeBits, machineWordType)
import Cogent.Compiler
import Cogent.Util

import Isabelle.InnerAST as I
import Isabelle.OuterAST as O

import System.FilePath ((</>), takeBaseName)
import qualified Text.PrettyPrint.ANSI.Leijen as L

allRefine :: FilePath -> String -> L.Doc
allRefine source log =
  let header = (L.string ("(*\n" ++ log ++ "\n*)\n") L.<$>)
  in header $ L.pretty (Theory arthy imports body :: O.Theory I.Type I.Term)
  where
    imports = TheoryImports [ thy ++ __cogent_suffix_of_normal_proof
                            , thy ++ __cogent_suffix_of_scorres ++ __cogent_suffix_of_stage STGNormal
                            , thy ++ __cogent_suffix_of_corres_proof
                            , thy ++ __cogent_suffix_of_mono_proof
                            , "CogentCRefinement.Cogent_Corres_Shallow_C"]
    body   = typeProof thy : exportThms thy :
             initFinalLocale thy output : sublocales thy : contextFinal thy : []
    thy    = mkProofName source Nothing
    arthy  = mkProofName source (Just __cogent_suffix_of_all_refine)
    output = maybe (mkOutputName source Nothing) takeBaseName __cogent_proof_input_c

typeProof :: String -> TheoryDecl I.Type I.Term
typeProof thy = TheoryString $ unlines
  [ "(*"
  , " * Derive simple typing rules from earlier ttyping proofs."
  , " * From f_typecorrect we derive f_typecorrect'."
  , " * For unification reasons later on, we also ensure that (fst f_type) is simplified"
  , " * to [] (ttyping has been proved for the monomorphic program)."
  , " *)"
  , "local_setup \\<open>"
  , "let val typeproof_thy = \"" ++ thy ++ __cogent_suffix_of_type_proof ++ "\""
  , "in"
  , "fold (fn f => fn ctxt => let"
  , "    val tt_thm = Proof_Context.get_thm ctxt (typeproof_thy ^ \".\" ^ f ^ \"_typecorrect\")"
  , "    val f_type = Syntax.read_term ctxt (typeproof_thy ^ \".\" ^ f ^ \"_type\")"
  , "    val f_type_def = Proof_Context.get_thm ctxt (typeproof_thy ^ \".\" ^ f ^ \"_type_def\")"
  , "    val k_empty = Goal.prove ctxt [] [] (@{mk_term \"prod.fst ?t \\<equiv> []\" t} f_type)"
  , "                    (K (simp_tac (ctxt addsimps [f_type_def]) 1))"
  , "    val t_thm = (tt_thm RS @{thm ttyping_imp_typing})"
  , "                |> rewrite_rule ctxt [@{thm snd_conv[THEN eq_reflection]}, k_empty]"
  , "    in Local_Theory.note ((Binding.name (f ^ \"_typecorrect'\"), []), [t_thm]) ctxt |> snd"
  , "    end)"
  , "    (filter (member op= Cogent_functions) entry_func_names)"
  , "end"
  , "\\<close>"
  ]

exportThms :: String -> TheoryDecl I.Type I.Term
exportThms thy = TheoryString $ unlines
  [ "(* C-refinement (exported to f_corres)."
  , " * If there are multiple \\<xi>-levels, we use the highest one. *)"
  , "context " ++ thy ++ " begin"
  , "ML \\<open>"
  , "fun both f (x, y) = (f x, f y);"
  , ""
  , "val cogent_entry_func_props ="
  , "  Symtab.dest prop_tab"
  , "  |> filter (member (op=) entry_func_names o #1 o snd)"
  , "  |> filter (member (op=) Cogent_functions o #1 o snd)"
  , "  |> sort_by (#1 o snd)"
  , "  |> partition_eq (fn (p1,p2) => #1 (snd p1) = #1 (snd p2))"
  , "  |> map (sort (option_ord int_ord o"
  , "                both (fn p => unprefix (#1 (snd p) ^ \"_corres_\") (fst p)"
  , "                              |> Int.fromString))"
  , "          #> List.last)"
  , "\\<close>"
  , "local_setup \\<open>"
  , "fold (fn (f, p) => Utils.define_lemmas (\"corres_\" ^ #1 p)"
  , "                     [Symtab.lookup finalised_thms f |> the |> the] #> snd)"
  , "     cogent_entry_func_props"
  , "\\<close>"
  , "end"
  , ""
  , "(* Monomorphisation (exported to f_monomorphic) *)"
  , "context value_sem begin"
  , "local_setup \\<open>"
  , "fold (fn (f, thm) => Utils.define_lemmas (f ^ \"_monomorphic\") [thm] #> snd)"
  , "     (Symtab.dest monoexpr_thms |> filter (member op= entry_func_names o fst))"
  , "\\<close>"
  , "end"
  , ""
  , "(* Normalisation. Not exporting from a locale,"
  , " * but the proofs below want to use Isabelle names. *)"
  , "local_setup \\<open>"
  , "fold (fn (f, thm) => Utils.define_lemmas (f ^ \"_normalised\") [thm] #> snd)"
  , "     (Symtab.dest normalisation_thms |> filter (member op= entry_func_names o fst))"
  , "\\<close>"
  ]

initFinalLocale :: String -> String -> TheoryDecl I.Type I.Term
initFinalLocale thy output = TheoryString $ unlines
  [ "(* Initialise final locale. *)"
  , "locale " ++ thy ++ "_cogent_shallow ="
  , "  \"" ++ output ++ "\" + correspondence +"
  , "  constrains val_abs_typing :: \"'b \\<Rightarrow> name \\<Rightarrow> type list \\<Rightarrow> bool\""
  , "         and upd_abs_typing :: \"abstyp \\<Rightarrow> name \\<Rightarrow> type list \\<Rightarrow> sigil \\<Rightarrow> ptrtyp set \\<Rightarrow> ptrtyp set \\<Rightarrow> (funtyp, abstyp, ptrtyp) store \\<Rightarrow> bool\""
  , "         and abs_repr       :: \"abstyp \\<Rightarrow> name \\<times> repr list\""
  , "         and abs_upd_val    :: \"abstyp \\<Rightarrow> 'b \\<Rightarrow> char list \\<Rightarrow> Cogent.type list \\<Rightarrow> sigil \\<Rightarrow> " ++ wordSize ++ " word set \\<Rightarrow> " ++ wordSize ++ " word set \\<Rightarrow> (char list, abstyp, " ++ wordSize ++ " word) store \\<Rightarrow> bool\""
  ]
 where wordSize = show $ primIntSizeBits machineWordType


sublocales :: String -> TheoryDecl I.Type I.Term
sublocales thy = TheoryString $ unlines
  [ "sublocale " ++ thy ++ "_cogent_shallow \\<subseteq> " ++ thy ++ " _ upd_abs_typing abs_repr"
  , "  by (unfold_locales)"
  , ""
  , "sublocale " ++ thy ++ "_cogent_shallow \\<subseteq> shallow val_abs_typing"
  , "  by (unfold_locales)"
  , ""
  , "sublocale " ++ thy ++ "_cogent_shallow \\<subseteq> correspondence_init"
  , "  by (unfold_locales)"
  ]

contextFinal :: String -> TheoryDecl I.Type I.Term
contextFinal thy = ContextDecl $ Context name body
  where name = thy ++ "_cogent_shallow"
        body = [ genFinalLemmas thy
               , TheoryString "print_theorems"
               ]

genFinalLemmas :: String -> TheoryDecl I.Type I.Term
genFinalLemmas thy = TheoryString $ unlines
  [ "(* Generate end-to-end refinement theorems, exported to corres_shallow_C_f *)"
  , "local_setup \\<open>"
  , "filter (member op= Cogent_functions) entry_func_names"
  , "|> fold (fn f => fn lthy => let"
  , "     val thm = make_corres_shallow_C \"" ++ desugar_thy ++ "\" \"" ++ typeproof_thy ++ "\" lthy f"
  , "     val (_, lthy) = Local_Theory.notes [((Binding.name (\"corres_shallow_C_\" ^ f), []), [([thm], [])])] lthy"
  , "     in lthy end)"
  , "\\<close>"
  ]
  where desugar_thy = thy ++ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage STGDesugar
        typeproof_thy = thy ++ __cogent_suffix_of_type_proof
