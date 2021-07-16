(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

(* Refinement chain from C to shallow-embedded Cogent. *)
theory Cogent_Corres_Shallow_C
  imports
    "Cogent.Cogent"
    "Cogent.Correspondence"
    "Cogent.Mono"
    "Cogent.TypeProofGen"
    "Cogent.Util"
    "CogentShallow.ShallowTuples"
    "CogentShallow.Shallow_Tac"
    "Deep_Embedding_Auto"
    "Cogent_Corres"
    "Corres_Tac"
    "Tidy"
begin


locale correspondence_init =
  correspondence +
  constrains upd_abs_typing :: "abstyp \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> sigil \<Rightarrow> ptrtyp set \<Rightarrow> ptrtyp set \<Rightarrow> (funtyp, abstyp, ptrtyp) store \<Rightarrow> bool"
       and abs_repr :: "abstyp \<Rightarrow> name \<times> repr list"
       and abs_upd_val :: "abstyp \<Rightarrow> 'b \<Rightarrow> char list \<Rightarrow> Cogent.type list \<Rightarrow> sigil \<Rightarrow> ptrtyp set \<Rightarrow> ptrtyp set \<Rightarrow> (funtyp, abstyp, ptrtyp) store \<Rightarrow> bool"

sublocale correspondence_init \<subseteq> update_sem_init upd_abs_typing abs_repr
  by (unfold_locales)


sublocale correspondence_init \<subseteq> correspondence
  by (unfold_locales)

context correspondence_init
begin

(*
 * Refinement specification.
 *
 * Legend:
 *   s:  shallow
 *   t:  shallow with tuples
 *   p:  polymorphic
 *   m:  monomorphic
 *   um: u_sem, mono
 *   C:  C
 *)

definition val_rel_shallow_C where
"val_rel_shallow_C
     (rename :: funtyp \<times> type list \<Rightarrow> funtyp)
     (v\<^sub>s :: 'sv)
     (v\<^sub>C :: 'cv :: cogent_C_val)
     (v\<^sub>p :: (funtyp, 'b) vval)
     (v\<^sub>u\<^sub>m :: (funtyp, abstyp, ptrtyp) uval)
     (\<xi>\<^sub>p :: (funtyp, 'b) vabsfuns)
     (\<sigma> :: (funtyp, abstyp, ptrtyp) store)
     (\<Xi>\<^sub>m :: funtyp \<Rightarrow> poly_type) \<equiv>
  \<exists>\<tau> r w.
    valRel \<xi>\<^sub>p v\<^sub>s v\<^sub>p \<and>
    \<Xi>\<^sub>m, \<sigma> \<turnstile> v\<^sub>u\<^sub>m \<sim> val.rename_val rename (val.monoval v\<^sub>p) : \<tau> \<langle>r, w\<rangle> \<and>
    val_rel v\<^sub>u\<^sub>m v\<^sub>C"

lemma val_rel_shallow_C_elim:
  "\<And>\<xi>. val_rel_shallow_C rename sv m vv uv \<xi> \<sigma> \<Xi>' \<Longrightarrow> valRel \<xi> sv vv"
  "\<And>\<xi>. val_rel_shallow_C rename sv m vv uv \<xi> \<sigma> \<Xi>' \<Longrightarrow> \<exists>\<tau> r w. \<Xi>', \<sigma> \<turnstile> uv \<sim> val.rename_val rename (val.monoval vv) : \<tau> \<langle>r, w\<rangle>"
  "\<And>\<xi>. val_rel_shallow_C rename sv m vv uv \<xi> \<sigma> \<Xi>' \<Longrightarrow> val_rel uv m"
  by (simp_all add: val_rel_shallow_C_def)

definition corres_shallow_C where
  "corres_shallow_C
     (rename :: funtyp \<times> type list \<Rightarrow> funtyp)
     (srel :: ((funtyp, abstyp, ptrtyp) store \<times> 's) set)
     (v\<^sub>s :: 'sv)
     (prog\<^sub>m :: funtyp expr)
     (prog\<^sub>C :: ('s, 'cv :: cogent_C_val) nondet_monad)
     (\<xi>\<^sub>u\<^sub>m :: (funtyp, abstyp, ptrtyp) uabsfuns)
     (\<xi>\<^sub>v\<^sub>m :: (funtyp, 'b) vabsfuns)
     (\<xi>\<^sub>v\<^sub>p :: (funtyp, 'b) vabsfuns)
     (\<gamma>\<^sub>u\<^sub>m :: (funtyp, abstyp, ptrtyp) uval env)
     (\<gamma>\<^sub>v\<^sub>m :: (funtyp, 'b) vval env)
     (\<Xi>\<^sub>m :: funtyp \<Rightarrow> poly_type)
     (\<Gamma>\<^sub>m :: ctx)
     (\<sigma> :: (funtyp, abstyp, ptrtyp) store)
     (s :: 's) \<equiv>
   proc_ctx_wellformed \<Xi>\<^sub>m \<longrightarrow>
   (\<xi>\<^sub>u\<^sub>m \<sim> \<xi>\<^sub>v\<^sub>m matches-u-v \<Xi>\<^sub>m) \<longrightarrow>
   upd.proc_env_matches_ptrs \<xi>\<^sub>u\<^sub>m \<Xi>\<^sub>m \<longrightarrow>
   (\<sigma>, s) \<in> srel \<longrightarrow>
   (\<exists>r w. \<Xi>\<^sub>m, \<sigma> \<turnstile> \<gamma>\<^sub>u\<^sub>m \<sim> \<gamma>\<^sub>v\<^sub>m matches \<Gamma>\<^sub>m \<langle>r, w\<rangle>) \<longrightarrow>
   (\<not> snd (prog\<^sub>C s) \<and>
   (\<forall>r' s'. (r', s') \<in> fst (prog\<^sub>C s) \<longrightarrow>
     (\<exists>\<sigma>' v\<^sub>u\<^sub>m v\<^sub>p.
      (\<xi>\<^sub>u\<^sub>m, \<gamma>\<^sub>u\<^sub>m \<turnstile> (\<sigma>, prog\<^sub>m) \<Down>! (\<sigma>', v\<^sub>u\<^sub>m)) \<and>
       (\<xi>\<^sub>v\<^sub>m, \<gamma>\<^sub>v\<^sub>m \<turnstile> prog\<^sub>m \<Down> val.rename_val rename (val.monoval v\<^sub>p)) \<and>
       (\<sigma>', s') \<in> srel \<and>
       val_rel_shallow_C rename v\<^sub>s r' v\<^sub>p v\<^sub>u\<^sub>m \<xi>\<^sub>v\<^sub>p \<sigma>' \<Xi>\<^sub>m)))"

lemma corres_shallow_C_intro:
    (* Procedure monomorphisation *)
      assumes mono_prog:
       "prog\<^sub>m = val.rename_expr rename (val.monoexpr prog\<^sub>p)"
    (* Dynamic environment *)
      assumes mono_env:
       "vv\<^sub>m = val.rename_val rename (val.monoval vv\<^sub>p)"
    (* Program typing *)
      assumes mono_proc_env_matches:
       "val.proc_env_matches \<xi>\<^sub>m \<Xi>"
    (* Program monomorphisation *)
      assumes mono_proc_env:
       "val.rename_mono_prog rename \<Xi> \<xi>\<^sub>m \<xi>\<^sub>p"
    (* Procedure typing *)
      assumes typingP:
       "\<Xi>, [], [Some \<tau>i] \<turnstile> prog\<^sub>m : \<tau>o"
    (* C-refinement *)
      assumes corresP:
       "corres srel prog\<^sub>m (prog\<^sub>C uv\<^sub>C) \<xi>\<^sub>u\<^sub>m [uv\<^sub>m] \<Xi> [Some \<tau>i] \<sigma> s"
    (* Shallow-deep refinement *)
      assumes scorresP:
       "val.scorres (prog\<^sub>s vv\<^sub>s) prog\<^sub>p [vv\<^sub>p] \<xi>\<^sub>p"
    (* Dynamic environment *)
      assumes mono_env_matches:
       "val.matches \<Xi> [vv\<^sub>m] [Some \<tau>i]"
  (* Goal *)
  shows
    "val_rel_shallow_C rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>\<^sub>p \<sigma> \<Xi> \<Longrightarrow>
     corres_shallow_C rename srel (prog\<^sub>s vv\<^sub>s) prog\<^sub>m (prog\<^sub>C uv\<^sub>C) \<xi>\<^sub>u\<^sub>m \<xi>\<^sub>m \<xi>\<^sub>p [uv\<^sub>m] [vv\<^sub>m] \<Xi> [Some \<tau>i] \<sigma> s"
  apply (clarsimp simp: corres_shallow_C_def val_rel_shallow_C_def)
  apply (cut_tac corresP[unfolded corres_def])
  apply (clarsimp)
  apply (erule impE)
   apply (fastforce dest: u_v_matches_to_matches_ptrs)
  apply clarsimp
  apply (rename_tac mm' s')
  apply (erule_tac x=mm' in allE)
  apply (erule_tac x=s' in allE)
  apply clarsimp
  apply (rename_tac \<sigma>' uv')
  apply (rule_tac x=\<sigma>' in exI)
  apply (rule_tac x=uv' in exI)
  apply (simp)
  apply (frule(3) val_executes_from_upd_executes, rule typingP)
  apply clarsimp
  apply (rename_tac vv')
  apply (cut_tac v'="vv'" in val.rename_monoexpr_correct(1)
   [OF _ mono_proc_env_matches mono_proc_env,
    where \<gamma>="[vv\<^sub>p]" and \<Gamma>="[Some \<tau>i]" and e="prog\<^sub>p"])
      apply simp
     apply (simp add: mono_env[symmetric] mono_env_matches)
    apply (simp add: mono_prog mono_env[symmetric])
   using mono_prog typingP apply fast
   apply (cut_tac scorresP[unfolded val.scorres_def])
  apply (frule(4) mono_correspondence(1))
   apply (rule typingP)
  apply (blast)
  done


(* Generate an end-to-end refinement theorem using corres_shallow_C.
 * Resolve as many of its premises as we can. *)
ML \<open>
fun Cogent_to_C_name str =
      (String.explode str
       |> map (fn c => if c = #"'" then "_prime" else String.implode [c])
       |> String.concat) ^ "'"

fun get_concl (Const (@{const_name Trueprop}, _) $ t) = get_concl t
  | get_concl (Const ("Pure.imp", _) $ _ $ t) = get_concl t
  | get_concl (Const ("Pure.all", _) $ Abs (_, _, t)) = get_concl t
  | get_concl t = t

fun make_corres_shallow_C desugar_thy deep_thy ctxt f = let
  (* Global program constants *)
  val poly_mono_rename = Syntax.read_term ctxt "rename"
  val proc_ctx = Syntax.read_term ctxt "\<Xi>"
  val state_rel = Syntax.read_term ctxt "state_rel"

  (*
   * Resolve corres_shallow_C_intro with the theorems for each refinement stage.
   * This might sound like a job for RS, but that doesn't work well because:
   * 1. RS needs to be told which premise to resolve
   * 2. RS cannot do rewriting (e.g. our normalisation_thms are equations)
   *
   * So we extract the assumptions of our per-stage theorems and manually add them
   * to the proof goal, akin to guessing the outcome of RS ahead of time.
   *)
  val basic_prop =
      @{mk_term
          "\<lbrakk> value_sem.rename_mono_prog val_abs_typing ?rename ?\<Xi> \<xi>\<^sub>m \<xi>\<^sub>p;
             vv\<^sub>m = val.rename_val ?rename (val.monoval vv\<^sub>p);

             val_rel_shallow_C ?rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>\<^sub>p \<sigma> ?\<Xi>;
             proc_ctx_wellformed ?\<Xi>;
             value_sem.proc_env_matches val_abs_typing \<xi>\<^sub>m ?\<Xi>;
             value_sem.matches val_abs_typing ?\<Xi> [vv\<^sub>m] [option.Some (fst (snd ?f_deep_type))]
           \<rbrakk> \<Longrightarrow>
           corres_shallow_C ?rename ?state_rel
              (?f_desugar vv\<^sub>s) ?f_deep (?f_C uv\<^sub>C)
              \<comment> \<open> \<xi> is schematic; instantiated by resolving corres_thm \<close>
              ?\<xi> \<xi>\<^sub>m \<xi>\<^sub>p [uv\<^sub>m] [vv\<^sub>m] ?\<Xi> [option.Some (fst (snd ?f_deep_type))] \<sigma> s"
      (f_desugar,
           f_deep,
             f_deep_type,
               f_C,
                 \<Xi>,
                   rename,
                     state_rel)}
      (Syntax.read_term ctxt (desugar_thy ^ "." ^ f),
           Syntax.read_term ctxt (deep_thy ^ "." ^ f),
             Syntax.read_term ctxt (deep_thy ^ "." ^ f ^ "_type"),
               Syntax.read_term ctxt (Cogent_to_C_name f),
                 proc_ctx,
                   poly_mono_rename,
                     state_rel)

  (* Get component theorems. *)
  (* FIXME: the lookup for norm_thm and scorres_thm assume that f has the same name
   *        in both the poly and mono programs (i.e. f is not polymorphic).
   *        If entry_func_names gets polymorphic functions, then this assumption breaks
   *        and we'd need to lookup the correct source name. *)
  val norm_thm = Proof_Context.get_thm ctxt (f ^ "_normalised")
  val mono_thm = Proof_Context.get_thm ctxt ("value_sem." ^ f ^ "_monomorphic")
  val typing_thm = Proof_Context.get_thm ctxt (f ^ "_typecorrect'")
  val scorres_thm = Proof_Context.get_thm ctxt ("scorres_" ^ f)
  val corres_thm = Proof_Context.get_thm ctxt ("corres_" ^ f)
  val proc_ctx_def_thm = Proof_Context.get_thm ctxt ("\<Xi>_def")

  (* Also instantiate scorres_thm to monomorphic type *)
  val scorres_thm = Drule.infer_instantiate ctxt [(("ts", 0), @{cterm "[] :: type list"})] scorres_thm
                    |> Simplifier.rewrite_rule ctxt @{thms specialise_nothing[THEN eq_reflection]}

  (* Abstract function assumptions for CorresProof *)
  (* We will resolve the val_rel assumption, so exclude it *)
  val corres_assms =
    Thm.prems_of corres_thm
    |> filter (fn prem => case strip_comb (get_concl prem) of
                              (Const (@{const_name val_rel}, _), _) => false
                            | _ => true)

  (* FIXME: abstract function assumptions for SCorres_Normal.
   *        SCorres_Normal currently does not generate them correctly *)
  val scorres_assms = []

  (* Our proof involves two locale assumptions:
   * one for correspondence_init (this locale) and one for
   * the target locale of the concrete program (passed in ctxt).
   * However, we expect the target locale to be a sublocale of correspondence_init,
   * so we can manually remove the correspondence_init assumption later.
   * FIXME: correct way to do this? *)

  val locale_assm = @{term "Trueprop (correspondence_init abs_repr val_abs_typing upd_abs_typing abs_upd_val)"}
  val locale_thm =
      case filter (exists_subterm (is_const @{const_name correspondence_init}) o Thm.prop_of)
                  (Locale.get_witnesses ctxt) of
          [] => error "Expected sublocale of correspondence_init"
        | (thm::_) => if Thm.prop_of thm aconv locale_assm then thm else
                        error "Expected sublocale of correspondence_init"
  val thm_with_assm =
    Goal.prove ctxt
      ["\<xi>\<^sub>m", "\<xi>\<^sub>p", "vv\<^sub>t", "vv\<^sub>s", "uv\<^sub>C", "vv\<^sub>p", "vv\<^sub>m", "uv\<^sub>m", "\<sigma>", "s"]
      (locale_assm :: corres_assms @ scorres_assms)
      (* XXX: locale_assm shows up twice, fix... *)
      (Logic.mk_implies (locale_assm, basic_prop))
      (fn {context, prems} =>
         (* Get premises of corres_shallow_C.
          * Instantiate vv\<^sub>s to avoid wrong unification in "prog\<^sub>s vv\<^sub>s". *)
         rtac @{thm corres_shallow_C_intro[where vv\<^sub>s=vv\<^sub>s]} 1 THEN
         REPEAT_DETERM (FIRST [
           (* Trivial assumptions *)
           atac 1,
           (* Derived value relations from val_rel_shallow_C *)
           SOLVES (eresolve_tac ctxt @{thms val_rel_shallow_C_elim} 1),
           (* Monomorphisation; reverse it to match corres_shallow_C_intro *)
           (rtac (mono_thm RS @{thm sym}) 1 THEN
               asm_full_simp_tac (context addsimps @{thms correspondence_init_def correspondence_def}) 1 THEN
               etac @{thm conjE} 1 THEN
               asm_full_simp_tac context 1),
           (* Deep embedding type-correctness *)
           rtac typing_thm 1,
           (* SCorres + normalisation equation *)
           (unfold_tac context [norm_thm]
              THEN rtac scorres_thm 1),
           (* C corres *)
           (unfold_tac context [proc_ctx_def_thm]
              THEN rtac corres_thm 1),
           (* Extra premises, which should all be trivial *)
           SOLVES ((resolve_tac ctxt prems THEN_ALL_NEW atac) 1)
         ]))
  in
    locale_thm RS thm_with_assm
  end
\<close>

end

end
