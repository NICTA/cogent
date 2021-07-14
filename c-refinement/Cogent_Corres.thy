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

theory Cogent_Corres
  imports
    "Cogent.AssocLookup"
    "Cogent.TypeTrackingSemantics"
    "Cogent.UpdateSemantics"
    "Cogent.Util"
    "Value_Relation"
begin

locale update_sem_init = update_sem +
constrains abs_typing :: "abstyp \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> sigil \<Rightarrow> ptrtyp set \<Rightarrow> ptrtyp set \<Rightarrow> bool"
       and abs_repr :: "abstyp \<Rightarrow> name \<times> repr list"

context update_sem_init
begin

inductive_cases u_sem_varE [elim]: "\<xi>, \<gamma> \<turnstile> (\<sigma>, Var x)  \<Down>! st"
inductive_cases u_sem_ifE [elim]: "\<xi>, \<gamma> \<turnstile> (\<sigma>, If b s t)  \<Down>! (\<sigma>', r)"
inductive_cases u_sem_takeE: "\<xi>,\<gamma> \<turnstile> (\<sigma>,Take x f e)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_putE: "\<xi>,\<gamma> \<turnstile> (\<sigma>,Put x f e)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_litE: "\<xi>,\<gamma> \<turnstile> (\<sigma>, Lit l)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_letE: "\<xi>,\<gamma> \<turnstile> (\<sigma>,Let x y)\<Down>! (\<sigma>',v)"


definition
  corres ::
  "((funtyp, abstyp, ptrtyp) store \<times> 's) set \<Rightarrow>
   funtyp expr \<Rightarrow>
   ('s,('a::cogent_C_val)) nondet_monad \<Rightarrow>
   (funtyp, abstyp, ptrtyp) uabsfuns \<Rightarrow>
   (funtyp, abstyp, ptrtyp) uval env \<Rightarrow>
   (funtyp \<Rightarrow> poly_type) \<Rightarrow>
   ctx \<Rightarrow>
   (funtyp, abstyp, ptrtyp) store \<Rightarrow>
   's \<Rightarrow>
   bool"
where
  "corres srel c m \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s \<equiv>
    proc_ctx_wellformed \<Xi> \<longrightarrow> \<xi> matches-u \<Xi> \<longrightarrow> (\<sigma>,s) \<in> srel \<longrightarrow>
   (\<exists>r w. \<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>) \<longrightarrow>
   (\<not> snd (m s) \<and>
   (\<forall>r' s'. (r',s') \<in> fst (m s) \<longrightarrow>
     (\<exists>\<sigma>' r.(\<xi>, \<gamma> \<turnstile> (\<sigma>,c)  \<Down>! (\<sigma>',r)) \<and> (\<sigma>',s') \<in> srel \<and> val_rel r r')))"


abbreviation "correspond' srel c m \<xi> \<gamma> \<Xi> ENV \<equiv> (\<forall>\<sigma> s. corres srel c m \<xi> \<gamma> \<Xi> ENV \<sigma> s)"

definition
  correspond ::
  "((funtyp, abstyp, ptrtyp) store \<times> 's) set \<Rightarrow>
   funtyp expr \<Rightarrow>
   ('s,('a::cogent_C_val)) nondet_monad \<Rightarrow>
   (funtyp,abstyp,ptrtyp) uabsfuns \<Rightarrow>
   (funtyp, abstyp, ptrtyp) uval env \<Rightarrow>
   (funtyp \<Rightarrow> poly_type) \<Rightarrow>
   (funtyp, abstyp, ptrtyp) store \<Rightarrow>
   's \<Rightarrow>
   bool"
where
  "correspond srel c m \<xi> \<gamma> \<Xi> \<sigma> s \<equiv>
    proc_ctx_wellformed \<Xi> \<longrightarrow> \<xi> matches-u \<Xi> \<longrightarrow> (\<sigma>,s) \<in> srel \<longrightarrow>
   (\<not> snd (m s) \<and>
   (\<forall>r' s'. (r',s') \<in> fst (m s) \<longrightarrow>
     (\<exists>\<sigma>' r.(\<xi>, \<gamma> \<turnstile> (\<sigma>,c)  \<Down>! (\<sigma>',r)) \<and> (\<sigma>',s') \<in> srel \<and> val_rel r r')))"


(* Rules about corres *)
lemma corres_u_sem_eq:
  "\<lbrakk> \<And>a. \<xi>', \<gamma> \<turnstile> (\<sigma>, f) \<Down>! a \<Longrightarrow> \<xi>', \<gamma> \<turnstile> (\<sigma>, g) \<Down>! a;
     corres srel f f' \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s
   \<rbrakk> \<Longrightarrow> corres srel g f' \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  apply (clarsimp simp: corres_def)
  apply blast
  done

lemma corres_monad_eq:
  "\<lbrakk> f' = g'; corres srel f f' \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s \<rbrakk> \<Longrightarrow> corres srel f g' \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s"
  by simp

lemma corres_def':
  "corres srel c m \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s =
   (proc_ctx_wellformed \<Xi>' \<longrightarrow> \<xi>' matches-u \<Xi>' \<longrightarrow> (\<sigma>,s) \<in> srel \<longrightarrow>
   (\<exists>r w. \<Xi>', \<sigma> \<turnstile> \<gamma> matches \<Gamma>' \<langle>r, w\<rangle>) \<longrightarrow>
   \<lbrace>\<lambda>s0. s0 = s\<rbrace> m \<lbrace>\<lambda>r' s'. \<exists>\<sigma>' r. (\<xi>', \<gamma> \<turnstile> (\<sigma>,c) \<Down>! (\<sigma>',r)) \<and> (\<sigma>',s') \<in> srel \<and> val_rel r r'\<rbrace>!)"
  by (auto simp: corres_def validNF_def valid_def no_fail_def)


(* Syntax-directed rules for Cogent *)
lemma corres_var:
  "val_rel (\<gamma>!x) (v'::'a::cogent_C_val) \<Longrightarrow>  \<comment> \<open> type_rel t TYPE('a) \<Longrightarrow> \<close>
   corres srel (Var x) (gets (\<lambda>_. v')) \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s"
  by (fastforce simp: fst_return corres_def snd_return intro: u_sem_var)

lemma corres_lit:
  "val_rel (UPrim lit) mv \<Longrightarrow> corres srel (Lit lit) (gets (\<lambda>_. mv)) \<xi> \<gamma> \<Xi> \<Gamma>  \<sigma> s"
  by (fastforce simp: corres_def snd_return fst_return intro: u_sem_lit)


lemma corres_cast_8_16:
  assumes typing_cast: "\<Xi>, [], \<Gamma>' \<turnstile> Cast U16 (Var x) : TPrim (Num U16)"
  assumes val_rel_var: "val_rel (\<gamma>!x) (x'::word8)"
  shows "corres srel (Cast U16 (Var x)) (gets (\<lambda>_. (ucast x' :: word16))) \<xi> \<gamma> \<Xi> \<Gamma>' \<sigma> s"
  apply (insert val_rel_var)
  apply (clarsimp simp: corres_def fst_return snd_return)
  apply (rename_tac r w)
  apply (insert typing_cast)
  apply (erule typing_castE)
  apply (erule typing_varE)
  apply (frule_tac matches_ptrs_proj', simp+)
  apply clarsimp
  apply (rename_tac rr')
  apply (erule uval_typing.cases, simp_all)
  apply (clarsimp split: lit.splits)
  apply (rename_tac \<tau> l)
  apply (case_tac l)
  apply (simp_all add: val_rel_word)+
  apply (rename_tac word)
  apply (rule_tac x=\<sigma> in exI)
  apply (fastforce intro!: u_sem_cast u_sem_var elim: subst simp: val_rel_word)
  done

lemma corres_cast_8_32:
  assumes typing_cast: "\<Xi>, [], \<Gamma>' \<turnstile> Cast U32 (Var x) : TPrim (Num U32)"
  assumes val_rel_var: "val_rel (\<gamma>!x) (x':: word8)"
  shows "corres srel (Cast U32 (Var x)) (gets (\<lambda>_. (ucast x' :: word32))) \<xi> \<gamma> \<Xi> \<Gamma>' \<sigma> s"
  apply (insert val_rel_var)
  apply (clarsimp simp: corres_def fst_return snd_return)
  apply (rename_tac r w)
  apply (insert typing_cast)
  apply (erule typing_castE)
  apply (erule typing_varE)
  apply (frule_tac matches_ptrs_proj', simp+)
  apply clarsimp
  apply (rename_tac rr')
  apply (erule uval_typing.cases, simp_all)
  apply (clarsimp split: lit.splits)
  apply (rename_tac \<tau> l)
  apply (case_tac l)
  apply (simp_all add: val_rel_word)+
  apply (rename_tac word)
  apply (rule_tac x=\<sigma> in exI)
  apply (fastforce intro!: u_sem_cast u_sem_var elim: subst simp: val_rel_word)
  done

lemma corres_cast_16_32:
  assumes typing_cast: "\<Xi>, [], \<Gamma>' \<turnstile> Cast U32 (Var x) : TPrim (Num U32)"
  assumes val_rel_var: "val_rel (\<gamma>!x) (x':: word16)"
  shows "corres srel (Cast U32 (Var x)) (gets (\<lambda>_. (ucast x' :: word32))) \<xi> \<gamma> \<Xi> \<Gamma>' \<sigma> s"
  apply (insert val_rel_var)
  apply (clarsimp simp: corres_def fst_return snd_return)
  apply (rename_tac r w)
  apply (insert typing_cast)
  apply (erule typing_castE)
  apply (erule typing_varE)
  apply (frule_tac matches_ptrs_proj', simp+)
  apply clarsimp
  apply (rename_tac rr')
  apply (erule uval_typing.cases, simp_all)
  apply (clarsimp split: lit.splits)
  apply (rename_tac \<tau> l)
  apply (case_tac l)
  apply (simp_all add: val_rel_word)+
  apply (rename_tac word)
  apply (rule_tac x=\<sigma> in exI)
  apply (fastforce intro!: u_sem_cast u_sem_var elim: subst simp: val_rel_word)
  done

lemma corres_cast_8_64:
  assumes typing_cast: "\<Xi>, [], \<Gamma>' \<turnstile> Cast U64 (Var x) : TPrim (Num U64)"
  assumes val_rel_var: "val_rel (\<gamma>!x) (x':: word8)"
  shows "corres srel (Cast U64 (Var x)) (gets (\<lambda>_. (ucast x' :: word64))) \<xi> \<gamma> \<Xi> \<Gamma>' \<sigma> s"
  apply (insert val_rel_var)
  apply (clarsimp simp: corres_def fst_return snd_return)
  apply (rename_tac r w)
  apply (insert typing_cast)
  apply (erule typing_castE)
  apply (erule typing_varE)
  apply (frule_tac matches_ptrs_proj', simp+)
  apply clarsimp
  apply (rename_tac rr')
  apply (erule uval_typing.cases, simp_all)
  apply (clarsimp split: lit.splits)
  apply (rename_tac \<tau> l)
  apply (case_tac l)
  apply (simp_all add: val_rel_word)+
  apply (rename_tac word)
  apply (rule_tac x=\<sigma> in exI)
  apply (fastforce intro!: u_sem_cast u_sem_var elim: subst simp: val_rel_word)
  done

lemma corres_cast_16_64:
  assumes typing_cast: "\<Xi>, [], \<Gamma>' \<turnstile> Cast U64 (Var x) : TPrim (Num U64)"
  assumes val_rel_var: "val_rel (\<gamma>!x) (x':: word16)"
  shows "corres srel (Cast U64 (Var x)) (gets (\<lambda>_. (ucast x' :: word64))) \<xi> \<gamma> \<Xi> \<Gamma>' \<sigma> s"
  apply (insert val_rel_var)
  apply (clarsimp simp: corres_def fst_return snd_return)
  apply (rename_tac r w)
  apply (insert typing_cast)
  apply (erule typing_castE)
  apply (erule typing_varE)
  apply (frule_tac matches_ptrs_proj', simp+)
  apply clarsimp
  apply (rename_tac rr')
  apply (erule uval_typing.cases, simp_all)
  apply (clarsimp split: lit.splits)
  apply (rename_tac \<tau> l)
  apply (case_tac l)
  apply (simp_all add: val_rel_word)+
  apply (rename_tac word)
  apply (rule_tac x=\<sigma> in exI)
  apply (fastforce intro!: u_sem_cast u_sem_var elim: subst simp: val_rel_word)
  done

lemma corres_cast_32_64:
  assumes typing_cast: "\<Xi>, [], \<Gamma>' \<turnstile> Cast U64 (Var x) : TPrim (Num U64)"
  assumes val_rel_var: "val_rel (\<gamma>!x) (x':: word32)"
  shows "corres srel (Cast U64 (Var x)) (gets (\<lambda>_. (ucast x' :: word64))) \<xi> \<gamma> \<Xi> \<Gamma>' \<sigma> s"
  apply (insert val_rel_var)
  apply (clarsimp simp: corres_def fst_return snd_return)
  apply (rename_tac r w)
  apply (insert typing_cast)
  apply (erule typing_castE)
  apply (erule typing_varE)
  apply (frule_tac matches_ptrs_proj', simp+)
  apply clarsimp
  apply (rename_tac rr')
  apply (erule uval_typing.cases, simp_all)
  apply (clarsimp split: lit.splits)
  apply (rename_tac \<tau> l)
  apply (case_tac l)
  apply (simp_all add: val_rel_word)+
  apply (rename_tac word)
  apply (rule_tac x=\<sigma> in exI)
  apply (fastforce intro!: u_sem_cast u_sem_var elim: subst simp: val_rel_word)
  done

lemmas corres_cast =
  corres_cast_8_16 corres_cast_8_32 corres_cast_16_32 corres_cast_8_64 corres_cast_16_64 corres_cast_32_64

(*
lemma list_all2_corres_varI:
  assumes "corres srel (Var i) c \<xi> \<gamma> \<Xi> \<Gamma>  \<sigma> s"
  assumes "list_all2 (\<lambda>m c. corres srel m c \<xi> \<gamma> \<Xi> \<Gamma>) (map Var is) cs"
  shows "list_all2 (\<lambda>m c. corres srel m c \<xi> \<gamma> \<Xi> \<Gamma>) (map Var []) []"
  and "list_all2 (\<lambda>m c. corres srel m c \<xi> \<gamma> \<Xi> \<Gamma>) (map Var (i#is)) (c # cs)"
  oops
*)


lemma in_unknown_bind:
  "(x \<in> fst ((unknown >>= prog) s)) = (\<exists>y. x \<in> fst (prog y s))"
  by (clarsimp simp: unknown_def bind_def select_def)

lemma corres_let:
  assumes split\<Gamma>: "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  assumes typing_x: "\<Xi>, [], \<Gamma>1 \<turnstile> x : t"
  assumes corres_x: "corres srel x x' \<xi> \<gamma> \<Xi> \<Gamma>1 \<sigma> s"
  assumes corres_cont: "\<And>v v' \<sigma>' s'. val_rel v (v'::'a::cogent_C_val) \<Longrightarrow>
                      corres srel y (y' v') \<xi> (v # \<gamma>) \<Xi> (Some t # \<Gamma>2) \<sigma>' s'"
  shows "corres srel (Let x y) (x' >>= y') \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s"
  apply (clarsimp simp: corres_def snd_bind in_monad)
  apply (rename_tac r w)
  apply (frule matches_ptrs_split'[OF split\<Gamma>])
  apply clarsimp
  apply (rename_tac r' w' r'' w'')
  apply (insert corres_x[unfolded corres_def])
  apply simp
  apply (erule impE, fast)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (rename_tac v' s')
   apply (drule_tac x=v' in spec, drule_tac x=s' in spec)
   apply clarsimp
   apply (rename_tac \<sigma>' v)
   apply (insert corres_cont[unfolded corres_def])
   apply (drule_tac x=v in meta_spec, drule_tac x=v' in meta_spec)
   apply simp
   apply (drule_tac x=\<sigma>' in meta_spec, drule_tac x=s' in meta_spec)
   apply (erule impE, assumption)
   apply (erule impE)
    apply (insert typing_x)
    apply (frule(4) preservation_mono(1)[where \<Gamma>=\<Gamma>1])
    apply (clarsimp)
    apply (rename_tac rv wv)
    apply (frule matches_ptrs_noalias)
    apply (rule_tac x="rv\<union>r''" in exI, rule_tac x="wv\<union>w''" in exI)
    apply (rule matches_ptrs_some, simp+)
       apply (force intro: matches_ptrs_frame)
      apply (force dest: frame_noalias_matches_ptrs(1))
     apply (force dest!: frame_noalias_matches_ptrs(2))
    apply blast
   apply fast
  apply clarsimp
  apply (rename_tac  r' s''  s' v')
  apply (drule_tac x=v' in spec, drule_tac x=s' in spec)
  apply clarsimp
  apply (rename_tac \<sigma>' v)
  apply (drule_tac x=v in meta_spec, drule_tac x=v' in meta_spec)
  apply clarsimp
  apply (drule_tac x=\<sigma>' in meta_spec, drule_tac x=s' in meta_spec)
  apply simp
  apply (erule impE)
   apply (insert typing_x)
   apply (frule(4) preservation_mono(1)[where \<Gamma>=\<Gamma>1])
   apply (clarsimp)
   apply (rename_tac rv wv)
   apply (frule matches_ptrs_noalias)
   apply (rule_tac x="rv\<union>r''" in exI, rule_tac x="wv\<union>w''" in exI)
   apply (rule matches_ptrs_some, simp+)
      apply (force intro: matches_ptrs_frame)
     apply (force dest: frame_noalias_matches_ptrs(1))
    apply (force dest!: frame_noalias_matches_ptrs(2))
   apply blast
  apply (fastforce intro!: u_sem_let)
  done

lemma corres_nested_let_base:
  assumes let_const_def: "LET_CONST \<equiv> (1 :: ('c :: len) word)"
  assumes split\<Gamma>: "[] \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1 | \<Gamma>2"
  assumes typing_x: "\<Xi>', [], \<Gamma>1 \<turnstile> x : t"
  assumes corres_x: "corres srel x x' \<xi> \<gamma> \<Xi>' \<Gamma>1 \<sigma> s"
  assumes corres_cont: "\<And>v v' \<sigma>' s'. val_rel v (v'::'a::cogent_C_val) \<Longrightarrow>
                      corres srel y (y' v') \<xi> (v # \<gamma>) \<Xi>' (Some t # \<Gamma>2) \<sigma>' s'"
  shows "corres srel (Let x y)
           (condition (\<lambda>_. LET_CONST \<noteq> 0) x' (dummy' dummy) >>= y')
         \<xi> \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  apply (fastforce intro!: corres_let intro: assms(2-) simp: let_const_def)
  done

(* Like corres_let, but remembers the bound value in corres_cont.
 * It is restricted to "gets" expressions, where a concrete value (x') is always available. *)
lemma corres_let_gets_propagate:
  assumes split\<Gamma>: "[] \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1 | \<Gamma>2"
  assumes typing_x: "\<Xi>', [], \<Gamma>1 \<turnstile> x : t"
  assumes corres_x: "corres srel x (gets (\<lambda>_. x')) \<xi>' \<gamma> \<Xi>' \<Gamma>1 \<sigma> s"
  assumes corres_cont: "\<And>v v' \<sigma>' s'. val_rel v (v'::'a::cogent_C_val) \<Longrightarrow> v' = x'
                         \<Longrightarrow> corres srel y (y' v') \<xi>' (v # \<gamma>) \<Xi>' (Some t # \<Gamma>2) \<sigma>' s'"
  shows "corres srel (Let x y) (gets (\<lambda>_. x') >>= y') \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  apply (monad_eq simp: corres_def snd_bind in_monad)
  apply (rename_tac r w)
  apply (frule matches_ptrs_split'[OF split\<Gamma>])
  apply clarsimp
  apply (rename_tac r' w' r'' w'')
  apply (insert corres_x[unfolded corres_def])
  apply simp
  apply (erule impE, fast)
  apply (insert corres_cont[unfolded corres_def])
  apply monad_eq
  apply (rename_tac \<sigma>' v)
  apply (drule_tac x=v in meta_spec, drule_tac x=x' in meta_spec)
  apply simp
  apply (drule_tac x=\<sigma>' in meta_spec, drule_tac x=s in meta_spec)
  apply (erule impE, assumption)
  apply (erule impE)
   apply (insert typing_x)
   apply (frule(4) preservation_mono(1)[where \<Gamma>=\<Gamma>1])
   apply (clarsimp)
   apply (rename_tac rv wv)
   apply (frule matches_ptrs_noalias)
   apply (rule_tac x="rv\<union>r''" in exI, rule_tac x="wv\<union>w''" in exI)
   apply (rule matches_ptrs_some, simp+)
      apply (force intro: matches_ptrs_frame)
     apply (force dest: frame_noalias_matches_ptrs(1))
    apply (force dest!: frame_noalias_matches_ptrs(2))
   apply blast
  apply clarsimp
  apply (rename_tac ret s')
  apply (drule_tac x=ret in spec, drule_tac x=s' in spec)
  apply (fastforce intro!: u_sem_let)
  done


lemma corres_letbang':
  assumes split\<Gamma>: "split_bang [] is \<Gamma>' \<Gamma>1 \<Gamma>2"
  assumes typing_x: "\<Xi>', [], \<Gamma>1 \<turnstile> x : t"
  assumes has_kind: " [] \<turnstile>  t :\<kappa>  k"
  assumes kind_escapable: "E \<in> k"
  assumes corres_x: "corres srel x x' \<xi>' \<gamma> \<Xi>' \<Gamma>1 \<sigma> s"
  assumes corres_cont: "\<And>v v' \<sigma>' s'. val_rel v (v'::'a::cogent_C_val) \<Longrightarrow>
                      corres srel y (y' v') \<xi>' (v # \<gamma>) \<Xi>' (Some t # \<Gamma>2) \<sigma>' s'"
  shows "corres srel (LetBang is x y) (x' >>= y') \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  apply (clarsimp simp: corres_def snd_bind in_monad)
  apply (rename_tac r w)
  apply (frule matches_ptrs_split_bang'[OF split\<Gamma>])
  apply clarsimp
  apply (rename_tac r' w' r'' w'' p)
  apply (insert corres_x[unfolded corres_def])
  apply simp
  apply (erule impE, fast)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (rename_tac v' s')
   apply (drule_tac x=v' in spec, drule_tac x=s' in spec)
   apply clarsimp
   apply (rename_tac \<sigma>' v)
   apply (insert corres_cont[unfolded corres_def])
   apply (drule_tac x=v in meta_spec, drule_tac x=v' in meta_spec)
   apply simp
   apply (drule_tac x=\<sigma>' in meta_spec, drule_tac x=s' in meta_spec)
   apply (erule impE, assumption)
   apply (erule impE)
    apply (insert typing_x)
    apply (frule(4) preservation_mono(1)[where \<Gamma>=\<Gamma>1])
    apply (clarsimp)
    apply (rename_tac rv wv)
    apply (frule matches_ptrs_noalias)
    apply (rule_tac x="rv\<union>r''" in exI, rule_tac x="wv\<union>(w''\<union>p)" in exI)
    apply (rule matches_ptrs_some, simp+)
       apply (force intro: matches_ptrs_frame)
      apply (rule frame_noalias_matches_ptrs(1), simp+, blast)
     apply (rule frame_noalias_matches_ptrs(2), simp+, blast)
    apply (insert has_kind kind_escapable)[]
    apply (frule(2) escapable_no_readers(1))
    apply blast
   apply fast
  apply clarsimp
  apply (rename_tac  r' s''  s' v')
  apply (drule_tac x=v' in spec, drule_tac x=s' in spec)
  apply clarsimp
  apply (rename_tac \<sigma>' v)
  apply (drule_tac x=v in meta_spec, drule_tac x=v' in meta_spec)
  apply clarsimp
  apply (drule_tac x=\<sigma>' in meta_spec, drule_tac x=s' in meta_spec)
  apply simp
  apply (erule impE)
   apply (insert typing_x)
   apply (frule(4) preservation_mono(1)[where \<Gamma>=\<Gamma>1])
   apply (clarsimp)
   apply (rename_tac rv wv)
   apply (frule matches_ptrs_noalias)
   apply (rule_tac x="rv\<union>r''" in exI, rule_tac x="wv\<union>(w''\<union>p)" in exI)
   apply (rule matches_ptrs_some, simp+)
       apply (force intro: matches_ptrs_frame)
      apply (rule frame_noalias_matches_ptrs(1), simp+, blast)
     apply (rule frame_noalias_matches_ptrs(2), simp+, blast)
    apply (insert has_kind kind_escapable)[]
    apply (frule(2) escapable_no_readers(1))
    apply blast
  apply (fastforce intro!: u_sem_letbang)
  done

(* The Cogent compiler wraps x' in a dummy condition to ease pattern matching. *)
lemma corres_letbang:
  assumes split\<Gamma>: "split_bang [] is \<Gamma>' \<Gamma>1 \<Gamma>2"
  assumes typing_x: "\<Xi>', [], \<Gamma>1 \<turnstile> x : t"
  assumes has_kind: " [] \<turnstile>  t :\<kappa>  k"
  assumes kind_escapable: "E \<in> k"
  assumes corres_x: "corres srel x x' \<xi>' \<gamma> \<Xi>' \<Gamma>1 \<sigma> s"
  assumes corres_cont: "\<And>v v' \<sigma>' s'. val_rel v (v'::'a::cogent_C_val) \<Longrightarrow>
                      corres srel y (y' v') \<xi>' (v # \<gamma>) \<Xi>' (Some t # \<Gamma>2) \<sigma>' s'"
  shows "corres srel (LetBang is x y)
           (condition (\<lambda>s. 1 \<noteq> (0::32 signed word)) x' not_reached' >>= y')
           \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  apply (subgoal_tac
    "(condition (\<lambda>s. 1 \<noteq> (0::32 signed word)) x' not_reached' >>= y')
      = (x' >>= y')")
  apply simp
  apply (rule corres_letbang'[OF assms], simp)
  apply monad_eq
  done

lemma corres_tuple:
assumes "val_rel (UProduct (\<gamma>!x) (\<gamma>!y)) p"
shows "corres srel (Tuple (Var x) (Var y)) (gets (\<lambda>_. p)) \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s"
  by (fastforce intro: u_sem_tuple u_sem_var simp: assms corres_def snd_return in_return)


lemma list_to_map_singleton: "[f x] = (map f [x])"  by auto
lemma list_to_map_more: "(f x) # (map f xs) = (map f (x#xs))" by auto

lemma u_sem_all_var:
  "\<xi>, \<gamma> \<turnstile>* (\<sigma>, map Var xs) \<Down>! (\<sigma>, map ((!) \<gamma>) xs)"
proof (induct xs)
   case Cons thus ?case by (fastforce intro: u_sem_all_cons u_sem_var)
qed (simp add: u_sem_all_empty)

lemma corres_struct:
assumes
 "\<And>\<sigma> s. (\<sigma>, s) \<in> srel \<Longrightarrow>
  val_rel (URecord (zip (map (nth \<gamma>) xs) (zip ns (map type_repr ts)))) p"
shows "corres srel (Struct ns ts (map Var xs)) (gets (\<lambda>_. p)) \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s"
  by (fastforce intro: u_sem_struct u_sem_all_var simp: assms corres_def snd_return in_return)

lemma corres_con:
assumes "val_rel (USum tag (\<gamma> ! x)  (map (\<lambda>(n,t,_).(n,type_repr t)) typ)) p"
shows "corres srel (Con typ tag (Var x)) (gets (\<lambda>_. p)) \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s"
  by (fastforce simp add: assms corres_def snd_return in_return intro: u_sem_con u_sem_var)

lemma corres_split:
  assumes split\<Gamma>: "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  assumes \<gamma>_x: "\<gamma>!x = UProduct a b"
  assumes \<Gamma>_x: "\<Gamma>!x = Some (TProduct ta tb)"
  assumes typing_x: "\<Xi>, [], \<Gamma>1 \<turnstile> Var x : TProduct ta tb"
  assumes typing_cont: "(\<Xi>, [], Some ta # Some tb # \<Gamma>2 \<turnstile> e : te)"
  assumes val_rel_fst: "val_rel a (x1::'a1::cogent_C_val)"
  assumes val_rel_snd: "val_rel b (x2::'a2::cogent_C_val)"
  assumes corres_cont: "\<And>a' b' x1' x2'.
      \<lbrakk> val_rel a' (x1'::'a1::cogent_C_val); val_rel b' (x2'::'a2::cogent_C_val) \<rbrakk> \<Longrightarrow>
                corres srel e (e' x1' x2') \<xi> (a' # b' # \<gamma>) \<Xi> (Some ta # Some tb # \<Gamma>2) \<sigma> s"
  shows "corres srel
           (Split (Var x) e)
           (do a' \<leftarrow> gets (\<lambda>_. x1);
               b' \<leftarrow> gets (\<lambda>_. x2);
               e' a' b' od) \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s"
  apply (clarsimp simp: corres_def)
  apply (rename_tac r w)
  apply (insert split\<Gamma> \<gamma>_x \<Gamma>_x typing_x typing_cont)
  apply (erule typing_varE)
  apply (frule(1) matches_ptrs_split')
  apply clarsimp
  apply (rename_tac r' w' r'' w'')
  apply (frule_tac \<Gamma>=\<Gamma>1 in matches_ptrs_proj', simp+)
  apply clarsimp
  apply (rename_tac rr')
  apply (erule uval_typing.cases, simp_all)
  apply (rename_tac \<Xi>' \<sigma>' a' ta' ra wa b' tb' rb wb)
  apply clarsimp
  apply (insert corres_cont[OF val_rel_fst val_rel_snd,unfolded corres_def])
  apply simp
  apply (erule impE)
  apply (frule matches_ptrs_noalias)
   apply (frule_tac ta=ta and tb=tb and \<Gamma>=\<Gamma>2 in matches_ptrs_some_some)
           apply (blast+)[9]
  apply clarsimp
  apply (rename_tac s' ev')
  apply (erule_tac x=s' in allE)
  apply (erule_tac x=ev' in allE)
  apply clarsimp
  apply (rename_tac \<sigma>'' ev)
  apply (rule_tac x=\<sigma>'' in exI)
  apply (rule_tac x=ev in exI)
  apply (fastforce intro!: u_sem_split u_sem_var elim:subst)
  done

lemma corres_split_lazy:
  "\<lbrakk> val_rel (\<gamma> ! x) x';
     [] \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1 | \<Gamma>2;
     \<exists>a b. \<gamma> ! x = UProduct a b \<and> val_rel a (p1 x') \<and> val_rel b (p2 x');
     \<Gamma>' ! x = Some (TProduct ta tb);
     \<Xi>', [], \<Gamma>1 \<turnstile> Var x : TProduct ta tb;
     \<Xi>', [], Some ta # Some tb # \<Gamma>2 \<turnstile> e : te;
     \<And>a' b' x1' x2'.
       \<lbrakk> val_rel a' x1';
         val_rel b' x2' \<rbrakk> \<Longrightarrow>
        corres srel e (e' x1' x2') \<xi>' (a' # b' # \<gamma>) \<Xi>' (Some ta # Some tb # \<Gamma>2) \<sigma> s
    \<rbrakk> \<Longrightarrow>
    corres srel (Split (Var x) e) (e' (p1 x') (p2 x'))
           \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  by (blast intro: corres_split[simplified])

lemma corres_take_unboxed':
  assumes x_sigil: "\<Gamma>!x = Some (TRecord typ Unboxed)"
  assumes \<gamma>_x: "\<gamma>!x = URecord fs"
  assumes split\<Gamma>: "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  assumes typing_stat: "\<Xi>, [], \<Gamma> \<turnstile> Take (Var x) f e : te"
  assumes typing_x:  "\<Xi>, [], \<Gamma>1 \<turnstile> (Var x) : TRecord typ Unboxed"
  assumes e_typ: "\<Xi>, [], Some (fst (snd (typ!f))) # Some (TRecord (typ[f := (fst (typ!f), fst (snd (typ!f)), taken)]) Unboxed) # \<Gamma>2 \<turnstile> e : te"
  assumes has_kind: "[] \<turnstile>  fst (snd (typ!f)) :\<kappa>  k"
  assumes shareable_or_taken: "(S \<in> k \<or> taken = Taken)"
  assumes x_unboxed: "corres srel e (e' (f' s)) \<xi> (fst (fs!f)# (\<gamma>!x)# \<gamma>) \<Xi> (Some (fst (snd (typ!f)))# Some (TRecord (typ [f := (fst (typ!f), fst (snd (typ!f)),taken)]) Unboxed)# \<Gamma>2) \<sigma> s"
shows "corres srel (Take (Var x) f e) (do z \<leftarrow> gets f'; e' z od) \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s"
  apply (clarsimp simp: corres_def in_monad snd_bind snd_gets snd_state_assert)
  apply (rename_tac r w)
  apply (insert typing_stat x_sigil \<gamma>_x)
  apply (erule typing_takeE)
  apply (rename_tac \<Gamma>1' \<Gamma>2' tr access tag t k taken')
  apply (erule typing_varE)
  apply (frule(1) matches_ptrs_split')
  apply clarsimp
  apply (rename_tac r1 w1 r2 w2)
  apply (frule_tac \<Gamma>=\<Gamma>1' in matches_ptrs_proj', (simp+)[2])
  apply clarsimp
  apply (rename_tac r1'a)
  apply (insert split\<Gamma>)
  apply (erule uval_typing.cases; simp)
  apply (rename_tac \<Xi>' \<sigma>' fs' typ' r1' w1)
  apply (drule(2) same_type_as_split_weakened_left)
  apply clarsimp
  apply (insert x_unboxed[unfolded corres_def] typing_x)
  apply (erule typing_varE)
  apply (frule(1) matches_ptrs_split')
  apply clarsimp
  apply (rename_tac r1x w1x r2x w2x)
  apply (drule matches_ptrs_noalias)
  apply (frule_tac \<Gamma>=\<Gamma>1 in matches_ptrs_proj', (simp+)[2])
  apply clarsimp
  apply (rename_tac r1x')
  apply (erule impE)
   apply (erule u_t_recE, simp)
   apply (cases taken)
    apply (frule_tac r=r1x' in uval_typing_record_take, ((simp add: kinding_def)+)[3])
    apply (clarsimp simp add: Int_Un_distrib Int_Un_distrib2)
    apply (rename_tac r1x'a w1a r1x'b w1b)
    apply (rule_tac x= "r1x'a \<union> (r1x'b \<union> r2x)" in exI, rule_tac x= "w1a \<union> (w1b \<union> w2x)" in exI)
    apply (rule matches_ptrs_some[OF _ matches_ptrs_some])
            apply simp
           apply (force intro: u_t_struct simp add: distinct_fst_tags_update)
          apply (blast+)[3]
       apply auto[4]
   apply clarsimp
  apply (frule_tac r=r1' in uval_typing_record_nth', simp+)
  apply clarsimp
  apply (rename_tac r1'' w1')
  apply (insert has_kind shareable_or_taken)
  apply clarsimp
  apply (frule(2) shareable_not_writable)
  apply (rule_tac x= "r1'' \<union> (r1x' \<union> r2x)" in exI, rule_tac x= "w1' \<union> (w1x \<union> w2x)" in exI)
  apply (rule matches_ptrs_some[OF _ matches_ptrs_some])
           apply simp
          apply (erule subst[where s="typ ! f"], simp)
          apply (intro u_t_struct, simp)
          apply (fast+)[3]
       apply auto[2]
     apply (fast+)[2]
   apply fast (* slow *)
  apply clarsimp
  apply (rename_tac s' ev')
  apply (erule_tac x=s' in allE)
  apply (erule_tac x=ev' in allE)
  apply clarsimp
  apply (rename_tac \<sigma>'' ev)
  apply (rule_tac x=\<sigma>'' in exI)
  apply (rule_tac x=ev in exI)
  apply (fastforce intro!: u_sem_take_ub u_sem_var elim:subst)
  done

lemma corres_take_unboxed:
  assumes x_sigil: "\<Gamma>!x = Some (TRecord typ Unboxed)"
  assumes \<gamma>_x: "\<gamma>!x = URecord fs"
  assumes split\<Gamma>: "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  assumes typing_stat: "\<Xi>, [], \<Gamma> \<turnstile> Take (Var x) f e : te"
  assumes typing_x:  "\<Xi>, [], \<Gamma>1 \<turnstile> (Var x) : TRecord typ Unboxed" (* needed? *)
  assumes e_typ: "\<Xi>, [], Some (fst (snd (typ!f))) # Some (TRecord (typ[f := (fst (typ!f), fst (snd (typ!f)), taken)]) Unboxed) # \<Gamma>2 \<turnstile> e : te"
  assumes has_kind: "[] \<turnstile> fst (snd (typ!f)) :\<kappa> k"
  assumes shareable_or_taken: "(S \<in> k \<or> taken = Taken)"
  assumes val_rel_f: "val_rel (fst (fs!f)) ((f' s)::'bb::cogent_C_val)"
  assumes type_rel_f: "type_rel (type_repr (fst (snd (typ!f)))) TYPE('bb)"
  assumes corres_cont:
   "\<And>fsf f's. val_rel fsf (f's::'bb) \<Longrightarrow>
    corres srel e (e' f's) \<xi> (fsf# (\<gamma>!x)# \<gamma>) \<Xi> (Some (fst (snd (typ!f)))# Some (TRecord (typ [f := (fst (typ!f), fst (snd (typ!f)),taken)]) Unboxed)# \<Gamma>2) \<sigma> s"
  shows "corres srel (Take (Var x) f e) (do z \<leftarrow> gets f'; e' z od) \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s"
  apply (rule corres_take_unboxed'[OF assms(1-8)])
  using assms(9-) by blast

lemma map2_nth_eq:
  "map f xs = map g ys \<Longrightarrow> i < length xs \<Longrightarrow> f (xs ! i) = g (ys ! i)"
  apply (frule map_eq_imp_length_eq)
  apply (rotate_tac -1)
  apply (induct xs ys arbitrary: i rule: list_induct2)
   apply simp
  apply simp
  apply (case_tac i)
   apply simp
  apply simp
  done

lemma map_list_update_id:
  "\<lbrakk> xs ! i = v; i < length xs; f v = f' v \<rbrakk> \<Longrightarrow>
   (map f xs)[i := f' v] = map f xs"
  apply (induct i arbitrary: xs)
   apply (case_tac xs, simp)
   apply simp
  apply (case_tac xs, simp)
  apply simp
  done

lemma corres_take_boxed':
  assumes sigil_wr: "sgl = Boxed Writable l"
  assumes x_sigil: "\<Gamma>!x = Some (TRecord typ sgl)"
  assumes \<gamma>_x: "\<gamma>!x = UPtr p repr"
  assumes split\<Gamma>: "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  assumes val_rel_x: "val_rel (\<gamma>!x) (x'::('a::cogent_C_val))"
  assumes typing_stat: "\<Xi>, [], \<Gamma> \<turnstile> Take (Var x) f e : te"
  assumes typing_x:  "\<Xi>, [], \<Gamma>1 \<turnstile> (Var x) : TRecord typ sgl" (* needed? *)
  assumes e_typ: "\<Xi>, [], Some (fst (snd (typ!f))) # Some (TRecord (typ[f := (fst (typ!f), fst (snd (typ!f)), taken)]) sgl) # \<Gamma>2 \<turnstile> e : te"
  assumes has_kind: "[] \<turnstile>  fst (snd (typ!f)) :\<kappa>  k"
  assumes shareable_or_taken: "(S \<in> k \<or> taken = Taken)"
  assumes x_boxed:
    "\<And> fs r w.
    \<lbrakk>(\<sigma>,s)\<in>srel; \<sigma> p = Some (URecord fs);
    \<Xi>, \<sigma> \<turnstile> UPtr p repr :u TRecord typ sgl \<langle>r, w\<rangle>\<rbrakk> \<Longrightarrow>
      is_valid s x' \<and>
      corres srel e (e' (f' s)) \<xi> (fst(fs!f)# (\<gamma>!x)# \<gamma>) \<Xi> (Some (fst (snd (typ!f))) # Some (TRecord (typ [f := (fst (typ!f), fst (snd (typ!f)),taken)]) sgl) # \<Gamma>2) \<sigma> s"
  shows
  "corres srel
  (Take (Var x) f e)
  (do _ \<leftarrow> guard (\<lambda>s. is_valid s x'); z \<leftarrow> gets f'; e' z od)
  \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s"
proof -
  have HELP: "\<And>tag t b. typ ! f = (tag, t, b) \<Longrightarrow> map (\<lambda> (n,t,_). (n, type_repr t)) typ = map (\<lambda> (n,t,_). (n, type_repr t)) (typ[f := (tag, t, Present)])"
    by (simp add: map_update, metis (mono_tags, lifting)  old.prod.case list_update_id map_update prod_injects(1))
  show ?thesis
    apply (clarsimp simp: corres_def in_monad snd_bind snd_gets snd_state_assert)
    apply (rename_tac r w)
    apply (insert typing_stat x_sigil \<gamma>_x)
    apply (erule typing_takeE)
    apply (rename_tac \<Gamma>1' \<Gamma>2' tr access tag t k taken')
    apply (erule typing_varE)
    apply (frule(1) matches_ptrs_split')
    apply clarsimp
    apply (rename_tac rx' wx' rx'' wx'')
    apply (frule_tac \<Gamma>=\<Gamma>1' in matches_ptrs_proj', simp+)
    apply clarsimp
    apply (rename_tac rrx')
    apply (insert split\<Gamma> val_rel_x)
    apply (erule uval_typing.cases, simp_all)
    apply (rename_tac \<Xi>' \<sigma>' fs' typ' r' w' p')
    apply (drule(2) same_type_as_split_weakened_left)
    apply (frule(2) uval_typing_record_nth')
    apply clarsimp
    apply (rename_tac rf' wf')
    apply (frule(3) uval_typing_taken_field[where taken=taken])
    apply clarsimp
    apply (rename_tac rft' wft')
    apply (frule(1) x_boxed[unfolded corres_def])
     apply (fastforce intro!: u_t_p_rec_w)
    apply clarsimp
    apply (insert typing_x)
    apply (erule typing_varE)
    apply (frule(1) matches_ptrs_split')
    apply clarsimp
    apply (rename_tac r' w' r'' w'')
    apply (drule matches_ptrs_noalias)
    apply (frule_tac \<Gamma>=\<Gamma>1 in matches_ptrs_proj', simp+)
    apply clarsimp
    apply (rename_tac rr')
    apply (erule impE)
     apply (erule_tac r=rr' in u_t_p_recE, simp)
     apply (cases taken)
      apply (frule_tac r=rr' in uval_typing_record_take, ((simp add: kinding_def)+)[3])
      apply (erule exE conjE)+
      apply (rename_tac rrr' ww' rr' w')
      apply (rule_tac x= "rrr' \<union> (rr'\<union> r'')" in exI, rule_tac x= "ww' \<union> ((insert p w')\<union> w'')" in exI)
      apply (rule matches_ptrs_some, simp)
         apply (rule matches_ptrs_some)
             apply (rule u_t_p_rec_w', (simp+)[3])
              apply (simp add: map_update)
              apply (subst map_list_update_id)
                 apply (simp+)[4]
             apply (force simp add: distinct_fst_tags_update)
            apply blast
           apply blast
          apply auto[1]
         apply blast
        apply auto[1]
       apply blast
      apply blast
     apply (frule_tac r=rr' in uval_typing_record_nth', simp+)
     apply clarsimp
     apply (rename_tac rrr' ww')
     apply (insert has_kind shareable_or_taken)
     apply simp
     apply (frule_tac w=ww' in shareable_not_writable(1), simp+)
     apply (rule_tac x= "rrr' \<union> (rr'\<union> r'')" in exI, rule_tac x= "ww' \<union> ((insert p w)\<union> w'')" in exI)
     apply (rule matches_ptrs_some, simp)
        apply (rule matches_ptrs_some)
            apply (simp add: list_helper)
            apply (rule u_t_p_rec_w)
               apply (blast+)[11]
    apply clarsimp
    apply (rename_tac s' ev')
    apply (erule_tac x=s' in allE)
    apply (erule_tac x=ev' in allE)
    apply clarsimp
    apply (rename_tac \<sigma>'' ev)
    apply (rule_tac x=\<sigma>'' in exI)
    apply (rule_tac x=ev in exI)
    apply (fastforce intro!: u_sem_take u_sem_var elim:subst)
    done
qed

lemma corres_take_boxed:
  assumes sigil_wr: "sgl = Boxed Writable l"
  assumes x_sigil: "\<Gamma>!x = Some (TRecord typ sgl)"
  assumes \<gamma>_x: "\<gamma>!x = UPtr p repr"
  assumes split\<Gamma>: "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  assumes val_rel_x: "val_rel (\<gamma>!x) (x'::('a::cogent_C_val) ptr)"
  assumes typing_stat: "\<Xi>, [], \<Gamma> \<turnstile> Take (Var x) f e : te"
  assumes typing_x:  "\<Xi>, [], \<Gamma>1 \<turnstile> (Var x) : TRecord typ sgl" (* needed? *)
  assumes e_typ: "\<Xi>, [], Some (fst (snd (typ!f))) # Some (TRecord (typ[f := (fst (typ!f), fst (snd (typ!f)), taken)]) sgl) # \<Gamma>2 \<turnstile> e : te"
  assumes has_kind: "[] \<turnstile> fst (snd (typ!f)) :\<kappa> k"
  assumes shareable_or_taken: "S \<in> k \<or> taken = Taken"
  assumes x_boxed:
  "\<And> fs r w. \<lbrakk>(\<sigma>, s)\<in> srel; \<sigma> p = Some (URecord fs); \<Xi>, \<sigma> \<turnstile> UPtr p repr :u TRecord typ sgl \<langle>r, w\<rangle>\<rbrakk> \<Longrightarrow>
   is_valid s x' \<and> val_rel (fst(fs!f)) ((f' s)::'bb::cogent_C_val)"
  assumes corres_cont:
  "\<And>fsf f's. val_rel fsf (f's::'bb)  \<Longrightarrow>
     corres srel e (e' f's) \<xi> (fsf# (\<gamma>!x)# \<gamma>) \<Xi> (Some (fst (snd (typ!f)))# Some (TRecord (typ [f := (fst (typ!f), fst (snd (typ!f)),taken)]) sgl)# \<Gamma>2) \<sigma> s"
  shows
  "corres srel
  (Take (Var x) f e)
  (do _ \<leftarrow> guard (\<lambda>s. is_valid s x'); z \<leftarrow> gets f'; e' z od)
  \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s"
  apply (rule corres_take_boxed'[OF assms(1-10)])
  using assms(11-) by fastforce

lemma corres_let_put_unboxed:
  assumes x_sigil: "\<Gamma>'!x = Some (TRecord typ Unboxed)"
  assumes x_len: "x < length \<Gamma>'"
  assumes split\<Gamma>: "[] \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1 | \<Gamma>2"
  assumes typing_put:  "\<Xi>', [], \<Gamma>1 \<turnstile> Put (Var x) f (Var e) : TRecord (typ[f := (fst (typ!f), fst (snd (typ!f)), Present)]) Unboxed" (* needed? *)
  assumes corres_cont:
   "\<And>fs. \<gamma>!x = URecord fs \<Longrightarrow> corres srel y (y' (nx' x')) \<xi> ((URecord (fs[f:= ((\<gamma>!e),  snd (fs ! f))])) # \<gamma>) \<Xi>' (Some (TRecord (typ[f := (fst (typ!f), fst (snd (typ!f)), Present)]) Unboxed) # \<Gamma>2) \<sigma> s"
  shows "corres srel
  (Let (Put (Var x) f (Var e)) y)
  ( (do
     rec \<leftarrow> gets (\<lambda>_. x');
     rec \<leftarrow> gets (\<lambda>_. nx' rec);
     rec' \<leftarrow> gets (\<lambda>_. rec);
     y' rec'
   od)) \<xi> \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  apply (clarsimp simp: corres_def)
  apply (rename_tac r w)
  apply (frule matches_ptrs_noalias)
  apply (frule matches_ptrs_split'[OF split\<Gamma>])
  apply clarsimp
  apply (rename_tac r' w' r'' w'')
  apply(subgoal_tac "\<exists>fs. \<gamma>!x = URecord fs")
  apply clarsimp
  apply (rename_tac fs)
  apply (insert corres_cont[unfolded corres_def], clarsimp)
  apply (drule_tac x=fs in meta_spec, simp)
  apply (erule impE)
   apply (frule(2) preservation_mono(1)[where \<Gamma>=\<Gamma>1, OF _ _ _ _ typing_put])
    apply (rule u_sem_put_ub)
    apply (erule subst[where s="\<gamma>!x"])
     apply (rule u_sem_var)+
   apply (clarsimp)
   apply (rename_tac rp wp)
   apply (rule_tac x="rp \<union> r''" in exI)
   apply (rule_tac x="wp \<union> w''" in exI)
   apply (rule matches_ptrs_some)
       apply assumption+
     apply (rule frame_noalias_matches_ptrs(1), simp+)
    apply (force dest: frame_noalias_matches_ptrs(2))
   apply fast
  apply clarsimp
  apply (rename_tac s' ev')
  apply (erule_tac x=s' in allE)
  apply (erule_tac x=ev' in allE)
  apply clarsimp
  apply (rename_tac \<sigma>'' ev)
  apply (rule_tac x=\<sigma>'' in exI)
  apply (rule_tac x=ev in exI)
  apply clarsimp
  apply (rule u_sem_let)
   apply (rule u_sem_put_ub)
   apply (erule subst[where s="\<gamma>!x"])
    apply (rule u_sem_var)+
  apply simp
  apply (insert x_sigil x_len)
  apply (frule(2) matches_ptrs_proj_single'[where i=x])
  apply clarsimp
  apply (erule uval_typing.cases, simp_all)
  done

lemma corres_let_put_boxed:
  assumes sigil_wr: "sgl = Boxed Writable ptrl"
  assumes x_sigil: "\<Gamma> ! x = Some (TRecord typ sgl)"
  assumes \<gamma>_x: "\<gamma> ! x = UPtr p repr"
  assumes split\<Gamma>: "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  assumes typing_stat: "\<Xi>, [], \<Gamma> \<turnstile> expr.Let (Put (Var x) f (Var e)) y : ts"
  assumes typing_put: "\<Xi>, [], \<Gamma>1 \<turnstile> Put (Var x) f (Var e) : TRecord (typ[f := (fst (typ!f), fst (snd (typ!f)), Present)]) sgl"
  assumes corres_cont: "\<And>\<sigma> s. corres srel y y' \<xi> ((\<gamma>!x) # \<gamma>) \<Xi> (Some (TRecord (typ[f := (fst (typ!f), fst (snd (typ!f)), Present)]) sgl) # \<Gamma>2) \<sigma> s"
  assumes x_boxed:
  "\<And>fs r w r' w'.
    \<lbrakk> (\<sigma>,s)\<in> srel
    ; \<sigma> p = Some (URecord fs)
    ; \<Xi>, \<sigma> \<turnstile> UPtr p repr :u TRecord typ sgl \<langle>r, w\<rangle>
    ; \<Xi>, \<sigma>(p := Some (URecord (fs [f := (\<gamma>!e,  snd (fs ! f))]))) \<turnstile> UPtr p repr :u TRecord typ sgl \<langle>r', w'\<rangle>
    \<rbrakk> \<Longrightarrow> is_valid s x' \<and> (\<sigma>(p := Some (URecord (fs [f := (\<gamma>!e,  snd (fs ! f))]))), h s) \<in> srel"
  shows "corres srel
           (Let (Put (Var x) f (Var e)) y)
           (do _ \<leftarrow> guard (\<lambda>s. is_valid s x'); _ \<leftarrow> modify h; y' od) \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s"
proof (clarsimp simp: corres_def in_monad snd_bind snd_modify snd_state_assert, auto)
  fix r w
  assume assms':
    "proc_ctx_wellformed \<Xi>"
    "\<xi> matches-u \<Xi>"
    "(\<sigma>, s) \<in> srel"
    "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>"

  obtain \<Gamma>1' \<Gamma>2' t
    where typing_stat_elim_lemmas:
      "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1' | \<Gamma>2'"
      "\<Xi>, [], \<Gamma>1' \<turnstile> Put (Var x) f (Var e) : t"
      "\<Xi>, [], Some t # \<Gamma>2' \<turnstile> y : ts"
    using typing_stat by blast

  obtain \<Gamma>3' \<Gamma>4' taken k ftag' fty' typ'
    where typing_put_elim_lems':
      "typ[f := (fst (typ ! f), fst (snd (typ ! f)), Present)] = typ'[f := (ftag', fty', Present)]"
      "[] \<turnstile> \<Gamma>1 \<leadsto> \<Gamma>3' | \<Gamma>4'"
      "\<Xi>, [], \<Gamma>3' \<turnstile> Var x : TRecord typ' sgl"
      "sigil_perm sgl \<noteq> Some ReadOnly"
      "f < length typ'"
      "typ' ! f = (ftag', fty', taken)"
      "[] \<turnstile> fty' :\<kappa> k"
      "D \<in> k \<or> taken = Taken"
      "\<Xi>, [], \<Gamma>4' \<turnstile> Var e : fty'"
    using typing_put
    by blast

  have typing_var_elim_lems':
    "[] \<turnstile> \<Gamma>3' \<leadsto>w (Cogent.empty (length \<Gamma>3'))[x := Some (TRecord typ' sgl)]"
    "x < length \<Gamma>3'"
    using typing_put_elim_lems' by blast+

  have ftag'_fty'_is:
    "ftag' = fst (typ!f)"
    "fty' = fst (snd (typ!f))"
    using typing_put_elim_lems'
    by (metis eq_updated_same_pace_imp_eq length_list_update prod.inject)+
  then have typ'_is: "typ' = typ"
    using same_type_as_split_weakened_left split_preservation_some_left
      split\<Gamma> typing_put_elim_lems' typing_var_elim_lems' x_sigil
    by (metis option.inject type.inject(8))

  note typing_put_elim_lems =
    typing_put_elim_lems'(2-)[simplified ftag'_fty'_is typ'_is]
  note typing_var_elim_lems =
    typing_var_elim_lems'[simplified ftag'_fty'_is typ'_is]

  have w_r_noalias: "w \<inter> r = {}"
    using matches_ptrs_noalias assms' by blast

  obtain r1 w1 r2 w2
    where split\<Gamma>_lemmas:
      "r = r1 \<union> r2"
      "w = w1 \<union> w2"
      "w1 \<inter> w2 = {}"
      "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>1 \<langle>r1, w1\<rangle>"
      "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>2 \<langle>r2, w2\<rangle>"
    using matches_ptrs_split'[OF split\<Gamma> assms'(4)] by blast

  obtain r13 w13p r14 w14
    where split\<Gamma>1_lemmas:
      "r1 = r13 \<union> r14"
      "w1 = w13p \<union> w14"
      "w13p \<inter> w14 = {}"
      "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>3' \<langle>r13, w13p\<rangle>"
      "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>4' \<langle>r14, w14\<rangle>"
    using matches_ptrs_split'[where \<sigma>=\<sigma>] typing_put_elim_lems split\<Gamma>_lemmas
    by metis

  obtain r13' where use\<Gamma>3'_lemmas:
    "r13' \<subseteq> r13"
    "\<Xi>, \<sigma> \<turnstile> \<gamma> ! x :u TRecord typ sgl \<langle>r13', w13p\<rangle>"
    using matches_ptrs_proj' split\<Gamma>1_lemmas(4) typing_var_elim_lems Cogent.singleton_def
    by metis

  obtain fs w13
    where uval_typing1_elim_lemmas:
      "repr = RRecord (map (\<lambda>(n, t, b). (n, type_repr t)) typ)"
      "w13p = insert p w13"
      "\<Xi>, \<sigma> \<turnstile>* fs :ur typ \<langle>r13', w13\<rangle>"
      "\<sigma> p = Some (URecord fs)"
      "p \<notin> w13"
      "p \<notin> r13'"
    using use\<Gamma>3'_lemmas(2) typing_put_elim_lems
    by (cases rule: uval_typing.cases; clarsimp simp add: \<gamma>_x sigil_wr split: prod.splits)

  have "\<xi>, \<gamma> \<turnstile> (\<sigma>, Var x) \<Down>! (\<sigma>, UPtr p repr)"
    using \<gamma>_x u_sem_var
    by metis
  then obtain r1' w1p'
    where preserve_mono_on_put_lemmas:
      "\<Xi>, \<sigma>(p \<mapsto> URecord (fs[f := (\<gamma> ! e, snd (fs ! f))])) \<turnstile> UPtr p repr :u TRecord (typ[f := (fst (typ ! f), fst (snd (typ ! f)), Present)]) sgl \<langle>r1', w1p'\<rangle>"
      "r1' \<subseteq> r1"
      "frame \<sigma> w1 (\<sigma>(p \<mapsto> URecord (fs[f := (\<gamma> ! e, snd (fs ! f))]))) w1p'"
    using preservation_mono(1)[OF _ _ _ u_sem_put[OF _ _ u_sem_var] typing_put]
      assms' split\<Gamma>_lemmas uval_typing1_elim_lemmas \<gamma>_x u_sem_var sigil_wr
    by blast

  obtain w1' ptrl
    where rec_elim1_lemmas:
        "w1p' = insert p w1'"
        "\<Xi>, \<sigma>(p \<mapsto> URecord (fs[f := (\<gamma> ! e, snd (fs ! f))])) \<turnstile>* (fs[f := (\<gamma> ! e, snd (fs ! f))]) :ur typ[f := (fst (typ ! f), fst (snd (typ ! f)), Present)] \<langle>r1', w1'\<rangle>"
        "distinct (map fst (typ[f := (fst (typ ! f), fst (snd (typ ! f)), Present)]))"
        "repr = RRecord (map (\<lambda> (n,t,_). (n, type_repr t)) (typ[f := (fst (typ ! f), fst (snd (typ ! f)), Present)]))"
        "sgl = Boxed Writable ptrl"
        "p \<notin> w1'"
        "p \<notin> r1'"
    using sigil_wr u_t_p_recE[OF preserve_mono_on_put_lemmas(1)]
    by (clarsimp, metis)

  obtain r1'' w1''
    where taken_field1_lemmas:
      "r1'' \<subseteq> r1'"
      "w1'' \<subseteq> w1'"
      "\<Xi>, \<sigma>(p \<mapsto> URecord (fs[f := (\<gamma> ! e, snd (fs ! f))])) \<turnstile>* fs[f := (\<gamma> ! e, snd (fs ! f))] :ur typ \<langle>r1'', w1''\<rangle>"
    using uval_typing_taken_field[where f=f and t="fst (snd (typ ! f))" and taken=taken and k=k, OF rec_elim1_lemmas(2)]
      typing_put_elim_lems
    by fastforce

  then have "\<Xi>, \<sigma>(p \<mapsto> URecord (fs[f := (\<gamma> ! e, snd (fs ! f))])) \<turnstile>
              UPtr p (RRecord (map (\<lambda> (n,t,_). (n, type_repr t)) (typ[f := (fst (typ ! f), fst (snd (typ ! f)), Present)]))) :u
              TRecord typ (Boxed Writable ptrl)
            \<langle>r1'', insert p w1''\<rangle>"
    using rec_elim1_lemmas taken_field1_lemmas
  proof (intro u_t_p_rec_w')
    show "RRecord (map (\<lambda> (n,t,_). (n, type_repr t)) (typ[f := (fst (typ ! f), fst (snd (typ ! f)), Present)])) = RRecord (map (\<lambda> (n,t,_). (n, type_repr t)) typ)"
      by (clarsimp, metis rec_elim1_lemmas(2) taken_field1_lemmas(3) type_repr_uval_repr(2))
  next
    show "distinct (map fst typ)"
      using rec_elim1_lemmas
      by (metis fst_conv list_update_id map_update)
  qed auto

  then have x_boxed_lemmas:
    "is_valid s x'"
    "(\<sigma>(p \<mapsto> URecord (fs[f := (\<gamma> ! e, snd (fs ! f))])), h s) \<in> srel"
    using x_boxed assms' uval_typing1_elim_lemmas \<gamma>_x rec_elim1_lemmas use\<Gamma>3'_lemmas
    by metis+

  have upd_matches2:
    "\<Xi>, \<sigma>(p \<mapsto> URecord (fs[f := (\<gamma> ! e, snd (fs ! f))])) \<turnstile> \<gamma> ! x # \<gamma> matches Some (TRecord (typ[f := (fst (typ ! f), fst (snd (typ ! f)), Present)]) sgl) # \<Gamma>2 \<langle>r1' \<union> r2, (insert p w1') \<union> w2\<rangle>"
  proof (intro matches_ptrs_some)
    show "\<Xi>, \<sigma>(p \<mapsto> URecord (fs[f := (\<gamma> ! e, snd (fs ! f))])) \<turnstile> \<gamma> ! x :u TRecord (typ[f := (fst (typ ! f), fst (snd (typ ! f)), Present)]) sgl \<langle>r1', insert p w1'\<rangle>"
      using preserve_mono_on_put_lemmas rec_elim1_lemmas sigil_wr \<gamma>_x
      by argo
  next
    show "\<Xi>, \<sigma>(p \<mapsto> URecord (fs[f := (\<gamma> ! e, snd (fs ! f))])) \<turnstile> \<gamma> matches \<Gamma>2 \<langle>r2, w2\<rangle>"
      using matches_ptrs_frame[where r=r2 and w=w2]
      using split\<Gamma>_lemmas preserve_mono_on_put_lemmas w_r_noalias
      by fast
  next
    show
      "insert p w1' \<inter> w2 = {}"
      "insert p w1' \<inter> r2 = {}"
      "w2 \<inter> r1' = {}"
      using frame_noalias_matches_ptrs(1) preserve_mono_on_put_lemmas(3) rec_elim1_lemmas(1) split\<Gamma>_lemmas(3) split\<Gamma>_lemmas(5)
        apply blast
      using frame_noalias_matches_ptrs(2) preserve_mono_on_put_lemmas(3) rec_elim1_lemmas(1) split\<Gamma>_lemmas(1) split\<Gamma>_lemmas(2) split\<Gamma>_lemmas(5) w_r_noalias
       apply blast
      using preserve_mono_on_put_lemmas(2) split\<Gamma>_lemmas(1) split\<Gamma>_lemmas(2) w_r_noalias
      apply blast
      done
  qed

  have smaller_corres:
    "\<not> snd (y' (h s))"
    "\<And>r' s'. (r', s') \<in> fst (y' (h s)) \<Longrightarrow> \<exists>\<sigma>' r. \<xi>, \<gamma> ! x # \<gamma> \<turnstile> (\<sigma>(p \<mapsto> URecord (fs[f := (\<gamma> ! e, snd (fs ! f))])), y) \<Down>! (\<sigma>', r) \<and> (\<sigma>', s') \<in> srel \<and> val_rel r r'"
    using corres_cont[unfolded corres_def] assms' upd_matches2 x_boxed_lemmas
    by fast+

  {
    show "is_valid s x'"
      using x_boxed_lemmas by simp
  }
  {
    assume
      "snd (y' (h s))"
    then show False
      using smaller_corres by simp
  }
  {
    fix r' s'

    assume
      "(r', s') \<in> fst (y' (h s))"
    then show "\<exists>\<sigma>' ra. \<xi>, \<gamma> \<turnstile> (\<sigma>, expr.Let (Put (Var x) f (Var e)) y) \<Down>! (\<sigma>', ra) \<and> (\<sigma>', s') \<in> srel \<and> val_rel ra r'"
      using smaller_corres(2)
      apply -
      apply (drule_tac x=r' and y=s' in meta_spec2)
      apply clarsimp
      apply (rule_tac x="\<sigma>'" in exI)
      apply (rule_tac x="r" in exI)
      apply (clarsimp simp add: \<gamma>_x)
      apply (intro u_sem_let[rotated])
       apply simp
      by (metis \<gamma>_x u_sem_put u_sem_var uval_typing1_elim_lemmas(4))
  }
qed

lemma u_sem_put':
  "\<xi>', \<gamma>' \<turnstile> (\<sigma>', x) \<Down>! (\<sigma>'', r) \<Longrightarrow>
   \<sigma>'' p = Some (URecord fs) \<Longrightarrow>
   r = UPtr p repr \<Longrightarrow>
   \<xi>', \<gamma>' \<turnstile> (\<sigma>'', e) \<Down>! (\<sigma>''', e') \<Longrightarrow>
   \<xi>', \<gamma>' \<turnstile> (\<sigma>', Put x f e) \<Down>! (\<sigma>'''(p \<mapsto> URecord (fs[f := (e', snd (fs ! f))])), r)"
  by (auto intro: u_sem_put)

lemma corres_put_boxed:
  assumes sigil_wr: "sgl = Boxed Writable ptrl"
  assumes x_sigil: "\<Gamma>!x = Some (TRecord typ sgl)"
  assumes \<gamma>_x: "\<gamma>!x = UPtr p repr"
  assumes split\<Gamma>: "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  assumes typing_put: "\<Xi>, [], \<Gamma> \<turnstile> Put (Var x) f (Var e) : TRecord (typ[f := (fst (typ ! f), fst (snd (typ ! f)), Present)]) sgl"
  assumes x_boxed:
  "\<And>fs r w r' w'.
    \<lbrakk>(\<sigma>,s)\<in> srel; \<sigma> p = Some (URecord fs);
    \<Xi>, \<sigma> \<turnstile> UPtr p repr :u TRecord typ sgl \<langle>r, w\<rangle>;
    \<Xi>, \<sigma>(p := Some (URecord (fs [f := (\<gamma>!e, snd (fs ! f))]))) \<turnstile> UPtr p repr :u TRecord typ sgl \<langle>r', w'\<rangle>\<rbrakk> \<Longrightarrow>
   is_valid s x' \<and> val_rel (UPtr p repr) x' \<and> (\<sigma>(p := Some (URecord (fs [f := (\<gamma>!e, snd (fs ! f))]))), h s) \<in> srel"
  shows "corres srel
           (Put (Var x) f (Var e))
           (do _ \<leftarrow> guard (\<lambda>s. is_valid s x'); _ \<leftarrow> modify h; gets (\<lambda>_. x') od) \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s"
  apply (clarsimp simp: corres_def in_monad snd_bind snd_modify snd_state_assert)
  apply (rename_tac r w)
  apply (insert typing_put \<gamma>_x x_sigil)
  apply (erule typing_putE)
  apply (rename_tac \<Gamma>1' \<Gamma>2' typ' sigil tag tf taken k)
  apply (erule typing_varE)+
  apply (frule matches_ptrs_noalias)
  apply (frule_tac \<Gamma>=\<Gamma> in matches_ptrs_split', simp, clarsimp)
  apply (rename_tac rx' wx' re' we')
  apply (frule_tac \<Gamma>=\<Gamma>1' in matches_ptrs_proj', simp+)
  apply (clarsimp, rename_tac rx'')
  apply (erule uval_typing.cases, tactic {* ALLGOALS (fn n => TRY (SOLVES (asm_full_simp_tac @{context} n))) *})
  apply (frule(2) preservation_mono(1)[where \<Gamma>=\<Gamma>, OF _ _ _ _ typing_put])
   apply (rule u_sem_put)
     apply (subst \<gamma>_x[symmetric])
     apply (rule u_sem_var)
    apply simp
   apply clarsimp
   apply (rule u_sem_var)
  apply (clarsimp)
  apply (erule u_t_p_recE)
   apply simp
  apply (frule_tac \<tau>s="(ts[f := (tag, tf, Present)])" and f=f and t=tf and taken=taken in uval_typing_taken_field)
     apply force
    apply simp+
  apply (frule(2) same_type_as_split_weakened_left)
  apply (drule same_type_as_split_weakened_left; simp)
  apply clarsimp
  apply (rename_tac rnfs wnfs)
  apply (frule(1) x_boxed)
    apply (fastforce intro!: u_t_p_rec_w')
   apply (simp add: sigil_wr)
   apply (rule_tac fs="fs [f := (\<gamma> ! e, snd (fs ! f))]" in u_t_p_rec_w')
       apply (simp only: list_helper)
      apply force
     apply force
    apply argo
   apply force
  apply clarsimp
  apply (rule_tac x="\<sigma>(p := Some (URecord (fs [f := (\<gamma>!e, snd (fs ! f))])))" in exI)
  apply (rule_tac x="\<gamma> ! x" in exI)
  apply (rule conjI)
   apply (rule u_sem_put')
      apply (rule u_sem_var)
     apply assumption
    apply assumption
   apply (rule u_sem_var)
  apply simp
  done

lemma corres_let_put_unboxed':
  assumes x_sigil: "\<Gamma>!x = Some (TRecord typ Unboxed)"
  assumes x_len: "x < length \<Gamma>"
  assumes split\<Gamma>: "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  assumes typing_put:  "\<Xi>, [], \<Gamma>1 \<turnstile> Put (Var x) f (Var e) : TRecord (typ[f := (fst (typ ! f), fst (snd (typ ! f)), Present)]) Unboxed" (* needed? *)
  assumes val_rel_upd_x : "\<And>fs. \<gamma>!x = URecord fs \<Longrightarrow> val_rel (URecord (fs[f:= ((\<gamma>!e),  snd (fs ! f))])) (nx' x')"
  assumes corres_cont:
   "\<And>v. val_rel v (nx' x') \<Longrightarrow>
   corres srel y (y' (nx' x')) \<xi> (v # \<gamma>) \<Xi>
   (Some (TRecord (typ[f := (fst (typ ! f), fst (snd (typ ! f)), Present)]) Unboxed) # \<Gamma>2) \<sigma> s"
  shows "corres srel
  (Let (Put (Var x) f (Var e)) y)
  (do
     rec \<leftarrow> gets (\<lambda>_. x');
     rec \<leftarrow> gets (\<lambda>_. nx' rec);
     rec' \<leftarrow> gets (\<lambda>_. rec);
     y' rec'
   od) \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s"
   by (blast intro: corres_let_put_unboxed[OF assms(1-4)] assms(5,6))

lemma corres_add_let:
  "corres srel (Let x (Var 0)) x' \<xi> \<gamma> \<Xi>' \<Gamma>' \<sigma> s
    \<Longrightarrow> corres srel x x' \<xi> \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  apply (clarsimp simp: corres_def)
  apply (drule mp, blast, clarsimp)
  apply (elim allE, drule(1) mp)
  apply clarsimp
  apply (erule u_sem_letE, erule u_sem_varE, clarsimp)
  apply blast
  done

lemma split_all_left:
  "\<forall>t. Some t \<in> set \<Gamma> \<longrightarrow> K' \<turnstile> t wellformed
    \<Longrightarrow> K' \<turnstile> \<Gamma> \<leadsto> \<Gamma> | replicate (length \<Gamma>) None"
  apply (induct \<Gamma>)
   apply (simp add: split_empty)
  apply (fastforce intro!: split_cons simp add: kinding_iff_wellformed split_comp.simps)
  done

lemma corres_no_let_put_unboxed':
  assumes x_sigil: "\<Gamma>'!x = Some (TRecord typ Unboxed)"
  assumes x_len: "x < length \<Gamma>'"
  assumes typing_put:  "\<Xi>', [], \<Gamma>' \<turnstile> Put (Var x) f (Var e) : TRecord (typ[f := (fst (typ ! f), fst (snd (typ ! f)), Present)]) Unboxed" (* needed? *)
  assumes val_rel_upd_x : "\<And>fs. \<gamma>!x = URecord fs \<Longrightarrow> val_rel (URecord (fs[f:= ((\<gamma>!e),  snd (fs ! f))])) (nx' x')"
  shows "corres srel
  ((Put (Var x) f (Var e)))
  (do
     rec \<leftarrow> gets (\<lambda>_. x');
     rec \<leftarrow> gets (\<lambda>_. nx' rec);
     gets (\<lambda>_. rec)
   od) \<xi> \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  apply (rule corres_add_let)
  apply (subst bind_return[symmetric], rule corres_let_put_unboxed[OF assms(1-2) _ typing_put])
   apply (rule split_all_left)
   apply (clarsimp dest!: typing_to_kinding_env(1)[OF typing_put])
  apply (clarsimp simp: corres_def return_def dest!: val_rel_upd_x)
  apply (fastforce intro: u_sem_var)
  done

lemma corres_unit:
  "val_rel UUnit bla \<Longrightarrow> corres srel Unit (gets (\<lambda>_. bla)) \<xi>' \<gamma>' \<Xi>' \<Gamma>' \<sigma> s"
  apply (monad_eq simp: corres_def)
  apply (rule exI)+
  apply (rule conjI)
   apply (rule u_sem_unit)
  apply simp
  done

lemma corres_app_abstract:
  "\<lbrakk>\<xi>' f_name = f;
   (\<sigma>,s)\<in>srel \<Longrightarrow> (\<exists>r w. uval_typing \<Xi>' \<sigma> x t r w) \<Longrightarrow> \<not> snd (f' x' s);
   (\<And>r' s'. (\<exists>r w. uval_typing \<Xi>' \<sigma> x t r w) \<Longrightarrow>
             (r', s') \<in> fst (f' x' s) \<Longrightarrow>
             (\<sigma>,s)\<in>srel \<Longrightarrow>
             \<exists>\<sigma>' r. f (\<sigma>, x) (\<sigma>', r) \<and> (\<sigma>', s') \<in> srel \<and> val_rel r r')\<rbrakk> \<Longrightarrow>
   corres srel (App (AFun f_name []) (Var 0))
    (do retval \<leftarrow> f' x';
        gets (\<lambda>_. retval)
    od) \<xi>' (x # \<gamma>) \<Xi>' (Some t # \<Gamma>') \<sigma> s"
  apply atomize
  apply (clarsimp simp: corres_def)
  apply (erule matches_ptrs_consE, simp)
  apply (erule impE)
   apply force
  apply (erule impE)
   apply force
  apply clarsimp
  apply (drule_tac x=r'a in spec)
  apply (drule_tac x=s' in spec)
  apply clarsimp
  apply (rule_tac x=\<sigma>' in exI)
  apply (rule_tac x=r in exI)
  apply (rule conjI)
   apply (rule u_sem_abs_app[where \<sigma>''=\<sigma>])
     apply (rule u_sem_afun)
    apply (rule u_sem_var)
   apply simp
  apply simp
  done

lemma corres_app_concrete:
  "\<lbrakk> \<Gamma>' ! n = Some t; n < length \<Gamma>';
     corres srel f (f' x') \<xi>' [\<gamma> ! n] \<Xi>' [Some t] \<sigma> s \<rbrakk> \<Longrightarrow>
   corres srel (App (Fun f []) (Var n)) (do retval \<leftarrow> f' x'; gets (\<lambda>_. retval) od) \<xi>' \<gamma> \<Xi>' (\<Gamma>') \<sigma> s"
  apply (clarsimp simp: corres_def)
  apply (erule impE)
   apply (drule(2) matches_ptrs_proj_single')
   apply clarsimp
   apply (rule exI)
   apply (rule exI)
   apply (rule matches_ptrs_cons[where \<tau>s="[]" and r'="{}" and w'="{}", simplified])
     apply simp
    apply (rule matches_ptrs_empty[where \<tau>s="[]", simplified])
   apply assumption
  apply clarsimp
  apply (erule_tac x=r' in allE)
  apply (erule_tac x=s' in allE)
  apply clarsimp
  apply (rename_tac r'')
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = r'' in exI)
  apply clarsimp
  apply (rule u_sem_app)
    apply (rule u_sem_fun)
   apply (rule u_sem_var)
  apply simp
  done

lemma sum_tag_is_same:
 "\<lbrakk> \<Xi>', \<sigma> \<turnstile> \<gamma> ! x :u t \<langle>r', w'\<rangle>;
     \<Xi>', [], \<Gamma>' \<turnstile> Esac (Var x) n : ret;  
    \<gamma> ! x = USum tag val ts;
    t = TSum typs;
     x < length \<Gamma>';
     \<Gamma>' ! x = Some t
  \<rbrakk> \<Longrightarrow> n = tag"
  apply clarsimp
  apply (erule u_t_sumE)
  apply (erule typing_esacE)
  apply (erule typing_varE)
  apply clarsimp
  apply (subgoal_tac "typs = tsa")
   apply clarsimp 
   apply (simp only: Util.filter_eq_singleton_iff2)
   apply clarsimp
  apply auto[1]
  by (simp add: same_type_as_weakened)

lemma corres_esac:(* CHANGED: fourth assumption added *)
  "\<lbrakk> val_rel (\<gamma> ! x) x';
     x < length \<Gamma>';
     \<Gamma>' ! x = Some (TSum typs);
    \<Xi>', [], \<Gamma>' \<turnstile> Esac (Var x) n : ret;  
     \<And> val rtyps. \<gamma> ! x = USum  n val rtyps \<Longrightarrow> val_rel val (get_val' x')
   \<rbrakk> \<Longrightarrow>
   corres srel (Esac (Var x) n) (gets (\<lambda>_. get_val' x')) \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  apply (monad_eq simp: corres_def)
  apply (frule(2) matches_ptrs_proj_single')
  apply clarsimp
  apply (erule u_t_sumE)
  apply (subst sum_tag_is_same[where \<gamma>="\<gamma>" and n="n" and \<Xi>'="\<Xi>'" and x="x" and \<sigma>="\<sigma>"])
        apply clarsimp
        apply (rule u_t_sum; simp)
       apply assumption
      apply assumption
     apply simp
    apply assumption
   apply assumption
  apply atomize
  apply clarsimp
  apply (rule_tac x=\<sigma> in exI)
  apply (rule_tac x=a in exI)
  apply simp
  apply (intro conjI)
   apply (rule u_sem_esac)
   apply (erule_tac s = "\<gamma> ! x" in subst)
   apply (rule u_sem_var)
  by (metis matches_ptrs_proj_single' sum_tag_is_same)

lemma corres_prim1:
  assumes "val_rel (eval_prim_u p [\<gamma>!x]) c"
  shows "corres srel (Prim p [Var x]) (gets (\<lambda>_. c)) \<xi> \<gamma> \<Xi> \<Gamma>' \<sigma> s"
  apply (clarsimp simp: corres_def snd_return in_return)
  apply (insert assms)
  apply (rule_tac x=\<sigma> in exI)
  apply (rule_tac x="eval_prim_u p [\<gamma> ! x]" in exI)
  apply simp
  apply (rule u_sem_prim)
  apply (rule u_sem_all_cons)
   apply (rule u_sem_var)
  apply (rule u_sem_all_empty)
  done

lemma corres_prim2:
  assumes
   "val_rel (eval_prim_u p [\<gamma>!v1, \<gamma>!v2]) c"
  shows "corres srel (Prim p [Var v1, Var v2]) (gets (\<lambda>_. c)) \<xi> \<gamma> \<Xi> \<Gamma>' \<sigma> s"
  apply (clarsimp simp: corres_def snd_return in_return)
  apply (insert assms)
  apply (rule_tac x=\<sigma> in exI)
  apply (rule_tac x="eval_prim_u p [\<gamma> ! v1, \<gamma> ! v2]" in exI)
  apply simp
  apply (rule u_sem_prim)
  apply (rule u_sem_all_cons)
   apply (rule u_sem_var)
  apply (rule u_sem_all_cons)
   apply (rule u_sem_var)
  apply (rule u_sem_all_empty)
  done

lemma corres_prim2_partial_right:
  assumes
   "val_rel (eval_prim_u pop [\<gamma> ! v1, \<gamma> ! v2])
        (f (if x < N then res else 0))"
   "(x :: ('a :: len) word) < N \<longrightarrow> cg"
  shows "corres srel (Prim pop [Var v1, Var v2])
        ((condition (\<lambda>_. x \<ge> N) (gets (\<lambda>_. 0))
            (guard (\<lambda>_. cg) >>= (\<lambda>_. gets (\<lambda>_. res))))
            >>= (\<lambda>x. gets (\<lambda>_. f x))) \<xi> \<gamma> \<Xi> \<Gamma>' \<sigma> s"
  apply (rule corres_monad_eq[rotated])
   apply (rule corres_prim2[OF assms(1)])
  apply (clarsimp simp: condition_def linorder_not_less[symmetric] assms(2))
  done

lemma corres_prim2_partial_left:
  assumes
   "val_rel (eval_prim_u pop [\<gamma> ! v1, \<gamma> ! v2])
        (f (if x = 0 then 0 else res))"
   "x \<noteq> 0 \<longrightarrow> cg"
  shows "corres srel (Prim pop [Var v1, Var v2])
        ((condition (\<lambda>_. x \<noteq> 0) (guard (\<lambda>_. cg) >>= (\<lambda>_. gets (\<lambda>_. res)))
            (gets (\<lambda>_. 0)))
            >>= (\<lambda>x. gets (\<lambda>_. f x))) \<xi> \<gamma> \<Xi> \<Gamma>' \<sigma> s"
  apply (rule corres_monad_eq[rotated])
   apply (rule corres_prim2[OF assms(1)])
  apply (clarsimp simp: condition_def linorder_not_less[symmetric] assms(2))
  done

lemma lookup_distinct_list:
  "(k, v) \<in> set xs \<Longrightarrow> distinct (map fst xs) \<Longrightarrow> the (find (\<lambda>x. fst x = k) xs) = (k, v)"
  apply (induct xs)
   apply simp
  apply force
  done

lemma list_all2_map_filter_helper[rule_format]:
  "map P1 xs = map P2 ys \<Longrightarrow>
   list_all2 P (map f xs) (map g ys) \<longrightarrow>
   list_all2 P (map f (filter P1 xs)) (map g (filter P2 ys))"
  by (induct xs ys rule: list_induct2') auto

lemma type_rep_tagged_update:
  "\<lbrakk>(tag, tag_t, Unchecked) \<in> set \<tau>s \<or> tag \<notin> fst ` set \<tau>s;
    distinct (map fst \<tau>s)\<rbrakk> \<Longrightarrow>
   map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) \<tau>s =
   map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) (tagged_list_update tag (tag_t, Checked) \<tau>s)"
  apply (induction \<tau>s)
   apply simp
  using image_iff by fastforce

(* Added assumption 7: tag is present and unchecked in the input type *)
lemma corres_case:
  fixes \<tau>s :: "(char list \<times> Cogent.type \<times> variant_state) list"
  assumes
    "x < length \<Gamma>'"
    "\<Gamma>'!x = Some (TSum \<tau>s)"
    "[] \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1 | \<Gamma>2"
    "get_tag' x' = tag' \<longrightarrow> val_rel (\<gamma>!x) x'"
    "case (\<gamma>!x) of USum vtag vval vtyps \<Rightarrow>
       if get_tag' x' = tag'
         then tag = vtag \<and> val_rel vval (get_A' x')
         else tag \<noteq> vtag \<and> val_rel (USum vtag vval vtyps) x'"
    "\<Xi>', [], \<Gamma>1 \<turnstile> Var x : TSum \<tau>s"
    "(tag, tag_t, Unchecked) \<in> set \<tau>s"
    "\<Xi>', [], Some tag_t # \<Gamma>2 \<turnstile> match : t"
    "\<Xi>', [], Some (TSum (tagged_list_update tag (tag_t,Checked) \<tau>s)) # \<Gamma>2 \<turnstile> not_match : t"
    "\<And>a a'. val_rel a a' \<Longrightarrow> corres srel match (match' a') \<xi>' (a # \<gamma>) \<Xi>' (Some tag_t # \<Gamma>2) \<sigma> s"
    "\<And>r. r = (\<gamma>!x) \<Longrightarrow> val_rel r x' \<Longrightarrow> corres srel not_match (not_match' x') \<xi>' (r # \<gamma>) \<Xi>' (Some (TSum (tagged_list_update tag (tag_t, Checked) \<tau>s)) # \<Gamma>2) \<sigma> s"
  shows "corres srel (Case (Var x) tag match not_match)
            (condition (\<lambda>_. get_tag' x' = tag')
              (match' (get_A' x'))
              (not_match' x'))
            \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  using assms
  apply (clarsimp simp: corres_def)
  apply (frule (1) matches_ptrs_split', clarsimp)
  apply (rename_tac r1 w1 r2 w2)
  apply (frule (2) preservation_mono(1)[where \<Gamma>="\<Gamma>1" and e="Var x"])
    apply (rule u_sem_var)
   apply assumption
  apply clarsimp
  apply (rename_tac rx wx)
  apply (erule u_t_sumE, clarsimp)
  apply (rename_tac vval vtyp vtag)
  apply (drule_tac x=vval in meta_spec)
  apply (drule_tac x="get_A' x'" in meta_spec)
  apply (drule_tac x="USum vtag vval (map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) \<tau>s)" in meta_spec)
 
  apply (case_tac "get_tag' x' = tag'")

   apply clarsimp
   apply (erule impE)
    apply (rule_tac x="rx \<union> r2" in exI, rule_tac x="wx \<union> w2" in exI)
    apply (rule matches_ptrs_some)
        apply (metis distinct_fst fst_conv)
       apply assumption
      apply (drule (2) frame_noalias_matches_ptrs(1)[where \<Gamma>=\<Gamma>2])
      apply assumption
  using matches_ptrs_noalias frame_noalias_matches_ptrs(2)
     apply fast
  using matches_ptrs_noalias frame_noalias_matches_ptrs(1)
    apply fast
   apply clarsimp
   apply (metis u_sem_case_m u_sem_var)

  apply clarsimp
  apply (erule impE)
   apply (rule_tac x="rx \<union> r2" in exI, rule_tac x="wx \<union> w2" in exI)
   apply (rule matches_ptrs_some)
       apply (rule u_t_sum)
           apply simp
          apply (rule_tac V="(vtag, vtyp, Unchecked) \<in> set \<tau>s" in revcut_rl)
           apply force
  using tagged_list_update_different_tag_preserves_values2
          apply metis
         apply force
        apply (rule variant_tagged_list_update_wellformedI)
           apply (metis (no_types, lifting) fst_conv image_iff)
          apply blast
         apply (meson kinding_iff_wellformed(1) kinding_simps(6) kinding_variant_wellformed_elem typing_to_wellformed(1))
  using kinding_iff_wellformed(1) kinding_simps(6) kinding_to_wellformedD(3) typing_to_wellformed(1)
        apply blast
       apply (rule type_rep_tagged_update; simp)
      apply simp
     apply (drule (2) frame_noalias_matches_ptrs(1)[where \<Gamma>=\<Gamma>2])
     apply blast
    using matches_ptrs_noalias frame_noalias_matches_ptrs(2)
    apply fast
   using matches_ptrs_noalias frame_noalias_matches_ptrs(1)
   apply fast
  apply clarsimp
  apply (erule_tac x=r' in allE)
  apply (erule_tac x=s' in allE)
  apply clarsimp
  apply (rule exI)+
  apply (rule conjI)
   apply (rule u_sem_case_nm)
     apply (force intro: u_sem_var elim: subst)
    apply simp
   apply assumption
  apply simp
  done

lemma corres_member_unboxed':
  "\<lbrakk>\<gamma>!x = URecord fs;
   (\<sigma>,s)\<in>srel \<Longrightarrow> val_rel (fst (fs! f)) (f')
   \<rbrakk> \<Longrightarrow>
   corres srel (Member (Var x) f)
    (gets (\<lambda>s. f' ))
    \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  by (monad_eq simp: corres_def) (fastforce intro: u_sem_member u_sem_var elim: subst)

lemma corres_member_unboxed:
  "\<lbrakk> \<exists>fs. \<gamma> ! x = URecord fs \<and> val_rel (fst (fs ! f)) f' \<rbrakk> \<Longrightarrow>
   corres srel (Member (Var x) f) (gets (\<lambda>s. f'))
          \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  apply (rule corres_member_unboxed'[simplified guard_True_bind,
           where fs="THE fs. \<gamma> ! x = URecord fs"])
  by auto

lemma corres_member_boxed:
  assumes
    "val_rel (\<gamma>!x) (x'::('a::cogent_C_val) ptr)"
    "\<Gamma>'!x = Some (TRecord typ sigil)"
    "\<gamma> ! x = UPtr (ptr_val x') repr"
    "\<Xi>', [], \<Gamma>' \<turnstile> Member (Var x) f : te'"
    "\<And>fs r w. \<lbrakk>(\<sigma>, s)\<in> srel; \<sigma> (ptr_val x') = Some (URecord fs);
               \<Xi>', \<sigma> \<turnstile> UPtr (ptr_val x') repr :u TRecord typ sigil \<langle>r, w\<rangle>\<rbrakk> \<Longrightarrow>
              is_valid' s x' \<and> val_rel (fst(fs!f)) ((f' s)::'bb::cogent_C_val)"
  shows "corres srel (Member (Var x) f)
          (do _ \<leftarrow> guard (\<lambda>s. is_valid' s x');
             gets (\<lambda>s. f' s )
          od) \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  using assms
  apply (monad_eq simp: corres_def val_rel_ptr_def)
  apply (rename_tac r w)
  apply atomize
  apply (erule typing_memberE)
  apply (rename_tac tr access k)
  apply (erule typing_varE)
  apply (frule_tac matches_ptrs_proj', simp+)
  apply clarsimp
  apply (rename_tac rr)
  apply (drule(1) same_type_as_weakened)
  apply clarsimp
  apply (rename_tac rf')
  apply (frule uval_typing.cases, simp_all)
   apply (rename_tac \<Xi>'' \<sigma>' fs' typ' r' p')
   apply (erule impE, fast)
   apply clarsimp
   apply (rule_tac x=\<sigma> in exI)
   apply (rule exI)
   apply (fastforce intro!: u_sem_memb_b u_sem_var elim: subst)
  using shareable_not_writable(1) apply fastforce
  done

lemma corres_fun:
  "val_rel (UFunction f []) (fun_tag' :: 32 signed word) \<Longrightarrow>
   corres srel (Fun f []) (gets (\<lambda>_. fun_tag')) \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  apply (monad_eq simp: corres_def)
  apply (rule exI)+
  apply (rule conjI)
   apply (rule u_sem_fun)
  apply simp
  done

lemma corres_afun:
  "val_rel (UAFunction f []) (fun_tag' :: 32 signed word) \<Longrightarrow>
   corres srel (AFun f []) (gets (\<lambda>_. fun_tag')) \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  apply (monad_eq simp: corres_def)
  apply (rule exI)+
  apply (rule conjI)
   apply (rule u_sem_afun)
  apply simp
  done

lemma corres_promote:
  assumes "val_rel (\<gamma>!x) x'"
  shows "corres srel (Promote t (Var x)) (gets (\<lambda>_. x')) \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  apply (monad_eq simp: corres_def)
  using assms u_sem_promote u_sem_var by blast


lemma corres_if_base:
  assumes split\<Gamma>: "[] \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1 | \<Gamma>2"
  assumes typing_cond: "\<Xi>', [], \<Gamma>1 \<turnstile> Var c : TPrim Bool"
  assumes val_rel_cond: "(bool_val' c' = 0 \<or> bool_val' c' = 1) \<and>
     \<gamma>!c = UPrim (LBool (bool_val' c' \<noteq> 0))"
  assumes corres_true: "corres srel a a' \<xi> \<gamma> \<Xi>' \<Gamma>2 \<sigma> s"
  assumes corres_false: "corres srel b b' \<xi> \<gamma> \<Xi>' \<Gamma>2 \<sigma> s"
  shows "corres srel (If (Var c) a b)
           (do x \<leftarrow> condition (\<lambda>s. bool_val' c' \<noteq> 0) a' b'; gets (\<lambda>_. x) od)
           \<xi> \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  apply (clarsimp simp: corres_def snd_condition in_condition)
  apply (rename_tac r w)
  apply (insert typing_cond)
  apply (erule typing_varE)
  apply (frule matches_ptrs_split'[OF split\<Gamma>])
  apply clarsimp
  apply (rename_tac r' w' r'' w'')
  apply (frule_tac \<Gamma>=\<Gamma>1 in matches_ptrs_proj', simp+)
  apply clarsimp
  apply (rename_tac rr')
  apply (insert val_rel_cond)
  apply clarsimp
  apply (cases "bool_val' c'=0")
   apply (insert corres_false[unfolded corres_def])[1]
   apply simp
   apply (erule impE, fast)
   apply clarsimp
   apply (rename_tac v' s')
   apply (erule_tac x=v' in allE)
   apply (erule_tac x=s' in allE )
   apply clarsimp
   apply (rename_tac \<sigma>' v)
   apply (rule_tac x=\<sigma>' in exI)
   apply (rule_tac x=v in exI)
   apply (fastforce intro!: u_sem_if u_sem_var elim: subst split: uval.splits lit.splits)
  apply (insert corres_true[unfolded corres_def])[1]
  apply simp
  apply (erule impE, fast)
  apply clarsimp
  apply (rename_tac v' s')
  apply (erule_tac x=v' in allE)
  apply (erule_tac x=s' in allE )
  apply clarsimp
  apply (rename_tac \<sigma>' v)
  apply (rule_tac x=\<sigma>' in exI)
  apply (rule_tac x=v in exI)
  apply (fastforce intro!: u_sem_if u_sem_var elim: subst split: uval.splits lit.splits)
  done

(* Lemmas for dealing with AutoCorres generated output. *)
lemma measure_call_subst:
    "\<lbrakk> monad_mono x; no_fail (\<lambda>s. s = s') (x m) \<rbrakk> \<Longrightarrow> measure_call x s' = x m s'"
  apply (clarsimp simp: measure_call_def validNF_def valid_def no_fail_def)
  apply (cases "x m s'")
  apply clarsimp
  apply (rule conjI[rotated])
   apply (rule_tac x=m in exI)
   apply simp
  apply (rule set_eqI)
  apply (rule iffI)
   apply clarsimp
   apply (drule monad_mono_incl[where m=m and s=s'])
    apply simp
   apply fastforce
  apply clarsimp
  apply (rule_tac x=m in exI)
  apply (drule monad_mono_incl[where m=m and s=s'])
   apply simp
  apply fastforce
  done

lemma corres_measure_call_subst:
  "\<lbrakk> monad_mono f';
     corres srel (App f (Var 0)) (do ret \<leftarrow> f' m; gets (\<lambda>_. ret) od)
            \<xi>' (a # \<gamma>) \<Xi>' (Some t # \<Gamma>') \<sigma> s \<rbrakk> \<Longrightarrow>
   corres srel (App f (Var 0)) (do ret \<leftarrow> measure_call f'; gets (\<lambda>_. ret) od)
          \<xi>' (a # \<gamma>) \<Xi>' (Some t # \<Gamma>') \<sigma> s"
  apply (clarsimp simp: corres_def)
  apply (subst measure_call_subst[where m = m], assumption, force simp: no_fail_def)+
  apply force
  done

lemma condition_true_pure:
  "P \<Longrightarrow> condition (\<lambda>_. P) A B = A"
  by monad_eq

lemma condition_false_pure:
  "\<not>P \<Longrightarrow> condition (\<lambda>_. P) A B = B"
  by monad_eq


(* Generic heap relation rules. *)
definition
  heap_rel_meta :: "('g \<Rightarrow> 'c ptr \<Rightarrow> bool)
    \<Rightarrow> ('g \<Rightarrow> 'c ptr \<Rightarrow> 'c)
    \<Rightarrow> (string, abstyp, addr) store \<Rightarrow> 'g
    \<Rightarrow> ('c :: cogent_C_val) ptr \<Rightarrow> bool"
where
  "heap_rel_meta is_v hp \<sigma> h p \<equiv>
   (\<forall>uv.
     \<sigma> (ptr_val p) = Some uv \<longrightarrow>
     type_rel (uval_repr uv) TYPE('c) \<longrightarrow>
     is_v h p \<and> val_rel uv (hp h p))"

lemma all_heap_rel_ptrD:
  "\<forall>(p :: 'a ptr). heap_rel_meta is_v hp \<sigma> h p
    \<Longrightarrow> \<sigma> (ptr_val p) = Some uv
    \<Longrightarrow> type_rel (uval_repr uv) TYPE('a :: cogent_C_val)
    \<Longrightarrow> is_v h p \<and> val_rel uv (hp h (p :: 'a ptr))"
  by (clarsimp simp: heap_rel_meta_def)

lemma all_heap_rel_updE:
  "\<forall>(p :: 'a ptr). heap_rel_meta is_v hp \<sigma> h p
    \<Longrightarrow> \<sigma> (ptr_val x) = Some uv
    \<Longrightarrow> uval_repr uv' = uval_repr uv
    \<Longrightarrow> \<forall>(p :: 'a ptr). ptr_val p \<noteq> ptr_val x \<longrightarrow> hp upd_h p = hp h p
    \<Longrightarrow> \<forall>(p :: 'a ptr). is_v upd_h p = is_v h p
    \<Longrightarrow> type_rel (uval_repr uv) (TYPE('a :: cogent_C_val))
        \<longrightarrow> (\<forall>(p :: 'a ptr). ptr_val p = ptr_val x
           \<longrightarrow> is_v h p
           \<longrightarrow> val_rel uv' (hp upd_h p))
    \<Longrightarrow> \<forall>(p :: 'a ptr). heap_rel_meta is_v hp (\<sigma>(ptr_val x \<mapsto> uv')) (upd_h) p"
  by (simp add: heap_rel_meta_def)

definition
  "abs_rel \<Xi>' srel afun_name \<xi>' afun_mon
    = (\<forall>\<sigma> st x x' r' w'. (\<sigma>, st) \<in> srel \<and> val_rel x x'
        \<and> \<Xi>', \<sigma> \<turnstile> x :u fst (snd (\<Xi>' afun_name)) \<langle>r', w'\<rangle>
        \<longrightarrow> \<not> snd (afun_mon x' st)
            \<and> (\<forall>st' y'. (y', st') \<in> fst (afun_mon x' st)
                \<longrightarrow> (\<exists>\<sigma>' y. \<xi>' afun_name (\<sigma>, x) (\<sigma>', y)
                    \<and> val_rel y y' \<and> (\<sigma>', st') \<in> srel)))"

lemma afun_corres:
  "abs_rel \<Xi>' srel s \<xi>' afun'
  \<Longrightarrow> i < length \<gamma> \<Longrightarrow> val_rel (\<gamma> ! i) v'
  \<Longrightarrow> \<Gamma>' ! i = Some (fst (snd (\<Xi>' s)))
  \<Longrightarrow> corres srel
     (App (AFun s []) (Var i))
     (do x \<leftarrow> afun' v'; gets (\<lambda>s. x) od)
     \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> st"
  apply (clarsimp simp: corres_def abs_rel_def)
  apply (frule matches_ptrs_length, simp)
  apply (frule(2) matches_ptrs_proj_single')
  apply clarsimp
  apply (elim allE, drule mp, blast)
  apply clarsimp
  apply (elim allE, drule(1) mp)
  apply clarsimp
  apply (intro exI conjI[rotated], assumption+)
  apply (rule u_sem_abs_app)
    apply (rule u_sem_afun)
   apply (rule u_sem_var)
  apply simp
  done

end

ML {*
local
  fun make_simp_xi_simpset ctxt xi_simp =
    put_simpset HOL_basic_ss ctxt
        addsimps [xi_simp]
        addsimps @{thms fst_conv snd_conv list.case char.case assoc_lookup_simps}
    (* Don't substitute under list.case - I think this is not relevant any more, since we've changed to assoc_lookup instead of case.
       But I'm not game to remove it yet. [amos] *)
    |> Simplifier.add_cong @{thm list.case_cong_weak}

in

(* Simplify all occurrences of Xi, and compute the lookup results as far as possible *)
fun simp_xi ctxt = let
    val xi_def = Proof_Context.get_thm ctxt "\<Xi>_def"
  in
    full_simplify (make_simp_xi_simpset ctxt xi_def)
  end

(* As above, but only simplify saturated calls to Xi - these are the cases where we will learn something *)
fun simp_xi_fully_applied ctxt = let
    val xi_def = Proof_Context.get_thm ctxt "\<Xi>_def"
    val xi_def_fully_applied = @{thm fun_cong} OF [@{thm meta_eq_to_obj_eq} OF [xi_def]]
  in
    full_simplify (make_simp_xi_simpset ctxt xi_def_fully_applied)
  end

val simp_xi_att = Attrib.thms >> (fn thms => Thm.rule_attribute thms (fn cg => let
    val ctxt = Context.proof_of cg
    val abb_tys = Proof_Context.get_thms ctxt "abbreviated_type_defs"
  in
    simp_xi ctxt #>
    full_simplify (put_simpset HOL_basic_ss ctxt
                   addsimps thms addsimps abb_tys)
  end))
end
*}

setup {* Attrib.setup @{binding simp_\<Xi>} simp_xi_att "cleans up thms about \<Xi>" *}

end

