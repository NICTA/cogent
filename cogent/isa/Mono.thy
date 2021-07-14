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

theory Mono
imports ValueSemantics
begin

context value_sem
begin


(* Rename abstract functions (AFun) in an expression.
 * This lets us switch between the polymorphic and monomorphic environments
 * where monomorphised functions have different names. *)
fun
  rename_expr :: "('b \<Rightarrow> 'c) \<Rightarrow> 'b expr \<Rightarrow> 'c expr"
where
  "rename_expr rename (AFun f ts)       = AFun (rename f) ts"
| "rename_expr rename (Fun f ts)        = Fun (rename_expr rename f) ts"
| "rename_expr rename (Var i)           = Var i"
| "rename_expr rename (Prim p es)       = Prim p (map (rename_expr rename) es)"
| "rename_expr rename (App a b)         = App (rename_expr rename a) (rename_expr rename b)"
| "rename_expr rename (Con as t e)      = Con as t (rename_expr rename e)"
| "rename_expr rename (Struct ns ts vs) = Struct ns ts (map (rename_expr rename) vs)"
| "rename_expr rename (Member v f)      = Member (rename_expr rename v) f"
| "rename_expr rename (Unit)            = Unit"
| "rename_expr rename (Cast t e)        = Cast t (rename_expr rename e)"
| "rename_expr rename (Lit v)           = Lit v"
| "rename_expr rename (SLit s)          = SLit s"
| "rename_expr rename (Tuple a b)       = Tuple (rename_expr rename a) (rename_expr rename b)"
| "rename_expr rename (Put e f e')      = Put (rename_expr rename e) f (rename_expr rename e')"
| "rename_expr rename (Let e e')        = Let (rename_expr rename e) (rename_expr rename e')"
| "rename_expr rename (LetBang vs e e') = LetBang vs (rename_expr rename e) (rename_expr rename e')"
| "rename_expr rename (Case e t a b)    = Case (rename_expr rename e) t (rename_expr rename a) (rename_expr rename b)"
| "rename_expr rename (Esac e t)        = Esac (rename_expr rename e) t"
| "rename_expr rename (If c t e)        = If (rename_expr rename c) (rename_expr rename t) (rename_expr rename e)"
| "rename_expr rename (Take e f e')     = Take (rename_expr rename e) f (rename_expr rename e')"
| "rename_expr rename (Split v va)      = Split (rename_expr rename v) (rename_expr rename va)"
| "rename_expr rename (Promote t e)     = (Promote t (rename_expr rename e))"

fun
  rename_val :: "('b \<Rightarrow> 'c) \<Rightarrow> ('b, 'a) vval \<Rightarrow> ('c, 'a) vval"
where
  "rename_val rename (VPrim lit)       = VPrim lit"
| "rename_val rename (VProduct t u)    = VProduct (rename_val rename t) (rename_val rename u)"
| "rename_val rename (VSum name v)     = VSum name (rename_val rename v)"
| "rename_val rename (VRecord vs)      = VRecord (map (rename_val rename) vs)"
| "rename_val rename (VAbstract t)     = VAbstract t"
| "rename_val rename (VAFunction f ts) = VAFunction (rename f) ts"
| "rename_val rename (VFunction f ts)  = VFunction (rename_expr rename f) ts"
| "rename_val rename VUnit             = VUnit"


(* Proof of semantic preservation across rename_expr and monoexpr. *)
definition
  rename_mono_prog ::
  "(('f \<times> type list) \<Rightarrow> 'f) \<Rightarrow> ('f \<Rightarrow> poly_type) \<Rightarrow> ('f, 'a) vabsfuns \<Rightarrow> ('f, 'a) vabsfuns \<Rightarrow> bool"
where
  "rename_mono_prog rename \<Xi> \<xi>\<^sub>r\<^sub>m \<xi>\<^sub>p \<equiv>
     \<xi>\<^sub>r\<^sub>m matches \<Xi> \<longrightarrow>
     proc_ctx_wellformed \<Xi> \<longrightarrow>
     (\<forall>f ts v v'. \<xi>\<^sub>r\<^sub>m (rename (f, ts)) (rename_val rename (monoval v)) v' \<longrightarrow>
        (\<exists> v''. v' = rename_val rename (monoval v'') \<and>  \<xi>\<^sub>p f v v''))"

fun
  rename_monoval_prog :: "(('f \<times> type list) \<Rightarrow> 'f) \<Rightarrow> ('f, 'a) vabsfuns \<Rightarrow> ('f \<times> type list) \<Rightarrow>
                  ('f, 'a) vval \<Rightarrow> ('f, 'a) vval \<Rightarrow> bool"
where
  "rename_monoval_prog rename \<xi> n v1 v2 =
     \<xi> (rename n) (rename_val rename (monoval v1)) (rename_val rename (monoval v2))"

lemma rename_monoval_prim_prim:
  "rename_val rename (monoval v) = VPrim l \<Longrightarrow> v = VPrim l"
  by (induct v, simp_all)

lemma map_rename_monoval_prim_prim:
  "map (rename_val rename \<circ> monoval) vs = map VPrim ls \<Longrightarrow> vs = map VPrim ls"
  by (induct vs arbitrary: ls) (auto simp: rename_monoval_prim_prim)

lemma rename_monoexpr_correct:
  assumes "proc_ctx_wellformed \<Xi>"
  and     "\<xi>\<^sub>r\<^sub>m matches \<Xi>"
  and     "rename_mono_prog rename \<Xi> \<xi>\<^sub>r\<^sub>m \<xi>\<^sub>p"
  and     "\<Xi> \<turnstile> map (rename_val rename \<circ> monoval) \<gamma> matches \<Gamma>"
  shows   "\<xi>\<^sub>r\<^sub>m, map (rename_val rename \<circ> monoval) \<gamma> \<turnstile> rename_expr rename (monoexpr e) \<Down> v' \<Longrightarrow>
             \<Xi>, [], \<Gamma> \<turnstile> rename_expr rename (monoexpr e) : \<tau>  \<Longrightarrow>
             \<exists>v. \<xi>\<^sub>p, \<gamma> \<turnstile> e \<Down>  v \<and> v' = rename_val rename (monoval v)"
  and     "\<xi>\<^sub>r\<^sub>m, map (rename_val rename \<circ> monoval) \<gamma> \<turnstile>* map (rename_expr rename \<circ> monoexpr) es \<Down> vs' \<Longrightarrow>
             \<Xi>, [], \<Gamma> \<turnstile>* map (rename_expr rename \<circ> monoexpr) es : \<tau>s \<Longrightarrow>
             \<exists>vs. (\<xi>\<^sub>p , \<gamma> \<turnstile>* es \<Down> vs) \<and> vs' = (map (rename_val rename \<circ> monoval) vs)"
  using assms
  proof (induct \<xi>\<^sub>r\<^sub>m "map (rename_val rename \<circ> monoval) \<gamma>" "rename_expr rename (monoexpr e)" v'
            and \<xi>\<^sub>r\<^sub>m "map (rename_val rename \<circ> monoval) \<gamma>" "map (rename_expr rename \<circ> monoexpr) es" vs'
         arbitrary: \<tau> \<Gamma> \<gamma> e
           and \<tau>s \<Gamma> \<gamma> es
         rule: v_sem_v_sem_all.inducts)
  case (v_sem_var \<xi> i \<gamma> e \<tau> \<Gamma>)
  then show ?case
    by (cases e) (force intro: v_sem_v_sem_all.v_sem_var dest: matches_length)+
next
  case (v_sem_lit \<xi> l \<gamma> e  \<tau> \<Gamma>) then show ?case
    by (cases e) (auto intro: v_sem_v_sem_all.v_sem_lit)
next
  case (v_sem_fun \<xi> f ts \<gamma> e \<tau> \<Gamma>) then show ?case
    by (cases e) (auto intro: v_sem_v_sem_all.v_sem_fun)
next
  case (v_sem_afun \<xi> f ts \<gamma> e \<tau> \<Gamma>) then show ?case
    by (cases e) (auto intro: v_sem_v_sem_all.v_sem_afun)
next
  case (v_sem_cast \<xi> re l \<tau> l'  \<gamma> e \<tau>' \<Gamma>)
  note IH1=this(2) and rest= this(1,3-) then show ?case
    apply (cases e, simp_all)
    apply (rule exI)
    apply (rule conjI)
     apply (erule typing_castE)
     apply (rule v_sem_v_sem_all.v_sem_cast)
      apply (rule IH1[THEN exE], simp_all)
    apply (rename_tac v)
    apply clarsimp
    by (case_tac v, simp_all)
next
  case v_sem_con then show ?case
    by (cases e) (fastforce intro: v_sem_v_sem_all.v_sem_con)+
next
  case v_sem_unit then show ?case
    by (cases e) (fastforce intro!:  v_sem_v_sem_all.v_sem_unit)+
next
  case v_sem_tuple then show ?case
    by (cases e) (fastforce intro: matches_split' v_sem_v_sem_all.v_sem_tuple)+
next
  case (v_sem_esac \<xi> t ts v \<gamma> e \<tau> \<Gamma>)
  note IH1=this(2) and rest= this(1,3-) from rest show ?case
    apply (cases e, simp_all)
    apply (erule typing_esacE)
    apply (cut_tac IH1, simp_all)
    apply (erule exE)
    apply (rename_tac vval)
    apply (case_tac vval, simp_all)
    by (fastforce intro!: v_sem_v_sem_all.v_sem_esac)
next
  case (v_sem_struct \<xi> xs vs ts \<gamma> ns e \<tau> \<Gamma>) then show ?case
    by (cases e) (fastforce intro: v_sem_v_sem_all.v_sem_struct)+
next
  case (v_sem_if \<xi> rb b e1 e2 v \<gamma> e \<tau> \<Gamma>)
  note IH1=this(2) and IH2=this(4) and rest=this(1,3, 5-) from rest show ?case
    apply (cases e, simp_all)
    apply (rename_tac exp1 exp2 exp3)
    apply (erule typing_ifE)
    apply (cut_tac IH1[OF _ _ _ _ _ _ matches_split'(1)], simp_all)
    apply (clarsimp)
    apply (rename_tac vval)
    apply (case_tac vval, simp_all)
    apply (subgoal_tac "\<exists>va. (\<xi>\<^sub>p , \<gamma> \<turnstile> if b then exp2 else exp3 \<Down> va) \<and> v = rename_val rename (monoval va)")
     apply (fastforce intro: v_sem_v_sem_all.v_sem_if)
    apply (rule IH2[OF _ _ _ _ _ _ matches_split'(2)], simp_all)
    apply (fastforce split: if_splits)
    done
next
  case v_sem_all_empty then show ?case
    by (simp add: v_sem_v_sem_all.v_sem_all_empty)
next
  case (v_sem_all_cons \<xi> e v es' vs' \<gamma> es \<tau>s \<Gamma>) then show ?case
    by (cases es) (fastforce dest: matches_split' intro!: v_sem_v_sem_all.intros)+
next
  case (v_sem_prim \<xi> es vs p \<gamma> e \<tau> \<Gamma>)
  note IH = this(2)
    and rest = this(1,3-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (clarsimp elim!: typing_primE)

    apply (cut_tac IH, simp_all)
    apply clarsimp
    apply (frule(4) preservation(2) [where \<tau>s = "[]" and K = "[]", simplified])
    apply (frule v_t_map_TPrimD)
    apply clarsimp
    apply (frule eval_prim_preservation)
     apply (simp)
    apply (erule vval_typing.cases, simp_all)
    apply (rule exI)
    apply (rule conjI)
     apply (rule v_sem_prim', simp_all)
    by (force dest: map_rename_monoval_prim_prim)
next
  case (v_sem_put \<xi> r fs re rv f \<gamma> e \<tau> \<Gamma>)
  note IH1=this(2)
    and IH2=this(4)
    and rest= this(1,3, 5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (rename_tac rec f' expr)
    apply (erule typing_putE)
    apply (cut_tac IH1[OF _ _ _ _ _ _ matches_split'(1)], simp_all)
    apply (clarsimp)
    apply (rename_tac rv')
    apply (case_tac rv', simp_all)
    apply (cut_tac IH2[OF _ _ _ _ _ _ matches_split'(2)], simp_all)
    by (fastforce simp: map_update intro: v_sem_v_sem_all.v_sem_put)
next case (v_sem_let \<xi> e1 rv1 e2 rv2 \<gamma> e \<tau> \<Gamma>)
  note IH1 = this(2)
    and  IH2 = this(4)
    and rest = this(1,3,5-)
  from rest show ?case
    apply (case_tac e, simp_all)
    apply (rename_tac exp1 exp2)
    apply (clarsimp elim!: typing_letE)
    apply (frule(1) matches_split'(1))
    apply (frule(1) matches_split'(2))
    apply (cut_tac IH1[OF _ _ _ _ _ _ matches_split'(1)], simp_all)
    apply clarsimp
    apply (rename_tac v1)
    apply (frule(4) preservation [where \<tau>s = "[]" and K = "[]", simplified])
    apply (drule(2) matches_cons'[OF matches_split'(2)])
    apply (subgoal_tac "\<exists>v. \<xi>\<^sub>p , v1 # \<gamma> \<turnstile> exp2 \<Down> v \<and> rv2 = rename_val rename (monoval v)")
     apply (force intro!: v_sem_v_sem_all.v_sem_let)
    apply (force intro!: IH2)
    done
next
  case (v_sem_letbang \<xi> e1 rv1 e2 rv2 vs \<gamma> e \<tau> \<Gamma>)
  note IH1 = this(2)
    and IH2 = this(4)
    and rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (rename_tac vs exp1 exp2)
    apply (clarsimp elim!: typing_letbE)
    apply (frule(1) matches_split_bang'(1))
    apply (frule(1) matches_split_bang'(2))
    apply (cut_tac IH1[OF _ _ _ _ _ _ matches_split_bang'(1)], simp_all)
    apply clarsimp
    apply (rename_tac v1)
    apply (frule(4) preservation [where \<tau>s = "[]" and K = "[]", simplified])
    apply (drule(2) matches_cons'[OF matches_split_bang'(2)])
      (* cut_tac, but we want to select \<gamma> *)
    apply (subgoal_tac "\<exists>v. \<xi>\<^sub>p , v1 # \<gamma> \<turnstile> exp2 \<Down> v \<and> rv2 = rename_val rename (monoval v)")
     apply (force intro!: v_sem_v_sem_all.v_sem_letbang)
    apply (force intro!: IH2)
    done
next
  case (v_sem_case_m \<xi> re f rv mre mrv nre \<gamma> e \<tau> \<Gamma>)
  note IH1=this(2)
    and IH2 = this(4)
    and rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (rename_tac exp1 tag exp2 exp3)
    apply (clarsimp elim!: typing_caseE)
    apply (rename_tac  \<Gamma>1 \<Gamma>2 ts tf)
    apply (frule(1) matches_split'(1))
    apply (frule(1) matches_split'(2))
    apply (cut_tac IH1[OF _ _ _ _ _ _ matches_split'(1)], simp_all)
    apply clarsimp
    apply (rename_tac v1)
    apply (case_tac v1, simp_all)
    apply (rename_tac t' v1')
    apply (frule(4) preservation [where \<tau>s = "[]" and K = "[]", simplified, rotated -3])
    apply (erule v_t_sumE')
    apply (drule(2) matches_cons'[OF matches_split'(2)])
    apply (subgoal_tac "\<exists>v. \<xi>\<^sub>p , v1' # \<gamma> \<turnstile> exp2 \<Down> v \<and> mrv = rename_val rename (monoval v)")
     apply (fastforce intro!: v_sem_v_sem_all.v_sem_case_m)
    apply (fastforce intro!: IH2 dest: distinct_fst)
    done
next
  case (v_sem_case_nm \<xi> rea f rv f' rne rnv rme \<gamma> e \<tau> \<Gamma>)
  then show ?case
  proof (cases e)
    case (Case ea f'' me ne)
    have rea_is: "rea = rename_expr rename (monoexpr ea)"
      and f''_is: "f'' = f'"
      and rme_is: "rme = rename_expr rename (monoexpr me)"
      and rne_is: "rne = rename_expr rename (monoexpr ne)"
      using v_sem_case_nm.hyps(6) Case
      by simp+

      obtain \<Gamma>1 \<Gamma>2 ts t
        where split\<Gamma>: "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
          and typing_renamed_ea: "\<Xi>, [], \<Gamma>1 \<turnstile> rename_expr rename (monoexpr ea) : TSum ts"
          and f'_in_ts: "(f', t, Unchecked) \<in> set ts"
          and "\<Xi>, [], Some t # \<Gamma>2 \<turnstile> rename_expr rename (monoexpr me) : \<tau>"
          and typing_renamed_ne: "\<Xi>, [], Some (TSum (tagged_list_update f' (t, Checked) ts)) # \<Gamma>2 \<turnstile> rename_expr rename (monoexpr ne) : \<tau>"
        using v_sem_case_nm.prems Case f''_is by auto
      have matches1: "\<Xi> \<turnstile> map (rename_val rename \<circ> monoval) \<gamma> matches \<Gamma>1"
        and matches2: "\<Xi> \<turnstile> map (rename_val rename \<circ> monoval) \<gamma> matches \<Gamma>2"
        using matches_split' split\<Gamma> v_sem_case_nm.prems(5) by blast+

      obtain v1'
        where "\<xi>\<^sub>p , \<gamma> \<turnstile> ea \<Down> v1'"
          and "VSum f rv = rename_val rename (monoval v1')"
        using matches1 rea_is typing_renamed_ea v_sem_case_nm.hyps(2) v_sem_case_nm.prems
        by blast
      then obtain v1
        where rv_is: "rv = rename_val rename (monoval v1)"
          and ea_usem: "\<xi>\<^sub>p , \<gamma> \<turnstile> ea \<Down> VSum f v1"
        by (case_tac v1', simp+)

      have "\<Xi> \<turnstile> rename_val rename (monoval (VSum f v1)) :v TSum ts"
        using preservation(1)[where \<tau>s="[]" and K="[]", simplified]
          v_sem_case_nm.prems(2-3) v_sem_case_nm.hyps(1)
          matches1 typing_renamed_ea rea_is rv_is
        by auto
      then have "\<Xi> \<turnstile> VSum f (rename_val rename (monoval v1)) :v TSum ts"
        by force
      then have "\<Xi> \<turnstile> VSum f (rename_val rename (monoval v1)) :v TSum (tagged_list_update f' (t, Checked) ts)"
        by (metis f'_in_ts sum_downcast[OF _ not_sym] v_sem_case_nm.hyps(3))
      then have matches2_aug: "\<Xi> \<turnstile> map (rename_val rename \<circ> monoval) (VSum f v1 # \<gamma>) matches Some (TSum (tagged_list_update f' (t, Checked) ts)) # \<Gamma>2"
        using matches2 rv_is by (force intro: matches_cons')
      then obtain v2
        where ne_usem: "\<xi>\<^sub>p , VSum f v1 # \<gamma> \<turnstile> ne \<Down> v2"
        and rnv_is: "rnv = rename_val rename (monoval v2)"
        using v_sem_case_nm.hyps(5)[OF _ _ typing_renamed_ne] v_sem_case_nm.prems(2-4) rne_is rv_is
        by force

      have "\<xi>\<^sub>p , \<gamma> \<turnstile> Case ea f'' me ne \<Down> v2"
        using ea_usem ne_usem f''_is v_sem_case_nm.hyps(3)
        by (auto intro: v_sem_v_sem_all.v_sem_case_nm)
      then show ?thesis
        using rnv_is Case by fast
    qed simp+
  next
  case (v_sem_member \<xi> re fs f \<gamma> e \<tau> \<Gamma>)
  note IH=this(2)
  and rest = this(1,3-)
  from rest show ?case
  apply (case_tac e, simp_all)
  apply (clarsimp elim!: typing_memberE)
  apply (cut_tac IH, simp_all)
  apply clarsimp
  apply (rename_tac rv)
  apply (case_tac rv, simp_all)
  apply (frule(4) preservation [where \<tau>s = "[]" and K = "[]", simplified])
  apply (erule v_t_recordE)
  apply (frule vval_typing_record_length)
  by (fastforce intro: v_sem_v_sem_all.v_sem_member)
  next case (v_sem_split \<xi> ab a b es rv \<gamma> e \<tau> \<Gamma>)
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  from rest show ?case
    apply (case_tac e, simp_all)
    apply (rename_tac exp1 exp2)
    apply (clarsimp elim!: typing_splitE)
    apply (cut_tac IH1[OF _ _ _ _ _ _ matches_split'(1)], simp_all)
    apply clarsimp
    apply (rename_tac v)
    apply (case_tac v, simp_all)
    apply (frule(5) preservation [where \<tau>s = "[]" and K = "[]", OF _ _ matches_split'(1), simplified])
    apply (rename_tac va vb)
    apply (erule v_t_productE)
    apply (drule(1) matches_split'(2)[rotated])
    apply (drule_tac x="rename_val rename (monoval vb)" in matches_cons', simp)
    apply (drule_tac x="rename_val rename (monoval va)" in matches_cons', simp)
    apply (subgoal_tac "\<exists>v. \<xi>\<^sub>p , va # vb # \<gamma> \<turnstile> exp2 \<Down> v \<and> rv = rename_val rename (monoval v)")
     apply (fastforce intro: v_sem_v_sem_all.v_sem_split)
    apply (force intro!: IH2)
    done
next
  case (v_sem_take \<xi> re fs f es rv \<gamma> e \<tau> \<Gamma>)
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  from rest show ?case
    apply (case_tac e, simp_all)
    apply (rename_tac exp1 field exp2)
    apply (clarsimp elim!: typing_takeE)
    apply (rename_tac \<Gamma>1 \<Gamma>2 ts s n t k taken)
    apply (cut_tac IH1[OF _ _ _ _ _ _ matches_split'(1)], simp_all)
    apply clarsimp
    apply (rename_tac v)
    apply (case_tac v, simp_all)
    apply (rename_tac fs')
    apply (frule(5) preservation [where \<tau>s = "[]" and K = "[]", OF _ _ matches_split'(1), simplified])
    apply (drule(1) matches_split'(2)[rotated])
    apply (drule_tac x="VRecord (map (rename_val rename \<circ> monoval) fs')" and \<tau>="TRecord (ts[f := (n, t, taken)]) s" and \<Gamma>=\<Gamma>2
        in matches_cons')
     apply (clarsimp simp add: map_update)
     apply (erule v_t_recordE)
     apply (fastforce intro: v_t_record dest: vval_typing_record_take simp add: map_fst_update)
    apply (drule_tac x="(map (rename_val rename \<circ> monoval) fs')!f" in matches_cons')
     apply (fastforce dest: vval_typing_record_nth)
    apply (subgoal_tac "\<exists>v. \<xi>\<^sub>p , fs' ! f # VRecord fs' # \<gamma> \<turnstile> exp2 \<Down> v \<and> rv = rename_val rename (monoval v)")
     apply (fastforce intro: v_sem_v_sem_all.v_sem_take)
    apply (intro IH2)
          apply (force dest: vval_typing_record_length)
         apply (blast+)[5]
    apply (force simp add: matches_Cons dest: vval_typing_record_length)
    done
  next
  case (v_sem_app \<xi> re f ts e' rv rsv \<gamma> e \<tau> \<Gamma>)
  note IH1 = this(2)
  and  IH2 = this(4)
  and  IH3 = this(6)
  and  rest = this(1,3,5,7-)
  from rest show ?case
  apply (cases e, simp_all)
  apply (erule typing_appE)
  apply (rename_tac \<Gamma>1 \<Gamma>2 t)
  apply (cut_tac IH1[OF _ _ _ _ _ _ matches_split'(1)], simp_all)
  apply clarsimp
  apply (rename_tac fv)
  apply (case_tac fv, simp_all)
  apply clarsimp
  apply (rename_tac expr ts')
  apply (cut_tac IH2[OF _ _ _ _ _ _ matches_split'(2)], simp_all)
  apply clarsimp
  apply (rename_tac v)
  apply (frule(5) preservation(1) [where \<tau>s = "[]" and K = "[]", OF _ _ matches_split'(1), simplified])
  apply (frule(5) preservation(1) [where \<tau>s = "[]" and K = "[]", OF _ _ matches_split'(2), simplified])
  apply (erule v_t_funE)
  apply (subgoal_tac "\<exists>r. \<xi>\<^sub>p , [v] \<turnstile> specialise ts' expr \<Down> r \<and> rsv = rename_val rename (monoval r)")
   apply (fastforce intro: v_sem_v_sem_all.v_sem_app)
  apply (force intro!: IH3 dest: value_subtyping simp: subtyping_simps matches_def)
  done
next
  case (v_sem_abs_app \<xi> re f ts e' rv rv' \<gamma> e \<tau> \<Gamma>)
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (case_tac e, simp_all)
    apply (clarsimp)
    apply (erule typing_appE)
    apply (rename_tac \<Gamma>1 \<Gamma>2 t)
    apply (cut_tac IH1[OF _ _ _ _ _ _ matches_split'(1)], simp_all)
    apply clarsimp
    apply (rename_tac fv)
    apply (subgoal_tac "\<xi> f rv rv'")
     apply (case_tac fv, simp_all)
    apply (rename_tac f' ts')
    apply (cut_tac IH2[OF _ _ _ _ _ _ matches_split'(2)], simp_all)
    by (fastforce intro: v_sem_v_sem_all.v_sem_abs_app simp: rename_mono_prog_def)
next
  case (v_sem_promote \<xi> ea ea' t')
  then show ?case
    by (cases e) (fastforce intro: v_sem_v_sem_all.v_sem_promote)+
qed

end

end
