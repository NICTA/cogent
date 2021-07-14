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

theory TypeTrackingSemantics
  imports
    UpdateSemantics
    TypeTrackingTyping
begin

context update_sem begin

inductive u_tt_sem_pres :: "('f \<Rightarrow> poly_type)
                          \<Rightarrow> ('f,'a,'l) uabsfuns
                          \<Rightarrow> ('f,'a,'l) uval env
                          \<Rightarrow> kind env
                          \<Rightarrow> tree_ctx
                          \<Rightarrow> type
                          \<Rightarrow> ('f,'a,'l) store \<times> 'f expr
                          \<Rightarrow> ('f,'a,'l) store \<times> ('f,'a,'l) uval
                          \<Rightarrow> bool"  ("_, _, _, _, _, _ T\<turnstile> _ \<Down>! _" [30,0,0,0,0,20] 60)
where
  u_tt_sem_pres_default : "\<lbrakk> \<not> composite_anormal_expr x
                           ; \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! st
                           ; \<Xi>, K, snd \<Gamma> \<turnstile> x : \<tau>
                           ; \<exists>rs ws. matches_ptrs \<Xi> \<sigma> \<gamma> (snd \<Gamma>) rs ws
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, x) \<Down>! st"

| u_tt_sem_pres_let     : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [Some t] \<Gamma>2
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, t T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', a')
                           ; \<Xi>, \<xi> , (a' # \<gamma>), K, \<Gamma>2, \<tau> T\<turnstile> (\<sigma>', b) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Let a b) \<Down>! st"

| u_tt_sem_pres_letbang : "\<lbrakk> ttsplit_bang is sps K \<Gamma> [] \<Gamma>1 [Some t] \<Gamma>2
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, t T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', a')
                           ; \<Xi>, \<xi> , (a' # \<gamma>), K, \<Gamma>2, \<tau> T\<turnstile> (\<sigma>', b) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, LetBang vs a b) \<Down>! st"

| u_tt_sem_pres_case_m  : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [] \<Gamma>2
                           ; ttsplit_triv \<Gamma>2 [typ1] \<Gamma>3 [typ2] \<Gamma>4
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TSum ts T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', USum t v rs)
                           ; \<Xi>, \<xi> , (v # \<gamma>),K,  \<Gamma>3, \<tau> T\<turnstile> (\<sigma>', m) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Case x t m n) \<Down>! st"

| u_tt_sem_pres_case_nm : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [] \<Gamma>2
                           ; ttsplit_triv \<Gamma>2 [typ1] \<Gamma>3 [typ2] \<Gamma>4
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TSum ts T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', USum t' v rs)
                           ; t' \<noteq> t
                           ; \<Xi>, \<xi> , (USum t' v rs # \<gamma>), K, \<Gamma>4, \<tau> T\<turnstile> (\<sigma>', n) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Case x t m n) \<Down>! st"

| u_tt_sem_pres_if      : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [] \<Gamma>2
                           ; ttsplit_triv \<Gamma>2 [] \<Gamma>3 [] \<Gamma>4
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TPrim Bool T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UPrim (LBool b))
                           ; \<Xi>, \<xi> , \<gamma>, K, (if b then \<Gamma>3 else \<Gamma>4), \<tau> T\<turnstile> (\<sigma>', if b then t else e) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, If x t e) \<Down>! st"

| u_tt_sem_pres_take    : "\<lbrakk> s = Boxed Writable l
                           ; ttsplit K \<Gamma> sps [] \<Gamma>1 [Some f_ty, Some (TRecord tak_fs s)] \<Gamma>2
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TRecord ts s T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UPtr p rp)
                           ; \<sigma>' p = Some (URecord fs)
                           ; \<Xi>, \<xi> , (fst (fs ! f) # UPtr p rp # \<gamma>), K, \<Gamma>2, \<tau> T\<turnstile> (\<sigma>', e) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Take x f e) \<Down>! st"

| u_tt_sem_pres_take_ub : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [Some f_ty, Some (TRecord tak_ts Unboxed)] \<Gamma>2
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TRecord ts Unboxed T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', URecord fs)
                           ; \<Xi>, \<xi> , (fst (fs ! f) # URecord fs # \<gamma>), K, \<Gamma>2, \<tau> T\<turnstile> (\<sigma>', e) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Take x f e) \<Down>! st"

| u_tt_sem_pres_split   : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [Some t, Some u] \<Gamma>2
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TProduct t u T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UProduct a b)
                           ; \<Xi>, \<xi> , (a # b # \<gamma>), K, \<Gamma>2, \<tau> T\<turnstile> (\<sigma>', e) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Split x e) \<Down>! st"


theorem intermediate_preservation:
assumes "proc_ctx_wellformed \<Xi>"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (snd \<Gamma>) \<langle>r, w\<rangle>"
and     "\<xi> matches-u \<Xi>"
shows   "\<lbrakk> \<xi>, \<gamma> \<turnstile>  (\<sigma>, e) \<Down>! (\<sigma>', v)
         ; \<Xi>, [], \<Gamma> T\<turnstile> e : \<tau>
         \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, [], \<Gamma>, \<tau> T\<turnstile> (\<sigma>, e) \<Down>! (\<sigma>', v)"
and     "\<lbrakk> \<xi>, \<gamma> \<turnstile>* (\<sigma>, es) \<Down>! (\<sigma>', vs)
         ; \<Xi>, [], (snd \<Gamma>) \<turnstile>* es : \<tau>s'
         \<rbrakk> \<Longrightarrow> True"
using assms proof (induct "(\<sigma>, e)"        "(\<sigma>', v )"
                      and "(\<sigma>, es)" "(\<sigma>', vs)"
                      arbitrary:  e   \<tau>   \<Gamma> r w v  \<sigma>' \<sigma>
                             and  es  \<tau>s' \<Gamma> r w vs \<sigma>' \<sigma>
                      rule: u_sem_u_sem_all.inducts)

  case u_sem_let show ?case using u_sem_let.prems u_sem_let.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_imp_split)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (erule u_tt_sem_pres_let)
     apply (rule u_sem_let.hyps(2), simp+)[1]
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_let.hyps(1)]
     , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply clarsimp
    apply (erule(1) u_sem_let.hyps(4))
     apply simp
     apply (erule matches_ptrs_some)
        apply (erule(2) matches_ptrs_frame)
        apply (drule(1) frame_noalias_matches_ptrs(2), blast, blast)
       apply (force dest: frame_noalias_matches_ptrs(1))
      apply (force dest!: frame_noalias_matches_ptrs(2))
     apply blast
    apply simp
    done

next

  case u_sem_letbang show ?case using u_sem_letbang.prems u_sem_letbang.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_bang_imp_split_bang)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split_bang', clarsimp)
    apply (erule u_tt_sem_pres_letbang)
     apply (rule u_sem_letbang.hyps(2), simp+)[1]
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_letbang.hyps(1)]
     , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply clarsimp
    apply (frule(2) escapable_no_readers(1))
    apply (erule(1) u_sem_letbang.hyps(4))
     apply simp
     apply (erule matches_ptrs_some)
        apply (erule(1) matches_ptrs_frame, blast)
        apply (drule(1) frame_noalias_matches_ptrs(2), blast, blast)
       apply (rule frame_noalias_matches_ptrs(1), simp+, blast)
      apply (rule frame_noalias_matches_ptrs(2), simp+, blast)
     apply auto[1]
    apply assumption
    done

next

  case u_sem_split show ?case using u_sem_split.prems u_sem_split.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_imp_split)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (erule u_tt_sem_pres_split)
     apply (rule u_sem_split.hyps(2), simp+)[1]
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_split.hyps(1)]
     , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply clarsimp
    apply (erule u_t_productE)
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (erule(1) u_sem_split.hyps(4))
     apply simp
      apply (rule matches_ptrs_some, simp, rule matches_ptrs_some, assumption)
           apply (erule(2) matches_ptrs_frame)
           apply fast
          apply blast
         apply fast
        apply blast
       apply blast
      apply fast
     apply blast
    apply blast
    done

next

  note if_splits[split del]
  case u_sem_if show ?case using u_sem_if.prems u_sem_if.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_imp_split)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (erule(1) u_tt_sem_pres_if)
     apply (rule u_sem_if.hyps(2), simp+)[1]
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_if.hyps(1)]
     , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply (clarsimp simp: ttsplit_triv_def)
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (rule u_sem_if.hyps(4), simp split: if_splits, assumption)
     apply (simp split: if_splits, erule(2) matches_ptrs_frame)
      apply blast
    apply (meson matches_ptrs_frame subset_helper sup.cobounded1 sup.cobounded2)
    apply assumption
    done

next

  case u_sem_case_m show ?case using u_sem_case_m.prems u_sem_case_m.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_imp_split)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (erule(1) u_tt_sem_pres_case_m)
     apply (rule u_sem_case_m.hyps(2), simp+)[1]
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_case_m.hyps(1)]
     , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply (clarsimp simp: ttsplit_triv_def)
    apply (erule u_t_sumE, clarsimp)
    apply (drule(1) distinct_fst[rotated 1], simp, simp)
    apply (erule(1) u_sem_case_m.hyps(4))
     apply simp
     apply (erule matches_ptrs_some)
        apply (erule(2) matches_ptrs_frame)
        apply (drule(1) frame_noalias_matches_ptrs(2), blast, blast)
       apply (force dest: frame_noalias_matches_ptrs(1))
      apply (force dest!: frame_noalias_matches_ptrs(2))
     apply blast
    apply simp
    done

next
  case (u_sem_case_nm \<xi> \<gamma> \<sigma> x \<sigma>'' t' v' rs t n m)

  from u_sem_case_nm.prems(1)
  show ?case
  proof (cases rule: ttyping.cases)
    case (ttyping_case ijs t\<Gamma>1 t\<Gamma>2 ta t\<Gamma>3 ts t\<Gamma>4)

    moreover have "[] \<turnstile> snd \<Gamma> \<leadsto> snd t\<Gamma>1 | snd t\<Gamma>2"
      using ttyping_case ttsplit_imp_split by fastforce
    moreover then obtain r1 w1 r2 w2
      where matches1: "\<Xi>, \<sigma> \<turnstile> \<gamma> matches snd t\<Gamma>1 \<langle>r1, w1\<rangle>"
        and matches2: "\<Xi>, \<sigma> \<turnstile> \<gamma> matches snd t\<Gamma>2 \<langle>r2, w2\<rangle>"
        and r_as_un: "r = r1 \<union> r2"
        and w_as_un: "w = w1 \<union> w2"
        and w1_2_disjoint: "w1 \<inter> w2 = {}"
      using matches_ptrs_split' u_sem_case_nm.prems(3)
      by blast
    moreover then have
      w1_r2_noalias: "w1 \<inter> r2 = {}"
      and w2_r1_noalias: "w2 \<inter> r1 = {}"
      using matches_ptrs_noalias u_sem_case_nm.prems(3) by blast+
    moreover obtain ijs \<Gamma>1a \<Gamma>2a
       where "fst t\<Gamma>2 = TyTrSplit ijs [Some ta] \<Gamma>1a [Some (TSum (tagged_list_update t (ta, Checked) ts))] \<Gamma>2a"
       and "t\<Gamma>3 = (\<Gamma>1a, [Some ta] @ snd t\<Gamma>2)"
       and t\<Gamma>4_is: "t\<Gamma>4 = (\<Gamma>2a, [Some (TSum (tagged_list_update t (ta, Checked) ts))] @ snd t\<Gamma>2)"
      using ttsplit_triv_def ttyping_case by blast
    ultimately show "\<Xi>, \<xi>, \<gamma>, [], \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Case x t m n) \<Down>! (\<sigma>', v)"
      using u_sem_case_nm.hyps
    proof (intro u_tt_sem_pres_case_nm)
      show "\<Xi>, \<xi>, \<gamma>, [], t\<Gamma>1, TSum ts T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>'', USum t' v' rs)"
        using u_sem_case_nm.hyps(2) matches1 u_sem_case_nm.prems ttyping_case by simp
    next
      have "\<Xi>, [], snd t\<Gamma>1 \<turnstile> x : TSum ts"
        by (simp add: ttyping_imp_typing ttyping_case)
      then obtain r1' w1'
        where usum_rs_under_\<sigma>'': "\<Xi>, \<sigma>'' \<turnstile> USum t' v' rs :u TSum ts \<langle>r1', w1'\<rangle>"
          and r1'_sub: "r1' \<subseteq> r1"
          and frame1: "frame \<sigma> w1 \<sigma>'' w1'"
        using preservation(1)[where \<tau>s=Nil, simplified] u_sem_case_nm.prems(2,4) matches1 u_sem_case_nm.hyps(1)
        by blast

      show "\<Xi>, \<xi>, USum t' v' rs # \<gamma>, [], t\<Gamma>4, \<tau> T\<turnstile> (\<sigma>'', n) \<Down>! (\<sigma>', v)"
        using u_sem_case_nm.prems ttyping_case
      proof (intro u_sem_case_nm.hyps(5))
        show "\<Xi>, \<sigma>'' \<turnstile> USum t' v' rs # \<gamma> matches snd t\<Gamma>4 \<langle>r1' \<union> r2, w1' \<union> w2\<rangle>"
          using frame1 frame_noalias_matches_ptrs matches2  w1_2_disjoint w1_r2_noalias
        proof (simp add: t\<Gamma>4_is, intro matches_ptrs_some)
          show "\<Xi>, \<sigma>'' \<turnstile> USum t' v' rs :u TSum (tagged_list_update t (ta, Checked) ts) \<langle>r1', w1'\<rangle>"
            by (simp add: sum_downcast_u ttyping_case u_sem_case_nm.hyps(3) usum_rs_under_\<sigma>'')
        next
          show "\<Xi>, \<sigma>'' \<turnstile> \<gamma> matches snd t\<Gamma>2 \<langle>r2, w2\<rangle>"
            using frame1 matches2 matches_ptrs_frame w1_2_disjoint w1_r2_noalias by blast
        next
          show "w2 \<inter> r1' = {}"
            using r1'_sub w2_r1_noalias by blast
        qed blast+
      qed simp+
    qed simp+
  qed (simp add: composite_anormal_expr_def)
next
  case (u_sem_take \<xi> \<gamma> \<sigma> x \<sigma>'' p r' fs f e)

  show ?case
    using u_sem_take.prems(1)
  proof (cases rule: ttyping.cases)
    case (ttyping_take ijs t\<Gamma>3 t ts n taken s t\<Gamma>4 k)

    obtain \<Gamma>1 \<Gamma>2
      where "[] \<turnstile> snd \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
        and snd_t\<Gamma>3_is: "snd t\<Gamma>3 = [] @ \<Gamma>1"
        and snd_t\<Gamma>4_is: "snd t\<Gamma>4 = [Some t, Some (TRecord (ts[f := (n, t, taken)]) s)] @ \<Gamma>2"
      using ttsplit_imp_split ttyping_take by blast
    moreover then obtain r1 w1 r2 w2
      where matches1: "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>1 \<langle>r1, w1\<rangle>"
        and matches2: "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>2 \<langle>r2, w2\<rangle>"
        and r_as_un: "r = r1 \<union> r2"
        and w_as_un: "w = w1 \<union> w2"
        and w1_w2_disjoint: "w1 \<inter> w2 = {}"
      using matches_ptrs_split' u_sem_take.prems(3) by blast
    moreover then have
      w1_r2_noalias: "w1 \<inter> r2 = {}"
      and w2_r1_noalias: "w2 \<inter> r1 = {}"
      using matches_ptrs_noalias u_sem_take.prems(3) by blast+

    have "\<Xi>, [], \<Gamma>1 \<turnstile> x : TRecord ts s"
      using snd_t\<Gamma>3_is ttyping_imp_typing ttyping_take by fastforce
    then obtain r1' w1'
      where uptr_p_under_\<sigma>'': "\<Xi>, \<sigma>'' \<turnstile> UPtr p r' :u TRecord ts s \<langle>r1', w1'\<rangle>"
        and r1'_sub: "r1' \<subseteq> r1"
        and frame1: "frame \<sigma> w1 \<sigma>'' w1'"
      using preservation(1)[where \<tau>s=Nil, simplified]
        u_sem_take.prems(2,4) matches1 u_sem_take.hyps(1)
      by blast

    have matches2_under_\<sigma>'': "\<Xi>, \<sigma>'' \<turnstile> \<gamma> matches \<Gamma>2 \<langle>r2, w2\<rangle>"
      using matches2 frame1 matches_ptrs_frame w1_w2_disjoint w1_r2_noalias
      by blast

    obtain w1'' ptrl
      where uptr_p_elim_lemmas:
        "w1' = insert p w1''"
        "\<Xi>, \<sigma>'' \<turnstile>* fs :ur ts \<langle>r1', w1''\<rangle>"
        "\<sigma>'' p = Some (URecord fs)"
        "r' = RRecord (map (\<lambda> (n,t,_). (n, type_repr t)) ts)"
        "distinct (map fst ts)"
        "s = Boxed Writable ptrl"
        "p \<notin> w1''"
        "p \<notin> r1'"
      using uptr_p_under_\<sigma>'' ttyping_take u_sem_take.hyps
      by auto

    then obtain rf wf r1a w1a
      where ut_fs_at_f: "\<Xi>, \<sigma>'' \<turnstile> fst (fs ! f) :u t \<langle>rf, wf\<rangle>"
        and ut_fs_taken_f: "\<Xi>, \<sigma>'' \<turnstile>* fs :ur ts[f := (n, t, Taken)] \<langle>r1a, w1a\<rangle>"
        and r1'_is: "r1' = rf \<union> r1a"
        and w1''_is: "w1'' = wf \<union> w1a"
        and "wf \<inter> w1a = {}"
      using uval_typing_record_take u_t_p_rec_w ttyping_take
      by (blast dest!: kinding_to_wellformedD)

    have disjointness_lemmas:
      "({p} \<union> wf \<union> w1a) \<inter> w2 = {}"
      "({p} \<union> wf \<union> w1a) \<inter> r2 = {}"
      "(rf \<union> r1a) \<inter> (wf \<union> w1a) = {}"
      "{p} \<inter> (wf \<union> w1a) = {}"
      "{p} \<inter> (rf \<union> r1a) = {}"
      "wf \<inter> w1a = {}"
      "w2 \<inter> (rf \<union> r1a) = {}"
      using frame_noalias_matches_ptrs(1)[OF frame1 matches2 w1_w2_disjoint]
        frame_noalias_matches_ptrs(2)[OF frame1 matches2 w1_r2_noalias]
        r1'_is  w1''_is uptr_p_elim_lemmas
            apply (force+)[2]
      using uptr_p_elim_lemmas uval_typing_pointers_noalias(2) r1'_is  w1''_is
          apply metis
      using uptr_p_elim_lemmas u_t_p_rec_w w1''_is r1'_is
         apply (blast+)[2]
      using \<open>wf \<inter> w1a = {}\<close>
       apply assumption
      using r1'_is r1'_sub w2_r1_noalias
      apply blast
      done

    have "\<Xi>, \<xi>, fst (fs ! f) # UPtr p r' # \<gamma>, [], t\<Gamma>4, \<tau> T\<turnstile> (\<sigma>'', e) \<Down>! (\<sigma>', v)"
    proof (cases taken)
      case Taken

      show ?thesis
        using u_sem_take.prems ttyping_take
      proof (intro u_sem_take.hyps(5))
        show "\<Xi>, \<sigma>'' \<turnstile> fst (fs ! f) # UPtr p r' # \<gamma> matches snd t\<Gamma>4 \<langle>rf \<union> (r1a \<union> r2), wf \<union> (insert p w1a \<union> w2)\<rangle>"
          using ut_fs_at_f matches2_under_\<sigma>'' disjointness_lemmas
        proof (simp only: snd_t\<Gamma>4_is append_Cons append.left_neutral, intro matches_ptrs_some[OF _ matches_ptrs_some])
          have "\<Xi>, \<sigma>'' \<turnstile>* fs :ur ts[f := (n, t, taken)] \<langle>r1a, w1a\<rangle>"
            by (simp add: ut_fs_taken_f Taken)
          moreover have "r' = RRecord (map (\<lambda> (n,t,_). (n, type_repr t)) (ts[f := (n, t, taken)]))"
            using Taken type_repr_uval_repr uptr_p_elim_lemmas ut_fs_taken_f            
            by metis
          ultimately show "\<Xi>, \<sigma>'' \<turnstile> UPtr p r' :u TRecord (ts[f := (n, t, taken)]) s \<langle>r1a, insert p w1a\<rangle>"
            using uptr_p_elim_lemmas ut_fs_taken_f r1'_is w1''_is
            by (simp, intro u_t_p_rec_w';
                fastforce
                simp add: uptr_p_elim_lemmas ttyping_take map_update
                intro!: distinct_list_update)
        qed fast+
      qed simp+
    next
      case Present
      then have wf_empty: "wf = {}"
        using shareable_not_writable(1) ut_fs_at_f ttyping_take
        by blast

      show ?thesis
        using u_sem_take.prems ttyping_take
      proof (intro u_sem_take.hyps(5))
        show "\<Xi>, \<sigma>'' \<turnstile> fst (fs ! f) # UPtr p r' # \<gamma> matches snd t\<Gamma>4 \<langle>rf \<union> ((rf \<union> r1a) \<union> r2), {} \<union> (insert p w1a \<union> w2)\<rangle>"
          using ut_fs_at_f matches2_under_\<sigma>'' disjointness_lemmas wf_empty
        proof (simp only: snd_t\<Gamma>4_is append_Cons append.left_neutral, intro matches_ptrs_some[OF _ matches_ptrs_some])
          have "ts[f := (n, t, Present)] = ts"
            by (simp add: list_helper ttyping_take)
          thus "\<Xi>, \<sigma>'' \<turnstile> UPtr p r' :u TRecord (ts[f := (n, t, taken)]) s \<langle>rf \<union> r1a, insert p w1a\<rangle>"
            using uptr_p_elim_lemmas wf_empty r1'_is uptr_p_under_\<sigma>'' w1''_is Present by auto
        qed fast+
      qed simp+
    qed
    moreover have "\<Xi>, \<xi>, \<gamma>, [], t\<Gamma>3, TRecord ts s T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>'', UPtr p r')"
      using u_sem_take.hyps(2) u_sem_take.prems ttyping_take matches1 snd_t\<Gamma>3_is by auto
    ultimately show "\<Xi>, \<xi>, \<gamma>, [], \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Take x f e) \<Down>! (\<sigma>', v)"
      using ttyping_take uptr_p_elim_lemmas
      by (force intro!: u_tt_sem_pres_take)
  qed (simp add: composite_anormal_expr_def)
next
  case (u_sem_take_ub \<xi> \<gamma> \<sigma> x \<sigma>'' fs f e)
  show ?case using u_sem_take_ub.prems u_sem_take_ub.hyps(1,3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply clarsimp
    apply (rename_tac \<Gamma>a \<Gamma>b ijs \<Gamma>1a \<Gamma>1b t ts n taken s \<Gamma>2a TR\<Gamma>2b k)
    apply (frule ttsplit_imp_split)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (rename_tac \<Gamma>2b)
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (rename_tac r1 w1 r2 w2)
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_take_ub.hyps(1)]
        , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply clarsimp
    apply (rename_tac r1' w1')
    apply (erule u_t_recE, simp_all)
    apply (rename_tac tsa)
    apply (erule u_tt_sem_pres_take_ub)
     apply (rule u_sem_take_ub.hyps(2), simp+)[1]
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (frule kinding_to_wellformedD)
    apply (frule(1) uval_typing_record_take, force, simp)
    apply (elim conjE exE)
    apply (rename_tac r1a w1a r1b w1b)
    apply (frule(2) matches_ptrs_frame, blast)
    apply (simp, erule disjE)
     apply (clarsimp)
     apply (frule(2) shareable_not_writable(1))
     apply simp
     apply (erule(1) u_sem_take_ub.hyps)
      apply simp
      apply (case_tac taken)
       apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
               apply (simp)
              apply (fastforce intro!: u_t_struct simp add: map_update intro: distinct_list_update)
             apply fast
            apply (blast+)[6]
      apply (rule pointerset_helper_matches_ptrs)
        apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
                apply (simp)
               apply (force intro!: u_t_struct simp: list_helper)
              apply (blast+)[10]
    apply (rule u_sem_take_ub.hyps(4))
       apply simp
      apply simp
     defer
     apply simp

    apply simp
    apply (rule pointerset_helper_matches_ptrs)
      apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
              apply (simp+)[2]
             apply (fastforce intro!: u_t_struct simp add: map_update intro: distinct_list_update)
            apply auto[3]
         apply blast
        apply auto[1]
       apply (blast+)[2]
     apply (simp+)[2]
    done

next

  case u_sem_abs_app show ?case using u_sem_abs_app.prems u_sem_abs_app.hyps(5)
      UpdateSemantics.u_sem_abs_app[OF u_sem_abs_app.hyps(1, 3, 5)]
    apply -
    apply (rule u_tt_sem_pres_default, simp add: composite_anormal_expr_def)
      apply simp
     apply (auto dest: ttyping_imp_typing)
    done

next
  case u_sem_app show ?case using u_sem_app.prems u_sem_app.hyps(5)
      UpdateSemantics.u_sem_app[OF u_sem_app.hyps(1, 3, 5)]
    apply -
    apply (rule u_tt_sem_pres_default, simp add: composite_anormal_expr_def)
      apply simp
     apply (auto dest: ttyping_imp_typing)
    done
qed  (fastforce intro!: u_tt_sem_pres_default
               intro: u_sem_u_sem_all.intros ttyping_imp_typing
               simp: composite_anormal_expr_def
               )+ (* takes about 8s *)

lemma u_tt_sem_pres_imp_u_sem:
  "\<Xi>, \<xi>, \<gamma>, [], \<Gamma>, \<tau> T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', uv)
    \<Longrightarrow> \<xi>, \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', uv)"
  by (induct rule: u_tt_sem_pres.induct, auto intro: u_sem_u_sem_all.intros)

end

lemma split_type_wellformed:
  "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2 \<Longrightarrow> Some t \<in> set \<Gamma> \<Longrightarrow> K \<turnstile> t wellformed"
  by (auto simp add: split_def split_comp.simps in_set_conv_nth list_all3_conv_all_nth kinding_def)

lemma split_bang_type_wellformed:
  "split_bang K is \<Gamma> \<Gamma>1 \<Gamma>2 \<Longrightarrow> Some t \<in> set \<Gamma>
    \<Longrightarrow> Some t \<in> set \<Gamma>1 \<or> Some t \<in> set \<Gamma>2 \<or> K \<turnstile> t wellformed"
  apply (induct arbitrary: "is" rule: split_bang.induct)
   apply (auto elim!: split_bang_comp.cases split_comp.cases)
  done

lemma weakening_type_wellformed:
  "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>' \<Longrightarrow> Some t \<in> set \<Gamma> \<Longrightarrow> K \<turnstile> t wellformed"
  by (fastforce simp add: kinding_def weakening_def weakening_comp.simps in_set_conv_nth list_all2_conv_all_nth)

lemma typing_to_kinding_env:
  "\<Xi>, K, \<Gamma> \<turnstile> e : u \<Longrightarrow> Some t \<in> set \<Gamma>
    \<Longrightarrow> K \<turnstile> t wellformed"
  "\<Xi>, K, \<Gamma> \<turnstile>* es : us \<Longrightarrow> Some t \<in> set \<Gamma>
    \<Longrightarrow> K \<turnstile> t wellformed"
  by (induct rule: typing_typing_all.inducts,
    auto simp add: Cogent.empty_def
      dest: split_bang_type_wellformed weakening_type_wellformed split_type_wellformed)

lemma ttyping_type_wellformed:
  "\<lbrakk> \<Xi>, K, \<Gamma> T\<turnstile> x : \<tau> \<rbrakk>
    \<Longrightarrow> \<forall>t. Some t \<in> set (snd \<Gamma>) \<longrightarrow> K \<turnstile> t wellformed"
  by (induct rule: ttyping.induct,
    auto dest!: ttsplit_imp_split ttsplit_bang_imp_split_bang
      dest: split_bang_type_wellformed split_type_wellformed typing_to_kinding_env)

context update_sem begin

lemma matches_ptrs_replicate_None:
  "length \<gamma> = n \<Longrightarrow> \<Xi>, \<sigma>' \<turnstile> \<gamma> matches replicate n None \<langle>{}, {}\<rangle>"
  by (hypsubst_thin, induct \<gamma>, auto intro: matches_ptrs.intros)

lemma u_tt_sem_pres_type_wellformed:
  "\<lbrakk> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', x) \<rbrakk>
    \<Longrightarrow> \<forall>t. Some t \<in> set (snd \<Gamma>) \<longrightarrow> K \<turnstile> t wellformed"
  by (induct rule: u_tt_sem_pres.induct,
    auto dest!: ttsplit_imp_split ttsplit_bang_imp_split_bang
      dest: split_bang_type_wellformed split_type_wellformed typing_to_kinding_env)

lemma u_tt_sem_pres_type_wellformed2:
  "\<lbrakk> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', x) \<rbrakk>
    \<Longrightarrow> K \<turnstile>  \<tau> wellformed"
  by (induct rule: u_tt_sem_pres.induct,
    auto dest!: typing_to_wellformed)

lemma u_tt_sem_pres_preservation:
  "\<Xi>, \<xi>, \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> st \<Down>! st' \<Longrightarrow> K = [] \<Longrightarrow>
    proc_ctx_wellformed \<Xi> \<Longrightarrow> \<xi> matches-u \<Xi> \<Longrightarrow>
    \<exists>rs ws. \<Xi>, fst st' \<turnstile> snd st' :u \<tau> \<langle>rs, ws\<rangle>"
  apply (induct rule: u_tt_sem_pres.induct, simp_all)
  apply clarsimp
  apply (frule(4) preservation(1)[where \<tau>s=Nil and K=Nil, simplified])
  apply auto
  done

lemma u_tt_sem_pres_length:
  "\<Xi>, \<xi>, \<gamma>, [], \<Gamma>, \<tau> T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', x)
    \<Longrightarrow> length \<gamma> = length (snd \<Gamma>)"
  by (induct rule: u_tt_sem_pres.induct,
    auto simp: ttsplit_def ttsplit_inner_def
               ttsplit_bang_def ttsplit_inner_def
         dest: matches_ptrs_length)

lemma let_elaborate_u_tt_sem_pres:
  assumes
    "\<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', x)"
    "K = []"
    "proc_ctx_wellformed \<Xi>"
    "\<xi> matches-u \<Xi>"
  shows "\<Xi>, \<xi> , \<gamma>, K, (TyTrSplit (map (map_option (\<lambda>_. TSK_L)) (snd \<Gamma>)) [] (fst \<Gamma>)
    [Some \<tau>] TyTrLeaf, snd \<Gamma>), \<tau> T\<turnstile> (\<sigma>, Let a (Var 0)) \<Down>! (\<sigma>', x)"
  using assms
proof (intro u_tt_sem_pres_let[OF ttsplitI])
  show "ttsplit_inner K (map (map_option (\<lambda>_. TSK_L)) (snd \<Gamma>)) (snd \<Gamma>) (snd \<Gamma>) (replicate (length (snd \<Gamma>)) None)"
    unfolding ttsplit_inner_def
    using assms
    by (fastforce simp add: map2_mapL map_idI  map_replicate_const dest: nth_mem u_tt_sem_pres_type_wellformed)
next
  show "\<Xi>, \<xi>, x # \<gamma>, K, (TyTrLeaf, Some \<tau> # replicate (length (snd \<Gamma>)) None), \<tau> T\<turnstile> (\<sigma>', Var 0) \<Down>! (\<sigma>', x)"
    using assms
    apply (auto
        intro!: u_tt_sem_pres_default typing_var
        intro: u_sem_var[where \<gamma>="x # xs" and i=0 for x xs, simplified]
        dest: u_tt_sem_pres_type_wellformed2
        simp add: composite_anormal_expr_def empty_def weakening_def weakening_comp.simps
        list_all2_same kinding_iff_wellformed)
    apply (frule u_tt_sem_pres_preservation, (simp+)[3])
    apply (force dest: u_tt_sem_pres_length intro: matches_ptrs_some matches_ptrs_replicate_None)
    done
next
  show "list_all ((\<noteq>) (Some TSK_NS)) (map (map_option (\<lambda>_. TSK_L)) (snd \<Gamma>))"
    by (simp add: list_all_length, metis map_option_eq_Some type_split_op.distinct(9))
qed auto

end

(* TODO remove n.b. some things in c-refinement use this *)
lemmas forall_less_Suc_eq = All_less_Suc2

end
