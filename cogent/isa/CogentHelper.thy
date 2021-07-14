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

theory CogentHelper
  imports TypeTrackingTyping  Data  "ML_Old"
keywords "ML_quiet" :: thy_decl % "ML"
begin

(* Rewrite rules to get expressions in the assumptions *)

lemma typing_lit': "\<lbrakk> K \<turnstile> \<Gamma> consumed; t = lit_type l \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Lit l : TPrim t"
  by (simp only: typing_lit)

lemma typing_put':  "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                     ; \<Xi>, K, \<Gamma>1 \<turnstile> e : TRecord ts s
                     ; sigil_perm s \<noteq> Some ReadOnly
                     ; f < length ts
                     ; ts ! f = (n,t, taken)
                     ; K \<turnstile> t :\<kappa> k
                     ; D \<in> k \<or> taken = Taken
                     ; \<Xi>, K, \<Gamma>2 \<turnstile> e' : t
                     ; ts' = (ts [f := (n,t,Present)])
                     \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Put e f e' : TRecord ts' s"
  by (fastforce intro!: typing_put simp add: kinding_defs)

lemma typing_prim' : "\<lbrakk> prim_op_type oper = (ts,t)
                      ; ts' = map TPrim ts
                      ; \<Xi>, K, \<Gamma> \<turnstile>* args : ts'
                      \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Prim oper args : TPrim t"
  by (simp only: typing_prim)


lemma typing_con' : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile> x : t
                     ; (tag, t, Unchecked) \<in> set ts
                     ; K \<turnstile> TSum ts wellformed
                     ; ts = ts'
                     \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Con ts tag x : TSum ts'"
  by (simp add: typing_con)

lemma typing_struct': "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile>* es : ts
                       ; ns = map fst ts'
                       ; distinct ns
                       ; map (fst \<circ> snd) ts' = ts
                       ; list_all (\<lambda>p. snd (snd p) = Present) ts'
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Struct ns ts es : TRecord ts' Unboxed"
  by (force intro: typing_struct simp add: zip_eq_conv_sym replicate_eq_map_conv_nth list_all_length)

lemma typing_afun': "\<lbrakk> \<Xi> f = (ks, t, u)
                     ; list_all2 (kinding K) ts ks
                     ; t' = instantiate ts t
                     ; u' = instantiate ts u
                     ; ks \<turnstile> TFun t u wellformed
                     ; K \<turnstile> \<Gamma> consumed
                     \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> AFun f ts : TFun t' u'"
  by (simp only: typing_afun)

lemma typing_fun': "\<lbrakk> \<Xi>, K', (TT, [Some t]) T\<turnstile> f : u
                    ; list_all2 (kinding K) ts K'
                    ; t' = instantiate ts t
                    ; u' = instantiate ts u
                    ; K' \<turnstile> t wellformed
                    ; K \<turnstile> \<Gamma> consumed
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Fun f ts : TFun t' u'"
  by (auto simp only: typing_fun snd_conv dest: ttyping_imp_typing)

lemma typing_var_weak: "\<lbrakk> K \<turnstile> t :\<kappa> k
                        ; K \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i t
                        ; i < length \<Gamma>
                        \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Var i : t"
  (* weaker than typing_var - the kinding assumption lets
     us easily instantiate t *)
  by (simp only: typing_var)

lemma typing_all_empty': "\<Gamma> = empty n \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>* [] : []"
  by (simp only: typing_all_empty)

lemma typing_all_empty'':
  "set \<Gamma> \<subseteq> {None}
    \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>* [] : []"
  apply (rule typing_all_empty'[where n="length \<Gamma>"])
  apply (clarsimp simp: Cogent.empty_def list_eq_iff_nth_eq)
  apply (frule subsetD, erule nth_mem)
  apply simp
  done

lemma split_bang_bang' :"\<lbrakk> 0 \<in> is
                      ; x' = bang x
                      ; is' = pred ` (Set.remove 0 is)
                      ; split_bang K is' xs as bs
                      ; type_wellformed (length K) x
                      \<rbrakk>  \<Longrightarrow> split_bang K is (Some x # xs) (Some x' # as) (Some x # bs)"
  by (clarsimp intro!: split_bang_cons simp add: split_bang_comp.simps)

lemma type_wellformed_prettyI: "type_wellformed (length K) t \<Longrightarrow> K \<turnstile> t wellformed"
  by simp

definition
  type_ctx_wellformed :: "kind env \<Rightarrow> ctx \<Rightarrow> bool"
where
  "type_ctx_wellformed K \<Gamma> = (\<forall>t. Some t \<in> set \<Gamma> \<longrightarrow> K \<turnstile> t wellformed)"

(* TODO this seems redundant now / 2018.11.27 ~ v.jackson
definition ttsplit_weak :: "kind env \<Rightarrow> tree_ctx \<Rightarrow> type_split_op option list
        \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> bool"
where
  "ttsplit_weak K \<Gamma> sps xs \<Gamma>1 ys \<Gamma>2 =
    (\<exists>\<Gamma>b \<Gamma>1a \<Gamma>2a T1 T2. \<Gamma> = (TyTrSplit sps xs T1 ys T2, \<Gamma>b)
        \<and> \<Gamma>1 = (T1, xs @ \<Gamma>1a)
        \<and> \<Gamma>2 = (T2, ys @ \<Gamma>2a)
        \<and> (\<forall>i < length sps. sps ! i \<noteq> Some TSK_NS)
        \<and> ttsplit_inner K sps \<Gamma>b \<Gamma>1a \<Gamma>2a)"

lemma ttsplit_weak_lemma:
  "ttsplit_weak K \<Gamma> sps xs \<Gamma>1 ys \<Gamma>2
    \<Longrightarrow> type_ctx_wellformed K (snd \<Gamma>1)
    \<Longrightarrow> type_ctx_wellformed K (snd \<Gamma>2)
    \<Longrightarrow> ttsplit K \<Gamma> sps xs \<Gamma>1 ys \<Gamma>2"
  apply (clarsimp simp: ttsplit_def ttsplit_weak_def type_ctx_wellformed_def)
  apply (clarsimp simp add: ttsplit_inner_def)
  apply (clarsimp simp: ttsplit_inner_def in_set_conv_nth all_conj_distrib)
  apply (clarsimp simp: image_def Product_Type.split_def set_zip)
  apply (drule_tac x=y in spec)+
  apply clarsimp
  apply (drule_tac x=i in spec)+
  apply (clarsimp split: if_splits)
  done

lemma ttsplit_weakI:
  "ttsplit_inner K sps False \<Gamma>b \<Gamma>1 \<Gamma>2 \<Longrightarrow> xs' = xs @ \<Gamma>1 \<Longrightarrow> ys' = ys @ \<Gamma>2
    \<Longrightarrow> ttsplit_weak K (TyTrSplit sps xs T1 ys T2, \<Gamma>b) sps xs (T1, xs') ys (T2, ys')"
  by (simp add: ttsplit_weak_def)
*)

lemmas ttyping_type_ctx_wellformed = ttyping_type_wellformed[folded type_ctx_wellformed_def]

lemma ttsplit_triv_type_ctxt_wellformed:
  "ttsplit_triv \<Gamma> x \<Gamma>1 y \<Gamma>2
    \<Longrightarrow> type_ctx_wellformed K (snd \<Gamma>1) \<or> type_ctx_wellformed K (snd \<Gamma>2)
    \<Longrightarrow> type_ctx_wellformed K (snd \<Gamma>)"
  by (auto simp: ttsplit_triv_def type_ctx_wellformed_def)

lemma ttyping_case':  "\<lbrakk> ttsplit K \<Gamma> ijs [] \<Gamma>1 [] \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 T\<turnstile> x : TSum ts
                   ; (tag, t, Unchecked) \<in> set ts
                   ; ttsplit_triv \<Gamma>2 [Some t] \<Gamma>3 [Some (TSum (tagged_list_update tag (t, Checked) ts))] \<Gamma>4
                   ; \<Xi>, K, \<Gamma>3 T\<turnstile> a : u
                   ; \<Xi>, K, \<Gamma>4 T\<turnstile> b : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Case x tag a b : u"
  by (simp only: ttyping_case[rotated])

lemma ttyping_take': "\<lbrakk> ttsplit K \<Gamma> ijs [] \<Gamma>1 [Some t, Some (TRecord ts' s)] \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 T\<turnstile> e : TRecord ts s
                   ; sigil_perm s \<noteq> Some ReadOnly
                   ; f < length ts
                   ; ts ! f = (n, t, Present)
                   ; K \<turnstile> t :\<kappa> k
                   ; ts = ts'[f := (n, t, Present)] \<and> fst (ts' ! f) = n \<and> fst (snd (ts' ! f)) = t \<and> (S \<in> k \<or> snd (snd (ts' ! f)) = Taken)
                   ; \<Xi>, K, \<Gamma>2 T\<turnstile> e' : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Take e f e' : u"
  apply clarify
  apply (rule ttyping_take[rotated], assumption+)
  apply simp
  done

definition
  "duplicate_list xs = xs @ xs"

lemma replicate_numeral:
  "replicate (numeral (num.Bit0 n)) x = duplicate_list (replicate (numeral n) x)"
  "replicate (numeral (num.Bit1 n)) x = x # duplicate_list (replicate (numeral n) x)"
  "replicate (numeral num.One) x = [x]"
    apply (simp only: numeral_Bit0 replicate_add duplicate_list_def)
   apply (simp only: eval_nat_numeral(3) numeral_Bit0 replicate_Suc replicate_add duplicate_list_def)
  apply simp
  done

lemmas replicate_unfold = replicate_numeral replicate_Suc replicate_0 duplicate_list_def append.simps

abbreviation(input)
  "NoneT == (None :: Cogent.type option)"
abbreviation(input)
  "SomeT == (Some :: Cogent.type \<Rightarrow> _)"

lemma list_update_eq_id:
  "length xs = n \<Longrightarrow> (i < n \<Longrightarrow> xs ! i = x) \<Longrightarrow> xs [i := x] = xs"
  by (induct xs arbitrary: i n, auto split: nat.split)


lemma list_all2_record_kind_subty_cons_nodrop:
  assumes
    "snd (snd p1) = snd (snd p2)"
    "list_all2 (record_kind_subty K) fs1 fs2"
  shows "list_all2 (record_kind_subty K) (p1 # fs1) (p2 # fs2)"
  using assms
  by clarsimp

lemma list_all2_record_kind_subty_cons_drop:
  assumes
    "K \<turnstile> (fst (snd p1)) :\<kappa> k"
    "D \<in> k"
    "snd (snd p1) < snd (snd p2)"
    "list_all2 (record_kind_subty K) fs1 fs2"
  shows "list_all2 (record_kind_subty K) (p1 # fs1) (p2 # fs2)"
  using assms
  by (simp add: list_all2_cons supersumption(1))

ML \<open>

structure TTyping_Tactics = struct

fun REPEAT_SUBGOAL tac s0 =
  let fun repeat tac s = if Thm.nprems_of s < Thm.nprems_of s0 then Seq.succeed s else
                           case Seq.pull (tac s) of
                               NONE => Seq.succeed s
                             | SOME (s', ss) => Seq.maps (repeat tac) (Seq.cons s' ss)
  in repeat tac s0 end

(* the thms parameter is a list of kinding theorems generated by either the cogent compiler or
 * in typing_all_vars, one for each type (i.e. a `SOME t`) in the current context.
 *)
fun weakening_tac ctxt thms =
  let val kndnet = Tactic.build_net thms
   in REPEAT_DETERM 
      ((rtac @{thm weakening_cons} THEN' (
        (rtac @{thm weakening_comp.none})
        ORELSE'
        (rtac @{thm weakening_comp.drop} THEN' resolve_from_net_tac ctxt kndnet THEN' SOLVED' (simp_tac ctxt))
        ORELSE'
        (rtac @{thm weakening_comp.keep} THEN' rtac @{thm kinding_imp_wellformed} THEN' resolve_from_net_tac ctxt kndnet))
      ) 1)
    THEN (rtac @{thm weakening_nil} 1)
  end

fun cogent_guided_ttsplits_tac ctxt sz script =
  let fun mktac i [] =
            if i = sz then rtac @{thm ttsplit_innerI(5)} 1 else
            rtac @{thm ttsplit_innerI(1)} 1 THEN mktac (i+1) []
        | mktac i ((n, tacs)::script') =
            if i = n
            then EVERY (map (fn t => DETERM (t ctxt)) tacs) THEN
                 mktac (i+1) script'
            else rtac @{thm ttsplit_innerI(1)} 1 THEN
                 mktac (i+1) ((n, tacs)::script')
  in rtac @{thm ttsplitI} 1 THEN
       mktac 0 script THEN
       asm_full_simp_tac ctxt 1 THEN
       asm_full_simp_tac ctxt 1
  end


datatype tac = RTac of thm
             | SimpSolveTac of thm list * thm list
             | SimpTac of thm list * thm list
             | ForceTac of thm list
             | WeakeningTac of thm list
             | SplitsTac of tac list option list
             | SubtypingTac of tac list
             | BlackBoxTac of (Proof.context -> int -> tactic)


val simp_solve = SimpSolveTac ([], [])

val simp = SimpTac ([], [])

datatype hints = KindingTacs of tac list
  | TTSplitBangTacs of tac list
  | TypingTacs of tac list

exception HINTS of string * hints leaftree

fun kinding (Leaf (KindingTacs tac)) = tac
  | kinding hint_tree_bad = raise HINTS ("kinding", hint_tree_bad)

fun typing_hint (Leaf (TypingTacs tacs)) = tacs
  | typing_hint hint_tree_bad = raise HINTS ("typing", hint_tree_bad)

fun apply_split @{term "Some TSK_L"} hints t = ((t, NONE), hints)
  | apply_split @{term "Some TSK_S"} hints t = ((t, t), hints)
  | apply_split @{term "Some TSK_R"} hints t = ((NONE, t), hints)
  | apply_split @{term "Some TSK_NS"} hints t = let
    val (kindhint, hints) = (case hints of
                      kindhint :: hints => (kindhint, hints)
                    | _ => raise HINTS ("apply_split: no kind hint found", Branch hints))
    val tacs = kinding kindhint
    val thm = case tacs of [RTac thm] => thm
      | _ => raise HINTS ("apply_split: kindhint failed to create an RTac", kindhint)
  in ((SOME thm, t), hints) end
  | apply_split @{term "None :: type_split_op option"} hints NONE = ((NONE, NONE), hints)
  | apply_split t _ _ = raise TERM ("apply_split", [t])

fun apply_splits ((sp, t) :: sp_ts) hints = let
    val ((x, y), hints) = apply_split sp hints t
    val ((xs, ys), hints) = apply_splits sp_ts hints
  in (((x :: xs), (y :: ys)), hints) end
  | apply_splits [] hints = (([], []), hints)

fun interpret_tac (RTac r) _ = rtac r
  | interpret_tac (SimpTac (a, d)) ctxt = asm_full_simp_tac (ctxt addsimps a delsimps d)
  | interpret_tac (SimpSolveTac (a, d)) ctxt = SOLVED' (asm_full_simp_tac (ctxt addsimps a delsimps d))
  | interpret_tac (ForceTac a) ctxt = force_tac (ctxt addsimps a)
  | interpret_tac (WeakeningTac thms) ctxt = K (weakening_tac ctxt thms)
  | interpret_tac (SplitsTac tacs) ctxt = K (guided_splits_tac ctxt tacs)
  | interpret_tac (SubtypingTac tacs) ctxt = EVERY' (map (fn hint => interpret_tac hint ctxt) tacs)
  | interpret_tac (BlackBoxTac tac) ctxt = tac ctxt
and guided_splits_tac ctxt (SOME splt :: script) =
  rtac @{thm split_cons} 1
    THEN EVERY' (map (fn t => interpret_tac t ctxt) splt) 1
    THEN guided_splits_tac ctxt script
| guided_splits_tac ctxt (NONE :: []) =
  REPEAT_DETERM ((rtac @{thm split_cons} THEN' rtac @{thm split_comp.none}) 1) THEN rtac @{thm split_empty} 1
| guided_splits_tac ctxt (NONE :: script) =
  REPEAT_DETERM ((rtac @{thm split_cons} THEN' rtac @{thm split_comp.none}) 1)
    THEN guided_splits_tac ctxt script
| guided_splits_tac ctxt [] = rtac @{thm split_empty} 1

fun kind_proof_single (@{term SomeT} $ t) k ctxt hint = let
    val tac = (case hint of
            (KindingTacs tac) => tac
            | _ => raise ERROR ("kind_proof_single: not a kinding tac"))
    val t = betapplys (@{term "kinding"}, [k, t, (@{schematic_term "?k :: kind"})])
    val ct = Thm.cterm_of ctxt (@{term Trueprop} $ t)
    val rs = EVERY (map (fn t => interpret_tac t ctxt 1) tac) (Thm.trivial ct)
    val t = (case Seq.pull rs of
          NONE => raise TERM ("kind_proof_single: failed", [k, t])
        | SOME (t, _) => t)
    in SOME t end
  | kind_proof_single @{term NoneT} k ctxt hints = NONE
  | kind_proof_single _ _ _ _ = raise ERROR ("kind_proof_single: thm not a Some or a None")

fun kind_proofs ((@{term SomeT} $ t) :: ts) k ctxt hints = let
    val (hintshd, hints) = (case hints of
                        (hintshd :: hints) => (hintshd, hints)
                      | _ => raise HINTS  ("kind_proofs: not enough hints", Branch hints))
    val tacs = kinding hintshd
(*
    val _ = case tacs of
        [RTac thm] => Display.pretty_thm ctxt thm |> Pretty.writeln
      | _ => warning "unexpected kinding tacs"
*)
    val t = betapplys (@{term "kinding"}, [k, t, (@{schematic_term "?k :: kind"})])
    val ct = Thm.cterm_of ctxt (@{term Trueprop} $ t)
    val rs = EVERY (map (fn t => interpret_tac t ctxt 1) tacs) (Thm.trivial ct)
    val t = (case Seq.pull rs of
          NONE => raise TERM ("kind_proofs: failed", [k, t])
        | SOME (t, _) => t)
    val (ts, hints) = kind_proofs ts k ctxt hints
  in (SOME t :: ts, hints) end
  | kind_proofs (@{term NoneT} :: ts) k ctxt hints = let
    val (ts, hints) = kind_proofs ts k ctxt hints
  in (NONE :: ts, hints) end
  | kind_proofs [] _ _ hints = ([], hints)
  | kind_proofs ts _ _ _ = raise TERM ("kind_proofs", ts)

fun follow_tt (Const (@{const_name TyTrSplit}, _) $ sps $ x $ T1 $ y $ T2, ts) k ctxt hints = let
    val ((ts1, ts2), hints) = apply_splits (HOLogic.dest_list sps ~~ ts) hints
    val (x_proofs, hints) = kind_proofs (HOLogic.dest_list x) k ctxt hints
    val (y_proofs, hints) = kind_proofs (HOLogic.dest_list y) k ctxt hints
  in (((T1, x_proofs @ ts1), (T2, y_proofs @ ts2)), hints) end
  | follow_tt (tt, _) _ _ _ = raise TERM ("follow_tt", [tt])

fun ttsplit_inner (@{term "Some TSK_S"} :: tsks) (SOME p :: Gamma) ctxt =
    let
      val rest = ttsplit_inner tsks Gamma
    in resolve_tac ctxt @{thms ttsplit_innerI(4)}
      THEN' (simp_tac
        ((put_simpset HOL_basic_ss ctxt)
          addsimps @{thms list.map prod.case bang.simps bang_sigil.simps})) (* need to reduce the bangs *)
      THEN' (resolve_tac ctxt [p])
      THEN' (SOLVED' (simp_tac ctxt))
      THEN' rest ctxt
    end
  | ttsplit_inner (@{term "Some TSK_L"} :: tsks) (SOME p :: Gamma) ctxt =
    let
      val rest = ttsplit_inner tsks Gamma
    in resolve_tac ctxt @{thms ttsplit_innerI(3)}
      THEN' (simp_tac
        ((put_simpset HOL_basic_ss ctxt)
          addsimps @{thms list.map prod.case bang.simps bang_sigil.simps})) (* need to reduce the bangs *)
      THEN' (resolve_tac ctxt [p RS @{thm kinding_imp_wellformed}])
      THEN' rest ctxt
    end
  | ttsplit_inner (@{term "Some TSK_R"} :: tsks) (SOME p :: Gamma) ctxt =
    let
      val rest = ttsplit_inner tsks Gamma
    in resolve_tac ctxt @{thms ttsplit_innerI(2)}
      THEN' (simp_tac
        ((put_simpset HOL_basic_ss ctxt)
          addsimps @{thms list.map prod.case bang.simps bang_sigil.simps})) (* need to reduce the bangs *)
      THEN' (resolve_tac ctxt [p RS @{thm kinding_imp_wellformed}])
      THEN' rest ctxt
    end
  | ttsplit_inner (@{term "Some TSK_NS"} :: tsks) (SOME p :: Gamma) ctxt =
    let
      val rest = ttsplit_inner tsks Gamma
    in resolve_tac ctxt @{thms ttsplit_innerI(5)}
      THEN' (simp_tac
        ((put_simpset HOL_basic_ss ctxt)
          addsimps @{thms list.map prod.case bang.simps bang_sigil.simps})) (* need to reduce the bangs *)
      THEN' (resolve_tac ctxt [p RS @{thm kinding_imp_wellformed}])
      THEN' rest ctxt
    end
  | ttsplit_inner (@{term "None :: type_split_op option"} :: tsks) (NONE :: Gamma) ctxt =
    let
      val rest = ttsplit_inner tsks Gamma
    in resolve_tac ctxt @{thms ttsplit_innerI(1)}
      THEN' rest ctxt
    end
  | ttsplit_inner [] [] ctxt = resolve_tac ctxt @{thms ttsplit_innerI(6)}
  | ttsplit_inner tsks _ _ = raise TERM ("ttsplit_inner", tsks)

fun ttsplit (Const (@{const_name TyTrSplit}, _) $ sps $ _ $ _ $ _ $ _, Gamma) = let
    val inner = ttsplit_inner (HOLogic.dest_list sps) Gamma
  in [RTac @{thm ttsplitI}, BlackBoxTac inner, simp_solve, simp_solve, simp_solve] end
  | ttsplit (t, _) = raise TERM ("ttsplit", [t])

fun ttsplit_bang (Const (@{const_name TyTrSplit}, _) $ sps $ _ $ _ $ _ $ _, Gamma) = let
    val inner = ttsplit_inner (HOLogic.dest_list sps) Gamma
  in [RTac @{thm ttsplit_bangI}, simp_solve, simp_solve, SimpTac (@{thms set_eq_subset}, []), BlackBoxTac inner] end
  | ttsplit_bang (t, _) = raise TERM ("ttsplit", [t])

fun dest_nat (@{term Suc} $ n) = dest_nat n + 1
  | dest_nat (@{term "0 :: nat"}) = 0
  | dest_nat n = HOLogic.dest_number n |> snd

fun dest_all_vars' (Const (@{const_name Var}, _) $ i :: vs)
    = (dest_nat i :: dest_all_vars' vs)
  | dest_all_vars' [] = []
  | dest_all_vars' ts = raise TERM ("dest_all_vars", ts)

val dest_all_vars = try (dest_all_vars' o HOLogic.dest_list)

fun the_G _ (SOME p) = p
  | the_G G NONE = raise THM ("the_G", 1, (map (fn NONE => @{thm TrueI} | SOME t => t) G))

fun typing_all_vars _ _ [] = let
  in [RTac @{thm typing_all_empty''}, simp_solve] end
  | typing_all_vars ctxt G (ix :: ixs) = let
    fun null (NONE : thm option) = true
      | null _ = false
    fun step (i, p) = RTac @{thm split_cons} :: (if member (op =) ixs i
      then (if i = ix then [RTac @{thm split_comp.share}, simp, RTac (the_G G p), simp_solve]
          else [RTac @{thm split_comp.right}, simp_solve])
      else (if null p then [RTac @{thm split_comp.none}]
          else [RTac @{thm split_comp.left}, simp_solve]))
    fun split_lr (i, p) =
      (if member (op =) ixs i
      then
        (if i = ix
        then (p,p)  (* share *)
        else (NONE,p)) (* right *)
      else (p,NONE) (* both none and left case *))
    val enumG = (0 upto (length G - 1) ~~ G)
    val steps = maps step enumG
    val (Gl, Gr) = map split_lr enumG |> split_list
    val thms = map_filter I Gl |> nubBy Thm.prop_of
    val rest = typing_all_vars ctxt Gr ixs
  in [RTac @{thm typing_all_cons}] @ steps @ [RTac @{thm split_empty},
    RTac @{thm typing_var_weak[unfolded singleton_def Cogent.empty_def]},
      RTac (the_G G (nth G ix)), simp, WeakeningTac thms, simp_solve] @ rest end

fun typing (Const (@{const_name Var}, _) $ i) G _ hints = let
    val i = dest_nat i
    val thm = the_G G (nth G i)
    val thms = map_filter I G |> nubBy Thm.prop_of
    val _ = (case typing_hint hints of
               [] => ()
             | _ => raise HINTS ("too many tacs", hints))
  in ([RTac @{thm typing_var_weak[unfolded singleton_def Cogent.empty_def]},
                RTac thm, simp, WeakeningTac thms, simp_solve]) end
  | typing (Const (@{const_name Struct}, _) $ _ $ _ $ xs) G ctxt hints
  = (case dest_all_vars xs of SOME ixs => let
      val _ = (case typing_hint hints of
                 [] => ()
               | _ => raise HINTS ("too many tacs", hints))
  in ([RTac @{thm typing_struct'}] @ typing_all_vars ctxt G ixs @ [simp_solve, simp_solve, simp_solve, simp_solve]) end
    | NONE => typing_hint hints)
  | typing (Const (@{const_name Prim}, _) $ _ $ xs) G ctxt hints
  = (case dest_all_vars xs of SOME ixs => let
    val _ = (case typing_hint hints of
               [] => ()
             | _ => raise HINTS ("too many tacs", hints))
  in ([RTac @{thm typing_prim'}, simp_solve, simp_solve] @ typing_all_vars ctxt G ixs) end
    | NONE => typing_hint hints)
  | typing _ _ _ hints = let
    in typing_hint hints end



fun ttyping (Const (@{const_name Split}, a) $ x $ y) tt k ctxt hint_tree : (tac*term) list = let
    val (splithints, typxhint, typyhint) = (case hint_tree of
        Branch [Branch splithints, typxhint, typyhint] => (splithints, typxhint, typyhint)
      | Leaf (TypingTacs _) => raise HINTS ("ttyping(Const): expected ttyping rule, got typing rule", hint_tree)
      | _ => raise HINTS ("ttyping(Const): hints in incorrect form", hint_tree))
    val ((ltt, rtt), splithints) = follow_tt tt k ctxt splithints
    val _ = (case splithints of [] => () | _ => raise HINTS ("ttyping(Const): hints not exhausted", hint_tree))
    val split_tac = ttsplit tt
    val l_tac = ttyping x ltt k ctxt typxhint
    val r_tac = ttyping y rtt k ctxt typyhint
    val term  = (Const (@{const_name Split}, a) $ x $ y)
  in
    ([(RTac @{thm ttyping_split}, term)] @ (map (fn a => (a,term)) split_tac) @ l_tac @ r_tac)
  end
  | ttyping (Const (@{const_name Let}, a) $ x $ y) tt k ctxt hint_tree = let
    val (splithints, typxhint, typyhint) = (case hint_tree of
        Branch [Branch splithints, typxhint, typyhint] => (splithints, typxhint, typyhint)
      | Leaf (TypingTacs _) => raise HINTS ("ttyping(Let): expected ttyping rule, got typing rule", hint_tree)
      | _ => raise HINTS  ("ttyping(Let): hints in incorrect form", hint_tree))
    val ((ltt, rtt), splithints) = follow_tt tt k ctxt splithints
    val _ = (case splithints of [] => () | _ => raise HINTS ("ttyping(Let): hints not exhausted", hint_tree))
    val split_tac = ttsplit tt
    val (l_tac) = ttyping x ltt k ctxt typxhint
    val (r_tac) = ttyping y rtt k ctxt typyhint
    val term  = (Const (@{const_name Let}, a) $ x $ y)
  in
    ([(RTac @{thm ttyping_let},term)] @ (map (fn a => (a,term)) split_tac) @ l_tac @ r_tac)
  end
  | ttyping (Const (@{const_name LetBang}, a) $ b $ x $ y) tt k ctxt hint_tree = let
    val (splitbanghints, splithints, typxhint, typyhint, kindhint) = (case hint_tree of
        Branch [Branch splitbanghints, Branch splithints, typxhint, typyhint, kindhint] =>
               (splitbanghints, splithints, typxhint, typyhint, kindhint)
      | Leaf (TypingTacs _) => raise HINTS ("ttyping(LetBang): expected ttyping rule, got typing rule", hint_tree)
      | _ => raise HINTS  ("ttyping(LetBang): hints in incorrect form", hint_tree))
    val ((ltt, rtt), splithints) = follow_tt tt k ctxt (append splitbanghints splithints)
    val _ = (case splithints of [] => () | _ => raise HINTS ("ttyping(LetBang): hints not exhausted", hint_tree))
    val tsb_tac = ttsplit_bang tt
    val x_tac = ttyping x ltt k ctxt typxhint
    val y_tac = ttyping y rtt k ctxt typyhint
    val k_tac = kinding kindhint
    val term  = (Const (@{const_name LetBang}, a) $ b $ x $ y)
  in
    ([(RTac @{thm ttyping_letb}, term)] @ (map (fn a => (a,term)) tsb_tac) @ x_tac @ y_tac
    @ (map (fn a => (a,term)) k_tac) @ [(simp_solve, term)])
  end
  | ttyping (Const (@{const_name Cogent.If}, a) $ c $ x $ y) tt k ctxt hint_tree = let
    val (typxhint, splithints, typahint, typbhint) = (case hint_tree of
        Branch [typxhint, Branch splithints, typahint, typbhint] =>
               (typxhint, splithints, typahint, typbhint)
      | Leaf (TypingTacs _) => raise HINTS ("ttyping(If): expected ttyping rule, got typing rule", hint_tree)
      | _ => raise HINTS  ("ttyping(If): hints in incorrect form", hint_tree))
    val ((condtt, casestt), splithints) = follow_tt tt k ctxt splithints
    (* The tt tree is generated with an additional split here.
       Technically it should be unnecessary, but would require changing how things work ~ v.jackson / 2018.09.19 *)
    val ((x_tt, y_tt), splithints) = follow_tt casestt k ctxt splithints
    val _ = (case splithints of [] => () | _ => raise HINTS ("ttyping(If): hints not exhausted", hint_tree))
    val split_tac = ttsplit tt
    val c_tac = ttyping c condtt k ctxt typxhint
    val x_tac = ttyping x x_tt k ctxt typahint
    val y_tac = ttyping y y_tt k ctxt typbhint
    val term  = (Const (@{const_name Cogent.If}, a) $ c $ x $ y)
  in
    ([(RTac @{thm ttyping_if}, term)] @ (map (fn a => (a,term)) split_tac)
    @ [(simp,term), (RTac @{thm ttsplit_trivI}, term), (simp_solve, term), (simp_solve,term)]
    @ c_tac @ x_tac @ y_tac)
  end
  | ttyping (Const (@{const_name Case}, a) $ x $ b $ m $ nm) tt k ctxt hint_tree = let
    val (typxhint, splithints, typahint, typbhint) = (case hint_tree of
        Branch [typxhint, Branch splithints, typahint, typbhint] =>
               (typxhint, splithints, typahint, typbhint)
      | Leaf (TypingTacs _) => raise HINTS ("ttyping(Case): expected ttyping rule, got typing rule", hint_tree)
      | _ => raise HINTS  ("ttyping(Case): hints in incorrect form", hint_tree))
    val ((ltt, rtt), splithints) = follow_tt tt k ctxt splithints
    val x_tac = ttyping x ltt k ctxt typxhint
    val ((m_tt, nm_tt), splithints) = follow_tt rtt k ctxt splithints
    val _ = (case splithints of [] => () | _ => raise HINTS ("ttyping(Case): hints not exhausted", hint_tree))
    val split_tac = ttsplit tt
    val m_tac = ttyping m m_tt k ctxt typahint
    val nm_tac = ttyping nm nm_tt k ctxt typbhint
    val term   = (Const (@{const_name Case}, a) $ x $ b $ m $ nm)
  in
    ([(RTac @{thm ttyping_case'}, term)] @ (map (fn a => (a,term)) split_tac) @ x_tac @ [(simp_solve, term)]
    @ [(simp,term), (RTac @{thm ttsplit_trivI},term), (simp_solve,term), (simp_solve,term)] @ m_tac @ nm_tac)
  end
  | ttyping (Const (@{const_name Take}, a) $ x $ b $ y) tt k ctxt hint_tree = let
    val (splithints, typehint, kindhint, type'hint) = (case hint_tree of
        Branch [Branch splithints, typehint, kindhint, type'hint] =>
               (splithints, typehint, kindhint, type'hint)
      | Leaf (TypingTacs _) => raise HINTS ("ttyping(Take): expected ttyping rule, got typing rule", hint_tree)
      | _ => raise HINTS  ("ttyping(Take): hints in incorrect form", hint_tree))
    val ((ltt, rtt), splithints) = follow_tt tt k ctxt splithints
    val _ = (case splithints of [] => () | _ => raise HINTS ("ttyping(Take): hints not exhausted", hint_tree))
    val split_tac = ttsplit tt
    val x_tac = ttyping x ltt k ctxt typehint
    val k_tac = kinding kindhint
    val y_tac = ttyping y rtt k ctxt type'hint
    val term  = (Const (@{const_name Take}, a) $ x $ b $ y)
  in
    ([(RTac @{thm ttyping_take'}, term)] @ (map (fn a => (a,term)) split_tac) @ x_tac
    @ [(simp_solve,term), (simp_solve,term), (simp_solve,term)] @ (map (fn a => (a,term)) k_tac)
    @ [(simp_solve,term)] @ y_tac)
  end
  | ttyping x (@{term TyTrLeaf}, G) _ ctxt hint_tree = let
    val ty_tac = typing x G ctxt hint_tree
  in
    ([(RTac @{thm ttyping_default},x), (SimpTac (@{thms composite_anormal_expr_def}, []),x)]
      @ (map (fn a => (a,x)) ty_tac))
  end
  | ttyping t _ _ _ _ = raise TERM ("ttyping", [t])

fun mk_ttsplit_tacs nm k ctxt hint_tree = let
    (* construct a simpset that knows about the definitions we find in a ttyping *)
    val ss = put_simpset HOL_basic_ss ctxt
        addsimps @{thms replicate_unfold}
        addsimps (Proof_Context.get_thms ctxt "abbreviated_type_defs")
    (* get the definitions we care about for our function *)
    val body_def = Proof_Context.get_thm ctxt (nm ^ "_def")
    val ty_def = Proof_Context.get_thm ctxt (nm ^ "_type_def")
    val tt_def = Proof_Context.get_thm ctxt (nm ^ "_typetree_def")
    (* simplify, then extract the actual definitions (i.e. the right part of the definition) *)
    val body = body_def |> simplify ss |> safe_mk_meta_eq |> Thm.concl_of |> Logic.dest_equals |> snd
    val tt   = tt_def |> simplify ss |> safe_mk_meta_eq |> Thm.concl_of |> Logic.dest_equals |> snd
    val ty   = ty_def |> simplify ss |> safe_mk_meta_eq |> Thm.concl_of |> Logic.dest_equals |> snd
    (* the unsimplified definition of the typetree *)
    val ity  = ty |> HOLogic.dest_prod |> snd |> HOLogic.dest_prod |> fst
    (* get the first kinding hint *)
    val (kinding_hint, hint_tree) = (case hint_tree of
                                                Branch [Leaf kindh, ttyph] => (kindh, ttyph)
                                              | _ => raise HINTS ("mk_ttsplit_tac: hints don't start with a kinding", hint_tree))
    val ps = kind_proof_single (@{term SomeT} $ ity) k ctxt kinding_hint
    (* generate the tactics *)
    val tacs = (ttyping body (tt, [ps]) k ctxt hint_tree)
  in tacs end

fun tacName (RTac _) = "RTac"
  | tacName (SimpSolveTac _) = "SimpSolveTac"
  | tacName (SimpTac _)      = "SimpTac"
  | tacName (ForceTac _)     = "ForceTac"
  | tacName (WeakeningTac _) = "WeakeningTac"
  | tacName (SplitsTac _) = "SplitsTac"
  | tacName (SubtypingTac _) = "SubtypingTac"
  | tacName (BlackBoxTac _) = "BlackBoxTac"


(* Match the patterns that ttyping finds *)
fun termName (Const (@{const_name AFun}, _) $ _ $ _)          = "AFun"
  | termName (Const (@{const_name Fun}, _) $ _ $ _)           = "Fun"
  | termName (Const (@{const_name Prim}, _) $ _ $ _)          = "Prim"
  | termName (Const (@{const_name App}, _) $ _ $ _)           = "App"
  | termName (Const (@{const_name Con}, _) $ _ $ _ $ _)       = "Con"
  | termName (Const (@{const_name Struct}, _) $ _ $ _ $ _)    = "Struct"
  | termName (Const (@{const_name Member}, _) $ _ $ _)        = "Member"
  | termName (Const (@{const_name Unit}, _))                  = "App"
  | termName (Const (@{const_name Lit}, _) $ _)               = "Lit"
  | termName (Const (@{const_name SLit}, _) $ _)              = "SLit"
  | termName (Const (@{const_name Cast}, _) $ _ $ _)          = "Cast"
  | termName (Const (@{const_name Tuple}, _) $ _ $ _)         = "Tuple"
  | termName (Const (@{const_name Put}, _) $ _ $ _ $ _)       = "Put"
  | termName (Const (@{const_name Let}, _) $ _ $ _)           = "Let"
  | termName (Const (@{const_name LetBang}, _) $ _ $ _ $ _)   = "LetBang"
  | termName (Const (@{const_name Case}, _) $ _ $ _ $ _ $ _)  = "Case"
  | termName (Const (@{const_name Esac}, _) $ _ $ _)          = "Esac"
  | termName (Const (@{const_name If}, _) $ _ $ _ $ _)        = "If"
  | termName (Const (@{const_name Take}, _) $ _ $ _ $ _)      = "Take"
  | termName (Const (@{const_name Split}, _) $ _ $ _)         = "Split"
  | termName (Const (@{const_name Promote}, _) $ _ $ _)       = "Promote"
  | termName _ = "Unknown"

fun mk_ttsplit_tacs_final nm k ctxt hint_tree
    = map (fn (tac, _) => (tac, interpret_tac tac)) (mk_ttsplit_tacs nm k ctxt hint_tree)


(* The same as mk_ttsplit_tacs_final, but it logs the timing of tactics *)
fun mk_ttsplit_tacs_timing_debug nm k ctxt hint_tree
    = let
        val runTac = fn term => fn tac => fn a => fn b => fn c =>
                              logTacticOnUse (tacName tac ^ ":" ^ termName term) 
                                     (fn () => (interpret_tac tac) a b c)
      in
        map (fn (tac,term) => (tac, runTac term tac)) (mk_ttsplit_tacs nm k ctxt hint_tree)
      end

fun apply_ttsplit_tacs_simple nm ctxt hints
    = mk_ttsplit_tacs_final nm @{term "[] :: kind env"} ctxt hints
    |> map (fn (_, t) => DETERM (t ctxt 1))
    |> EVERY

fun tactic_debug_tac ctxt tacs = let
  fun inner i (tac :: tacs) t = (case Seq.pull (tac ctxt t)
    of SOME (t', _) => (inner (i + 1) tacs t')
     | NONE => (tracing (string_of_int i) ; Seq.empty))
     | inner _ [] t = Seq.single t
in inner 0 tacs end

end (* end TTyping_Tactics *)
\<close>

ML \<open>
val _ =
  Outer_Syntax.command @{command_keyword "ML_quiet"} "ML text within theory or local theory"
    (Parse.ML_source >> (fn source =>
      Toplevel.generic_theory
        (ML_Context.exec (fn () =>
            ML_Context.eval_source (ML_Compiler.verbose false ML_Compiler.flags) source) #>
          Local_Theory.propagate_ml_env)));
\<close>

end
