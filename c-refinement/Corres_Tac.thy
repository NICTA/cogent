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

theory Corres_Tac
imports
  "Cogent_Corres"
  "Cogent.ProofTrace"
  "Cogent.CogentHelper"
  "Cogent.ML_Old"
  Value_Relation_Generation
begin

(*
 * Fix Cogent/C mismatch caused by unused return values of C blocks.
 * Cogent code can bind a value without using it. This commonly appears in code like
 *
 *   -- first, a message from our sponsors
 *   let debug_output = stuff
 *   and _ = _debug_print debug_output
 *   -- now back to our regularly scheduled programming
 *   ...
 *
 * where debug_output becomes unused because the call to _debug_print is stripped for verification.
 *
 * When AutoCorres comes across this code, it figures that debug_output is unused,
 * so its generated code for "stuff" appends "gets (\<lambda>_. ())".
 * This breaks Corres_Tac's expectation that the C code for "stuff" returns a value that
 * corresponds to the Cogent code.
 *
 * We fix that up by walking the AutoCorres output and removing the extra "gets (\<lambda>_. ())",
 * allowing the original return value of "stuff" to be propagated.
 * The most annoying bit is that the last statement of a monad block is the most deeply nested.
 * So our rules need to iterate through pairs of consecutive statements in the same manner
 * as @{term simp_last_bind}. The other annoying bit is that we need to change the return type
 * from unit to the corresponding type (e.g. of debug_output).
 * We use a stack of schematic variables to remember where to apply the type changes.
 *
 * This could also be fixed directly in AutoCorres, assuming someone remembers how l2 works...
 *)

definition "cogent_C_unused_return__internal X Y \<equiv> X = (do Y; return () od)"

lemma cogent_C_unused_return_step:
  "\<And>A A' B B'. A = A' \<Longrightarrow> B = B' \<Longrightarrow> A >>= K_bind B = A' >>= K_bind B'"
  "\<And>A A' B B'. A = A' \<Longrightarrow> (\<And>v. B v = B' v) \<Longrightarrow> A >>= B = A' >>= B'"
  by meson+

(* This should be the only interesting statement block.
 * For Let and LetBang codegen, C always returns true and R is unused,
 * so we don't care what the rules do to it. *)
lemma cogent_C_unused_return_L:
  "\<lbrakk> L = L';
     cogent_C_unused_return__internal (L' :: ('s, unit) nondet_monad) (L'' :: ('s, 'a) nondet_monad);
     X = X' \<rbrakk> \<Longrightarrow>
   (do (_ :: unit) \<leftarrow> condition C L R; X od)
    =
   (do (_ :: 'a) \<leftarrow> condition C L'' (do R; return undefined od); X' od)"
  apply (simp add: cogent_C_unused_return__internal_def)
  (* goal assumptions cause normal monad_eq to loop *)
  apply (tactic \<open> simp_tac (@{context} addsimps (MonadEqThms.get @{context})) 1 \<close>)
  apply blast
  done

lemma cogent_C_unused_return__internal:
  "\<And>A. cogent_C_unused_return__internal (do v \<leftarrow> A; gets (\<lambda>_. ()) od) A"
  "\<And>A A' B B'. \<lbrakk> A = A'; (\<And>v. cogent_C_unused_return__internal (B v) (B' v)) \<rbrakk> \<Longrightarrow>
                cogent_C_unused_return__internal (A >>= B) (A' >>= B')"
  "\<And>A A'. A = A' \<Longrightarrow> cogent_C_unused_return__internal A A'"
  by (monad_eq simp: cogent_C_unused_return__internal_def | blast)+

(* Test: *)
schematic_goal
  (* input *)
  "(do stuff1;
       stuff2;
       _ \<leftarrow>
         condition C1
           (do _ \<leftarrow>
                 condition C2
                   (do _ \<leftarrow> gets (\<lambda>_. r1);
                       gets (\<lambda>_. ()) od)   \<comment> \<open> <-- \<close>
                   bla1;
               gets (\<lambda>_. ()) od)           \<comment> \<open> <-- \<close>
           bla2;
       _ \<leftarrow>
         condition C3 stuff3 stuff4;       \<comment> \<open> no change \<close>
       stuff5 od)
    = ?A"
  (* expected output *)
  "?A =
   (do stuff1;
       stuff2;
       _ \<leftarrow>
         condition C1
           (condition C2
              (gets (\<lambda>_. r1))
              (do bla1; return undefined od))
           (do bla2; return undefined od);
       _ \<leftarrow>
         condition C3 stuff3 stuff4;
       stuff5 od)"
  (* do it *)
  apply ((rule cogent_C_unused_return_L cogent_C_unused_return_step cogent_C_unused_return__internal refl)+)[1]
  (* check *)
  by (rule refl)

(* Apply the rewrite to a corres proof state.
 * In corres_tac, we apply this tactic blindly and it rewrites all unit-returning blocks
 * in the C code. This should be safe because no genuine Cogent code ever returns unit
 * (the unit type in Cogent is currently compiled to unit_t in C, instead of void). *)
(* FIXME: maybe make this part of Tidy *)

context update_sem_init begin
lemma cogent_corres_unused_return:
  "m = m' \<Longrightarrow>
   corres srel c m' \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s \<Longrightarrow>
   corres srel c m \<xi> \<gamma> \<Xi> \<Gamma> \<sigma> s"
  by simp

ML \<open>
fun cogent_C_unused_return_tac ctxt = let
  (* import into ctxt's locale *)
  val corres_rule = Proof_Context.get_thm ctxt "cogent_corres_unused_return"
  in fn n =>
      rtac corres_rule n
      THEN SOLVES (REPEAT_DETERM
             (resolve_tac ctxt @{thms cogent_C_unused_return_L cogent_C_unused_return_step
                                      cogent_C_unused_return__internal refl} n)) end
\<close>
end


ML \<open>
(* Create derivative equations that only apply in a given context.
 *
 *   make_contextual_eq_thms "f" ["a = b", "c = d"] ctxt
 *    = ["f a = f b", "f c = f d"]
 *)
fun make_contextual_eq_thms (context : term) (eq_thms : thm list) ctxt : thm list =
  let fun dest_eq (Const (@{const_name "Trueprop"}, _) $ eq) = dest_eq eq
        | dest_eq (Const (@{const_name "Pure.eq"}, _) $ l $ r) = (l, r)
        | dest_eq (Const (@{const_name "HOL.eq"}, _) $ l $ r) = (l, r)
        | dest_eq t = raise (TERM ("ContextThms.dest_eq", [t]))
      fun make_eq_thm thm0 =
        let val ((_, [thm]), _) = Variable.import true [thm0] (Variable.set_body false ctxt);
            val (lhs, rhs) = dest_eq (Thm.prop_of thm)
                             handle TERM _ => raise THM ("make_contextual_eq_thms: not an equation", 0, [thm0])
            val prop = @{term Trueprop} $ (@{term "(=)"} $ (context $ lhs) $ (context $ rhs))
            val prop' = map_types (K dummyT) prop |> Syntax.check_term ctxt
                        handle ERROR _ => raise TERM ("make_contextual_eq_thms: equality term is invalid", [prop])
            fun free_var v = case Syntax.check_term ctxt (Free (v, dummyT)) of
                                Free (_, TFree _) => true
                              | _ => false
        in Goal.prove ctxt (filter free_var (Term.add_free_names prop' [])) [] prop'
                      (K (simp_tac (ctxt addsimps [thm]) 1))
           handle ERROR msg => raise TERM ("make_contextual_eq_thms proof failed:\n" ^ msg, [prop']) end
  in map make_eq_thm eq_thms end
\<close>

lemma simp_trivial_gets:
  "do x \<leftarrow> gets (\<lambda>_. v); B x od = B v"
  by simp
(* Limit simp_trivial_gets to the top level *)
local_setup \<open>
fn ctxt =>
Local_Theory.note
  ((Binding.name "corres_simp_gets", []),
   (make_contextual_eq_thms @{term "\<lambda>m. update_sem_init.corres abs_typing abs_repr srel c m \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"} @{thms simp_trivial_gets} ctxt))
  ctxt |> snd
\<close>

lemma simp_condition_bind:
  "do retval \<leftarrow> condition b x y; gets (\<lambda>s. retval) od = condition b x y" by simp

local_setup \<open>
fn ctxt =>
Local_Theory.note
  ((Binding.name "corres_simp_cond_gets", []),
   (make_contextual_eq_thms @{term "\<lambda>m. update_sem_init.corres abs_typing abs_repr srel c m \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"} @{thms simp_condition_bind} ctxt))
  ctxt |> snd
\<close>

lemma ucast_up_lesseq[OF refl]:
  "upcast = ucast
    \<Longrightarrow> is_up (upcast :: ('a :: len) word \<Rightarrow> ('b :: len) word)
    \<Longrightarrow> (upcast x \<le> upcast y) = (x \<le> y)"
  by (simp add: word_le_nat_alt unat_ucast_upcast)

lemma ucast_up_less[OF refl]:
  "upcast = ucast
    \<Longrightarrow> is_up (upcast :: ('a :: len) word \<Rightarrow> ('b :: len) word)
    \<Longrightarrow> (upcast x < upcast y) = (x < y)"
  by (simp add: word_less_nat_alt unat_ucast_upcast)

lemma ucast_up_mod[OF refl]:
  "upcast = ucast
    \<Longrightarrow> is_up (upcast :: ('c :: len) word \<Rightarrow> ('d :: len) word)
    \<Longrightarrow> (upcast x mod upcast y) = upcast (x mod y)"
  apply (rule word_unat.Rep_eqD)
  apply (simp only: unat_mod unat_ucast_upcast)
  done

lemma ucast_up_div[OF refl]:
  "upcast = ucast
    \<Longrightarrow> is_up (upcast :: ('c :: len) word \<Rightarrow> ('d :: len) word)
    \<Longrightarrow> (upcast x div upcast y) = upcast (x div y)"
  apply (rule word_unat.Rep_eqD)
  apply (simp only: unat_div unat_ucast_upcast)
  done

lemma ucast_up_eq_0[OF refl]:
  "upcast = ucast
    \<Longrightarrow> is_up (upcast :: ('c :: len) word \<Rightarrow> ('d :: len) word)
    \<Longrightarrow> (upcast x = 0) = (x = 0)"
  by (metis word_unat.Rep_inject unat_ucast_upcast ucast_0)

lemma ucast_down_bitwise[OF refl]:
  "dcast = ucast
    \<Longrightarrow> (bitOR (dcast x) (dcast y)) = dcast (bitOR x y)"
  "dcast = ucast
    \<Longrightarrow> (bitAND (dcast x) (dcast y)) = dcast (bitAND x y)"
  "dcast = ucast
    \<Longrightarrow> (bitXOR (dcast x) (dcast y)) = dcast (bitXOR x y)"
  "dcast = ucast
    \<Longrightarrow> is_down (dcast :: ('a :: len) word \<Rightarrow> ('b :: len) word)
    \<Longrightarrow> (bitNOT (dcast x)) = dcast (bitNOT x)"
  by (auto intro!: word_eqI simp add: word_size nth_ucast word_ops_nth_size
      is_down_def target_size_def source_size_def)

lemma ucast_down_shiftl[OF refl]:
  "dcast = ucast
    \<Longrightarrow> is_down (dcast :: ('a :: len) word \<Rightarrow> ('b :: len) word)
    \<Longrightarrow> dcast (x << n) = dcast x << n"
  apply clarsimp
  apply (rule word_eqI)
  apply (simp add: word_size nth_shiftl nth_ucast)
  apply (simp add: is_down_def source_size_def target_size_def word_size)
  apply auto
  done

lemma ucast_up_down_shiftr[OF refl]:
  "dcast = ucast
    \<Longrightarrow> is_down (dcast :: ('a :: len) word \<Rightarrow> ('b :: len) word)
    \<Longrightarrow> dcast (ucast x >> n) = x >> n"
  apply clarsimp
  apply (rule word_eqI)
  apply (simp add: word_size nth_shiftr nth_ucast)
  apply (simp add: is_down_def source_size_def target_size_def word_size)
  apply (auto dest: test_bit_size simp: word_size)
  done

lemma ucast_up_sless_disgusting[OF refl]:
  "(upcast :: ('c :: len) word \<Rightarrow> ('d :: len) word) = ucast
    \<Longrightarrow> len_of TYPE('c) < len_of TYPE('d)
    \<Longrightarrow> (upcast x <s upcast y) = (x < y)"
  apply (clarsimp simp: word_sless_msb_less msb_nth nth_ucast
                        word_less_nat_alt unat_ucast_upcast
                        is_up_def source_size_def target_size_def word_size)
  apply (auto dest: test_bit_size simp: word_size)
  done

lemma ucast_up_sle_disgusting[OF refl]:
  "(upcast :: ('c :: len) word \<Rightarrow> ('d :: len) word) = ucast
    \<Longrightarrow> len_of TYPE('c) < len_of TYPE('d)
    \<Longrightarrow> (upcast x <=s upcast y) = (x \<le> y)"
  apply (clarsimp simp: word_sle_msb_le msb_nth nth_ucast
                        word_le_nat_alt unat_ucast_upcast
                        is_up_def source_size_def target_size_def word_size)
  apply (auto dest: test_bit_size simp: word_size)
  done

(* Corres tactic *)

ML \<open>
(* Used to decode Cogent Var indices *)
fun decode_isa_nat @{term "0 :: nat"} = 0
  | decode_isa_nat (@{term Suc} $ n) = decode_isa_nat n + 1
  | decode_isa_nat n = HOLogic.dest_number n |> snd

fun TRY_FST tac1 tac2 st = (tac2 ORELSE ((DETERM tac1) THEN tac2)) st
fun TRY_FST_N tac1 tac2 st = (tac2 ORELSE (tac1 THEN tac2)) st
fun TRY_MORE_FST tac1 tac2 st = (tac2 ORELSE ((DETERM tac1) THEN (TRY_MORE_FST tac1 tac2))) st

(* Determine whether a Cogent type contains a TFun anywhere.
 * This is used as a crude heuristic for applying corres_let_gets_propagate. *)
fun Cogent_type_contains_TFun (Const (@{const_name TFun}, _)) = true
  | Cogent_type_contains_TFun (Abs (_, _, t)) = Cogent_type_contains_TFun t
  | Cogent_type_contains_TFun (f $ x) = Cogent_type_contains_TFun f orelse Cogent_type_contains_TFun x
  | Cogent_type_contains_TFun _ = false

(* Matches within a typing judgement. *)
fun Cogent_typing_returns_TFun (@{term Trueprop} $
                                (Const (@{const_name typing}, _) $ tenv $ kind $ env $ expr $ typ)) =
      Cogent_type_contains_TFun typ
  | Cogent_typing_returns_TFun t = raise TERM ("Cogent_typing_returns_TFun: not a typing rule", [t])

(* Number of expected nondet_monad statements for each Cogent atom in a Let. *)
fun atom_stmts @{const_name Var}     = SOME 1
  | atom_stmts @{const_name Prim}    = NONE
  | atom_stmts @{const_name App}     = SOME 2
  | atom_stmts @{const_name Con}     = SOME 1
  | atom_stmts @{const_name Struct}  = SOME 1
  | atom_stmts @{const_name Unit}    = SOME 1
  | atom_stmts @{const_name Lit}     = SOME 1
  | atom_stmts @{const_name Cast}    = SOME 1
  | atom_stmts @{const_name Tuple}   = SOME 1
  | atom_stmts @{const_name Esac}    = SOME 1
  | atom_stmts @{const_name Fun}     = SOME 1
  | atom_stmts @{const_name AFun}    = SOME 1
  | atom_stmts @{const_name Promote} = SOME 1
  (* Let (Put...) is handled outside of corres_let_tac. *)
  | atom_stmts _ = NONE
fun sigil_atom_stmts @{const_name Member} Unboxed = SOME 1
  | sigil_atom_stmts @{const_name Member} _       = SOME 2
  | sigil_atom_stmts _ _ = NONE
fun rec_sigil (Const (@{const_name TRecord}, _) $ _ $ @{term Unboxed}) = SOME Unboxed
  | rec_sigil (Const (@{const_name TRecord}, _) $ _ $ (@{const Boxed} $ @{const ReadOnly} $ _)) = SOME ReadOnly
  | rec_sigil (Const (@{const_name TRecord}, _) $ _ $ (@{const Boxed} $ @{const Writable} $ _)) = SOME Writable
  | rec_sigil _ = NONE

(* Guess the number of statements for this atom.
 * "Member (Var 0) 0" is passed as {head = Member, args = [Var 0, 0]}.
 * The type env is used to distinguish unboxed and boxed member accesses. *)
fun atom_stmts' (head : string) (args : term list) (env : term) =
  case atom_stmts head of SOME n => SOME n | NONE => (case (head, args)
    of (@{const_name Member}, Const (@{const_name Var}, _) $ n :: _) => let
    val ty = case nth (HOLogic.dest_list env) (decode_isa_nat n) of
      (Const (@{const_name Some}, _) $ ty) => ty | t => raise TERM ("atom_stmts': Gamma none", [t])
    val sg = case rec_sigil ty of SOME s => s | _ => raise ERROR ("atom_stmts': cannot parse sigil for record: " ^ @{make_string} ty)
  in sigil_atom_stmts head sg end
    | (@{const_name Prim}, primop :: _) => let
    val is_guarded = case head_of primop of @{const "LShift"} => true
        | @{const "RShift"} => true | @{const "Divide"} => true
        | @{const "Mod"} => true | _ => false
  in if is_guarded then SOME 2 else SOME 1 end
    | _ => NONE)

(* Inspect a "corres ..." subgoal. *)
fun dest_corres_prop prop =
    case prop of
         @{term Trueprop} $ (Const (@{const_name "update_sem_init.corres"}, _) $
                               _ $ _ $ (* locale parameters *)
                               srel $ cogent $ m $ xi $ gam $ Xi $ Gam $ si $ s) =>
           SOME (srel, cogent, m, xi, gam, Xi, Gam, si, s)
       | _ => NONE
fun dest_corres_goal goal_num st =
  if Thm.nprems_of st < goal_num then NONE else
  Logic.concl_of_goal (Thm.prop_of st) goal_num |> dest_corres_prop

(* Guess the C types mentioned in a rule. This can reduce the amount of
 * val_rel and type_rels that we need to unfold.
 * Ideally, this should be tracked in the lemma buckets. *)

fun scrape_C_types thm = let
    fun filter_Const P (Const (c_name, _)) = if P c_name then [c_name] else []
      | filter_Const P (f $ x) = filter_Const P f @ filter_Const P x
      | filter_Const P (Abs (_, _, t)) = filter_Const P t
      | filter_Const _ _ = []
    fun c_type_name str = String.tokens (fn x => x = #".") str
                          |> filter (String.isSuffix "_C") |> take 1
  in Thm.prop_of thm
     |> filter_Const (c_type_name #> null #> not)
     |> map c_type_name |> List.concat
     |> distinct (op =)
  end

(* Apply a conversion to the n'th arg in the concl of the chosen subgoal. *)
fun nth_arg_conv_tac n ngoal ctxt conv st = if Thm.nprems_of st < ngoal then no_tac st else
  let val subgoal = Logic.get_goal (Thm.prop_of st) ngoal
      val all_vars = length (strip_all_vars subgoal)
      val imps = length (Logic.strip_imp_prems (strip_all_body subgoal))
      val goal_concl = Logic.concl_of_goal (Thm.prop_of st) ngoal
  in
  Conv.gconv_rule
    (Utils.nth_arg_conv n conv
     |> (if fst (strip_comb goal_concl) = @{term Trueprop} then Conv.arg_conv else I)
     |> Conv.concl_conv imps
     |> (fn conv => Conv.params_conv all_vars (K conv) ctxt)) ngoal st
  |> Seq.succeed
  end
  handle CTERM _ => no_tac st

(* Remove "val_rel a a'" assumptions if a' does not appear anywhere else in the subgoal.
   Special case for appearance within corres propositions - ignore elements of \<gamma>
   that are not given types in \<Gamma>. *)
val val_rel_thin_tac = SUBGOAL (fn (goal, n) => let
  val hyps = Logic.strip_assums_hyp goal
  val concl = Logic.strip_assums_concl goal
  fun match_xi_bvars (Const (@{const_name Cons}, _) $ _ $ xs)
          (Const (@{const_name Cons}, _) $ Const (@{const_name None}, _) $ ys) = match_xi_bvars xs ys
    | match_xi_bvars (Const (@{const_name Cons}, _) $ x $ xs)
          (Const (@{const_name Cons}, _) $ y $ ys) = maps spot_bvars [x, y] @ match_xi_bvars xs ys
    | match_xi_bvars xs ys = maps spot_bvars [xs, ys]
  and spot_bvars t = case (dest_corres_prop t, t) of
    (SOME (srel, cogent, m, xi, gam, Xi, Gam, si, s), _)
        => maps spot_bvars [srel, cogent, m, xi, Xi, si, s] @ match_xi_bvars gam Gam
  | (NONE, f $ x) => spot_bvars f @ spot_bvars x
  | (NONE, Abs (_, _, bd)) => map (fn x => x - 1) (filter (fn x => x > 0) (spot_bvars bd))
  | (NONE, Bound n) => [n]
  | _ => []
  val used_bvars = (maps spot_bvars (concl :: hyps))
    |> map (fn x => (x, ())) |> Inttab.make_list
  fun keep (@{term Trueprop} $ (Const (@{const_name val_rel}, _) $ _ $ Bound n))
        = (Inttab.lookup used_bvars n <> SOME [()])
    | keep _ = true
  val drops = filter_out (keep o fst) (hyps ~~ (0 upto length hyps - 1))
    |> map snd |> rev
  fun thin i = (rotate_tac i n THEN etac thin_rl n THEN rotate_tac (~ i) n)
  in EVERY (map thin drops) end)

fun corres_tac ctxt
               (typing_tree : thm tree)
               (fun_defs : thm list)
               (absfun_corres : thm list)
               (fun_corres : thm list)
               (corres_if: thm)
               (corres_esac: thm list)
               (val_rel_simps : thm list)
               (type_rel_simps : thm list)
               (tag_enum_defs : thm list)
               (LETBANG_TRUE_def: thm)
               (list_to_map_simps: thm list)
               (verbose : bool)
               : tactic =
let

  fun corres_Cogent_head goal_num st =
    Option.map (#2 #> strip_comb #> fst #> dest_Const #> fst) (dest_corres_goal goal_num st)

  fun get_thm nm = Proof_Context.get_thm ctxt nm;
  fun get_thms nm = Proof_Context.get_thms ctxt nm;

  (* Basic rules. *)
  val corres_let = get_thm "corres_let";
  val corres_nested_let = get_thm "corres_nested_let";
  val corres_let_propagate = get_thm "corres_let_gets_propagate";
  val corres_letbang = get_thm "corres_letbang";
  val corres_app_concrete = get_thm "corres_app_concrete";
  val corres_var = get_thm "corres_var";
  val corres_con = get_thm "corres_con";
  val corres_lit = get_thm "corres_lit";
  val corres_prim1 = get_thm "corres_prim1";
  val corres_prim2 = get_thm "corres_prim2";
  val corres_prim2_partial_right = get_thm "corres_prim2_partial_right";
  val corres_prim2_partial_left = get_thm "corres_prim2_partial_left";
  val eval_prim_simps = @{thms eval_prim_u_def
    ucast_down_add ucast_down_mult up_ucast_inj_eq
    ucast_down_minus ucast_up_less ucast_up_lesseq
    ucast_down_bitwise[symmetric] ucast_down_shiftl unat_ucast_upcast
    ucast_up_down_shiftr ucast_id
    ucast_up_div ucast_up_mod ucast_up_eq_0 checked_div_def
    ucast_up_sle_disgusting ucast_up_sless_disgusting
    is_up_def is_down_def source_size_def
    target_size_def word_size ucast_down_ucast_id
    };
  val eval_prim_ineq_guard_simps = @{thms word_less_nat_alt word_le_nat_alt}
  val corres_unit = get_thm "corres_unit";
  val corres_fun = get_thm "corres_fun";
  val corres_afun = get_thm "corres_afun";
  val corres_promote = get_thm "corres_promote";
  val corres_cast = get_thms "corres_cast";
  val corres_struct = get_thm "corres_struct";
  val corres_let_put_unboxed = get_thm "corres_let_put_unboxed'";
  val corres_no_let_put_unboxed = get_thm "corres_no_let_put_unboxed'";

  (* Type-specialised rule buckets. *)
  val net_resolve_tac = Tactic.build_net #> resolve_from_net_tac ctxt
  val corres_case_rule = Case.get ctxt |> net_resolve_tac;
  val corres_member_boxed_rule = MemberReadOnly.get ctxt |> net_resolve_tac;
  val corres_take_boxed_rule = TakeBoxed.get ctxt |> net_resolve_tac;
  val corres_take_unboxed_rule = TakeUnboxed.get ctxt |> net_resolve_tac;
  val corres_put_boxed_rule = PutBoxed.get ctxt |> net_resolve_tac;
  val corres_let_put_boxed_rule = LetPutBoxed.get ctxt |> net_resolve_tac;

  (* Miscellaneous rules. *)
  val bind_assoc_sym = @{thm bind_assoc[symmetric]};
  val recguard_true_rule = get_thm "condition_true_pure";

  val type_rel_simps = type_rel_simps @ TypeRelSimp.get ctxt;
  val val_rel_simps_prim = @{thms val_rel_word}
    @ [get_thm "val_rel_bool_t_C_def"]
  val val_rel_simps = val_rel_simps @ ValRelSimp.get ctxt;
  fun make_thm_index guess thms = let
      val nmths = map swap (maps (fn t => map (pair t) (guess t)) thms)
    in Symtab.make_list nmths end
  fun lookup_thm_index table = List.mapPartial (Symtab.lookup table) #> List.concat #> distinct Thm.eq_thm
  val type_rel_index = make_thm_index scrape_C_types type_rel_simps
  val val_rel_index = make_thm_index guess_val_rel_type val_rel_simps

  (* Basic tactics. *)
  fun SOLVES' tac = fn n => SOLVES (tac n);
  fun TRY' tac = fn n => TRY (tac n);
  val simp = asm_full_simp_tac ctxt;
  val subgoal_simp = TRY' (SOLVES' simp);
  fun simp_add thms = asm_full_simp_tac (add_simps thms ctxt);
  fun subgoal_simp_add thms = TRY' (SOLVES' (simp_add thms));
  fun fastforce_add thms = Clasimp.fast_force_tac (add_simps thms ctxt);
  fun clarsimp_add thms = Clasimp.clarsimp_tac (add_simps thms ctxt);
  fun subst thms = EqSubst.eqsubst_tac ctxt [0] thms;
  val rule = rtac;
  val rules = resolve_tac ctxt;

  (* Common simpsets. *)
  val val_rel_simp_ctxt = ctxt addsimps val_rel_simps
  val type_rel_simp_ctxt = ctxt addsimps type_rel_simps
  fun subgoal_val_rel_simp_add thms = TRY' (val_rel_thin_tac
      THEN' SOLVES' (asm_full_simp_tac (val_rel_simp_ctxt addsimps thms)))
  fun subgoal_type_rel_simp_add thms = TRY' (SOLVES' (asm_full_simp_tac (type_rel_simp_ctxt addsimps thms)))
  fun subgoal_val_rel_clarsimp_add thms = TRY' (val_rel_thin_tac
      THEN' SOLVES' (Clasimp.clarsimp_tac (val_rel_simp_ctxt addsimps thms)))

  fun real_goal_of (@{term Pure.imp} $ _ $ t) = real_goal_of t
    | real_goal_of (@{term Trueprop} $ t) = real_goal_of t
    | real_goal_of (Const (@{const_name Pure.all}, _) $ Abs (x, ty, t)) = betapply (real_goal_of t, Free (x, ty))
    | real_goal_of t = t

  (* Apply an abstract function corres rule.
   * These rules may come in all shapes and sizes; try to solve their assumptions by simp. *)
  fun apply_absfun absfun_thm st =
    if exists_subterm (fn t => is_const @{const_name measure_call} t) (Thm.prop_of st)
    then (* resolve AutoCorres' "measure_call" construct *)
         st |>
         (rule (get_thm "corres_measure_call_subst") 1
          THEN
          (fn st => (case Logic.concl_of_goal (Thm.prop_of st) 1 |> real_goal_of of
                       Const (@{const_name "monad_mono"}, _) $ Abs (_ (* measure var *), _, call) =>
                         case fst (strip_comb call) of
                           Const (f, _) => rule (get_thm (Long_Name.base_name f ^ "_mono")) 1 st)
                    handle Match => raise TERM ("Corres_Tac: failed to resolve measure_call",
                                                [Logic.concl_of_goal (Thm.prop_of st) 1]))
          THEN
          (rule absfun_thm
           THEN_ALL_NEW
           (SOLVES' (val_rel_thin_tac THEN'
                      (rule @{thm order_refl} ORELSE'
                       simp_add (type_rel_simps @ val_rel_simps @ @{thms recguard_dec_def}))))) 1
         )
    else
         st |>
         (rule absfun_thm
          THEN_ALL_NEW
          (SOLVES' (val_rel_thin_tac THEN' simp_add (type_rel_simps @ val_rel_simps @ @{thms recguard_dec_def})))) 1

  (* Strip the recursion guard from recursive function bodies.
   * We try to simp away the guard condition. *)
  fun simp_recguard_tac n st =
    case dest_corres_goal n st of
       NONE => raise THM ("corres_tac/simp_recguard_tac: expected a corres subgoal here", 0, [st])
     | SOME (_, _, c_def, _, _, _, _, _, _) =>
         (case strip_comb c_def of
             (Const (@{const_name condition}, _), _) =>
               (case (if verbose then tracing "Proving: recursion guard\n" else ();
                      subst [recguard_true_rule] n THEN SOLVES (simp n)) st |> Seq.pull of
                   SOME (st', _) => Seq.succeed st'
                 | NONE => raise THM ("corres_tac/simp_recguard_tac: failed to discharge recursion guard\n", 0, [st]))
           | _ => all_tac st);

  (* Prove corres recursively. *)
  fun corres_tac_rec typing_tree depth = let
     fun print msg st = ((if verbose then tracing (String.implode (replicate (depth*2) #" ") ^ msg ^ "\n") else ()); Seq.single st);
     fun tree_nth nth = List.nth (tree_rest typing_tree, nth);
     fun rule_tree nth n st = TRY (TRY_FST (simp n) (rule (tree_hd (tree_nth nth)) n) |> SOLVES) st
             handle Subscript => (print "Warning: rule_tree failed" THEN no_tac) st;
     fun corres_tac_nth nth st = corres_tac_rec (tree_nth nth) (depth+1) st;

     fun tree_nth' tree nth = List.nth (tree_rest tree, nth);
     fun rule_tree' tree nth n st = rule (tree_hd (tree_nth' tree nth)) n st
             handle Subscript => (print "Warning: rule_tree' failed" THEN no_tac) st;

     (* For Let (Fun...) and similar constructs, we need to remember the value of the Fun
      * so that we can apply the corres lemma for that function. *)
     fun apply_corres_let n st =
       (if Cogent_typing_returns_TFun (Thm.prop_of (tree_hd (tree_nth 1))) (* check the type of the bound-expr *)
        then (print "Debug: using corres_let_propagate" THEN rule corres_let_propagate n) st
        else rule corres_let n st
       ) handle Subscript => (print "Warning: tree_nth failed in apply_corres_let" THEN no_tac) st

     (* Process a program of the form (Let x y...).
      * While x is guaranteed to be an atomic expression, atoms may translate
      * to more than one statement in the C monad.
      * For two-statement atoms, we use bind_assoc to pull out the statement pair
      * before continuing.
      *)
     fun corres_let_tac n st =
      (case dest_corres_goal n st of
          SOME (_, Const (@{const_name Cogent.Let}, _) $ lhs $ rhs, _, _, _, _, env, _, _) =>
          (case strip_comb lhs of
            (Const (lhs_head, _), args) =>
              (case atom_stmts' lhs_head args env of
                  SOME 1 => apply_corres_let n
                                THEN print ("corres_let: " ^ lhs_head)
                               THEN rule_tree 0 n
                              THEN rule_tree 1 n
                             THEN TRY (corres_tac_nth 1)
                            THEN TRY (corres_tac_nth 2)
                | SOME 2 => subst [bind_assoc_sym] n
                            THEN apply_corres_let n
                                THEN print ("corres_let: " ^ lhs_head)
                               THEN rule_tree 0 n
                              THEN rule_tree 1 n
                             THEN TRY (corres_tac_nth 1)
                            THEN TRY (corres_tac_nth 2)
                | _ => no_tac)
            | _ => no_tac)
        | _ => no_tac) st;

      (* Check the head of the Cogent program before applying a tactic.
       * This is useful when the tactic doesn't fail quickly (eg. for type-specialised rule buckets). *)
      fun check_Cogent_head head tac st =
        case corres_Cogent_head 1 st of
           NONE => tac st (* not sure if we'd expect this to work *)
         | SOME head' => if head = head' then tac st else no_tac st;
    in
      (fn t => case corres_Cogent_head 1 t of SOME h => print ("Proving: " ^ h) t | _ => all_tac t)
      THEN
      (* Evaluate Cogent environment lookups (ie. list lookups) eagerly *)
      ((nth_arg_conv_tac 7 (* \<gamma> *) 1 ctxt (Simplifier.rewrite ctxt)
       THEN nth_arg_conv_tac 9 (* \<Gamma> *) 1 ctxt (Simplifier.rewrite ctxt))
       THEN
       (* Prune val_rel assumptions and variables. *)
       val_rel_thin_tac 1 THEN prune_params_tac ctxt
       THEN
       ((rule corres_var 1
         THEN print "corres_var"
         THEN subgoal_simp 1)

        ORELSE
        (rule corres_unit 1
         THEN print "corres_unit"
         THEN subgoal_val_rel_simp_add [] 1)

        ORELSE
        (rule corres_con 1
         THEN print "corres_con"
         THEN subgoal_val_rel_simp_add [] 1)

        ORELSE
        (rule corres_lit 1
         THEN print "corres_lit"
         THEN subgoal_val_rel_simp_add [] 1)

        ORELSE
        (rule corres_prim1 1
         THEN print "corres_prim (unary)"
         THEN val_rel_thin_tac 1 THEN fastforce_add (val_rel_simps_prim @ eval_prim_simps) 1)

        ORELSE
        (rule corres_prim2 1
         THEN print "corres_prim (binary)"
         THEN val_rel_thin_tac 1 THEN fastforce_add (val_rel_simps_prim @ eval_prim_simps) 1)

        ORELSE
        (rule corres_prim2_partial_right 1
         THEN print "corres_prim (binary, partial, right)"
         THEN (val_rel_thin_tac THEN' simp_add (eval_prim_simps @ val_rel_simps)
             THEN_ALL_NEW simp_add (eval_prim_simps @ eval_prim_ineq_guard_simps)) 1
         THEN subgoal_val_rel_simp_add (eval_prim_simps @ eval_prim_ineq_guard_simps) 1
        )

        ORELSE
        (rule corres_prim2_partial_left 1
         THEN print "corres_prim (binary, partial, left)"
         THEN (val_rel_thin_tac THEN' simp_add (eval_prim_simps @ val_rel_simps)
             THEN_ALL_NEW simp_add (eval_prim_simps @ eval_prim_ineq_guard_simps)) 1
         THEN subgoal_val_rel_simp_add (eval_prim_simps @ eval_prim_ineq_guard_simps) 1
        )

        ORELSE
        (rule corres_fun 1
         THEN print "corres_fun"
         THEN subgoal_val_rel_simp_add [] 1)

        ORELSE
        (rule corres_afun 1
         THEN print "corres_afun"
         THEN subgoal_val_rel_simp_add [] 1)

        ORELSE
        (rule corres_promote 1
         THEN print "corres_promote"
         THEN subgoal_val_rel_simp_add [] 1)

        ORELSE
        ((simp_tac (put_simpset HOL_basic_ss ctxt addsimps list_to_map_simps) 1)
         THEN rule corres_struct 1
         THEN print "corres_struct"
         THEN subgoal_val_rel_simp_add [] 1)

        ORELSE
        (rules corres_cast 1
         THEN print "corres_cast"
         THEN rule_tree 0 1
         THEN subgoal_simp 1)

        ORELSE check_Cogent_head @{const_name App}
        (((fn n => rule corres_app_concrete n
                   THEN print "corres_app_concrete"
                   THEN simp n THEN simp n
                   THEN rules fun_corres n)
          THEN_ALL_NEW subgoal_simp_add (@{thm recguard_dec_def} :: fun_corres)) 1)

        ORELSE check_Cogent_head @{const_name App}
        (APPEND_LIST (map apply_absfun absfun_corres)
         THEN print "corres_app_abstract")

        ORELSE
        (rules corres_esac 1
         THEN print "corres_esac"
             THEN subgoal_simp 1
            THEN subgoal_simp 1
           THEN subgoal_simp 1
          THEN rule_tree 0 1
         THEN subgoal_val_rel_simp_add [] 1

        ORELSE check_Cogent_head @{const_name Member}
        (corres_member_boxed_rule 1
         THEN print "corres_member_boxed"
               THEN rule_tree 0 1
              THEN subgoal_simp 1
             THEN subgoal_simp 1
            THEN subgoal_type_rel_simp_add [] 1
           THEN subgoal_type_rel_simp_add [] 1
          THEN rule_tree 0 1
         THEN TRY (TRY_FST (simp 1) (rule_tree' (tree_nth 0) 0 1) |> SOLVES))

        ORELSE
        (rule (Proof_Context.get_thm ctxt "corres_member_unboxed") 1
         THEN subgoal_val_rel_clarsimp_add [] 1)

        ORELSE check_Cogent_head @{const_name Take}
        (corres_take_unboxed_rule 1
         THEN print "corres_take_unboxed"
                    THEN subgoal_simp 1
                   THEN rule_tree 0 1
                  THEN subgoal_val_rel_simp_add [] 1
                 THEN subgoal_type_rel_simp_add [] 1
                THEN subgoal_type_rel_simp_add [] 1
               THEN TRY (TRY (simp 1) THEN SOLVES (rule (tree_hd typing_tree) 1))
              THEN rule_tree 1 1
             THEN rule_tree 3 1
            THEN rule_tree 2 1
           THEN subgoal_simp 1
          THEN TRY (corres_tac_nth 3))

        ORELSE check_Cogent_head @{const_name Take}
        (corres_take_boxed_rule 1
         THEN print "corres_take_boxed"
                    THEN subgoal_simp 1
                   THEN rule_tree 0 1
                  THEN subgoal_val_rel_simp_add [] 1
                 THEN subgoal_type_rel_simp_add [] 1
                THEN subgoal_type_rel_simp_add [] 1
               THEN TRY (TRY_FST (simp 1) (SOLVES (rule (tree_hd typing_tree) 1)))
              THEN rule_tree 1 1
             THEN rule_tree 3 1
            THEN rule_tree 2 1
           THEN subgoal_simp 1
          THEN TRY (corres_tac_nth 3))

        ORELSE
        (rule corres_if 1
         THEN print "corres_if"
             THEN rule_tree 0 1
            THEN rule_tree 1 1
           THEN subgoal_val_rel_simp_add [] 1
          THEN TRY (corres_tac_nth 2)
         THEN TRY (corres_tac_nth 3))

        ORELSE check_Cogent_head @{const_name Let}
        (rule corres_let_put_unboxed 1
         THEN print "corres_put_unboxed"
               THEN subgoal_simp 1
              THEN subgoal_simp 1
             THEN rule_tree 0 1
            THEN rule_tree 1 1
           THEN subgoal_val_rel_clarsimp_add [] 1
          THEN TRY (corres_tac_nth 2))

        ORELSE check_Cogent_head @{const_name Put}
        (rule corres_no_let_put_unboxed 1
         THEN print "corres_put_unboxed (no let)"
             THEN subgoal_simp 1
            THEN subgoal_simp 1
           THEN TRY (TRY (simp 1) THEN SOLVES (rule (tree_hd typing_tree) 1))
          THEN subgoal_val_rel_clarsimp_add [] 1)

        ORELSE check_Cogent_head @{const_name Let}
        (corres_let_put_boxed_rule 1
         THEN print "corres_let_put_boxed"
                  THEN rule_tree 0 1
                 THEN subgoal_simp 1
                THEN subgoal_type_rel_simp_add [] 1
               THEN subgoal_simp 1
              THEN subgoal_simp 1
             THEN TRY (TRY_FST (simp 1) (SOLVES (rule (tree_hd typing_tree) 1)))
            THEN rule_tree 1 1
           THEN subgoal_simp 1
          THEN TRY (corres_tac_nth 2))

        ORELSE check_Cogent_head @{const_name Put}
        (corres_put_boxed_rule 1
         THEN print "corres_put_boxed"
                THEN rule_tree' (tree_nth 0 handle Subscript => error "tree_nth failed") 0 1
               THEN subgoal_simp 1
              THEN subgoal_type_rel_simp_add [] 1
             THEN subgoal_simp 1
            THEN subgoal_simp 1
           THEN TRY (TRY_FST (simp 1) (SOLVES (rule (tree_hd typing_tree) 1)))
          THEN subgoal_simp 1)

        ORELSE check_Cogent_head @{const_name Case}
        (rtac (get_thm "corres_simp_cond_gets" RS @{thm iffD2}) 1 THEN
         (corres_case_rule 1
            THEN print "corres_case"
                    THEN subgoal_simp 1
                   THEN subgoal_simp 1
                  THEN rule_tree 0 1
                 THEN subgoal_simp 1
                THEN rule_tree 1 1
               THEN rule_tree 2 1
              THEN rule_tree 3 1
             THEN TRY (corres_tac_nth 2)
            THEN TRY (corres_tac_nth 3)))

        ORELSE check_Cogent_head @{const_name Let}
        (rtac corres_nested_let 1
         THEN print "corres_let (nested)"
             THEN rule_tree 0 1
            THEN rule_tree 1 1
           THEN TRY (corres_tac_nth 1)
          THEN TRY (corres_tac_nth 2))

        ORELSE corres_let_tac 1

        ORELSE check_Cogent_head @{const_name LetBang}
        ((simp_tac (put_simpset HOL_basic_ss ctxt addsimps [LETBANG_TRUE_def]) 1)
         THEN
         rule corres_letbang 1
         THEN print "corres_letbang"
               THEN rule_tree 0 1
              THEN rule_tree 1 1
             THEN rule_tree 3 1
            THEN subgoal_simp 1
           THEN TRY (corres_tac_nth 1)
          THEN TRY (corres_tac_nth 2))

        ORELSE check_Cogent_head @{const_name Split}
        (rtac (get_thm "corres_split") 1
         THEN print "corres_split"
                 THEN rule_tree 0 1
                THEN subgoal_val_rel_simp_add [] 1
               THEN subgoal_simp 1
              THEN rule_tree 1 1
             THEN rule_tree 2 1
            THEN subgoal_val_rel_simp_add [] 1
           THEN subgoal_val_rel_simp_add [] 1
          THEN TRY (corres_tac_nth 1))
      )))
   end
in
  (simp_tac (put_simpset HOL_basic_ss ctxt addsimps fun_defs) 1)
  THEN simp_recguard_tac 1
  THEN (fn st => (if verbose then tracing "Fixing unused variables\n" else ();
                  cogent_C_unused_return_tac ctxt 1 st))
  THEN corres_tac_rec typing_tree 0
end
\<close>

ML\<open>
fun peel_two tree =  hd (tree_rest (hd (tree_rest (hd tree))));
\<close>



(* Analyse the program and generate proofs based on its call tree. *)
ML \<open>
fun partition _ [] = ([], [])
  | partition P (x::xs) = let val (ps, ns) = partition P xs in
                          if P x then (x::ps, ns) else (ps, x::ns) end

fun max a b = if a < b then b else a
fun maximum [] = error "maximum: empty list"
  | maximum [x] = x
  | maximum (x::xs) = max x (maximum xs)

fun get_Cogent_funtype ctxt fname = let
  val simps = Proof_Context.get_thms ctxt "abbreviated_type_defs"
  in
    Proof_Context.get_thm ctxt (fname ^ "_type_def")
    |> simplify (ctxt addsimps simps)
  end

(* check whether the function argument type contains a TFun *)
fun funtype_is_first_order (funtype:term) =
  case funtype of (Const (@{const_name Pair}, _) $ _ $
                    (Const (@{const_name Pair}, _) $ arg $ _)) =>
                  not (Cogent_type_contains_TFun arg)
                | _ => raise TERM ("Expected a Cogent type signature", [funtype])

(* scrape all direct function calls *)
val get_simple_function_calls = let
  fun search (Const (@{const_name App}, _) $
        (Const (@{const_name Fun}, _) $ Const (callee, _) $ _) $ _) = [Long_Name.base_name callee]
    | search (Const (@{const_name App}, _) $
        (Const (@{const_name AFun}, _) $ callee $ _) $ _) = [Utils.decode_isa_string callee]
    | search (f $ x) = search f @ search x
    | search _ = []
  in search end

(*
 * Infer a call graph. We assume that the program only has:
 *  - first-order Cogent functions,
 *  - first-order abstract functions, and
 *  - second-order abstract functions with first-order Cogent function arguments.
 *)
datatype FunType = AbsFun | CogentFun;

(* Warning: CogentCallTree inlines a full subtree at each call site.
 * If this doesn't scale, we will need more indirection. *)
datatype 'a CogentCallOrder = FirstOrderCall of 'a CogentCallTree
                          | SecondOrderCall of ('a CogentCallTree * (term * 'a CogentCallTree) list)
     and 'a CogentCallTree = CogentCallTree of ('a * FunType * string * 'a CogentCallOrder list);

fun CogentCallTree_name    (CogentCallTree (_, _, name, _))  = name
fun CogentCallTree_funtype (CogentCallTree (_, typ, _, _))   = typ
fun CogentCallTree_data    (CogentCallTree (a, _, _, _))     = a
fun CogentCallTree_calls   (CogentCallTree (_, _, _, calls)) = calls

(* We need a stack of environments \<xi> to verify with higher-order absfuns later on.
 * Each such function call increments \<xi>.
 * Get the stack height and the position of each function in the call tree.
 * Note that a function may appear in multiple environments. *)
fun calc_call_depth tr = maximum (0 :: map calc_call_order_depth (CogentCallTree_calls tr))
and calc_call_order_depth (FirstOrderCall f) = calc_call_depth f
  | calc_call_order_depth (SecondOrderCall (f, args)) =
       maximum (map calc_call_depth (f::map snd args)) + (if CogentCallTree_funtype f = AbsFun then 1 else 0)

(*
 * FIXME: this only deals with one function (call tree) at a time.
 * If there are multiple entry points, we'd want to handle them simultaneously
 * to avoid redundant \<xi>'s and subproofs.
 *)
fun annotate_depth tr = let
  fun annotate' d (CogentCallTree ((), ty, name, calls)) = let
    in CogentCallTree (d, ty, name, map (annotate_call' d) calls) end
  and annotate_call' d (FirstOrderCall f) = FirstOrderCall (annotate' d f)
    | annotate_call' d (SecondOrderCall (f, args)) = let
        val d' = if CogentCallTree_funtype f = AbsFun then d-1 else 0
        in SecondOrderCall (annotate' d f, map (apsnd (annotate' d')) args) end
  in annotate' (calc_call_depth tr) tr end

fun make_call_tree (Cogent_functions, Cogent_abstract_functions) HO_hints ctxt = let
  val Cogent_abstract_functions_HO =
      filter_out (get_Cogent_funtype ctxt #> Thm.prop_of #> Utils.rhs_of_eq #> funtype_is_first_order)
                 Cogent_abstract_functions
  val FO_call_graph =
      Cogent_functions
      |> map (fn n => (n, Proof_Context.get_thm ctxt (n ^ "_def") |> Thm.prop_of |> Utils.rhs_of_eq
                          |> get_simple_function_calls |> distinct (op =)))
      |> map (apsnd (filter (fn f => not (exists (fn af => f = af) Cogent_abstract_functions_HO))))
  val absfun_decls = map (fn name => (name, CogentCallTree ((), AbsFun, name, []))) Cogent_abstract_functions
  fun func_name (Left f) = f
    | func_name (Right f) = f
  fun add_fun (name, FO_callees) table = let
        fun subtree f = case Symtab.lookup table f of
                SOME tr => tr
              | (* assume that we get Cogent_functions in topological order *)
                NONE => error ("make_call_tree: " ^ quote name ^ " calls " ^ quote f ^
                               " but we don't know anything about it (yet)")
        val FO_callees' = FO_callees
                          |> map (fn f => FirstOrderCall (subtree f))
        val HO_callees = Symtab.lookup_list HO_hints name
                         |> map (fn (f, args) => SecondOrderCall (subtree (func_name f), map (apsnd (subtree o func_name)) args))
      in Symtab.update_new (name, CogentCallTree ((), CogentFun, name, FO_callees' @ HO_callees)) table end
  in
    fold add_fun FO_call_graph (Symtab.make absfun_decls)
  end

(* Obtain the absfuns included in each \<xi>_n, up to the call tree depth. *)
fun make_uabsfuns_defs (tr as CogentCallTree (depth, _, _, _)) = let
      fun collect_absfuns d (CogentCallTree (d', ty, name, calls)) callees =
            (if d = d' andalso ty = AbsFun then [(AbsFun, name, map CogentCallTree_name callees)] else []) @
            maps (fn c => case c of
                  FirstOrderCall t => collect_absfuns d t []
                | SecondOrderCall (f, args) => collect_absfuns d f (map snd args) @
                                               maps (fn arg => collect_absfuns d (snd arg) []) args) calls
    in map (fn d => collect_absfuns d tr []) (0 upto depth) end

(* Declare each of the \<xi>_n as a const. *)
fun declare_uabsfuns' _ [] thy  = thy
  | declare_uabsfuns' n (_::defs) thy = let
      val name = "\<xi>_" ^ string_of_int n
      val typ = @{typ "(funtyp, abstyp, ptrtyp) uabsfuns"}
      val ctxt = thy |> Toplevel.theory_toplevel |> Toplevel.context_of
      val (_, thy') = Sign.declare_const ctxt ((Binding.name name, typ) , NoSyn) thy
      in declare_uabsfuns' (n+1) defs thy'
      end

(* Convenience wrapper. *)
fun declare_uabsfuns tr thy =
  make_uabsfuns_defs tr
  |> map (map #2 o filter (fn (funtyp, _, _) => funtyp = AbsFun))
  |> (fn defs => declare_uabsfuns' 0 defs thy)

fun isAutoCorresFunRec ctxt f =
  (Proof_Context.get_thms ctxt (f ^ "'.simps"); true)
  handle ERROR _ => false

(* Manufacture fake corres rules for first-order absfuns. *)
fun generate_FO_absfun_corres (xi:term) ctxt (fname:string) = let
  val abs_rel = Syntax.read_term ctxt "abs_rel"
  val state_rel = Syntax.read_term ctxt "state_rel"
  val Xi = Syntax.read_term ctxt "\<Xi> :: string \<Rightarrow> poly_type"
  val _ = if isAutoCorresFunRec ctxt fname then
            error ("Corres_Tac: expected first-order function call for " ^ quote fname ^ " but it is recursive")
          else ()
  val cfun = Syntax.read_term ctxt (fname ^ "'")
  val prop = @{mk_term "Trueprop (?abs_rel ?Xi ?state_rel ?fname ?xi ?cfun)"
               (abs_rel, Xi, state_rel, fname, xi, cfun)}
              (abs_rel, Xi, state_rel, Utils.encode_isa_string fname, xi, cfun)
             |> strip_type |> Syntax.check_term ctxt
  in
    Goal.prove ctxt [] [] prop (K (Skip_Proof.cheat_tac ctxt 1)) RS Proof_Context.get_thm ctxt "afun_corres"
  end

(* The same, but for (higher-order absfun, callees) pairs. *)
fun generate_HO_absfun_corres (xi:term) ctxt (fname:string) (callees:(term * string) list) min_measure = let
  val corres = Syntax.read_term ctxt "corres"
  val state_rel = Syntax.read_term ctxt "state_rel"
  val Xi = Syntax.read_term ctxt "\<Xi> :: string \<Rightarrow> poly_type"
  val cfun = Syntax.read_term ctxt (fname ^ "'")
  val prop = if isAutoCorresFunRec ctxt fname
    then @{mk_term "\<lbrakk> i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma> ! i = Some (fst (snd (?Xi ?fname))); m \<ge> ?min_m \<rbrakk> \<Longrightarrow>
                    ?corres ?state_rel (App (AFun ?fname []) (Var i))
                            (do x \<leftarrow> ?cfun m v'; gets (\<lambda>s. x) od) ?xi \<gamma> ?Xi \<Gamma> \<sigma> s"
               (corres, Xi, state_rel, fname, xi, cfun, min_m)}
               (corres, Xi, state_rel, Utils.encode_isa_string fname, xi, cfun,
                Int.toString min_measure |> Syntax.read_term ctxt)
    else @{mk_term "\<lbrakk> i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma> ! i = Some (fst (snd (?Xi ?fname))) \<rbrakk> \<Longrightarrow>
                    ?corres ?state_rel (App (AFun ?fname []) (Var i))
                            (do x \<leftarrow> ?cfun v'; gets (\<lambda>s. x) od) ?xi \<gamma> ?Xi \<Gamma> \<sigma> s"
               (corres, Xi, state_rel, fname, xi, cfun)}
               (corres, Xi, state_rel, Utils.encode_isa_string fname, xi, cfun)
  fun callee_assm (getter, callee) = @{mk_term "Trueprop (?getter v' = ?callee_tag)" (getter, callee_tag)}
                                     (getter, Syntax.read_term ctxt ("FUN_ENUM_" ^ callee))
  fun give_xi_type (t as Const (nm, T)) = (if nm = fst (dest_Const Xi) then Xi else t)
    | give_xi_type t = t
  val prop' = map callee_assm callees |> foldr Logic.mk_implies prop
              |> strip_type |> map_aterms give_xi_type |> Syntax.check_term ctxt
  in
    Goal.prove ctxt ["i", "\<gamma>", "\<Gamma>", "v", "v'", "\<sigma>", "s", "m"] [] prop' (K (Skip_Proof.cheat_tac ctxt 1))
  end

fun unfold_abbreviatedType_term ctxt (Const (nm, @{typ "Cogent.type"}))
    = if String.isPrefix "abbreviatedType" (Long_Name.base_name nm)
        then Proof_Context.get_thm ctxt (nm ^ "_def")
            |> safe_mk_meta_eq |> Thm.concl_of |> Logic.dest_equals |> snd |> SOME
        else NONE
  | unfold_abbreviatedType_term _ _ = NONE

(* Generate and prove corres rules for Cogent functions. *)
fun make_FO_fun_corres_prop xi_index ctxt fname min_measure = let
  val read = Syntax.read_term ctxt
  val Xi = read "\<Xi> :: string \<Rightarrow> poly_type"
  fun give_xi_type (t as Const (nm, T)) = (if nm = fst (dest_Const Xi) then Xi else t)
    | give_xi_type t = t
  val cfun = read (fname ^ "'")
  val prop = if isAutoCorresFunRec ctxt fname
    then @{mk_term "\<And>a a' \<sigma> s m. val_rel a a' \<Longrightarrow> m \<ge> ?min_m \<Longrightarrow>
                   ?corres ?state_rel ?cogent (?cfun m a') ?\<xi> [a] ?\<Xi> [Some (fst (snd ?cogent_type))] \<sigma> s"
               (corres, state_rel, cogent, cfun, \<xi>, \<Xi>, cogent_type, min_m)}
               (read "corres", read "state_rel", read fname, cfun,
                read ("\<xi>_" ^ Int.toString xi_index), Xi, read (fname ^ "_type"),
                Int.toString min_measure |> Syntax.read_term ctxt)
    else @{mk_term "\<And>a a' \<sigma> s. val_rel a a' \<Longrightarrow>
                   ?corres ?state_rel ?cogent (?cfun a') ?\<xi> [a] ?\<Xi> [Some (fst (snd ?cogent_type))] \<sigma> s"
               (corres, state_rel, cogent, cfun, \<xi>, \<Xi>, cogent_type)}
               (read "corres", read "state_rel", read fname, cfun,
                read ("\<xi>_" ^ Int.toString xi_index), Xi, read (fname ^ "_type"))
  in prop |> strip_type |> map_aterms give_xi_type |> Syntax.check_term ctxt end

(* Unfold types in corres rules. *)
fun unfold_Cogent_simps ctxt =
  Proof_Context.get_thms ctxt "fst_conv" @
  Proof_Context.get_thms ctxt "snd_conv" @
  Proof_Context.get_thms ctxt "abbreviated_type_defs"
fun unfold_Cogent_types ctxt simps fname thm =
  Local_Defs.unfold ctxt (Proof_Context.get_thms ctxt (fname ^ "_type_def") @ simps) thm

fun mapAccumL _ [] acc = ([], acc)
  | mapAccumL f (x::xs) acc = let val (x', acc') = f x acc
                                   val (xs', acc'') = mapAccumL f xs acc'
                              in (x'::xs', acc'') end

type obligations = (string * FunType * string list * cterm) Symtab.table

fun corres_tree_obligations trs ctxt : obligations = let
  fun descend (CogentCallTree ((xi_index, _), AbsFun, name, [])) tab = let
      val thm_name = name ^ "_corres_" ^ string_of_int xi_index in
      if Symtab.defined tab thm_name then (thm_name, tab) else let
      (* generate a fake corres rule and for interesting reasons throw it away *)
        val x = generate_FO_absfun_corres (Syntax.read_term ctxt ("\<xi>_" ^ string_of_int xi_index)) ctxt name
                |> forall_intr_vars
        in tracing ("  adding thm " ^ thm_name);
          (thm_name, Symtab.update (thm_name, (name, AbsFun, [], Thm.cprop_of x)) tab) end end
    | descend (CogentCallTree ((xi_index, min_measure), CogentFun, name, callees)) tab = let
      (* Calls to CogentFuns, which we should prove. *)
        val thm_name = name ^ "_corres_" ^ string_of_int xi_index
      in if Symtab.defined tab thm_name then (thm_name, tab) else let
        val (callee_nms, tab) = mapAccumL (fn c => fn tab => case c of
                FirstOrderCall f => descend f tab
              | SecondOrderCall (f as CogentCallTree ((fxi_index, fmin_measure), AbsFun, fname, []), args) => let
                  (* Second-order AbsFun calls are specialised to their callees. *)
                  val nm = (space_implode "_" (fname::map (CogentCallTree_name o snd) args)
                      ^ "_corres_" ^ string_of_int fxi_index)
                  in if Symtab.defined tab nm then (nm, tab) else let
                    val tab = fold (snd oo descend) (map snd args) tab
                    val f_thm = generate_HO_absfun_corres (Syntax.read_term ctxt ("\<xi>_" ^ string_of_int fxi_index))
                                                   ctxt fname (map (apsnd CogentCallTree_name) args) fmin_measure
                                |> forall_intr_vars
                    in tracing ("  adding thm " ^ nm);
                       (nm, Symtab.update (nm, (fname, AbsFun, [], Thm.cprop_of f_thm)) tab) end end
              | tr' => raise TERM ("descend: callees: tr': " ^ @{make_string} tr', [])
              ) callees tab
        val prop = make_FO_fun_corres_prop xi_index ctxt name min_measure
        val _ = tracing ("  adding thm " ^ thm_name)
        in (thm_name, Symtab.update (thm_name, (name, CogentFun, callee_nms, Thm.cterm_of ctxt prop)) tab) end end
      | descend tr' _ = raise TERM ("descend: tr': " ^ @{make_string} tr', [])

  val tab = fold (snd oo descend o snd) (Symtab.dest trs) Symtab.empty
  in tab end

fun corres_tac_driver corres_tac typing_tree_of ctxt (tab : obligations) thm_name
  = case Symtab.lookup tab thm_name of SOME (fname, CogentFun, assums, prop) => let
    val lookup_assums = map (Symtab.lookup tab #> the) assums
    val (callee_info, callee_abs_info) = lookup_assums
        |> partition (fn v => #2 v = CogentFun)
    val (callee_names, callee_abs_names) = (callee_info, callee_abs_info) |> apply2 (map #1)
    val (callee_thm_props, callee_abs_thm_props) = (callee_info, callee_abs_info) |> apply2 (map #4)

    val type_unfold_simps = unfold_Cogent_simps ctxt

    val fun_defs = Proof_Context.get_thms ctxt (fname ^ "_def") @
                   Proof_Context.get_thms ctxt (fname ^ "'_def'") @
                   Proof_Context.get_thms ctxt (fname ^ "_type_def") @
                   type_unfold_simps
    val _ = @{trace} ("corres_tac_driver: Proving " ^ thm_name,
        { prop = prop, callee_props = callee_thm_props,
            callee_abs_props = callee_abs_thm_props })

  in Goal.prove ctxt []
        (map Thm.term_of (callee_thm_props @ callee_abs_thm_props))
            (Thm.term_of prop)
    (fn args => let
        val callee_thms = take (length callee_thm_props) (#prems args) ~~ callee_names
                          |> map (fn (assum, name) => unfold_Cogent_types ctxt type_unfold_simps name assum)
        val callee_abs_thms = drop (length callee_thm_props) (#prems args) ~~ callee_abs_names
                          |> map (fn (assum, name) => assum |> simp_xi_fully_applied ctxt |> unfold_Cogent_types ctxt type_unfold_simps name)
        val _ = @{trace} ("Assumptions for " ^ thm_name, callee_thms, callee_abs_thms)
      in corres_tac (#context args) (peel_two (typing_tree_of fname))
         fun_defs callee_abs_thms callee_thms
      end)
  end
  | SOME (_, AbsFun, [], _) => @{thm TrueI}
  | v => error ("corres_tac_driver: tab contents: " ^ thm_name ^ ": " ^ @{make_string} v)

fun finalise (tab : obligations) ctxt thm_tab = let
    fun to_rsn NONE = Thm.trivial (Thm.global_cterm_of @{theory} @{schematic_term "?P :: prop"})
      | to_rsn (SOME thm) = thm

    fun cleanup thm = thm
        |> (ALLGOALS val_rel_thin_tac
            THEN prune_params_tac ctxt
            THEN distinct_subgoals_tac)
        |> Seq.hd

    fun inner nm ftab =
     case Symtab.lookup ftab nm of SOME thm => (thm, ftab)
      | NONE => let
        val _ = tracing ("finalise: " ^ nm)
        val assum_nms = Symtab.lookup tab nm |> the |> #3
        val (concr_assums, abs_assums) = partition (fn n => CogentFun = (Symtab.lookup tab n |> the |> #2)) assum_nms
        val assum_nms = concr_assums @ abs_assums
        val thm = Symtab.lookup thm_tab nm |> the
        val (assums, ftab) = mapAccumL inner assum_nms ftab
        val rthm = case thm of NONE => NONE
          | SOME t => if Thm.eq_thm (t, @{thm TrueI}) then NONE
            else SOME ((map to_rsn assums MRS gen_all (Variable.maxidx_of ctxt) t) |> cleanup)
      in (rthm, Symtab.update (nm, rthm) ftab) end

  in fold (snd oo inner) (Symtab.keys tab) Symtab.empty end

fun all_corres_goals corres_tac typing_tree_of time_limit ctxt (tab : obligations) =
  let
    val tl = Time.fromSeconds time_limit
    fun run_tac nm = corres_tac_driver corres_tac typing_tree_of ctxt tab nm
                   handle ERROR x => (tracing ("Failed: " ^ nm ^ " with error:\n" ^ x); raise ERROR x)
    fun driver nm = Timing.timing (try (Timeout.apply tl
            run_tac)) nm
        |> (fn (dur, res) => (tracing ("Time for " ^ nm ^ ": " ^ Timing.message dur); res))
        |> (fn NONE => (tracing ("Failed: " ^ nm); (nm, NONE))
             | SOME thm => (tracing ("Succeeded: " ^ nm); (nm, SOME thm)))
    val res = Par_List.map driver (Symtab.keys tab)
    val thm_tab = Symtab.make res
  in thm_tab end

(* Top-level driver that attempts to prove a CogentCallTree.
 * For each function in the tree, it proves a corres theorem and assigns a standard name.
 * If a theorem by that name already exists, that is used instead.
 *
 * The naming scheme is: <fun>_[<funarg1>_<funarg2>_...]_corres_<xi_index>
 * Eg. for f called with function arguments g and h: f_g_h_corres_1
 * These names can be obtained using callee_corres_thms.
 *
 * Known issues:
 *  - Does not handle C recursion guards.
 *  - Does not handle higher-order CogentFuns.
 *  - Should be parallelised.
 *)
fun corres_tree tr typing_tree_of corres_tac run_proofs skip_initial time_limit ctxt = let
  fun cache_proof ctxt thm_name (make_thms : unit -> thm list) =
    (Proof_Context.get_thms ctxt thm_name, ctxt)
    handle ERROR _ =>
      Utils.define_lemmas thm_name (make_thms ()) ctxt

  fun mapAccumL _ [] acc = ([], acc)
    | mapAccumL f (x::xs) acc = let val (x', acc') = f x acc
                                    val (xs', acc'') = mapAccumL f xs acc'
                                in (x'::xs', acc'') end

  val type_unfold_simps = unfold_Cogent_simps ctxt

  val skip_ctr = Unsynchronized.ref skip_initial
  val failed_proofs = Unsynchronized.ref []

  fun descend (CogentCallTree (xi_index, AbsFun, name, [])) ctxt = let
      (* Simple AbsFun calls. Higher-order calls are handled elsewhere. *)
        val (thm, ctxt) =
          cache_proof ctxt (name ^ "_corres_" ^ string_of_int xi_index) (fn () =>
            [generate_FO_absfun_corres (Syntax.read_term ctxt ("\<xi>_" ^ string_of_int xi_index)) ctxt name
             |> unfold_Cogent_types ctxt type_unfold_simps name])
        in (CogentCallTree ((xi_index, thm), AbsFun, name, []), ctxt) end
    | descend (CogentCallTree (xi_index, CogentFun, name, callees)) ctxt = let
      (* Calls to CogentFuns, which we should prove. *)
        val (callees', ctxt) = mapAccumL (fn c => fn ctxt => case c of
                FirstOrderCall f => descend f ctxt |> apfst FirstOrderCall
              | SecondOrderCall (f as CogentCallTree (fxi_index, AbsFun, fname, []), args) => let
                  (* Second-order AbsFun calls are specialised to their callees. *)
                  val (args', ctxt) = mapAccumL descend (map snd args) ctxt
                  val (f_thm, ctxt) = cache_proof ctxt
                        (space_implode "_" (fname::map (CogentCallTree_name o snd) args) ^ "_corres_" ^ string_of_int fxi_index)
                        (fn () => [generate_HO_absfun_corres (Syntax.read_term ctxt ("\<xi>_" ^ string_of_int fxi_index))
                                                             ctxt fname (map (apsnd CogentCallTree_name) args) 42
                                   |> unfold_Cogent_types ctxt type_unfold_simps fname])
                  in (SecondOrderCall (CogentCallTree ((fxi_index, f_thm), AbsFun, fname, []), map fst args ~~ args'), ctxt) end)
              callees ctxt
        val thm_name = name ^ "_corres_" ^ string_of_int xi_index
        val _ = if !skip_ctr > 0 then @{trace} ("skipping " ^ string_of_int (!skip_ctr) ^ " more") else ()
        val run_proofs = run_proofs andalso !skip_ctr <= 0
        val _ = (skip_ctr := !skip_ctr-1)
        val (thm, ctxt) =
          cache_proof ctxt thm_name (fn () => let
            (* Warning: actual proofs ahead. *)
            val corres = Syntax.read_term ctxt "corres"
            val fun_term = Syntax.read_term ctxt name
            val fun_type = Syntax.read_term ctxt (name ^ "_type")
            val fun_c = Syntax.read_term ctxt (name ^ "'")
            val state_rel = Syntax.read_term ctxt "state_rel"
            val xi = Syntax.read_term ctxt ("\<xi>_" ^ string_of_int xi_index)
            val Xi = Syntax.read_term ctxt "\<Xi> :: string \<Rightarrow> poly_type"
            val prop = @{mk_term "\<And>a a' \<sigma> s. val_rel a a' \<Longrightarrow> ?corres ?state_rel ?fun_term (?fun_c a') ?xi [a] ?Xi
                                                                       [Some (fst (snd ?fun_type))] \<sigma> s"
                         (corres, state_rel, fun_term, fun_c, xi, Xi, fun_type)}
                         (corres, state_rel, fun_term, fun_c, xi, Xi, fun_type)
                       |> strip_type |> Syntax.check_term ctxt
            val (callee_thms, callee_abs_thms) = callees'
                  |> map (fn call => case call of FirstOrderCall f => f
                                                | SecondOrderCall (f, _) => f)
                  |> partition (fn tr => CogentCallTree_funtype tr = CogentFun)
                  |> apply2 (map (CogentCallTree_data #> snd))
            val (callee_thms, callee_abs_thms) = (List.concat callee_thms, List.concat callee_abs_thms)

            val fun_defs = Proof_Context.get_thms ctxt (name ^ "_def") @
                           Proof_Context.get_thms ctxt (name ^ "'_def'") @
                           Proof_Context.get_thms ctxt (name ^ "_type_def") @
                           type_unfold_simps
            val _ = @{trace} ("cogent_corres_tree: " ^ (if run_proofs then "Proving " else "Skipping ") ^ thm_name,
                              { prop = Thm.cterm_of ctxt prop,
                                callees = callees
                                          |> map (fn call => case call of FirstOrderCall f => f
                                                                        | SecondOrderCall (f, _) => f)
                                          |> map CogentCallTree_name |> commas })
            fun fallback_thm msg = (warning ("Failed to prove " ^ thm_name ^ "; error: " ^ msg);
                                    failed_proofs := thm_name :: !failed_proofs;
                                    Goal.prove ctxt [] [] prop (K (Skip_Proof.cheat_tac ctxt 1)))
            val (time, thms) = (fn f => Timing.timing f ()) (fn () =>
                 [(Timeout.apply (Time.fromSeconds time_limit) (fn () =>
                   (((((Goal.prove ctxt [] [] prop (fn {context, prems} =>
                     if not run_proofs then Skip_Proof.cheat_tac ctxt 1 else
                        (corres_tac context (peel_two (typing_tree_of name)) fun_defs
                                    callee_abs_thms callee_thms))
                 handle Bind => fallback_thm (@{make_string} Bind))
                 handle Match => fallback_thm (@{make_string} Match))
                 handle Option => fallback_thm (@{make_string} Option))
                 handle THM t => fallback_thm (@{make_string} (THM t)))
                 handle TERM t => fallback_thm (@{make_string} (TERM t)))
                 handle ERROR e => fallback_thm (@{make_string} (ERROR e))) ()
                 handle Timeout.TIMEOUT t => fallback_thm (@{make_string} (Timeout.TIMEOUT t)))
                |> unfold_Cogent_types ctxt type_unfold_simps name])
            val _ = tracing ("Time for " ^ thm_name ^ ": " ^ Timing.message time)
          in thms end)
        in (CogentCallTree ((xi_index, thm), CogentFun, name, callees'), ctxt) end

  val (tr', ctxt) = descend tr ctxt
  val _ = if null (!failed_proofs) then () else warning ("Failed proofs: " ^ commas_quote (!failed_proofs))
  in (tr', ctxt) end

(* Convenience function for getting the expected corres thm names. *)
fun callee_corres_thms (CogentCallTree (_, _, _, callees)) = callees
      |> map (fn call => case call of
                 FirstOrderCall f => (f, CogentCallTree_name f ^ "_corres_" ^ string_of_int (CogentCallTree_data f))
               | SecondOrderCall (f, args) => (f, space_implode "_" (map CogentCallTree_name (f :: map snd args)) ^
                                                  "_corres_" ^ string_of_int (CogentCallTree_data f)))
                  |> partition (fn (tr, _) => CogentCallTree_funtype tr = CogentFun)
                  |> apply2 (map snd)

(* Assign AutoCorres recursion measures.
 * Each second-order function call involves a trip to the dispatcher,
 * meaning that the measure decreases by 2 instead of 1. *)
fun calc_call_measure tr = maximum (1 :: map calc_call_order_measure (CogentCallTree_calls tr))
and calc_call_order_measure (FirstOrderCall f) = 1 + calc_call_measure f
  | calc_call_order_measure (SecondOrderCall (f, args)) =
       1 + max (maximum (map (calc_call_measure o snd) args) + 2) (calc_call_measure f)

fun annotate_measure tr = let
  fun annotate' d (CogentCallTree (x, ty, name, calls)) = let
    in CogentCallTree ((x, d), ty, name, map (annotate_call' d) calls) end
  and annotate_call' d (FirstOrderCall f) = FirstOrderCall (annotate' (d-1) f)
    | annotate_call' d (SecondOrderCall (f, args)) =
        SecondOrderCall (annotate' (d-1) f, map (apsnd (annotate' (d-3))) args)
  in annotate' (calc_call_measure tr) tr end

fun map_annotations f (CogentCallTree (a, ty, name, calls)) =
      CogentCallTree (f a, ty, name, calls |>
        map (fn c => case c of FirstOrderCall a => FirstOrderCall (map_annotations f a)
                             | SecondOrderCall (a, bs) =>
                                 SecondOrderCall (map_annotations f a, map (apsnd (map_annotations f)) bs)))
\<close>

end
