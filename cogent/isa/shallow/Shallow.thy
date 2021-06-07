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

theory Shallow
imports
  "Cogent.ValueSemantics"
  ShallowUtil
begin

type_synonym funtyp = "char list"

inductive_cases v_sem_letE: "\<xi> , \<gamma> \<turnstile> Let a b \<Down> b'"
inductive_cases v_sem_letBangE: "\<xi> , \<gamma> \<turnstile> LetBang vs a b \<Down> b'"
inductive_cases v_sem_litE: "\<xi> , \<gamma> \<turnstile> Lit l \<Down> v"
inductive_cases v_sem_primE: "\<xi> , \<gamma> \<turnstile> Prim p as \<Down> r"
inductive_cases v_sem_memberE: "\<xi> , \<gamma> \<turnstile> Member x f \<Down> r"
inductive_cases v_sem_tupleE: "\<xi> , \<gamma> \<turnstile> Tuple a b \<Down> r"
inductive_cases v_sem_if: " \<xi> , \<gamma> \<turnstile> If x t e \<Down> r"
inductive_cases v_sem_conE: "\<xi> , \<gamma> \<turnstile> Con i t x \<Down> r"
inductive_cases v_sem_esacE: "\<xi>, \<gamma> \<turnstile> Esac v  n \<Down> r"
inductive_cases v_sem_caseE:  "\<xi> , \<gamma> \<turnstile> Case x c m n \<Down> r"
inductive_cases v_sem_splitE: "\<xi> , \<gamma> \<turnstile> Split x e \<Down> e'"
inductive_cases v_sem_takeE: "\<xi> , \<gamma> \<turnstile> Take x f e \<Down> e'"
inductive_cases v_sem_putE: "\<xi> , \<gamma> \<turnstile> Put x f e \<Down> e'"
inductive_cases v_sem_castE: "\<xi> , \<gamma> \<turnstile> Cast \<tau> e \<Down> e'"
inductive_cases v_sem_structE: "\<xi> , \<gamma> \<turnstile> Struct ns ts xs \<Down> e'"
inductive_cases v_sem_AppE: "\<xi> , \<gamma> \<turnstile> App f v \<Down> e'"
inductive_cases v_sem_allE: "\<xi> , \<gamma> \<turnstile>* es \<Down> es'"
inductive_cases v_sem_all_NilE: "\<xi> , \<gamma> \<turnstile>* [] \<Down> es'"
inductive_cases v_sem_all_ConsE: "\<xi> , \<gamma> \<turnstile>* (e#es) \<Down> es'"
inductive_cases v_sem_unitE: "\<xi> , \<gamma> \<turnstile> Unit \<Down> r"
inductive_cases v_sem_promoteE: "\<xi>, \<gamma> \<turnstile> Promote \<tau> e \<Down> r"

lemmas v_sem_elims =
  v_sem_letE
  v_sem_letBangE
  v_sem_litE
  v_sem_primE
  v_sem_memberE
  v_sem_tupleE
  v_sem_if
  v_sem_conE
  v_sem_esacE
  v_sem_caseE
  v_sem_splitE
  v_sem_takeE
  v_sem_putE
  v_sem_castE
  v_sem_structE
  v_sem_AppE
  v_sem_allE
  v_sem_all_NilE
  v_sem_all_ConsE
  v_sem_unitE
  v_sem_promoteE

(* Should we use type class here, instead of using "defs (overloaded)"?
 * Christine's approach with type class looks more systematic.*)
consts valRel :: "(funtyp,'b) vabsfuns \<Rightarrow> 'a \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
overloading
 valRel_bool  \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> bool \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
 valRel_u8    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 8 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
 valRel_u16   \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 16 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
 valRel_u32   \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 32 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
 valRel_u64   \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 64 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
 valRel_unit  \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> unit \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
 valRel_pair  \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 'x \<times> 'y \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
 valRel_fun   \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
begin

fun valRel_bool :: "(funtyp,'b) vabsfuns \<Rightarrow> bool \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_bool \<xi> b v = (v = (vval.VPrim (LBool b)))"

fun valRel_u8 :: "(funtyp,'b) vabsfuns \<Rightarrow> 8 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u8 \<xi> w v = (v = vval.VPrim (LU8 w))"

fun valRel_u16 :: "(funtyp,'b) vabsfuns \<Rightarrow> 16 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u16 \<xi> w v = (v = vval.VPrim (LU16 w))"

fun valRel_u32 :: "(funtyp,'b) vabsfuns \<Rightarrow> 32 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u32 \<xi> w v = (v = vval.VPrim (LU32 w))"

fun valRel_u64 :: "(funtyp,'b) vabsfuns \<Rightarrow> 64 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u64 \<xi> w v = (v = vval.VPrim (LU64 w))"

fun valRel_unit :: "(funtyp,'b) vabsfuns \<Rightarrow> unit \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_unit \<xi> w v = (v = vval.VUnit)"

fun valRel_pair :: "(funtyp,'b) vabsfuns \<Rightarrow> 'x \<times> 'y \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_pair \<xi> p v = (\<exists> va vb. v = (vval.VProduct va vb) \<and> valRel \<xi> (fst p) va \<and> valRel \<xi> (snd p) vb)"

fun valRel_fun :: "(funtyp,'b) vabsfuns \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_fun \<xi> f f' =
((\<exists>e ts. f' = VFunction e ts \<and>
          (\<forall>x x' v'. valRel \<xi> x x' \<longrightarrow> (\<xi>, [x'] \<turnstile> specialise ts e \<Down> v') \<longrightarrow> valRel \<xi> (f x) v')) \<or>
  (\<exists>afun ts. f' = VAFunction afun ts \<and> (\<forall>x x' v'. valRel \<xi> x x' \<longrightarrow> \<xi> afun x' v' \<longrightarrow> valRel \<xi> (f x) v')))"

end

context value_sem
begin

text {* Shallow & deep embedding correspondence:
  deep embedding is a refinement of the shallow representation
*}
definition
  scorres :: "'s \<Rightarrow> (funtyp) expr \<Rightarrow> (funtyp,'a) vval env \<Rightarrow> (funtyp,'a) vabsfuns \<Rightarrow> bool"
where
  "scorres s d \<gamma> \<xi> \<equiv> (\<forall>r. (\<xi>, \<gamma> \<turnstile> d \<Down> r) \<longrightarrow> valRel \<xi> s r)"

(* Mechanism to pattern-match on shallow variables. *)
definition "shallow_tac__var x \<equiv> x"


text {* Straightforward rules. *}

lemma scorres_var:
  "valRel \<xi> s (\<gamma>!i) \<Longrightarrow> scorres (shallow_tac__var s) (Var i) \<gamma> \<xi>"
  unfolding scorres_def shallow_tac__var_def
  by fastforce

lemma scorres_unit:
  "scorres (u::unit) Unit \<gamma> \<xi>"
  by (clarsimp simp: scorres_def elim!: v_sem_elims)

lemma scorres_promote:
assumes "scorres x x' \<gamma> \<xi>"
shows "scorres x(Promote ts x') \<gamma> \<xi>"
  using assms
by (clarsimp simp:scorres_def elim!:v_sem_elims)

lemma scorres_let_desugar:
assumes
  "scorres v a \<gamma> \<xi>"
  "\<And>v' a'. valRel \<xi> v' a' \<Longrightarrow> scorres (s (shallow_tac__var v')) b (a'#\<gamma>) \<xi>"
shows
  "scorres (Let\<^sub>d\<^sub>s v s) (expr.Let a b) \<gamma> \<xi>"
  using assms
  by (auto simp:Let\<^sub>d\<^sub>s_def scorres_def shallow_tac__var_def elim!: v_sem_elims)

lemma scorres_let:
assumes
  "scorres v a \<gamma> \<xi>"
  "\<And>v' a'. valRel \<xi> v' a' \<Longrightarrow> scorres (s (shallow_tac__var v')) b (a'#\<gamma>) \<xi>"
shows
  "scorres (HOL.Let v s) (expr.Let a b) \<gamma> \<xi>"
  using assms
  by (auto simp: scorres_def shallow_tac__var_def elim!: v_sem_elims)

lemma scorres_letBang_desugar:
assumes
  "scorres v a \<gamma> \<xi>"
  "\<And>v' a'. valRel \<xi> v' a' \<Longrightarrow> scorres (s (shallow_tac__var v')) b (a'#\<gamma>) \<xi>"
shows
  "scorres (Let\<^sub>d\<^sub>s v s) (expr.LetBang vs a b) \<gamma> \<xi>"
  using assms
  by (auto simp: scorres_def Let\<^sub>d\<^sub>s_def shallow_tac__var_def elim!: v_sem_elims)

lemma scorres_letBang:
assumes
  "scorres v a \<gamma> \<xi>"
  "\<And>v' a'. valRel \<xi> v' a' \<Longrightarrow> scorres (s (shallow_tac__var v')) b (a'#\<gamma>) \<xi>"
shows
  "scorres (HOL.Let v s) (expr.LetBang vs a b) \<gamma> \<xi>"
  using assms
  by (auto simp: scorres_def shallow_tac__var_def elim!: v_sem_elims)

lemma scorres_if:
  assumes a: "scorres a a' \<gamma> \<xi>"
  assumes b: "scorres b b' \<gamma> \<xi>"
  assumes c: "scorres c c' \<gamma> \<xi>"
  shows "scorres (if a then b else c) (If a' b' c') \<gamma> \<xi>"
  using a b c
  by (fastforce simp: scorres_def elim!: v_sem_if split: if_splits)

lemma scorres_fun:
  (* Must match format for callee theorems. *)
  assumes "\<And>v v'. valRel \<xi> v v' \<Longrightarrow> scorres (f v) (specialise ts f') [v'] \<xi>"

  shows "scorres f (Fun f' ts) \<gamma> \<xi>"
  using assms
  by (auto simp: scorres_def elim!: v_sem_elims)


text {* Cumbersome rules for numbers and bools. *}

lemma scorres_lit:
  "\<And>b b'. b = b' \<Longrightarrow> scorres b (Lit (LBool b')) \<gamma> \<xi>"
  "\<And>w w'. w = w' \<Longrightarrow> scorres w (Lit (LU8 w')) \<gamma> \<xi>"
  "\<And>w w'. w = w' \<Longrightarrow> scorres w (Lit (LU16 w')) \<gamma> \<xi>"
  "\<And>w w'. w = w' \<Longrightarrow> scorres w (Lit (LU32 w')) \<gamma> \<xi>"
  "\<And>w w'. w = w' \<Longrightarrow> scorres w (Lit (LU64 w')) \<gamma> \<xi>"
  by (auto simp: scorres_def elim: v_sem_litE)

lemma scorres_prim_add:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x + y :: 8  word) (Prim (Plus U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x + y :: 16 word) (Prim (Plus U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x + y :: 32 word) (Prim (Plus U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x + y :: 64 word) (Prim (Plus U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_sub:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x - y :: 8  word) (Prim (Minus U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x - y :: 16 word) (Prim (Minus U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x - y :: 32 word) (Prim (Minus U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x - y :: 64 word) (Prim (Minus U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_times:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x * y :: 8  word) (Prim (Times U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x * y :: 16 word) (Prim (Times U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x * y :: 32 word) (Prim (Times U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x * y :: 64 word) (Prim (Times U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_divide:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_div x y :: 8  word) (Prim (Divide U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_div x y :: 16 word) (Prim (Divide U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_div x y :: 32 word) (Prim (Divide U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_div x y :: 64 word) (Prim (Divide U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_mod:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_mod x y :: 8  word) (Prim (Mod U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_mod x y :: 16 word) (Prim (Mod U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_mod x y :: 32 word) (Prim (Mod U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_mod x y :: 64 word) (Prim (Mod U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_not:
  "scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres (\<not> x) (Prim Not [x']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)

lemma scorres_prim_and:
  "scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x \<and> y) (Prim And [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)

lemma scorres_prim_or:
  "scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x \<or> y) (Prim Or [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)

lemma scorres_prim_gt:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) > y) (Prim (Gt U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) > y) (Prim (Gt U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) > y) (Prim (Gt U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) > y) (Prim (Gt U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_ge:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) \<ge> y) (Prim (Ge U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) \<ge> y) (Prim (Ge U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) \<ge> y) (Prim (Ge U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) \<ge> y) (Prim (Ge U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_lt:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) < y) (Prim (Lt U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) < y) (Prim (Lt U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) < y) (Prim (Lt U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) < y) (Prim (Lt U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_le:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) \<le> y) (Prim (Le U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) \<le> y) (Prim (Le U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) \<le> y) (Prim (Le U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) \<le> y) (Prim (Le U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_eq:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) = y) (Prim (Eq (Num U8 )) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) = y) (Prim (Eq (Num U16)) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) = y) (Prim (Eq (Num U32)) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) = y) (Prim (Eq (Num U64)) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: bool   ) = y) (Prim (Eq Bool     ) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_neq:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) \<noteq> y) (Prim (NEq (Num U8 )) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) \<noteq> y) (Prim (NEq (Num U16)) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) \<noteq> y) (Prim (NEq (Num U32)) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) \<noteq> y) (Prim (NEq (Num U64)) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: bool   ) \<noteq> y) (Prim (NEq Bool     ) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_bitand:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) AND y) (Prim (BitAnd U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) AND y) (Prim (BitAnd U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) AND y) (Prim (BitAnd U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) AND y) (Prim (BitAnd U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_bitor:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) OR y) (Prim (BitOr U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) OR y) (Prim (BitOr U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) OR y) (Prim (BitOr U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) OR y) (Prim (BitOr U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_bitxor:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) XOR y) (Prim (BitXor U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) XOR y) (Prim (BitXor U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) XOR y) (Prim (BitXor U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) XOR y) (Prim (BitXor U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_lshift:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_shift shiftl (x :: 8  word) y) (Prim (LShift U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_shift shiftl (x :: 16 word) y) (Prim (LShift U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_shift shiftl (x :: 32 word) y) (Prim (LShift U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_shift shiftl (x :: 64 word) y) (Prim (LShift U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_rshift:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_shift shiftr (x :: 8  word) y) (Prim (RShift U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_shift shiftr (x :: 16 word) y) (Prim (RShift U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_shift shiftr (x :: 32 word) y) (Prim (RShift U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_shift shiftr (x :: 64 word) y) (Prim (RShift U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_complement:
  "\<And>x x'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres (NOT (x::8  word)) (Prim (Complement U8 ) [x']) \<gamma> \<xi>"
  "\<And>x x'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres (NOT (x::16 word)) (Prim (Complement U16) [x']) \<gamma> \<xi>"
  "\<And>x x'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres (NOT (x::32 word)) (Prim (Complement U32) [x']) \<gamma> \<xi>"
  "\<And>x x'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres (NOT (x::64 word)) (Prim (Complement U64) [x']) \<gamma> \<xi>"
  by (auto elim!: v_sem_elims simp: scorres_def eval_prim_def)

lemma scorres_cast:
  "\<And>x x'. scorres (x :: 8  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 8  word) (Cast U8  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 8  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 16 word) (Cast U16 x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 8  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (Cast U32 x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 8  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (Cast U64 x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 16 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 16 word) (Cast U16 x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 16 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (Cast U32 x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 16 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (Cast U64 x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (Cast U32 x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (Cast U64 x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (Cast U64 x') \<gamma> \<xi>"
  by (auto simp: scorres_def ucast_id elim!: v_sem_elims)


text {* Rules for records and sums. *}

definition
  (* we pass \<xi> to fix the hidden type variables *)
  "shallow_tac_rec_field \<xi> field_name field_update field_num \<equiv>
     (\<forall>rec fs v v'.
        (valRel \<xi> rec (VRecord fs) \<longrightarrow> valRel \<xi> (field_name rec) (fs ! field_num))
        \<and>
        (valRel \<xi> v v' \<longrightarrow> valRel \<xi> rec (VRecord fs) \<longrightarrow>
         valRel \<xi> (field_update (\<lambda>_. v) rec) (VRecord (fs[field_num := v']))))"

lemma shallow_tac_rec_fieldI:
  assumes
    "\<And>rec fs. valRel \<xi> rec (VRecord fs) \<Longrightarrow> valRel \<xi> (field_name rec) (fs ! field_num)"
    "\<And>rec v fs v'.
        valRel \<xi> v v' \<Longrightarrow> valRel \<xi> rec (VRecord fs) \<Longrightarrow>
        valRel \<xi> (field_update (\<lambda>_. v) rec) (VRecord (fs[field_num := v']))"
  shows "shallow_tac_rec_field \<xi> field_name field_update field_num"
  using assms by (simp add: shallow_tac_rec_field_def)

lemma scorres_take:
assumes
  "shallow_tac_rec_field \<xi> field field_upd field'" (* first *)

  "scorres rec rec' \<gamma> \<xi>"
  "\<And>(rec :: 'rec) rec' v v'.
      valRel \<xi> rec rec' \<Longrightarrow> valRel \<xi> v v' \<Longrightarrow>
      scorres (cont (shallow_tac__var v) (shallow_tac__var rec))
              cont' (v' # rec' # \<gamma>) \<xi>"
shows
  "scorres (HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t rec field) (case_prod cont)) (Take rec' field' cont') \<gamma> \<xi>"
  using assms
  by (fastforce simp: scorres_def shallow_tac_rec_field_def shallow_tac__var_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def elim!: v_sem_elims)

lemma scorres_member:
assumes
  "shallow_tac_rec_field \<xi> field field_upd field'" (* first *)

  "scorres rec rec' \<gamma> \<xi>"
shows
  "scorres (field rec) (Member rec' field') \<gamma> \<xi>"
  using assms
  by (fastforce simp: scorres_def shallow_tac_rec_field_def elim!: v_sem_elims)

lemma scorres_put:
assumes
  "shallow_tac_rec_field \<xi> field field_upd field'" (* first *)

  "scorres rec rec' \<gamma> \<xi>"
  "scorres v v' \<gamma> \<xi>"
shows
  "scorres (field_upd (\<lambda>_. v) rec) (Put rec' field' v') \<gamma> \<xi>"
  using assms
  by (fastforce simp: scorres_def shallow_tac_rec_field_def shallow_tac__var_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def elim!: v_sem_elims)

lemmas scorres_simple_step =
  scorres_unit
  scorres_if
  scorres_let
  scorres_let_desugar
  scorres_letBang
  scorres_letBang_desugar
  scorres_cast
  scorres_prim_add
  scorres_prim_sub
  scorres_prim_times
  scorres_prim_divide
  scorres_prim_mod
  scorres_prim_and
  scorres_prim_or
  scorres_prim_not
  scorres_prim_eq
  scorres_prim_neq
  scorres_prim_gt
  scorres_prim_ge
  scorres_prim_lt
  scorres_prim_le
  scorres_prim_bitand
  scorres_prim_bitor
  scorres_prim_complement
  scorres_prim_bitxor
  scorres_prim_lshift
  scorres_prim_rshift
  scorres_promote


text {* NB: compiler expected to supply rules for: Struct, Promote, Con, Case, Esac *}

text {* Rule templates. *}
lemma scorres_con:
assumes
  "scorres x x' \<gamma> \<xi>" (* first *)

  "\<And>x x'. valRel \<xi> x x' \<Longrightarrow> valRel \<xi> (tcon x) (VSum tag x')"
shows
  "scorres (tcon x) (Con ts tag x') \<gamma> \<xi>"
  using assms
  by (clarsimp simp: scorres_def elim!: v_sem_elims)

lemma scorres_app:
  assumes "scorres f f' \<gamma> \<xi>" (* first *)
  assumes "scorres v v' \<gamma> \<xi>"
  shows "scorres (f v) (App f' v') \<gamma> \<xi>"
  using assms
  by (auto elim!: v_sem_elims simp: scorres_def shallow_tac__var_def)


(* these rules are currently unused *)
lemma scorres_split:
  "scorres v x \<gamma> \<xi> \<Longrightarrow>
   (\<And>a b a' b'. valRel \<xi> a a' \<Longrightarrow> valRel \<xi> b b' \<Longrightarrow>
                 scorres (s (shallow_tac__var a) (shallow_tac__var b)) e (a'#b'#\<gamma>) \<xi>) \<Longrightarrow>
   scorres (case v of (a, b) \<Rightarrow> s a b) (Split x e) \<gamma> \<xi>"
  unfolding scorres_def shallow_tac__var_def
  by (cases v) (auto simp: scorres_def elim!: v_sem_elims)

lemma scorres_tuple:
  assumes "scorres a a' \<gamma> \<xi>"
  assumes "scorres b b' \<gamma> \<xi>"
  shows "scorres (a, b) (Tuple a' b') \<gamma> \<xi>"
  using assms
  by (auto simp: scorres_def elim!: v_sem_tupleE)

end

end
