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

theory CogentHigherOrder imports
  "Cogent.TypeProofGen"
  "AutoCorres.AutoCorres"
begin

(*
 * Abstract semantics for guessing function arguments to higher-order function calls.
 * These semantics only work when the hofun and funarg are hardcoded in the function
 * that contains the hofun call site.
 *
 * Example:
 *   -- previously defined
 *   funarg x = ...
 *   hofun (f, x, n) = ...
 *
 *   -- hofun-funarg call can be inferred correctly
 *   f x = let args = (funarg, x, 42)
 *         in hofun args
 *
 *   -- multiple (all hardcoded) funargs can be detected inside compound values
 *   f = hofun2 ((funarg1, x), (y, z), Some funarg2)
 *
 *   -- fails: funarg isn't statically known
 *   f funarg = hofun (funarg, 0, 42)
 *
 *  -- also fails: farg's value isn't (syntactically) hardcoded
 *   f x = let farg = if true then funarg else funarg
 *         in hofun (farg, x, 42)
 *)

type_synonym 'f FunCall = "('f, 'f expr) sum"

(*
 * Function value annotations for Cogent values.
 * An InValue lists known function pointers inside a Cogent value and their locations.
 * Each "InData list" contains information about one part of the value, ending in
 * an IsFunction that specifies the function name.
 * (Eg. if nothing is known about a Cogent value, its Invalue is [].)
 *)
datatype 'f  InData = InProduct nat
                    | InRecord nat
                    | InSum string (* tag name; used by make_HO_call_hints *)
                    | IsFunction "'f FunCall"

type_synonym 'f InValue = "'f InData list list"

primrec InValue_of where
  "InValue_of None = []"
| "InValue_of (Some tv) = snd tv"

fun unzip :: "('a \<times> 'b) list \<Rightarrow> 'a list \<times> 'b list" where
  "unzip [] = ([], [])"
| "unzip ((a,b)#xs) = (let (as, bs) = unzip xs in (a#as, b#bs))"

definition "BadType = undefined" (* type mismatch detected *)

(*
 * FIXME: port this to ML for performance.
 *
 * Interpret an expression, returning a list of call sites and
 * statically known funargs. Return value is (calls \<times> ptrs) where:
 *  \<bullet> calls is a list of (fun, fptrs) pairs describing function calls and their funargs.
 *    Note that first-order calls are included (fptrs will be null).
 *  \<bullet> ptrs points to known function values in the return value of the expression.
 *)
fun funcall_sem :: "'f InValue env \<Rightarrow> 'f expr \<Rightarrow> ('f FunCall \<times> 'f InValue) list \<times> 'f InValue" where
  "funcall_sem \<gamma> (Var v) = ([], \<gamma> ! v)"
| "funcall_sem \<gamma> (AFun absfun _) = ([], [[IsFunction (Inl absfun)]])"
| "funcall_sem \<gamma> (Fun f _) = ([], [[IsFunction (Inr f)]])"
| "funcall_sem \<gamma> (App (AFun absfun _) x) =
     (let (calls, ptrs) = funcall_sem \<gamma> x
      in (calls @ [(Inl absfun, ptrs)], []))"
| "funcall_sem \<gamma> (App (Fun f _) x) =
     (let (calls, ptrs) = funcall_sem \<gamma> x
      in (calls @ [(Inr f, ptrs)], []))"
| "funcall_sem \<gamma> (App f x) = (fst (funcall_sem \<gamma> f) @ fst (funcall_sem \<gamma> x), [])"
| "funcall_sem \<gamma> (Con _ tag x) =
     (let (calls, ptrs) = funcall_sem \<gamma> x
      in (calls, map ((#) (InSum tag)) ptrs))"
| "funcall_sem \<gamma> (Struct ns tys xs) =
     (let (callss, ptrss) = unzip (map (funcall_sem \<gamma>) xs)
      in (concat callss, concat (map (\<lambda>(n, v). map ((#) (InRecord n)) v) (enumerate 0 ptrss))))"
| "funcall_sem \<gamma> (Member x f) =
     (case funcall_sem \<gamma> x of (calls, ptrs) \<Rightarrow>
        (calls, map tl (filter (\<lambda>ptr. case ptr of InRecord f' # _ \<Rightarrow> f = f' | _ \<Rightarrow> BadType) ptrs)))"
| "funcall_sem \<gamma> (Cast _ x) = funcall_sem \<gamma> x"
| "funcall_sem \<gamma> (Tuple x y) = (let (calls, ptrs) = funcall_sem \<gamma> x;
                                   (calls', ptrs') = funcall_sem \<gamma> y
                               in (calls @ calls', map ((#) (InProduct 0)) ptrs @ map ((#) (InProduct 1)) ptrs'))"
| "funcall_sem \<gamma> (Put x f y) =
     (let (calls, ptrs) = funcall_sem \<gamma> x;
          (calls', ptrs') = funcall_sem \<gamma> y
      in (calls @ calls',
          filter (\<lambda>ptr. case ptr of InRecord f' # _ \<Rightarrow> f \<noteq> f' | _ \<Rightarrow> BadType) ptrs @
          map ((#) (InRecord f)) ptrs'))"
| "funcall_sem \<gamma> (Let x y) =
     (let (calls, ptrs) = funcall_sem \<gamma> x;
          (calls', ptrs') = funcall_sem (ptrs # \<gamma>) y
      in (calls @ calls', ptrs'))"
| "funcall_sem \<gamma> (LetBang _ x y) =
     (let (calls, ptrs) = funcall_sem \<gamma> x;
          (calls', ptrs') = funcall_sem (ptrs # \<gamma>) y
      in (calls @ calls', ptrs'))"
| "funcall_sem \<gamma> (Case x c y z) =
     (let (calls, ptrs) = funcall_sem \<gamma> x;
          (ycalls, yptrs) = funcall_sem (map tl (filter (\<lambda>ptr. case ptr of InSum c' # _ \<Rightarrow> c = c' | _ \<Rightarrow> BadType) ptrs) # \<gamma>) y;
          (zcalls, zptrs) = funcall_sem (map tl (filter (\<lambda>ptr. case ptr of InSum c' # _ \<Rightarrow> c \<noteq> c' | _ \<Rightarrow> BadType) ptrs) # \<gamma>) z
      in (calls @ ycalls @ zcalls, []))" (* cannot determine ptrs statically *) (* TODO: warn if [yz]ptrs nonempty *)
| "funcall_sem \<gamma> (Esac x tag) =
     (let (calls, ptrs) = funcall_sem \<gamma> x
      in (calls, map tl (filter (\<lambda>ptr. case ptr of InSum _ # _ \<Rightarrow> True | _ \<Rightarrow> BadType) ptrs)))"
| "funcall_sem \<gamma> (If x y z) =
     (let (calls, ptrs) = funcall_sem \<gamma> x;
          (ycalls, yptrs) = funcall_sem \<gamma> y;
          (zcalls, zptrs) = funcall_sem \<gamma> z
      in (calls @ ycalls @ zcalls, []))" (* cannot determine ptrs statically *)
| "funcall_sem \<gamma> (Take x f y) =
     (let (calls, ptrs) = funcall_sem \<gamma> x;
          (calls', ptrs') = funcall_sem (map tl (filter (\<lambda>ptr. case ptr of InRecord f' # _ \<Rightarrow> f = f' | _ \<Rightarrow> BadType) ptrs) # ptrs # \<gamma>) y
      in (calls @ calls', ptrs'))"
| "funcall_sem \<gamma> (Split x y) =
     (let (calls, ptrs) = funcall_sem \<gamma> x;
          (calls', ptrs') = funcall_sem
             (map tl (filter (\<lambda>ptr. case ptr of InProduct 0 # _ \<Rightarrow> True | _ \<Rightarrow> BadType) ptrs) #
              map tl (filter (\<lambda>ptr. case ptr of InProduct (Suc 0) # _ \<Rightarrow> True | _ \<Rightarrow> BadType) ptrs) # \<gamma>) y
      in (calls @ calls', ptrs'))"
| "funcall_sem \<gamma> _ = ([], [])"

(* Use the simplifier to extract higher-order function call information. *)
ML \<open>
structure CogentHigherOrder = struct
(* ML representation of InData type *)
datatype InData = InRecord of int
                | InProduct of int
                | InSum of string
                | IsFunction of (string, string) Either

fun dest_funcall (Const (@{const_name Inl}, _) $ absfun) = Left (HOLogic.dest_string absfun)
  | dest_funcall (Const (@{const_name Inr}, _) $ Const (f, _)) = Right f
  | dest_funcall f = raise TERM ("dest_funcall: unrecognised call", [f])

fun parse_ptr ptr =
    HOLogic.dest_list ptr
    |> map (fn p =>
         (case p of
             Const (@{const_name InRecord}, _) $ n => InRecord (HOLogic.dest_nat n)
           | Const (@{const_name InProduct}, _) $ n => InProduct (HOLogic.dest_nat n)
           | Const (@{const_name InSum}, _) $ s => InSum (HOLogic.dest_string s)
           | Const (@{const_name IsFunction}, _) $ f => IsFunction (dest_funcall f)))

fun parse_calls calls =
    HOLogic.dest_list calls |> map HOLogic.dest_prod
    |> map (fn (f, ptrs) => (dest_funcall f, HOLogic.dest_list ptrs |> map parse_ptr))

fun get_HO_calls ctxt f =
  (* Expression that evaluates to the higher-order call lists *)
  @{mk_term "filter (\<lambda>call. snd call \<noteq> []) (fst (funcall_sem [[]] ?f))" f}
    (Syntax.read_term ctxt f)
  |> Thm.cterm_of ctxt
  (* Unfold funcall_sem *)
  |> Simplifier.rewrite (ctxt addsimps (Proof_Context.get_thms ctxt (f ^ "_def")))
  |> Thm.prop_of |> Utils.rhs_of_eq
  |> parse_calls

(* Post-processing: translate InData accessors to C datatype accessors, which can be plugged
 *                  into the Corres_Tac code. *)
fun the'' str x =
    (the x) handle Option => error (str ())

fun nth'' str xs n =
    (nth xs n) handle Subscript => error (str ())

fun nth_field_of struct_info C_typ n =
      nth'' (fn _ => raise TYPE ("Type does not have field #" ^ string_of_int n, [C_typ], []))
            (Typtab.lookup struct_info C_typ
             |> the'' (fn _ => raise TYPE ("No such struct: ", [C_typ], []))
             |> #field_info) n

fun ptrs_to_C_getter struct_info C_typ (InRecord n :: ptrs) = let
      val field = nth_field_of struct_info C_typ n
      val (getter', funarg) = ptrs_to_C_getter struct_info (#field_type field) ptrs
      in (#name field :: getter', funarg) end
  | ptrs_to_C_getter struct_info C_typ (InProduct n :: ptrs) = let
      val field = nth_field_of struct_info C_typ n
      val (getter', funarg) = ptrs_to_C_getter struct_info (#field_type field) ptrs
      in (#name field :: getter', funarg) end
  | ptrs_to_C_getter struct_info C_typ (InSum s :: ptrs) = let
      val field_info = Typtab.lookup struct_info C_typ
                       |> the'' (fn _ => raise TYPE ("No such struct: ", [C_typ], [])) |> #field_info
      val field = case filter (fn field => #name field = s ^ "_C") field_info of
                     [field] => field
                   | _ => raise TYPE ("Type does not have field " ^ quote s, [C_typ], [])
      val (getter', funarg) = ptrs_to_C_getter struct_info (#field_type field) ptrs
      in (#name field :: getter', funarg) end
  | ptrs_to_C_getter struct_info C_typ [IsFunction f] = ([], f)
  | ptrs_to_C_getter _ _ _ = error "ptrs_to_C_getter: failed to parse ptrs"

fun make_HO_call_hints ctxt C_src f = let
      val ACfunctions = Symtab.lookup (AutoCorresFunctionInfo.get (Proof_Context.theory_of ctxt)) C_src
                        |> Utils.the' ("No such C file: " ^ quote C_src)
                        |> (fn finfo => FunctionInfo.Phasetab.lookup finfo FunctionInfo.TS)
                        |> Utils.the' ("Failed to get type strengthening function table")
      val struct_info = Symtab.lookup (HeapInfo.get (Proof_Context.theory_of ctxt)) C_src
                        |> Utils.the' ("No such C file: " ^ quote C_src)
                        |> #heap_info
                        |> #struct_types
      in get_HO_calls ctxt f
         |> map (fn (call, ptrs) => let
              val hofun = (case call of Left f => f | Right f => f)
              val [(_, hoarg_typ)] = Symtab.lookup ACfunctions hofun
                                     |> Utils.the' ("No such C func: " ^ quote hofun) |> #args
              in (call, map (ptrs_to_C_getter struct_info hoarg_typ) ptrs) end)
         end

end
\<close>

end
