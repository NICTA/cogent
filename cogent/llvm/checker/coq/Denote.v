From Coq Require Import List ZArith String.

From ExtLib Require Import Structures.Monads Structures.Functor Structures.Reducible Data.Map.FMapAList.
From ITree Require Import ITree Events.State Events.Exception.
From Vellvm Require Import Util Utils.Error.

From Checker Require Import Cogent Utils.Instances Utils.Fail.

Import Monads.
Import ListNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Inductive uval : Set :=
| UPrim (l : lit)
| URecord (us : list (uval * repr))
| UUnit
| UPtr (a : addr) (r : repr)
| UFunction (f : name).

Definition ctx : Type := list uval.

Variant MemE : Type -> Type :=
| LoadMem (a : addr) : MemE (option uval)
| StoreMem (a : addr) (u : uval) : MemE unit.

Definition FailE := exceptE string.

Definition CogentL0 := MemE +' FailE.

Definition CogentL1 := FailE.

Section Denote.

  Definition option_bind {A T} (x : option A) (f : A -> T) (m : string) : itree CogentL0 T := 
    match x with
    | Some y => ret (f y)
    | None => throw m
    end.

  Definition extract_prim (x : uval) : itree CogentL0 lit :=
    match x with
    | UPrim v => ret v
    | _ => throw "not a prim"
    end.
  
  Definition denote_prim (op : prim_op) (xs : list uval) : itree CogentL0 uval :=
    xs' <- map_monad extract_prim xs ;;
    option_bind (eval_prim_op op xs') UPrim "op error".

  Definition access_member (fs : list (uval * repr)) (f : nat) : itree CogentL0 uval :=
    option_bind (nth_error fs f) fst "invalid member access".

  (* is this built-in somewhere? *)
  Fixpoint list_upd {T} (l : list T) (n : nat) (r : T) : list T :=
    match l, n with
    | x::xs, 0 => r::xs
    | x::xs, S u => x::(list_upd xs u r)
    | _, _ => l
    end.

  Fixpoint denote_expr (γ : ctx) (e : expr) : itree CogentL0 uval :=
    (* define some nested functions that are mutually recursive with denote_expr *)
    let fix denote_member (γ : ctx) (e : expr) (f : nat) {struct e} : itree CogentL0 (uval * uval) :=
      r <- denote_expr γ e ;;
      m <- match r with
      | URecord fs => access_member fs f
      | UPtr p r =>
          m <- trigger (LoadMem p) ;;
          match m with
          | Some (URecord fs) => access_member fs f
          | _ => throw "invalid memory access"
          end
      | _ => throw "expression is not a record"
      end ;;
      ret (r, m) in
    match e with
    | Prim p xs =>
        xs' <- map_monad (denote_expr γ) xs ;;
        denote_prim p xs'
    | Lit l => ret (UPrim l)
    | Var i => option_bind (nth_error γ i) id "unknown variable"
    | Let a b =>
        a' <- denote_expr γ a ;;
        denote_expr (a' :: γ) b
    | Unit => ret UUnit
    (* | If x t e =>
        x' <- denote_expr γ x ;;
        match x' with
        | UPrim (LBool b) => denote_expr γ (if b then t else e)
        | _ => throw "expression is not a boolean"
        end
    | Cast τ e =>
        e' <- denote_expr γ e ;;
        match e' with
        | UPrim l => option_bind (cast_to τ l) UPrim "invalid cast"
        | _ => throw "invalid cast"
        end
    | Struct ts xs =>
        vs <- map_monad (denote_expr γ) xs ;;
        ret (URecord (combine vs (map type_repr ts)))
    | Member e f => snd <$> denote_member γ e f
    | Take x f e => 
        '(r, m) <- denote_member γ x f ;;
        denote_expr (m :: r :: γ) e
    | Put x f e =>
        x' <- denote_expr γ x ;;
        e' <- denote_expr γ e ;;
        (* can we avoid code repetition between this and denote_member? *)
        match x' with
        | URecord fs =>
            rep <- option_bind (nth_error fs f) snd "invalid member access" ;;
            ret (URecord (list_upd fs f (e', rep)))
        | UPtr p r =>
            m <- trigger (LoadMem p) ;;
            match m with
            | Some (URecord fs) =>
                rep <- option_bind (nth_error fs f) snd "invalid member access" ;;
                trigger (StoreMem p (URecord (list_upd fs f (e', rep)))) ;;
                ret (UPtr p r)
            | _ => throw "invalid memory access"
            end
        | _ => throw "expression is not a record"
        end
    | Fun n ft => ret (UFunction n)
    | App x y =>
        f <- denote_expr γ x ;;
        a <- denote_expr γ y ;;
        trigger (Call f a) *)
    end.

  Definition function_denotation := uval -> itree CogentL0 uval.

  Definition denote_function (b : expr) : function_denotation :=
    fun a => denote_expr [a] b.

  Definition program_denotation := alist name function_denotation.

  Definition denote_program (p : cogent_prog) : program_denotation :=
    map (fun '(FunDef n t rt b) => (n, denote_function b)) p.

End Denote.

From ExtLib Require Import Structures.Maps.

Section Interpretation.

  Definition memory := alist addr uval.
  Definition empty_memory : memory := empty.
  Definition dummy_memory : memory := 
    alist_add _ 23 (URecord [(UPrim (LU8 5), RPrim (Num U8))]) empty_memory.

  Definition handle_mem {E} : MemE ~> stateT memory (itree E) :=
    fun _ e σ =>
      match e with
      | LoadMem a => ret (σ, alist_find _ a σ)
      | StoreMem a u => ret (alist_add _ a u σ, tt)
      end.
  
  Definition interp_mem : itree CogentL0 ~> stateT memory (itree CogentL1) :=
    interp_state (case_ handle_mem pure_state).

  Definition handle_failure : FailE ~> failT (itree void1) :=
    fun _ '(Throw m) => ret (inl m).

  (* from Helix *)
  Definition inject_signature {E} : void1 ~> E := fun _ (x : void1 _) => match x with end.
  Hint Unfold inject_signature : core.

  Definition interp_expr {E} (l0 : itree CogentL0 uval) (mem : memory)
                               : failT (itree E) (memory * uval) :=
    let l1 := interp_mem _ l0 mem in
    let l2 := interp handle_failure l1 in
    translate inject_signature l2.

  Definition interp_cogent {E} (p : program_denotation) (fn : name) (a : uval) (mem : memory) 
                         : failT (itree E) (memory * uval) :=
    match alist_find _ fn p with
    | Some f => interp_expr (f a) mem
    | None => ret (inl ("unknown function " ++ fn))
    end.

  Definition run_cogent (p : cogent_prog) (fn : name) (a : uval)
                      : failT (itree void1) (memory * uval) :=
    interp_cogent (denote_program p) fn a dummy_memory.

End Interpretation.