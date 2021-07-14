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

theory Type_Relation_Generation
imports
 Cogent_Corres
 Read_Table
begin

ML\<open> (* type_rel_def *)

local

fun mk_rhs_of_type_rel_rec _ (field_info:HeapLiftBase.field_info list) =
(* type_rel generation for TRecord
 * We assume that there are (length field_info) bound variables
 * corresponding to the type repr for each field. *)
 let
  val _ = @{print} field_info
  val num_fields = List.length field_info;

  (* mk_hd_conjct makes e.g. @{term "ty = TRecord [(''a'', a), (''b'', b)]"} in the body.*)
  val mk_hd_conjct =
   let
    fun make_name s = if String.isSuffix "_C" s then 
                           (* remove the _C suffix *)
                           String.substring (s, 0, String.size s - 2) 
                      else error ("mk_rhs_of_type_rel_rec: not a C field " ^ s)
    val ml_list_for_TRecord = map_index (fn (n, i ) =>
     encode_isa_pair (HOLogic.mk_string (# name i |> make_name), Bound (num_fields - n - 1))) field_info;
    val RRecord = Const (@{const_name RRecord}, dummyT) $ mk_isa_list ml_list_for_TRecord
   in
    HOLogic.mk_eq (Free ("ty", dummyT), RRecord)
   end;

  (* mk_tl_conjcts makes e.g.
     "[@{term "type_rel a TYPE(x)"}, @{term "type_rel b TYPE(y)"}]" in the body.*)
  val mk_tl_conjcts = map_index (fn (n, field) =>
        @{term type_rel} $ Bound (num_fields - n - 1) $
          Const ("Pure.type", Type ("itself", [#field_type field])) |> strip_atype)
        field_info

  val body  =  (mk_hd_conjct :: mk_tl_conjcts) |> mk_HOL_conjs;

  val field_names = get_field_names field_info;
  val ex_qnts = field_names;
 in
  mk_exists ex_qnts body
 end;

fun mk_rhs_of_type_rel_sum _ (field_info:HeapLiftBase.field_info list) =
 let
  val field_info = filter (fn f => #name f <> "tag_C") field_info
  val num_fields = List.length field_info;

  (* mk_hd_conjct makes e.g. @{term "ty = RSum [(''a'', a), (''b'', b)]"} in the body.*)
  val mk_hd_conjct =
   let
    val ml_list_for_TSum = map_index (fn (n, field) =>
          encode_isa_pair (Utils.encode_isa_string (cut_C (#name field)), Bound (num_fields - n - 1))) field_info;
    val RSum             = Const (@{const_name RSum}, dummyT) $ mk_isa_list ml_list_for_TSum
   in
    HOLogic.mk_eq (Free ("ty", dummyT), RSum)
   end;

  (* mk_tl_conjcts makes e.g.
     "[@{term "type_rel a TYPE(x)"}, @{term "type_rel b TYPE(y)"}]" in the body.*)
  val mk_tl_conjcts = map_index (fn (n, field) =>
        @{term type_rel} $ Bound (num_fields - n - 1) $
          Const ("Pure.type", Type ("itself", [#field_type field])) |> strip_atype)
        field_info

  val body  =  (mk_hd_conjct :: mk_tl_conjcts) |> mk_HOL_conjs;

  val field_names = get_field_names field_info;
  val ex_qnts = field_names;
 in
  mk_exists ex_qnts body
 end;

fun mk_rhs_of_type_rel_prod _ (field_info:HeapLiftBase.field_info list) =
 let
  val (atyp, btyp) = case field_info of
                        [a, b] => (#field_type a, #field_type b)
                      | _ => error "mk_rhs_of_type_rel_prod: expected 2 fields in product type"
 in
  @{mk_term "\<exists>a b. ty = RProduct a b \<and> type_rel a TYPE(?'a::cogent_C_val) \<and> type_rel b TYPE(?'b::cogent_C_val)"
    ('a, 'b)} (atyp, btyp)
 end;

val mk_rhs_of_type_rel_abs = @{term "\<exists> x list . ty = RCon x list"} |> strip_atype;

fun gen_mk_rhs_of_type_rel ctxt file_name uval =
 let
  val thy           = Proof_Context.theory_of ctxt;
  fun field_info ty = get_field_info (get_struct_info thy file_name) ty;
 in
  case uval of
    (USum (ty_name, _))   => mk_rhs_of_type_rel_sum ctxt (field_info ty_name)
  | (UProduct ty_name)    => mk_rhs_of_type_rel_prod ctxt (field_info ty_name)
  | (URecord (ty_name,_)) => mk_rhs_of_type_rel_rec ctxt (field_info ty_name)
  | (UAbstract _)         => mk_rhs_of_type_rel_abs
 end;

in

(* TODO review this *)

fun type_rel_def file_name uval ctxt =
 let
  val ty_name = get_uval_name uval;
  val ty      = Syntax.read_typ ctxt (ty_name ^ "_C itself") ;
  val lhs     = strip_atype @{term "type_rel"} $ Free ("ty", dummyT) $ Free("tag", ty);
  val rhs     = gen_mk_rhs_of_type_rel ctxt file_name uval;
  val equ     = mk_eq_tm lhs rhs ctxt;
  val type_rel_name = "type_rel_" ^ ty_name ^"_C_def";
  val spec_def = Specification.definition NONE [] [] ((Binding.name type_rel_name, []), equ) ctxt;
  val thm      = spec_def |> fst |> snd |> snd;
  val lthy     = snd spec_def;
  val lthy'    = TypeRelSimp.add_local thm lthy;
  val _ = tracing ("generating type_rel for " ^ (get_uval_name uval))
 in lthy' end;

end;
\<close>

end
