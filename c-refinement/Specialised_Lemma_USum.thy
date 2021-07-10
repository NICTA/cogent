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

theory Specialised_Lemma_USum
imports
  Read_Table
  SpecialisedLemmaTactic
begin

context update_sem_init
begin

ML \<open>

fun bool_of_variant_state Checked = true
| bool_of_variant_state Unchecked = false

fun variant_state_of_bool true = @{term Checked}
| variant_state_of_bool false = @{term Unchecked}

fun get_checkeds_of_usum_uval uval =
    usum_list_of_checked uval |>  map bool_of_variant_state

\<close>

ML\<open> (* get_castable_uvals_from *)
local

infix can_be_casted_to
fun (uval1 can_be_casted_to uval2) ctxt heap_info =
(* Check if a pattern matching failure in case with a scrutinee of type uval1 will result in an expression of type uval2 *)
(* Returns NONE if uval1 cannot be casted to uval2.*)
(* Returns (SOME int) if uval1 can be casted to uval2 and we lose the int-th field in the c-struct for
 uval1 by copying uval1 to uval2.*)
 let
  fun uval_to_field_names uval = heap_info_uval_to_field_names heap_info uval;
  fun uval_to_field_types uval = heap_info_uval_to_field_types heap_info uval;
  val field_names1 = uval_to_field_names uval1;
  val field_names2 = uval_to_field_names uval2;
  val field_types1 = uval_to_field_types uval1;
  val field_types2 = uval_to_field_types uval2;
  fun check_diff c1 c2 =
    (c1 ~~ c2) |>
    map_index I |>
    filter (fn (_,(a,b)) => a <> b)
 in
  if (field_names1 = field_names2) andalso (field_types1 = field_types2)
  then case check_diff (get_checkeds_of_usum_uval uval1) (get_checkeds_of_usum_uval uval2) of
       (* Only if going from unchecked to checked *)
        [(ix,(false,true))] => SOME ix
       (* If multiple differences, or no differences, we don't need to worry about case *)
       | _ => NONE
  else NONE
 end;

fun get_castable_uvals_from' _ _ (_:uval) []        = []
  | get_castable_uvals_from' ctxt heap (from:uval) (to::tos) =
   let val some_rmved_field_num  = (from can_be_casted_to to) ctxt heap;
       val some_pair = case some_rmved_field_num of
                        SOME ix => SOME (ix, to)
                      | NONE => NONE
   in some_pair :: get_castable_uvals_from' ctxt heap from tos
   end;

in

fun get_castable_uvals_from ctxt heap from tos =
    get_castable_uvals_from' ctxt heap from (get_usums tos) |> get_somes

end;
\<close>


ML\<open> fun mk_case_prop from_uval to_uval variant_ctor_num file_nm ctxt =
(* field_num is the number of the field that is being tested for matching.*)
 let
  val struct_field_num = variant_ctor_num + 1
  val _ = tracing ("  started mk_case_prop for variant_ctor_num " ^ string_of_int variant_ctor_num)
  val from_struct_C_nm = get_ty_nm_C from_uval;
  val to_struct_C_nm   = get_ty_nm_C to_uval;
  val _ = tracing ("  casting from " ^ from_struct_C_nm ^ " to " ^ to_struct_C_nm)
  val heap = Symtab.lookup (HeapInfo.get (Proof_Context.theory_of ctxt)) file_nm
      |> Utils.the' "heap in mk_case_prop failed."
      |> #heap_info;
  val get_struct_info  = fn struct_C_nm => Symtab.lookup (heap |> #structs) struct_C_nm
      |> Utils.the' "get_struct_info in mk_prop in Specialised_Lemma_USum.thy failed.";
  val from_struct_info = get_struct_info from_struct_C_nm;
  val to_struct_info   = get_struct_info to_struct_C_nm;
  val from_field_info  = #field_info from_struct_info;
  val nth_field_ml_tag_name = from_field_info |> (fn list => List.nth (list, struct_field_num)) |> #name
                              |> cut_C;
  val nth_field_tag_name = nth_field_ml_tag_name |> Utils.encode_isa_string;
  val get_tag_names = fn uval => heap_info_uval_to_field_names heap uval |> tl |> map (unsuffix "_C");
  val from_tag_nms  = get_tag_names from_uval;
  val from_tag_checks = get_checkeds_of_usum_uval from_uval
  val to_tag_checks   = get_checkeds_of_usum_uval to_uval

  val alternative_tys = map (fn n => Free ("alt_ty" ^ string_of_int n, @{typ "Cogent.type"}))
    (1 upto length from_tag_nms)
  val tag_ty_bits    = from_tag_nms ~~ alternative_tys ~~ from_tag_checks
  val to_tag_ty_bits    = from_tag_nms ~~ alternative_tys ~~ to_tag_checks
  fun mk_triple_tag ((a,b),c) = HOLogic.mk_prod (HOLogic.mk_string a, HOLogic.mk_prod (b, variant_state_of_bool c))
  val from_sumT      = @{term TSum} $ HOLogic.mk_list @{typ "(string \<times> Cogent.type \<times> variant_state)"}
                       (map mk_triple_tag tag_ty_bits)
  val to_sumT        = @{term TSum} $ HOLogic.mk_list @{typ "(string \<times> Cogent.type \<times> variant_state)"}
                       (map mk_triple_tag to_tag_ty_bits)
  val taken_typ      = List.nth (alternative_tys, variant_ctor_num)

  val from_tag_C = from_field_info |> hd |> #getter; (* tag_C is always the first element of struct.*)
  val corres     = Syntax.read_term ctxt "corres";

  (* Monadic C code in the conclusion.*)
  val monadic_c =
   let
    val TAG_ENUM = Syntax.read_term ctxt ("TAG_ENUM_" ^ nth_field_ml_tag_name);
    val match_tag_getter = List.nth (from_field_info, struct_field_num) |> #getter;
   in
    @{term "\<lambda> from_tag_C TAG_ENUM match_tag_getter.
         (condition (\<lambda>_. from_tag_C x' = TAG_ENUM)
           (match' (match_tag_getter x'))
           (not_match' x'))"}
     $ from_tag_C $ TAG_ENUM $ match_tag_getter
   end;

  fun mk_ass2 tag_list    = @{mk_term "\<Gamma>' ! x = Some ?tag_list" tag_list} tag_list;
  fun mk_ass6 tag_list    = @{mk_term "\<Xi>', [], \<Gamma>1 \<turnstile> Var x : ?tag_list" tag_list} tag_list;
  fun mk_ass9 other_tags  = @{mk_term "\<Xi>', [], Some ?other_tags # \<Gamma>2 \<turnstile> not_match : t" other_tags} other_tags;
  fun mk_ass11 other_tags =
   @{mk_term "\<And>r. r = (\<gamma>!x) \<Longrightarrow> val_rel r x' \<Longrightarrow> ?corres srel not_match (not_match' x') \<xi>' (r # \<gamma>) \<Xi>'
    (Some (?other_tags) # \<Gamma>2) \<sigma> s" (corres, other_tags)} (corres, other_tags);

  val ass1 = @{term "x < length \<Gamma>'"};
  val ass2 = mk_ass2 from_sumT;
  val ass3 = @{term "[] \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1 | \<Gamma>2"};
  val ass4 = @{term "val_rel (\<gamma> ! x) x'"};
  (* Ass 5 discharged by instantiating at concrete type *)
  val ass6 = mk_ass6 from_sumT
  (* Ass 7 discharged by instantiating at concrete type *)
  val ass8 = @{term "\<lambda>taken_typ. \<Xi>', [], Some taken_typ # \<Gamma>2 \<turnstile> match : t"} $ taken_typ;
  val ass9 = mk_ass9 to_sumT;
  val ass10 = @{mk_term "\<And>a a'. val_rel a a' \<Longrightarrow>
   ?corres srel match (match' a') \<xi>' (a # \<gamma>) \<Xi>' (Some ?match_typ # \<Gamma>2) \<sigma> s"(corres, match_typ)}
    (corres, taken_typ);
  val ass11= mk_ass11 to_sumT;
  val prms = map (HOLogic.mk_Trueprop o strip_atype)
     [ass1, ass2, ass3, ass4, ass6, ass8, ass9] @ [ass10, ass11];

  val cncl = @{mk_term
          "?corres srel (Case (Var x) ?nth_field_tag_name match not_match) ?monadic_c \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
          (corres, nth_field_tag_name, monadic_c)} (corres, nth_field_tag_name, monadic_c)
          |> HOLogic.mk_Trueprop;

in
  mk_meta_imps prms cncl ctxt |> Syntax.check_term ctxt
end
\<close>

ML\<open> (* mk_case_lem_for_uval *)
local

fun mk_case_lem_name (from:uval) field_num ctxt =
 let
  val cs = get_checkeds_of_usum_uval from
  val cs_str = cs |> map (fn b => if b then "C" else "U") |> String.concat
 in
  "corres_case_" ^ get_uval_name from ^ "_" ^ Int.toString field_num ^ "th_field_" ^ cs_str
 end

fun mk_case_lem_from_to (from:uval) field_num (to:uval) file_nm ctxt  =
{ name = mk_case_lem_name from field_num ctxt,
  bucket = Case,
  prop = mk_case_prop from to field_num file_nm ctxt,
  mk_tactic = if true then (fn ctxt => corres_case_tac ctxt 1) else K (Skip_Proof.cheat_tac ctxt 1) };

fun mk_case_lems_from_tos from (num_tos : (int * uval) list) file_nm ctxt = map
   (fn num_to => mk_case_lem_from_to from (fst num_to) (snd num_to) file_nm ctxt) num_tos

in

fun mk_case_lems_for_uval file_nm ctxt uvals from =
 let
  val heap_info = Symtab.lookup (HeapInfo.get (Proof_Context.theory_of ctxt)) file_nm
                 |> Utils.the' "the' in mk_specialised_case_lemmas_for_uval failed."
                 |> #heap_info;
  val num_tos   = get_castable_uvals_from ctxt heap_info from uvals;
  val lems      = mk_case_lems_from_tos from num_tos file_nm ctxt;
 in
  lems
 end;

end;
\<close>

ML\<open> (* local_setup_specialised_esacs *)
local

fun specialise_esac_thm ctxt trm =
 let
  val cterm_of    = Thm.cterm_of ctxt;
  val corres_esac = Proof_Context.get_thm ctxt "corres_esac";
  val vars        = Term.add_vars (Thm.prop_of corres_esac) [];
  (* get_val' is the 5th variable counting from 0.*)
  val get_val'    = List.nth (vars, 5);
  val my_esac     = Drule.infer_instantiate ctxt [(("get_val'", 0), cterm_of trm)] corres_esac (* TODO make sure 0 means what I think it means *)
 in my_esac end;

fun mk_specialised_esac_lemma file_nm ctxt from_usum =
 let
  val from_C_nm       = get_ty_nm_C from_usum;
  val _               = tracing ("  mk_specialised_esac_lemma for " ^ from_C_nm)
  val thy             = Proof_Context.theory_of ctxt;
  val is_usum         = get_usums [from_usum] |> null |> not;
  val with_checks     = map_index I (get_checkeds_of_usum_uval from_usum)
  val uncheckeds      = List.filter (fn (_,x) => not x) with_checks
 in
    case uncheckeds of
     [(ix,_)] =>
      let
        fun get_struct_info (hinfo : HeapLiftBase.heap_info)
                            = Symtab.lookup (#structs hinfo) from_C_nm;
        val some_hinfo      = (Symtab.lookup (HeapInfo.get thy) file_nm) +> #heap_info;
        val some_sinfo      = some_hinfo ?> get_struct_info;
        val some_finfo      = some_sinfo +> #field_info;
        fun get_ix_field list = List.nth (list, ix + 1);
        val some_fst_getter = some_finfo +> get_ix_field +> #getter;
        val _               = if is_usum
                              then tracing ("  " ^ from_C_nm ^ " is for esac.")
                              else tracing ("  " ^ from_C_nm ^ " is not for esac.");
        val some_thm        = if is_usum
                              then some_fst_getter +> specialise_esac_thm ctxt
                              else NONE
     in some_thm end
    | _ => (tracing ("  " ^ from_C_nm ^ " is not for esac."); NONE)
  end

in

fun local_setup_specialised_esacs file_nm lthy =
 let
  val _      = tracing "started local_setup_specialised_esacs"
  val thy    = Proof_Context.theory_of lthy;
  val usums  = read_table file_nm thy
              |> get_usums
              |> get_uvals_for_which_ac_mk_st_info file_nm thy;
  fun mk_some_esac_lemma usum = mk_specialised_esac_lemma file_nm lthy usum;
  val esac_thms = List.mapPartial mk_some_esac_lemma usums;
  val lthy' = Local_Theory.notes [((Binding.name "corres_esacs", []), [(esac_thms, [])])] lthy |> snd
 in lthy' end;

end;
\<close>

end

end
