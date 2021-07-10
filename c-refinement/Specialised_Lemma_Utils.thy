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

theory Specialised_Lemma_Utils
imports Utils
begin

text\<open> This theory file contains utility functions that are specific to the generation and proof of
 the specialised lemmas.
\<close>

ML\<open> datatype bucket =
  TakeBoxed
| TakeUnboxed
| PutBoxed
| LetPutBoxed
| PutUnboxed
| MemberBoxed
| MemberReadOnly
| TagDef
| Esac
| Case
| ValRelSimp
| IsValidSimp
| TypeRelSimp
| HeapSimp \<close>

ML\<open> fun bucket_to_string bucket = case bucket of
  TakeBoxed   => "TakeBoxed"
| TakeUnboxed => "TakeUnboxed"
| PutBoxed    => "PutBoxed"
| LetPutBoxed => "LetPutBoxed"
| PutUnboxed  => "PutUnboxed"
| MemberBoxed => "MemberBoxed"
| MemberReadOnly => "MemberReadOnly"
| TagDef      => "TagDef"
| Esac        => "Esac"
| Case        => "Case"
| ValRelSimp  => "ValRelSimp"
| IsValidSimp => "IsValidSimp"
| TypeRelSimp => "TypeRelSimp"
| HeapSimp    => "HeapSimp"
\<close>

ML\<open> structure Unborn_Thms = Proof_Data
(* Unborn_Thms is a list of thm-names which I tried to prove but failed to do so.
 * Note that I do not include thm-names if I tried to cheat.*)
 (type T = string list;
  fun init _ = [];)
\<close>

ML\<open> fun add_unborns unborn_thm = Unborn_Thms.map (fn unborn_thms => unborn_thm::unborn_thms); \<close>

text\<open> Lemma buckets. \<close>

ML \<open> structure TakeBoxed = Named_Thms_Ext
 (val name = @{binding "TakeBoxed"}
  val description = "Theorems for boxed takes.") \<close>

ML \<open> structure TakeUnboxed = Named_Thms_Ext
 (val name = @{binding "TakeUnboxed"}
  val description = "Theorems for unboxed takes.") \<close>

ML \<open> structure PutBoxed = Named_Thms_Ext
 (val name = @{binding "PutBoxed"}
  val description = "Theorems for boxed puts.") \<close>

ML \<open> structure LetPutBoxed = Named_Thms_Ext
 (val name = @{binding "LetPutBoxed"}
  val description = "Theorems for boxed let-puts.") \<close>

ML \<open> structure PutUnboxed = Named_Thms_Ext
 (val name = @{binding "PutUnboxed"}
  val description = "Theorems for unboxed puts.") \<close>

ML \<open> structure MemberReadOnly = Named_Thms_Ext
 (val name = @{binding "MemberReadOnly"}
  val description = "Theorems for read-only member.") \<close>

ML \<open> structure MemberBoxed = Named_Thms_Ext
 (val name = @{binding "MemberBoxed"}
  val description = "Theorems for boxed member.") \<close>

ML \<open> structure Case = Named_Thms_Ext
 (val name = @{binding "Case"}
  val description = "Theorems for case.") \<close>

ML \<open> structure ValRelSimp = Named_Thms_Ext
 (val name = @{binding "ValRelSimp"}
  val description = "Simplification rules about value relation.") \<close>

ML \<open> structure IsValidSimp = Named_Thms_Ext
 (val name = @{binding "IsValidSimp"}
  val description = "Simplification rules about is_valid.") \<close>

ML \<open> structure TypeRelSimp = Named_Thms_Ext
 (val name = @{binding "TypeRelSimp"}
  val description = "Simplification rules about type relation.") \<close>

ML \<open> structure HeapSimp = Named_Thms_Ext
 (val name = @{binding "HeapSimp"}
  val description = "Simplification rules about heap relation.") \<close>

setup\<open> (* Set up lemma buckets.*)
 TakeBoxed.setup o TakeUnboxed.setup o PutUnboxed.setup o PutBoxed.setup o
 MemberReadOnly.setup o MemberBoxed.setup o Case.setup o
 ValRelSimp.setup o IsValidSimp.setup o
 TypeRelSimp.setup o HeapSimp.setup \<close>

ML\<open> fun local_setup_add_thm bucket thm = case bucket of
  TakeBoxed     => TakeBoxed.add_local thm
| TakeUnboxed   => TakeUnboxed.add_local thm
| PutBoxed      => PutBoxed.add_local thm
| LetPutBoxed   => LetPutBoxed.add_local thm
| PutUnboxed    => PutUnboxed.add_local thm
| MemberBoxed   => MemberBoxed.add_local thm
| MemberReadOnly=> MemberReadOnly.add_local thm
| ValRelSimp    => ValRelSimp.add_local thm
| IsValidSimp   => IsValidSimp.add_local thm
| TypeRelSimp   => TypeRelSimp.add_local thm
| HeapSimp      => HeapSimp.add_local thm
| Case          => Case.add_local thm
| _             => error "add_thm in Value_Relation_Generation.thy failed."
\<close>

ML\<open> fun setup_add_thm bucket thm = case bucket of
  TakeBoxed     => TakeBoxed.add_thm thm   |> Context.theory_map
| TakeUnboxed   => TakeUnboxed.add_thm thm |> Context.theory_map
| PutBoxed      => PutBoxed.add_thm thm    |> Context.theory_map
| LetPutBoxed   => LetPutBoxed.add_thm thm |> Context.theory_map
| PutUnboxed    => PutUnboxed.add_thm thm  |> Context.theory_map
| MemberBoxed   => MemberBoxed.add_thm thm |> Context.theory_map
| MemberReadOnly=> MemberReadOnly.add_thm thm |> Context.theory_map
| Case          => Case.add_thm thm        |> Context.theory_map
| ValRelSimp    => ValRelSimp.add_thm thm  |> Context.theory_map
| IsValidSimp   => IsValidSimp.add_thm thm |> Context.theory_map
| TypeRelSimp   => TypeRelSimp.add_thm thm |> Context.theory_map
| HeapSimp      => HeapSimp.add_thm thm    |> Context.theory_map
| _             => error "add_thm in SpecialisedLemmaForTakePut.thy failed."
\<close>

ML\<open> val local_setup_put_lemmas_in_bucket =
  let
    fun note (name:string) (getter) lthy = Local_Theory.note ((Binding.make (name, @{here}), []), getter lthy) lthy |> snd;
  in
    note "type_rel_simp" TypeRelSimp.get #>
    note "val_rel_simp" ValRelSimp.get #>
    note "take_boxed" TakeBoxed.get #>
    note "take_unboxed" TakeUnboxed.get #>
    note "put_boxed" PutBoxed.get #>
    note "let_put_boxed" LetPutBoxed.get #>
    note "put_unboxed" PutUnboxed.get #>
    note "member_boxed" MemberBoxed.get #>
    note "member_readonly" MemberReadOnly.get #>
    note "case" Case.get #>
    note "is_valid_simp" IsValidSimp.get #>
    note "heap_simp" HeapSimp.get
  end;
\<close>

ML\<open> type lem = { name: string, bucket: bucket, prop: term, mk_tactic: Proof.context -> tactic }; \<close>

ML\<open> val cheat_specialised_lemmas =
 Attrib.setup_config_bool @{binding "cheat_specialised_lemmas"} (K false);
\<close>
(* An example to show how to manupulate this flag.*)
declare [[ cheat_specialised_lemmas = false ]]

ML\<open> (* type definition on the ML-level.*)
datatype sigil = ReadOnly | Writable | Unboxed

datatype variant_state = Checked | Unchecked

datatype uval = UProduct of string
              | USum of string * variant_state list (* for each constructor, whether it is checked or not *)
              | URecord of string * sigil
              | UAbstract of string;
;
type uvals = uval list;\<close>

ML\<open> (* unify_sigils to remove certain kind of duplication.*)
fun unify_sigils (URecord (ty_name,_)) = URecord (ty_name,Writable)
  | unify_sigils uval                  = uval
  (* value-relations and type-relations are independent of sigils.
   * If we have multiple uvals with different sigils but with the same type and name,
   * we should count them as one to avoid trying to instantiate the same thing multiple times.*)
\<close>

ML\<open> (* unify_usum_tys *)
fun unify_usum_tys (USum (ty_name,_)) = USum (ty_name, [])
  | unify_usum_tys uval               = uval
\<close>

ML\<open> (* unify_uabstract *)
fun unify_uabstract (UAbstract _) = UAbstract "dummy"
 |  unify_uabstract uval          = uval;
\<close>

ML\<open> (* get_usums, get_uproducts, get_urecords *)
fun get_usums uvals = filter (fn uval => case uval of  (USum _) => true | _ => false) uvals
fun get_uproducts uvals = filter (fn uval => case uval of  (UProduct _) => true | _ => false) uvals
fun get_urecords uvals = filter (fn uval => case uval of  (URecord _) => true | _ => false) uvals
\<close>

ML\<open> (* get_uval_name *)
fun get_uval_name (URecord (ty_name, _)) = ty_name
 |  get_uval_name (USum    (ty_name, _)) = ty_name
 |  get_uval_name (UProduct ty_name) = ty_name
 |  get_uval_name (UAbstract ty_name) = ty_name
\<close>

ML\<open> fun get_uval_names uvals = map get_uval_name uvals;\<close>

ML\<open> (* get_uval_sigil *)
fun get_uval_sigil (URecord (_, sigil)) = sigil
 |  get_uval_sigil _ = error "get_uval_sigil failed. The tyep of this argument is not URecord."
\<close>

ML\<open> val get_uval_writable_records =
 filter (fn uval => case uval of (URecord (_, Writable)) => true | _ => false);
\<close>

ML\<open> val get_uval_unbox_records =
 filter (fn uval => case uval of (URecord (_, Unboxed)) => true | _ => false);
\<close>

ML\<open> val get_uval_readonly_records =
 filter (fn uval => case uval of (URecord (_, ReadOnly)) => true | _ => false);
\<close>

ML\<open> fun usum_list_of_checked uval = case uval of
    USum (_, checked) => checked
  | _ => error ("usum_list_of_checked: not USum")
\<close>

ML\<open> fun is_UAbstract (UAbstract _) = true
      | is_UAbstract  _            = false;
\<close>

ML\<open> fun get_ty_nm_C uval = uval |> get_uval_name |> (fn nm => nm ^ "_C"); \<close>

ML\<open> fun heap_info_uval_to_struct_info (heap:HeapLiftBase.heap_info) (uval:uval) =
 let
  val uval_C_nm = get_uval_name uval ^ "_C";
 in
  Symtab.lookup (#structs heap) uval_C_nm
  |> Utils.the' ("This heap_info does not have structs." ^ uval_C_nm)
 end : HeapLiftBase.struct_info;
\<close>

ML\<open> fun heap_info_uval_to_field_names heap_info uval =
 heap_info_uval_to_struct_info heap_info uval |> #field_info |> map #name;
\<close>

ML\<open> fun heap_info_uval_to_field_types heap_info uval =
 heap_info_uval_to_struct_info heap_info uval |> #field_info |> map #field_type;
\<close>

text\<open> The functions related to AutoCorres.\<close>

ML\<open> fun ac_mk_struct_info_for file_nm thy uval =
(* checks if autocorres generates struct_info for a given uval. Returns a boolean value.*)
 let
  val st_C_nm   = get_ty_nm_C uval;
  val heap_info = Symtab.lookup (HeapInfo.get thy) file_nm
                 |> Utils.the' "heap_info in ac_mk_struct_info_for failed."
                 |> #heap_info;
  val flag      = Symtab.lookup (#structs heap_info) st_C_nm |> is_some;
 in flag end;
\<close>

ML\<open> fun get_uvals_for_which_ac_mk_st_info file_nm thy uvals =
 (* returns a list of uvals for which autocorres creates struct info.*)
 filter (ac_mk_struct_info_for file_nm thy) uvals;
\<close>

ML\<open> fun get_uvals_for_which_ac_mk_heap_getters file_nm thy uvals =
 (* returns a list of uvals for which autocorres creates #heap_getters info.*)
 filter (fn uval => ac_mk_heap_getters_for file_nm thy (get_ty_nm_C uval)) uvals;
\<close>
end
