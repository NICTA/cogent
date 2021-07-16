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

theory UpdateSemantics
  imports Cogent
begin

datatype ('f, 'a, 'l) uval = UPrim lit
                           | UProduct "('f,'a,'l) uval" "('f,'a,'l) uval"
                           | USum name "('f,'a,'l) uval" "(name \<times> repr) list"
                           | URecord "(('f,'a,'l) uval \<times> repr) list"
                           | UAbstract "'a"
                           | UFunction "'f expr" "type list"
                           | UAFunction "'f" "type list"
                           | UUnit
                           | UPtr "'l" repr

(* NB: The "type" in the store is just a tag used for the C proofs.
 *     The u_sem rules simply carry this tag along into the updated store. *)
type_synonym ('f, 'a, 'l) store = "'l \<Rightarrow> ('f, 'a, 'l) uval option"


type_synonym ('f,'a,'l) ufundef = "('f,'a,'l) store \<times> ('f,'a,'l) uval
                                 \<Rightarrow> ('f,'a,'l) store \<times> ('f,'a,'l) uval
                                 \<Rightarrow> bool"

type_synonym ('f, 'a, 'l) uabsfuns = "'f \<Rightarrow> ('f, 'a, 'l) ufundef"

definition eval_prim_u :: "prim_op \<Rightarrow> ('f, 'a, 'l) uval list \<Rightarrow> ('f, 'a, 'l) uval"
where
  "eval_prim_u pop xs = UPrim (eval_prim_op pop (map (\<lambda>vv. case vv of UPrim v \<Rightarrow> v | _ \<Rightarrow> LBool False) xs))"




inductive u_sem :: "('f,'a,'l) uabsfuns
                  \<Rightarrow> ('f,'a,'l) uval env
                  \<Rightarrow> ('f,'a,'l) store \<times> 'f expr
                  \<Rightarrow> ('f,'a,'l) store \<times> ('f,'a,'l) uval
                  \<Rightarrow> bool"
          ("_, _ \<turnstile> _ \<Down>! _" [30,0,0,20] 60)
and       u_sem_all :: "('f,'a,'l) uabsfuns
                      \<Rightarrow> ('f,'a,'l) uval env
                      \<Rightarrow> ('f,'a,'l) store \<times> 'f expr list
                      \<Rightarrow> ('f,'a,'l) store \<times> ('f,'a,'l) uval list
                      \<Rightarrow> bool"
          ("_, _ \<turnstile>* _ \<Down>! _" [30,0,0,20] 60)
where
  u_sem_var     : "\<xi> , \<gamma> \<turnstile> (\<sigma>, Var i) \<Down>! (\<sigma>, \<gamma> ! i)"

| u_sem_lit     : "\<xi> , \<gamma> \<turnstile> (\<sigma>, Lit l) \<Down>! (\<sigma>, UPrim l)"

| u_sem_prim    : "\<lbrakk> \<xi> , \<gamma> \<turnstile>* (\<sigma>, as) \<Down>! (\<sigma>', as')
                   \<rbrakk> \<Longrightarrow>  \<xi> , \<gamma> \<turnstile> (\<sigma>, Prim p as) \<Down>! (\<sigma>', eval_prim_u p as')"

| u_sem_cast    : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, e) \<Down>! (\<sigma>', UPrim l)
                   ; cast_to \<tau> l = Some l'
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Cast \<tau> e) \<Down>! (\<sigma>', UPrim l')"

| u_sem_fun     : "\<xi> , \<gamma> \<turnstile> (\<sigma>, Fun f ts) \<Down>! (\<sigma>, UFunction f ts)"

| u_sem_afun    : "\<xi> , \<gamma> \<turnstile> (\<sigma>, AFun f ts) \<Down>! (\<sigma>, UAFunction f ts)"

| u_sem_abs_app : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma> , x) \<Down>! (\<sigma>' , UAFunction f ts)
                   ; \<xi> , \<gamma> \<turnstile> (\<sigma>', y) \<Down>! (\<sigma>'', a)
                   ; \<xi> f (\<sigma>'', a) (\<sigma>''', r)
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, App x y) \<Down>! (\<sigma>''', r)"

| u_sem_app     : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma> , x) \<Down>! (\<sigma>' , UFunction f ts)
                   ; \<xi> , \<gamma> \<turnstile> (\<sigma>', y) \<Down>! (\<sigma>'', a)
                   ; \<xi> , [ a ] \<turnstile> (\<sigma>'', specialise ts f) \<Down>! st
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, App x y) \<Down>! st"

| u_sem_con     : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', x')
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Con ts t x) \<Down>! (\<sigma>', USum t x' (map (\<lambda>(n,t,_). (n,type_repr t)) ts))"

| u_sem_member  : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, e) \<Down>! (\<sigma>', URecord fs)
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Member e f) \<Down>! (\<sigma>', fst (fs ! f))"

| u_sem_memb_b  : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, e) \<Down>! (\<sigma>', UPtr p r)
                   ; \<sigma>' p = Some (URecord fs)
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Member e f) \<Down>! (\<sigma>', fst (fs ! f))"

| u_sem_unit    : "\<xi> , \<gamma> \<turnstile> (\<sigma>, Unit) \<Down>! (\<sigma>, UUnit)"

| u_sem_tuple   : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma> , x) \<Down>! (\<sigma>' , x')
                   ; \<xi> , \<gamma> \<turnstile> (\<sigma>', y) \<Down>! (\<sigma>'', y')
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Tuple x y) \<Down>! (\<sigma>'', UProduct x' y')"

| u_sem_esac    : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, t) \<Down>! (\<sigma>', USum tag v ts')
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Esac t tag) \<Down>! (\<sigma>', v)"

| u_sem_let     : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', a')
                   ; \<xi> , (a' # \<gamma>) \<turnstile> (\<sigma>', b) \<Down>! st
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Let a b) \<Down>! st"

| u_sem_letbang : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', a')
                   ; \<xi> , (a' # \<gamma>) \<turnstile> (\<sigma>', b) \<Down>! st
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, LetBang vs a b) \<Down>! st"

| u_sem_case_m  : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', USum t v ts)
                   ; \<xi> , (v # \<gamma>) \<turnstile> (\<sigma>', m) \<Down>! st
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Case x t m n) \<Down>! st"

| u_sem_case_nm : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', USum t' v rs)
                   ; t' \<noteq> t
                   ; \<xi> , (USum t' v rs # \<gamma>) \<turnstile> (\<sigma>', n) \<Down>! st
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Case x t m n) \<Down>! st"

| u_sem_if      : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UPrim (LBool b))
                   ; \<xi> , \<gamma> \<turnstile> (\<sigma>', if b then t else e) \<Down>! st
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, If x t e) \<Down>! st"

| u_sem_struct  : "\<lbrakk> \<xi> , \<gamma> \<turnstile>* (\<sigma>, xs) \<Down>! (\<sigma>', vs)
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Struct ts xs) \<Down>! (\<sigma>', URecord (zip vs (map type_repr ts)))"

| u_sem_take    : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UPtr p r)
                   ; \<sigma>' p = Some (URecord fs)
                   ; \<xi> , (fst (fs ! f) # UPtr p r # \<gamma>) \<turnstile> (\<sigma>', e) \<Down>! st
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Take x f e) \<Down>! st"

| u_sem_take_ub : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', URecord fs)
                   ; \<xi> , (fst (fs ! f) # URecord fs # \<gamma>) \<turnstile> (\<sigma>', e) \<Down>! st
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Take x f e) \<Down>! st"

| u_sem_put     : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UPtr p r)
                   ; \<sigma>' p = Some (URecord fs)
                   ; \<xi> , \<gamma> \<turnstile> (\<sigma>', e) \<Down>! (\<sigma>'', e')
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Put x f e)
                      \<Down>! (\<sigma>'' (p := Some (URecord (fs [ f := (e', snd (fs ! f) )]))), UPtr p r)"

| u_sem_put_ub  : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', URecord fs)
                   ; \<xi> , \<gamma> \<turnstile> (\<sigma>', e) \<Down>! (\<sigma>'', e')
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Put x f e) \<Down>! (\<sigma>'', URecord (fs [ f := (e', snd (fs ! f)) ]))"


| u_sem_split   : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UProduct a b)
                   ; \<xi> , (a # b # \<gamma>) \<turnstile> (\<sigma>', e) \<Down>! st
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Split x e) \<Down>! st"


| u_sem_promote : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, e) \<Down>! e'
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Promote t' e) \<Down>! e'"

| u_sem_all_empty : "\<xi> , \<gamma> \<turnstile>* (\<sigma>, []) \<Down>! (\<sigma>, [])"

| u_sem_all_cons  : "\<lbrakk> \<xi> , \<gamma> \<turnstile>  (\<sigma> , x ) \<Down>! (\<sigma>' , v )
                     ; \<xi> , \<gamma> \<turnstile>* (\<sigma>', xs) \<Down>! (\<sigma>'', vs)
                     \<rbrakk> \<Longrightarrow>  \<xi> , \<gamma> \<turnstile>* (\<sigma>, x # xs) \<Down>! (\<sigma>'', v # vs)"

definition frame :: "('f, 'a, 'l) store \<Rightarrow> 'l set \<Rightarrow> ('f, 'a, 'l) store \<Rightarrow> 'l set \<Rightarrow> bool"
           where
  "frame \<sigma> pi \<sigma>' po \<equiv> \<forall>p. (p \<in> pi \<and> p \<notin> po \<longrightarrow> \<sigma>' p = None)
                       \<and>  (p \<notin> pi \<and> p \<in> po \<longrightarrow> \<sigma>  p = None)
                       \<and>  (p \<notin> pi \<and> p \<notin> po \<longrightarrow> \<sigma>  p = \<sigma>' p)"


locale update_sem =
  fixes abs_typing :: "'a \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> sigil \<Rightarrow> 'l set \<Rightarrow> 'l set \<Rightarrow> ('f, 'a, 'l) store \<Rightarrow> bool"
  and   abs_repr   :: "'a \<Rightarrow> name \<times> repr list"
  assumes abs_typing_bang : "abs_typing av n \<tau>s s r w \<sigma> \<Longrightarrow> abs_typing av n (map bang \<tau>s) (bang_sigil s) (r \<union> w) {} \<sigma>"
  and     abs_typing_noalias : "abs_typing av n \<tau>s s r w \<sigma> \<Longrightarrow> r \<inter> w = {}"
  and     abs_typing_readonly : "sigil_perm s \<noteq> Some Writable \<Longrightarrow> abs_typing av n \<tau>s s r w \<sigma> \<Longrightarrow> w = {}"
  and     abs_typing_escape   : "sigil_perm s \<noteq> Some ReadOnly \<Longrightarrow> [] \<turnstile>* \<tau>s :\<kappa> k \<Longrightarrow> E \<in> k
                                  \<Longrightarrow> abs_typing av n \<tau>s s r w \<sigma> \<Longrightarrow> r = {}"
  and     abs_typing_valid : "abs_typing av n \<tau>s s r w \<sigma> \<Longrightarrow> p \<in> r \<union> w \<Longrightarrow> \<sigma> p \<noteq> None"
  and     abs_typing_unique_repr   : "abs_typing av n \<tau>s s r w \<sigma> \<Longrightarrow> abs_typing av n' \<tau>s' s' r' w' \<sigma>
                                    \<Longrightarrow> type_repr (TCon n \<tau>s s) = type_repr (TCon n' \<tau>s' s')"
  and     abs_typing_repr : "abs_typing av n \<tau>s s r w \<sigma> \<Longrightarrow> abs_repr av = (n, map type_repr \<tau>s)"
  and     abs_typing_frame: "frame \<sigma> u \<sigma>' u' \<Longrightarrow> abs_typing av n \<tau>s s r w \<sigma> \<Longrightarrow> r \<inter> u = {}
                              \<Longrightarrow> w \<inter> u = {} \<Longrightarrow> abs_typing av n \<tau>s s r w \<sigma>'"

context update_sem begin

fun uval_repr :: "('f, 'a, 'l) uval \<Rightarrow> repr" where
  "uval_repr (UPrim lit) = RPrim (lit_type lit)"
| "uval_repr (UProduct a b) = RProduct (uval_repr a) (uval_repr b)"
| "uval_repr (USum a b reprs) = RSum reprs"
| "uval_repr (URecord fs) = RRecord (map snd fs)"
| "uval_repr (UAbstract a) = (let (x,y) = abs_repr a in RCon x y)"
| "uval_repr (UFunction _ _) = RFun"
| "uval_repr (UAFunction _ _) = RFun"
| "uval_repr (UUnit) = RUnit"
| "uval_repr (UPtr p r) = RPtr r"

fun uval_repr_deep :: "('f, 'a, 'l) uval \<Rightarrow> repr" where
  "uval_repr_deep (UPrim lit) = RPrim (lit_type lit)"
| "uval_repr_deep (UProduct a b) = RProduct (uval_repr_deep a) (uval_repr_deep b)"
| "uval_repr_deep (USum a b reprs) = RSum reprs"
| "uval_repr_deep (URecord fs) = RRecord (map uval_repr_deep (map fst fs))"
| "uval_repr_deep (UAbstract a) = (let (x,y) = abs_repr a in RCon x y)"
| "uval_repr_deep (UFunction _ _) = RFun"
| "uval_repr_deep (UAFunction _ _) = RFun"
| "uval_repr_deep (UUnit) = RUnit"
| "uval_repr_deep (UPtr p r) = RPtr r"

inductive uval_typing :: "('f \<Rightarrow> poly_type)
                       \<Rightarrow> ('f, 'a, 'l) store
                       \<Rightarrow> ('f, 'a, 'l) uval
                       \<Rightarrow> type
                       \<Rightarrow> 'l set
                       \<Rightarrow> 'l set
                       \<Rightarrow> bool"  ("_, _ \<turnstile> _ :u _ \<langle>_, _\<rangle>" [30,0,0,0,20] 80)
and uval_typing_record :: "('f \<Rightarrow> poly_type)
                        \<Rightarrow> ('f, 'a, 'l) store
                        \<Rightarrow> (('f, 'a, 'l) uval \<times> repr) list
                        \<Rightarrow> (name \<times> type \<times> record_state) list
                        \<Rightarrow> 'l set
                        \<Rightarrow> 'l set
                        \<Rightarrow> bool" ("_, _ \<turnstile>* _ :ur _ \<langle>_, _\<rangle>" [30,0,0,0,20] 80) where


  u_t_prim     : "\<Xi>, \<sigma> \<turnstile> UPrim l :u TPrim (lit_type l) \<langle>{}, {}\<rangle>"

| u_t_product  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile> a :u t \<langle>r , w \<rangle>
                  ; \<Xi>, \<sigma> \<turnstile> b :u u \<langle>r', w'\<rangle>
                  ; w  \<inter> w' = {}
                  ; w  \<inter> r' = {}
                  ; w' \<inter> r  = {}
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UProduct a b :u TProduct t u \<langle>r \<union> r', w \<union> w'\<rangle>"

| u_t_sum      : "\<lbrakk> \<Xi>, \<sigma> \<turnstile> a :u t \<langle>r, w\<rangle>
                  ; (tag, t, Unchecked) \<in> set ts
                  ; distinct (map fst ts)
                  ; [] \<turnstile> TSum ts wellformed
                  ; rs = map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) ts
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> USum tag a rs :u TSum ts \<langle>r, w\<rangle>"

| u_t_struct   : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r, w\<rangle>
                  ; distinct (map fst ts)
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> URecord fs :u TRecord ts Unboxed \<langle>r, w\<rangle>"

| u_t_abstract : "\<lbrakk> abs_typing a n ts Unboxed r w \<sigma>
                  ; [] \<turnstile>* ts wellformed
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UAbstract a :u TCon n ts Unboxed \<langle>r, w\<rangle>"

| u_t_afun     : "\<lbrakk> \<Xi> f = (ks, a, b)
                  ; list_all2 (kinding []) ts ks
                  ; ks \<turnstile> TFun a b wellformed
                  ; [] \<turnstile> TFun (instantiate ts a) (instantiate ts b) \<sqsubseteq> TFun a' b'
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UAFunction f ts :u TFun a' b' \<langle>{}, {}\<rangle>"

| u_t_function : "\<lbrakk> \<Xi> , K , [ Some t ] \<turnstile> f : u
                  ; K \<turnstile> t wellformed
                  ; list_all2 (kinding []) ts K
                  ; [] \<turnstile> TFun (instantiate ts t) (instantiate ts u) \<sqsubseteq> TFun t' u'
                  \<rbrakk> \<Longrightarrow> \<Xi> , \<sigma> \<turnstile> UFunction f ts :u TFun t' u' \<langle>{}, {}\<rangle>"

| u_t_unit     : "\<Xi>, \<sigma> \<turnstile> UUnit :u TUnit \<langle>{}, {}\<rangle>"

| u_t_p_rec_ro : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r, {}\<rangle>
                  ; \<sigma> l = Some (URecord fs)
                  ; distinct (map fst ts)
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UPtr l (RRecord (map (type_repr \<circ> fst \<circ> snd) ts)) :u TRecord ts (Boxed ReadOnly ptrl) \<langle>insert l r, {}\<rangle>"

| u_t_p_rec_w  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r, w\<rangle>
                  ; \<sigma> l = Some (URecord fs)
                  ; l \<notin> (w \<union> r)
                  ; distinct (map fst ts)
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UPtr l (RRecord (map (type_repr \<circ> fst \<circ> snd) ts)) :u TRecord ts (Boxed Writable ptrl) \<langle>r, insert l w\<rangle>"

| u_t_p_abs_ro : "\<lbrakk> s = Boxed ReadOnly ptrl
                  ; abs_typing a n ts s r {} \<sigma>
                  ; [] \<turnstile>* ts wellformed
                  ; \<sigma> l = Some (UAbstract a)
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UPtr l (RCon n (map type_repr ts)) :u TCon n ts s \<langle>insert l r, {}\<rangle>"

| u_t_p_abs_w  : "\<lbrakk> s = Boxed Writable ptrl
                  ; abs_typing a n ts s r w \<sigma>
                  ; [] \<turnstile>* ts wellformed
                  ; \<sigma> l = Some (UAbstract a)
                  ; l \<notin> (w \<union> r)
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UPtr l (RCon n (map type_repr ts)) :u TCon n ts s \<langle>r, insert l w\<rangle>"

| u_t_r_empty  : "\<Xi>, \<sigma> \<turnstile>* [] :ur [] \<langle>{}, {}\<rangle>"
| u_t_r_cons1  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  x  :u  t  \<langle>r , w \<rangle>
                  ; \<Xi>, \<sigma> \<turnstile>* xs :ur ts \<langle>r', w'\<rangle>
                  ; w  \<inter> w' = {}
                  ; w  \<inter> r' = {}
                  ; w' \<inter> r  = {}
                  ; type_repr t = rp
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile>* ((x,rp) # xs) :ur ((n, t, Present) # ts) \<langle>r \<union> r', w \<union> w'\<rangle>"

| u_t_r_cons2  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* xs :ur ts \<langle>r, w\<rangle>
                  ; [] \<turnstile> t wellformed
                  ; type_repr t = rp
                  ; uval_repr x = rp
                  ; uval_repr_deep x = rp
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile>* ((x,rp) # xs) :ur ((n, t, Taken) # ts) \<langle>r, w\<rangle>"

lemma u_t_prim' : "\<tau> = lit_type l \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UPrim l :u TPrim \<tau> \<langle>{}, {}\<rangle>"
   by (simp add: u_t_prim)

inductive_cases u_t_primE     [elim] : "\<Xi>, \<sigma> \<turnstile> UPrim l :u TPrim \<tau> \<langle>r, w\<rangle>"
inductive_cases u_t_functionE [elim] : "\<Xi>, \<sigma> \<turnstile> UFunction f ts :u TFun \<tau> \<rho> \<langle>r, w\<rangle>"
inductive_cases u_t_afunE     [elim] : "\<Xi>, \<sigma> \<turnstile> UAFunction f ts :u TFun \<tau> \<rho> \<langle>r, w\<rangle>"
inductive_cases u_t_sumE      [elim] : "\<Xi>, \<sigma> \<turnstile> v :u TSum \<tau>s \<langle>r, w\<rangle>"
inductive_cases u_t_productE  [elim] : "\<Xi>, \<sigma> \<turnstile> UProduct a b :u TProduct \<tau> \<rho> \<langle>r, w\<rangle>"
inductive_cases u_t_recE      [elim] : "\<Xi>, \<sigma> \<turnstile> URecord fs :u \<tau> \<langle>r, w\<rangle>"
inductive_cases u_t_p_recE    [elim] : "\<Xi>, \<sigma> \<turnstile> UPtr p rp :u TRecord fs s \<langle>r, w\<rangle>"
inductive_cases u_t_r_emptyE  [elim] : "\<Xi>, \<sigma> \<turnstile>* [] :ur \<tau>s \<langle>r, w\<rangle>"
inductive_cases u_t_r_consE   [elim] : "\<Xi>, \<sigma> \<turnstile>* (x # xs) :ur \<tau>s \<langle>r, w\<rangle>"

inductive uval_typing_all :: "('f \<Rightarrow> poly_type)
                            \<Rightarrow> ('f, 'a, 'l) store
                            \<Rightarrow> ('f, 'a, 'l) uval list
                            \<Rightarrow> type list
                            \<Rightarrow> 'l set
                            \<Rightarrow> 'l set
                            \<Rightarrow> bool" ("_, _ \<turnstile>* _ :u _ \<langle>_, _\<rangle>" [30,0,0,0,0,20] 80) where
  u_t_all_empty  : "\<Xi>, \<sigma> \<turnstile>* [] :u [] \<langle>{}, {}\<rangle>"

| u_t_all_cons   : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  x  :u t  \<langle>r , w \<rangle>
                    ; \<Xi>, \<sigma> \<turnstile>* xs :u ts \<langle>r', w'\<rangle>
                    ; w  \<inter> w' = {}
                    ; w  \<inter> r' = {}
                    ; w' \<inter> r  = {}
                    \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile>* (x # xs) :u (t # ts) \<langle>r \<union> r', w \<union> w'\<rangle>"

inductive matches_ptrs :: "('f \<Rightarrow> poly_type)
                         \<Rightarrow> ('f, 'a, 'l) store
                         \<Rightarrow> ('f, 'a, 'l) uval env
                         \<Rightarrow> ctx
                         \<Rightarrow> 'l set
                         \<Rightarrow> 'l set
                         \<Rightarrow> bool" ("_, _ \<turnstile> _ matches _ \<langle>_, _\<rangle>" [30,0,0,0,0,20] 60) where

  matches_ptrs_empty : "\<Xi>, \<sigma> \<turnstile> [] matches [] \<langle>{}, {}\<rangle>"

| matches_ptrs_none  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile> xs matches \<Gamma> \<langle>r, w\<rangle>
                        \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> (x # xs) matches (None # \<Gamma>) \<langle>r, w\<rangle>"

| matches_ptrs_some  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile> x  :u      t  \<langle>r , w \<rangle>
                        ; \<Xi>, \<sigma> \<turnstile> xs matches ts \<langle>r', w'\<rangle>
                        ; w  \<inter> w' = {}
                        ; w  \<inter> r' = {}
                        ; w' \<inter> r  = {}
                        \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> (x # xs) matches (Some t # ts) \<langle>r \<union> r', w \<union> w'\<rangle>"

inductive_cases matches_ptrs_consE: "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (\<tau> # \<tau>s) \<langle> r , w \<rangle>"

definition proc_env_matches_ptrs :: "(('f,'a,'l) uabsfuns) \<Rightarrow> ('f \<Rightarrow> poly_type) \<Rightarrow> bool"
           ("_ matches-u _" [30,20] 60) where
  "\<xi> matches-u \<Xi> \<equiv> (\<forall> f. let (K, \<tau>i, \<tau>o) = \<Xi> f
                          in (\<forall> \<sigma> \<sigma>' \<tau>s v v' r w. list_all2 (kinding []) \<tau>s K
                                             \<longrightarrow> (\<Xi> , \<sigma> \<turnstile> v   :u instantiate \<tau>s \<tau>i \<langle>r, w\<rangle>)
                                             \<longrightarrow> \<xi> f (\<sigma>, v) (\<sigma>', v')
                                             \<longrightarrow> (\<exists>r' w'. (\<Xi> , \<sigma>' \<turnstile> v' :u instantiate \<tau>s \<tau>o \<langle>r', w'\<rangle>)
                                              \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w')))"


lemma uval_typing_to_wellformed:
  shows "\<Xi>, \<sigma> \<turnstile> v :u t \<langle>r, w\<rangle> \<Longrightarrow> [] \<turnstile> t wellformed"
    and "\<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r, w\<rangle> \<Longrightarrow> [] \<turnstile>* (map (fst \<circ> snd) ts) wellformed"
proof (induct rule: uval_typing_uval_typing_record.inducts)
  case (u_t_function \<Xi> K t f u ts t' u' \<sigma>)
  then show ?case
    apply -
    apply (rule subtyping_wellformed_preservation)
     apply assumption
    apply (fastforce intro: instantiate_wellformed dest: typing_to_wellformed list_all2_kinding_wellformedD)
    done
next case u_t_afun     then show ?case
    by (fastforce intro: subtyping_wellformed_preservation instantiate_wellformed dest: list_all2_kinding_wellformedD)
qed  (auto simp add: list_all_iff)


lemma uval_typing_all_record:
  assumes
    "\<Xi>, \<sigma> \<turnstile>* vs :u ts \<langle>r, w\<rangle>"
    "length ns = length ts"
  shows
    "\<Xi>, \<sigma> \<turnstile>* (zip vs (map (type_repr) ts)) :ur zip ns (zip ts (replicate (length ts) Present)) \<langle>r, w\<rangle>"
  using assms
proof (induct arbitrary: ns rule: uval_typing_all.induct)
qed (auto intro!: uval_typing_uval_typing_record.intros simp add: length_Suc_conv)

lemma uval_typing_pointers_noalias:
  shows "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  v  :u  \<tau>  \<langle> r , w \<rangle> \<rbrakk> \<Longrightarrow> r \<inter> w = {}"
    and "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* vs :ur \<tau>s \<langle> r , w \<rangle> \<rbrakk> \<Longrightarrow> r \<inter> w = {}"
proof (induct rule: uval_typing_uval_typing_record.inducts)
  case (u_t_abstract a n ts r w \<Xi> \<sigma>)
  then show ?case using abs_typing_readonly by force
next
  case (u_t_p_abs_w a n ts r \<sigma> l w \<Xi> ptrl)
  then show ?case using abs_typing_noalias by blast
qed auto

lemma shareable_not_writable:
assumes "S \<in> k"
shows "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  v  :u  \<tau>  \<langle> r , w \<rangle>; K \<turnstile>  \<tau>  :\<kappa>  k \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s \<langle> r , w \<rangle>; K \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
  using assms
  by (induct rule: uval_typing_uval_typing_record.inducts)
    (fastforce
      simp add: kinding_simps kinding_record_simps kinding_variant_set
      dest: abs_typing_readonly[where s = Unboxed,simplified])+

lemma discardable_not_writable:
assumes "D \<in> k"
shows "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  v  :u  \<tau>  \<langle> r , w \<rangle>; K \<turnstile>  \<tau>  :\<kappa>  k \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s \<langle> r , w \<rangle>; K \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
  using assms
  by (induct rule: uval_typing_uval_typing_record.inducts)
    (force simp add: kinding_simps kinding_record_simps kinding_variant_set
      dest: abs_typing_readonly[where s = Unboxed,simplified])+


lemma discardable_not_writable_all:
assumes "D \<in> k"
shows   "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs :u \<tau>s \<langle> r , w \<rangle>; K \<turnstile>* \<tau>s :\<kappa> k \<rbrakk> \<Longrightarrow> w = {}"
proof (induct rule: uval_typing_all.induct)
qed (auto simp add: kinding_simps kinding_all_simps dest: discardable_not_writable [OF assms])

lemma escapable_no_readers:
shows   "\<lbrakk> \<Xi> , \<sigma> \<turnstile>  x  :u  \<tau>  \<langle>r, w\<rangle> ; E \<in> k; [] \<turnstile>  \<tau>  :\<kappa>  k \<rbrakk> \<Longrightarrow> r = {}"
and     "\<lbrakk> \<Xi> , \<sigma> \<turnstile>* xs :ur \<tau>s \<langle>r, w\<rangle> ; E \<in> k; [] \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> r = {}"
proof (induct arbitrary: k and k rule: uval_typing_uval_typing_record.inducts)
next
  case (u_t_p_abs_w s ptrl n ts r w \<sigma> l \<Xi>)
  then show ?case using abs_typing_escape[where s=s]
    by (fastforce simp add: kinding_simps)
qed (fastforce dest!: abs_typing_escape [where s = Unboxed , simplified, rotated -1]
               simp add: kinding_simps kinding_record_simps kinding_all_set kinding_variant_set)+


lemma map_tprim_kinding:
shows "[] \<turnstile>* map (TPrim) \<tau>s :\<kappa> {D,S,E}"
  by (induct \<tau>s) (auto simp add: kinding_simps kinding_all_simps)

lemma tprim_no_pointers:
assumes "\<Xi> , \<sigma> \<turnstile> v :u TPrim \<tau> \<langle>r, w\<rangle>"
shows   "r = {}"
and     "w = {}"
proof -
  from assms show "w = {}"by (auto intro!: discardable_not_writable(1) [OF _ assms, where k = "{D}"]
                                   simp add: kinding_simps)
  from assms show "r = {}"by (auto elim!:  uval_typing.cases)
qed

lemma tfun_no_pointers:
assumes "\<Xi> , \<sigma> \<turnstile> v :u TFun \<tau> \<rho> \<langle>r, w\<rangle>"
shows   "r = {}"
and     "w = {}"
proof -
  from assms show "w = {}" by (auto elim!:  uval_typing.cases)
  from assms show "r = {}" by (auto elim!:  uval_typing.cases)
qed

lemma map_tprim_no_pointers:
assumes "\<Xi> , \<sigma> \<turnstile>* vs :u map TPrim \<tau>s \<langle>r, w\<rangle>"
shows   "r = {}"
and     "w = {}"
using assms proof -
obtain ys where X: "map TPrim \<tau>s = ys" by (clarsimp)
show "r = {}" using assms [simplified X] X
  proof (induct arbitrary: \<tau>s rule: uval_typing_all.induct )
       case u_t_all_empty then show ?case by (simp)
  next case u_t_all_cons  with X show ?case apply (clarsimp)
                                            apply (rule tprim_no_pointers, simp).
  qed

show "w = {}" using assms apply -
                          apply (rule discardable_not_writable_all [where k = "{D, S, E}"])
                          apply (auto intro: map_tprim_kinding).
qed

lemma map_tprim_no_pointers':
assumes "\<Xi> , \<sigma> \<turnstile>* vs :u map TPrim \<tau>s \<langle>r, w\<rangle>"
shows   "\<Xi> , \<sigma> \<turnstile>* vs :u map TPrim \<tau>s \<langle>{}, {}\<rangle>"
using assms by (auto dest: map_tprim_no_pointers)


lemma matches_ptrs_none [simp]:
shows "(\<Xi>, \<sigma> \<turnstile> (x # xs) matches (None # ts) \<langle>r , w\<rangle>)
     = (\<Xi>, \<sigma> \<turnstile> xs       matches ts \<langle>r , w\<rangle>)"
proof (rule iffI)
     assume "\<Xi>, \<sigma> \<turnstile> (x # xs) matches (None # ts) \<langle>r, w\<rangle>"
then show   "\<Xi>, \<sigma> \<turnstile> xs       matches ts          \<langle>r, w\<rangle>"
     by (auto elim: matches_ptrs.cases)

next assume "\<Xi>, \<sigma> \<turnstile> xs       matches ts          \<langle>r, w\<rangle>"
then show   "\<Xi>, \<sigma> \<turnstile> (x # xs) matches (None # ts) \<langle>r, w\<rangle>"
     by (auto intro: matches_ptrs.intros)
qed



lemma pointerset_helper:
assumes "\<Xi>, \<sigma> \<turnstile> v :u \<tau> \<langle>r, w\<rangle>"
and     "r = r'"
and     "w = w'"
shows   "\<Xi>, \<sigma> \<turnstile> v :u \<tau> \<langle>r', w'\<rangle>"
using assms by auto

lemma pointerset_helper_record:
assumes "\<Xi>, \<sigma> \<turnstile>* vs :ur \<tau>s \<langle>r, w\<rangle>"
and     "r = r'"
and     "w = w'"
shows   "\<Xi>, \<sigma> \<turnstile>* vs :ur \<tau>s \<langle>r', w'\<rangle>"
using assms by auto


lemma pointerset_helper_matches_ptrs:
assumes "\<Xi>, \<sigma> \<turnstile> vs matches \<tau>s \<langle>r, w\<rangle>"
and     "r = r'"
and     "w = w'"
shows   "\<Xi>, \<sigma> \<turnstile> vs matches \<tau>s \<langle>r', w'\<rangle>"
using assms by auto

lemma pointerset_helper_frame:
assumes "frame \<sigma> w \<sigma>' w'"
and     "w  = u "
and     "w' = u'"
shows   "frame \<sigma> u \<sigma>' u'"
using assms by auto



lemma bang_idempotent':
shows "((\<lambda>(c, t). (c, bang t)) \<circ> (\<lambda>(a, b). (a, bang b))) = (\<lambda>(c,t).(c,bang t))"
by (rule ext, clarsimp simp: bang_idempotent)

lemma list_all2_bang_type_helper:
 "\<lbrakk> list_all2 (\<lambda>t. (=) (type_repr t)) ts rs ; [] \<turnstile>* ts :\<kappa>  k\<rbrakk>
        \<Longrightarrow> list_all2 (\<lambda>t. (=) (type_repr t)) (map (bang) ts) rs"
  by (induct rule: list_all2_induct; auto simp add: kinding_simps kinding_all_simps intro!: bang_type_repr)

lemma bang_type_repr':
assumes "[] \<turnstile>* ts :\<kappa>r k"
shows   "(map (type_repr \<circ> fst \<circ> snd \<circ> apsnd (apfst bang)) ts) = (map (type_repr \<circ> fst \<circ> snd) ts)"
  using assms
  by (fastforce dest: bang_type_repr)

lemma uval_typing_bang:
shows   "\<Xi>, \<sigma> \<turnstile> v :u \<tau> \<langle>r, w\<rangle> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> v :u bang \<tau> \<langle>r \<union> w, {}\<rangle>"
and     "\<Xi>, \<sigma> \<turnstile>* vs :ur \<tau>s \<langle>r, w\<rangle> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile>* vs :ur  (map (apsnd (apfst bang)) \<tau>s) \<langle>r \<union> w, {}\<rangle>"
proof (induct rule: uval_typing_uval_typing_record.inducts)
  case u_t_product then show ?case
    by (auto dest: uval_typing_uval_typing_record.u_t_product intro: pointerset_helper)
next
  case (u_t_sum \<Xi> \<sigma> a t r w g ts rs)
  then show ?case
    using bang_wellformed
    by (force intro!: uval_typing_uval_typing_record.intros simp: list_all_iff)
next
  case u_t_abstract then show ?case
    by (force intro: uval_typing_uval_typing_record.intros bang_wellformed abs_typing_bang[where s = Unboxed, simplified])
next
  case (u_t_p_rec_ro \<Xi> \<sigma> fs ts r l ptrl)
  moreover have "\<Xi>, \<sigma> \<turnstile> UPtr l (RRecord (map (type_repr \<circ> fst \<circ> snd \<circ> apsnd (apfst bang)) ts)) :u TRecord (map (apsnd (apfst bang)) ts) (Boxed ReadOnly ptrl) \<langle>insert l r, {}\<rangle>"
    using u_t_p_rec_ro
    by (fastforce dest: uval_typing_to_wellformed(2) uval_typing_uval_typing_record.u_t_p_rec_ro)
  ultimately show ?case
    by (force dest: uval_typing_to_wellformed(2) simp add: fst_apfst_compcomp snd_apsnd_compcomp map_snd3_keep)
next
  case (u_t_p_rec_w \<Xi> \<sigma> fs ts r w l ptrl)
  moreover have "\<Xi>, \<sigma> \<turnstile> UPtr l (RRecord (map (type_repr \<circ> fst \<circ> snd \<circ> apsnd (apfst bang)) ts)) :u TRecord (map (apsnd (apfst bang)) ts) (Boxed ReadOnly ptrl) \<langle>insert l (r \<union> w), {}\<rangle>"
    using u_t_p_rec_w uval_typing_uval_typing_record.u_t_p_rec_ro by fastforce
  ultimately show ?case
    by (auto dest!: uval_typing_to_wellformed(2) simp add: fst_apfst_compcomp snd_apsnd_compcomp map_snd3_keep)
next
  case (u_t_p_abs_ro s ptrl a n ts r \<sigma> l \<Xi>)
  then have "\<Xi>, \<sigma> \<turnstile> UPtr l (RCon n (map type_repr (map bang ts))) :u TCon n (map bang ts) (Boxed ReadOnly ptrl) \<langle>insert l r, {}\<rangle>"
    by (fastforce intro!: uval_typing_uval_typing_record.intros dest: abs_typing_bang bang_kind(2) bang_wellformed)
  then show ?case
    using u_t_p_abs_ro by clarsimp
next
  case (u_t_p_abs_w s ptrl a n ts r w \<sigma> l \<Xi>)
  then have "\<Xi>, \<sigma> \<turnstile> UPtr l (RCon n (map type_repr (map bang ts))) :u TCon n (map bang ts) (Boxed ReadOnly ptrl) \<langle>insert l (r \<union> w), {}\<rangle>"
    by (fastforce intro!: uval_typing_uval_typing_record.intros dest: abs_typing_bang bang_kind(2) bang_wellformed)
  then show ?case
    using u_t_p_abs_w by clarsimp
next
  case (u_t_r_cons1 \<Xi> \<sigma> x t r w xs ts r' w' rp n)
  have f1: "r \<union> r' \<union> (w \<union> w') = (r \<union> w) \<union> (r' \<union> w')"
    by blast
  from u_t_r_cons1
  show ?case
    apply (auto simp: f1 intro!: uval_typing_uval_typing_record.u_t_r_cons1[where w="{}" and w'="{}" and r="r \<union> w" and r'="r' \<union> w'", simplified])
    apply (fastforce dest: bang_type_repr(1) uval_typing_to_wellformed(1))+
    done
next case u_t_r_cons2 then show ?case
    by (auto intro!: uval_typing_uval_typing_record.intros dest: bang_wellformed)
qed (auto simp add: map_snd3_keep intro!: uval_typing_uval_typing_record.intros)


lemma u_t_afun_instantiate:
assumes "list_all2 (kinding K') ts K"
and     "list_all2 (kinding []) \<delta> K'"
and     "K \<turnstile> t wellformed"
and     "K \<turnstile> u wellformed"
and     "\<Xi> f = (K, t, u)"
shows   "\<Xi> , \<sigma> \<turnstile> UAFunction f (map (instantiate \<delta>) ts) :u TFun (instantiate \<delta> (instantiate ts t))
                                                               (instantiate \<delta> (instantiate ts u)) \<langle>{}, {}\<rangle>"
proof -
  from assms have tfun_eq:
    "TFun (instantiate \<delta> (instantiate ts t))
          (instantiate \<delta> (instantiate ts u))
   = TFun (instantiate (map (instantiate \<delta>) ts) t)
          (instantiate (map (instantiate \<delta>) ts) u)"
  by (force intro: instantiate_instantiate dest: list_all2_lengthD)

  have tfun_sub:
    "[] \<turnstile> TFun (instantiate (map (instantiate \<delta>) ts) t) (instantiate (map (instantiate \<delta>) ts) u)
        \<sqsubseteq> TFun (instantiate       \<delta> (instantiate ts t)) (instantiate       \<delta> (instantiate ts u))"
    using assms tfun_eq
    by (metis (mono_tags, lifting) list_all2_substitutivity specialisation_subtyping subty_tfun subtyping_refl)

with assms show ?thesis by (force intro:  uval_typing_uval_typing_record.intros
                                         list_all2_substitutivity
                                  simp add: kinding_simps)
qed

lemma u_t_function_instantiate:
  assumes "\<Xi>, K, [Some t] \<turnstile> f : u"
  and     "K \<turnstile> t wellformed"
  and     "list_all2 (kinding []) \<delta> K'"
  assumes "list_all2 (kinding K') ts K"
  shows   "\<Xi> , \<sigma> \<turnstile> UFunction f (map (instantiate \<delta>) ts) :u TFun (instantiate \<delta> (instantiate ts t))
                                                                (instantiate \<delta> (instantiate ts u)) \<langle>{}, {}\<rangle>"
proof -
  from assms have tfun_eq:
    "TFun (instantiate \<delta> (instantiate ts t))
          (instantiate \<delta> (instantiate ts u))
   = TFun (instantiate (map (instantiate \<delta>) ts) t)
          (instantiate (map (instantiate \<delta>) ts) u)"
           by (force intro: instantiate_instantiate dest: list_all2_lengthD dest!: typing_to_wellformed)

         
  have tfun_sub:
    "[] \<turnstile> TFun (instantiate (map (instantiate \<delta>) ts) t) (instantiate (map (instantiate \<delta>) ts) u)
        \<sqsubseteq> TFun (instantiate       \<delta> (instantiate ts t)) (instantiate       \<delta> (instantiate ts u))"
    using assms tfun_eq
    by (metis (mono_tags, lifting) list_all2_substitutivity specialisation_subtyping subty_tfun subtyping_refl typing_to_wellformed(1))

 with assms show ?thesis by (force intro: uval_typing_uval_typing_record.intros
                                 list_all2_substitutivity
                          simp add: kinding_simps)
qed

lemma matches_ptrs_noalias:
assumes "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>"
shows   "w \<inter> r = {}"
using assms proof (induct rule: matches_ptrs.induct)
qed (auto dest!: uval_typing_pointers_noalias)

lemma matches_ptrs_some_bang:
assumes "\<Xi>, \<sigma> \<turnstile> x :u t \<langle>r, w\<rangle>"
and     "\<Xi>, \<sigma> \<turnstile> xs matches ts \<langle>r' \<union> b, w'\<rangle>"
and     "w \<inter> w' = {}"
and     "w \<inter> r' = {}"
and     "w' \<inter> r = {}"
shows   "\<Xi>, \<sigma> \<turnstile> x # xs matches Some (bang t) # ts \<langle>r \<union> (r' \<union> (b \<union> w)), w'\<rangle>"
proof -
have SetLemma : "r \<union> (r' \<union> (b \<union> w)) = (r \<union> w) \<union> (r' \<union> b)" by auto
from assms show ?thesis by (auto simp:  SetLemma
                                 intro: matches_ptrs_some [where w = "{}", simplified]
                                        uval_typing_bang)
qed

lemma matches_ptrs_split':
assumes "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>"
shows   "\<exists>r' w' r'' w''. r = r' \<union> r''
                       \<and> w = w' \<union> w''
                       \<and> w' \<inter> w'' = {}
                       \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>1 \<langle>r' , w' \<rangle>)
                       \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>2 \<langle>r'', w''\<rangle>)"
using assms proof (induct arbitrary: \<gamma> r w rule: split_induct)
     case split_empty then show ?case by (fastforce elim:  matches_ptrs.cases
                                                    intro: matches_ptrs.intros)
next case (split_cons x xs a as b bs)
  then show ?case
  proof (cases \<Xi> \<sigma> \<gamma> x xs r w rule: matches_ptrs_consE)
       case 1 with split_cons show ?case   by simp
  next case 2 with split_cons show ?thesis by (auto elim: split_comp.cases)
  next case (3 _ _ rx wx _ rs ws)
    with split_cons show ?thesis
    proof (cases rule: split_comp.cases)
         case none  with 3 show ?thesis by simp
    next case left  with 3 show ?thesis
      apply (clarsimp dest!: split_cons(3))
      apply (rule_tac x = "rx \<union> r'" in exI)
      apply (rule_tac x = "wx \<union> w'" in exI)
      apply (rule_tac x = "r''"     in exI, rule,blast)
      apply (rule_tac x = "w''"     in exI)
      apply (force intro!: matches_ptrs.intros)
    done
    next case right with 3 show ?thesis
      apply (clarsimp dest!: split_cons(3))
      apply (rule_tac x = "r'"       in exI)
      apply (rule_tac x = "w'"       in exI)
      apply (rule_tac x = "rx \<union> r''" in exI, rule, blast)
      apply (rule_tac x = "wx \<union> w''" in exI)
      apply (force intro!: matches_ptrs.intros)
    done
    next case share with 3 show ?thesis
      apply (clarsimp dest!: split_cons(3))
      apply (rule_tac V="S \<in> {S}" in revcut_rl, blast)
      apply (drule(2) shareable_not_writable)
      apply (clarsimp)
      apply (rule_tac x = "rx \<union> r'"  in exI)
      apply (rule_tac x = "w'"       in exI)
      apply (rule_tac x = "rx \<union> r''" in exI, rule, blast)
      apply (rule_tac x = "w''"      in exI)
      apply (force intro: matches_ptrs_some [where w = "{}", simplified])
    done
    qed
  qed
qed

lemma matches_ptrs_split:
assumes "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "list_all2 (kinding []) \<tau>s K"
shows   "\<exists>r' w' r'' w''. r = r' \<union> r''
                       \<and> w = w' \<union> w''
                       \<and> w' \<inter> w'' = {}
                       \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>1) \<langle>r' , w' \<rangle>)
                       \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>2) \<langle>r'', w''\<rangle>)"
using assms by (auto dest:  instantiate_ctx_split
                     intro: matches_ptrs_split' [simplified])




lemma matches_ptrs_split_bang':
  assumes "split_bang [] vs \<Gamma> \<Gamma>1 \<Gamma>2"
    and "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>"
  shows "\<exists>r' w' r'' w'' b. r = r' \<union> r''
                         \<and> w' \<inter> w'' = {}
                         \<and> w = w' \<union> w'' \<union> b
                         \<and> b \<inter> (w' \<union> w'') = {}
                         \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>1 \<langle>r' \<union> b, w'     \<rangle>)
                         \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>2 \<langle>r''   , w'' \<union> b\<rangle>)"
  using assms
proof (induct arbitrary: \<gamma> r w rule: split_bang.induct)
  case split_bang_empty then show ?case
    by (fastforce elim: matches_ptrs.cases intro: matches_ptrs.intros)
next
  case (split_bang_cons K "is" xs as bs x a b)

  then show ?case
  proof (cases x)
    case None
    then obtain g \<gamma>'
      where \<gamma>_is: "\<gamma> = g # \<gamma>'"
        and "\<Xi>, \<sigma> \<turnstile> \<gamma>' matches xs \<langle>r, w\<rangle>"
      using split_bang_cons.prems
      by (fastforce elim: matches_ptrs_consE)
    then obtain r1 w1 r2 w2 p
      where
        "r = r1 \<union> r2"
        "w1 \<inter> w2 = {}"
        "w = w1 \<union> w2 \<union> p"
        "p \<inter> (w1 \<union> w2) = {}"
        "\<Xi>, \<sigma> \<turnstile> \<gamma>' matches as \<langle>r1 \<union> p, w1\<rangle>"
        "\<Xi>, \<sigma> \<turnstile> \<gamma>' matches bs \<langle>r2, w2 \<union> p\<rangle>"
      using split_bang_cons.hyps by meson
    moreover have
      "a = None"
      "b = None"
      using split_bang_cons.hyps
      by (simp add: None split_bang_comp.simps split_comp.simps)+
    ultimately show ?thesis
      by (metis \<gamma>_is matches_ptrs.matches_ptrs_none)
  next
    case (Some t)
    then obtain g \<gamma>' r1 w1 r2 w2
      where split\<gamma>:
        "\<gamma> = g # \<gamma>'"
        "r = r1 \<union> r2"
        "w = w1 \<union> w2"
        "\<Xi>, \<sigma> \<turnstile> g :u t \<langle>r1, w1\<rangle>"
        "\<Xi>, \<sigma> \<turnstile> \<gamma>' matches xs \<langle>r2, w2\<rangle>"
        "w1 \<inter> w2 = {}"
        "w1 \<inter> r2 = {}"
        "w2 \<inter> r1 = {}"
      using split_bang_cons.prems
      by (fastforce elim!: matches_ptrs_consE)
    then obtain r21 w21 r22 w22 p
      where split\<gamma>':
        "r2 = r21 \<union> r22"
        "w21 \<inter> w22 = {}"
        "w2 = w21 \<union> w22 \<union> p"
        "p \<inter> (w21 \<union> w22) = {}"
        "\<Xi>, \<sigma> \<turnstile> \<gamma>' matches as \<langle>r21 \<union> p, w21\<rangle>"
        "\<Xi>, \<sigma> \<turnstile> \<gamma>' matches bs \<langle>r22, w22 \<union> p\<rangle>"
      using split_bang_cons.hyps by meson

    show ?thesis
    proof (cases "0 \<in> is")
      case True

      have "\<Xi>, \<sigma> \<turnstile> g # \<gamma>' matches a # as \<langle>r1 \<union> (r21 \<union> (p \<union> w1)), w21\<rangle>"
        using split\<gamma> split\<gamma>' split_bang_cons.hyps True Some
        by (auto
            simp add: Some split_bang_comp.simps split_comp.simps
            intro: matches_ptrs_some_bang)
      moreover have "\<Xi>, \<sigma> \<turnstile> g # \<gamma>' matches b # bs \<langle>r1 \<union> r22, w1 \<union> (w22 \<union> p)\<rangle>"
        using split\<gamma> split\<gamma>' split_bang_cons.hyps True Some
        by (auto
            simp add: Some split_bang_comp.simps split_comp.simps
            intro: matches_ptrs_some)
      ultimately show ?thesis
        apply (rule_tac x = "r1 \<union> r21" in exI)
        apply (rule_tac x = "w21"      in exI)
        apply (rule_tac x = "r1 \<union> r22" in exI)
        apply (rule_tac x = "w22"      in exI)
        apply (rule_tac x = "p \<union> w1"   in exI)
        using split\<gamma> split\<gamma>'
        by (auto simp add: Un_ac)
    next
      case False

      have "K \<turnstile> Some t \<leadsto> a \<parallel> b"
        using False split_bang_cons.hyps
        by (simp add: Some split_bang_comp.simps)
      then show ?thesis
      proof (cases rule: split_comp.cases)
        case left
        moreover have "\<Xi>, \<sigma> \<turnstile> g # \<gamma>' matches Some t # as \<langle>r1 \<union> (r21 \<union> p), w1 \<union> w21\<rangle>"
          using split\<gamma> split\<gamma>'
          by (auto intro: matches_ptrs_some)+
        ultimately show ?thesis
          apply (rule_tac x = "r1 \<union> r21" in exI)
          apply (rule_tac x = "w1 \<union> w21" in exI)
          apply (rule_tac x = "r22"      in exI)
          apply (rule_tac x = "w22"      in exI)
          apply (rule_tac x = "p"        in exI)
          using split\<gamma> split\<gamma>'
          by (auto simp add: Un_ac)
      next
        case right
        moreover have "\<Xi>, \<sigma> \<turnstile> g # \<gamma>' matches Some t # bs \<langle>r1 \<union> r22, w1 \<union> (w22 \<union> p)\<rangle>"
          using split\<gamma> split\<gamma>'
          by (auto intro: matches_ptrs_some)
        ultimately show ?thesis
          apply (rule_tac x = "r21"      in exI)
          apply (rule_tac x = "w21"      in exI)
          apply (rule_tac x = "r1 \<union> r22" in exI)
          apply (rule_tac x = "w1 \<union> w22" in exI)
          apply (rule_tac x = "p"        in exI)
          using split\<gamma> split\<gamma>'
          by (auto simp add: Un_ac)
      next
        case share
        moreover then have w1_empty: "w1 = {}"
          using shareable_not_writable split\<gamma> by blast
        moreover have "\<Xi>, \<sigma> \<turnstile> g # \<gamma>' matches Some t # as \<langle>r1 \<union> (r21 \<union> p), {} \<union> w21\<rangle>"
          using split\<gamma> split\<gamma>'
          by (intro matches_ptrs_some, auto simp add: w1_empty)
        moreover have "\<Xi>, \<sigma> \<turnstile> g # \<gamma>' matches Some t # bs \<langle>r1 \<union> r22, {} \<union> (w22 \<union> p)\<rangle>"
          using split\<gamma> split\<gamma>'
          by (intro matches_ptrs_some, auto simp add: w1_empty)
        ultimately show ?thesis
          apply (rule_tac x = "r1 \<union> r21" in exI)
          apply (rule_tac x = "w21"      in exI)
          apply (rule_tac x = "r1 \<union> r22" in exI)
          apply (rule_tac x = "w22"      in exI)
          apply (rule_tac x = "p"        in exI)
          using split\<gamma> split\<gamma>'
          by (auto simp: Un_assoc)
      qed
    qed
  qed
qed


lemma matches_ptrs_split_bang:
assumes "split_bang K vs \<Gamma> \<Gamma>1 \<Gamma>2"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "list_all2 (kinding []) \<tau>s K"
shows   "\<exists>r' w' r'' w'' b. r = r' \<union> r''
                         \<and> w' \<inter> w'' = {}
                         \<and> w = w' \<union> w'' \<union> b
                         \<and> b \<inter> (w' \<union> w'') = {}
                         \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>1) \<langle>r'  \<union> b , w'     \<rangle>)
                         \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>2) \<langle>r''     , w'' \<union> b\<rangle>)"
using assms by (auto dest:  instantiate_ctx_split_bang
                     intro: matches_ptrs_split_bang' [simplified])

lemma matches_ptrs_weaken':
assumes "[] \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>  \<langle>r, w\<rangle>"
shows   "\<exists> r'. (r' \<subseteq> r) \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>' \<langle>r', w\<rangle>)"
using assms(1) [simplified weakening_def] and assms(2-)
proof (induct arbitrary: \<gamma> r w rule: list_all2_induct )
     case Nil  then show ?case by auto
next case Cons then show ?case
  proof (cases rule: weakening_comp.cases)
       case none with Cons show ?thesis by (force elim!: matches_ptrs_consE)
  next case keep with Cons show ?thesis
    apply (safe elim!: matches_ptrs_consE dest!: Cons(3))
    apply (rule_tac x = "r \<union> r'a" in exI)
    apply (force intro!: matches_ptrs.intros)
  done
next case drop
  with Cons show ?thesis
      apply (safe elim!: matches_ptrs_consE weakening_comp.cases dest!: Cons(3))
    apply (rule_tac V="w = {}" in revcut_rl)
     apply (rule discardable_not_writable; auto)
    apply (clarsimp)
    apply (rule_tac x = "r'a" in exI)
    apply (force)
  done
  qed
qed

lemma matches_ptrs_weaken:
assumes "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "list_all2 (kinding []) \<tau>s K"
shows   "\<exists>r'. (r' \<subseteq> r) \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>') \<langle>r', w\<rangle>) "
using assms by (auto dest:  instantiate_ctx_weaken
                     intro: matches_ptrs_weaken' [simplified])



lemma matches_ptrs_cons:
assumes "list_all2 (kinding []) \<tau>s K"
and     "\<Xi> , \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r', w'\<rangle>"
and     "\<Xi> , \<sigma> \<turnstile> x :u instantiate \<tau>s \<tau> \<langle>r, w\<rangle>"
and     "w  \<inter> w' = {}"
and     "w  \<inter> r' = {}"
and     "w' \<inter> r  = {}"
shows   "\<Xi> , \<sigma> \<turnstile> (x # \<gamma>) matches (instantiate_ctx \<tau>s (Some \<tau> # \<Gamma>)) \<langle>r \<union> r', w \<union> w'\<rangle>"
using assms by (auto intro: matches_ptrs_some)

lemma matches_ptrs_empty:
shows "\<Xi> , \<sigma> \<turnstile> [] matches instantiate_ctx \<tau>s [] \<langle>{}, {}\<rangle>"
by (simp add: matches_ptrs_empty instantiate_ctx_def)

lemma matches_ptrs_length:
assumes "\<Xi> , \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>"
shows   "length \<gamma> = length \<Gamma>"
using assms by (auto elim: matches_ptrs.induct)

lemma matches_ptrs_empty_env:
assumes "\<Xi>, \<sigma> \<turnstile> \<gamma> matches empty n \<langle>r, w\<rangle>"
shows   "r = {}"
and     "w = {}"
using assms [simplified empty_def] proof (induct n arbitrary: \<gamma> r w)
case 0
  case 1 then show ?case by (auto elim: matches_ptrs.cases)
  case 2 then show ?case by (auto elim: matches_ptrs.cases)
next case (Suc n)
  case 1 with Suc show ?case by (fastforce elim!: matches_ptrs_consE)
  case 2 with Suc show ?case by (fastforce elim!: matches_ptrs_consE)
qed

lemma matches_ptrs_proj':
assumes "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>"
and     "[] \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i \<tau>"
and     "i < length \<Gamma>"
shows   "\<exists> r' \<subseteq> r. \<Xi>, \<sigma> \<turnstile> (\<gamma> ! i) :u \<tau> \<langle>r', w\<rangle>"
proof -
  from assms obtain r' where S: "r' \<subseteq> r"
                       and   I: "\<Xi> , \<sigma> \<turnstile> \<gamma> matches (singleton (length \<Gamma>) i \<tau>) \<langle>r', w\<rangle>"
       by (auto dest: matches_ptrs_weaken')
  from assms obtain env where "singleton (length \<Gamma>) i \<tau> = env" by simp
  from I [simplified this] S assms(3-) this
  show ?thesis proof (induct arbitrary: i \<Gamma> rule: matches_ptrs.inducts )
       case matches_ptrs_empty then moreover   have "\<Gamma> = []" by (simp add: empty_def)
                                    ultimately show ?case    by simp
  next case (matches_ptrs_none  \<Xi> \<sigma> xs \<Gamma>' r w x i \<Gamma>)
       show ?case proof (cases i)
            case 0       with matches_ptrs_none show ?thesis by ( cases "length \<Gamma>"
                                                                , simp_all add: empty_def )
       next case (Suc n)
         moreover with matches_ptrs_none have "\<Gamma>' = (empty (length \<Gamma> - 1))[n := Some \<tau>]"
                                         by (cases "length \<Gamma>", simp_all add: empty_def)
         moreover with matches_ptrs_none have "length \<Gamma> = Suc (length \<Gamma>')"
                                         by (simp add: empty_def)
         ultimately show ?thesis apply -
                                 apply (insert matches_ptrs_none)
                                 apply (auto).
       qed
  next case (matches_ptrs_some)
       show ?case proof (cases i)
            case 0 with matches_ptrs_some show ?thesis
              apply (cases "length \<Gamma>", simp_all add: empty_def)
              apply (clarsimp dest!:matches_ptrs_empty_env(2) [simplified empty_def])
              apply (blast).
       next case (Suc n) with matches_ptrs_some show ?thesis by ( cases "length \<Gamma>"
                                                                , simp_all add: empty_def )
       qed
  qed
qed



lemma matches_ptrs_proj:
assumes "list_all2 (kinding []) \<tau>s K"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "K \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i \<tau>"
and     "i < length \<Gamma>"
shows   "\<exists> r' \<subseteq> r. \<Xi>, \<sigma> \<turnstile> (\<gamma> ! i) :u (instantiate \<tau>s \<tau>) \<langle>r', w\<rangle>"
using assms by (fastforce dest:   instantiate_ctx_weaken
                          intro!: matches_ptrs_proj' [simplified])

lemma matches_ptrs_proj_single':
assumes "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>"
and     "i < length \<Gamma>"
and     "\<Gamma> ! i = Some \<tau>"
shows   "\<exists>r' w'. (r' \<subseteq> r) \<and> (w' \<subseteq> w) \<and> (\<Xi>, \<sigma> \<turnstile> (\<gamma> ! i) :u \<tau> \<langle>r', w'\<rangle>)"
using assms proof (induct arbitrary: i rule: matches_ptrs.induct)
     case matches_ptrs_empty then show ?case by simp
next case matches_ptrs_none  then show ?case
  proof (cases i)
       case 0   with matches_ptrs_none show ?thesis by simp
  next case Suc with matches_ptrs_none show ?thesis by simp
  qed
next case matches_ptrs_some then show ?case
  proof (cases i)
       case 0   with matches_ptrs_some show ?thesis by auto
  next case Suc with matches_ptrs_some show ?thesis
    apply (clarsimp dest!: matches_ptrs_some(3))
    apply (rule_tac x = r'a in exI, rule, blast)
    apply (rule_tac x = w'a in exI, rule, blast)
    apply (simp)
  done
  qed
qed


lemma matches_ptrs_proj_consumed':
assumes "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>"
and     "[] \<turnstile> \<Gamma> consumed"
shows   "w = {}"
using assms proof(induction rule: matches_ptrs.induct)
  case (matches_ptrs_some \<Xi> \<sigma> x t r w xs ts r' w')
  then have "[] \<turnstile> t :\<kappa> {D}"
    by (auto simp: weakening_def empty_def kinding_def
            elim!: weakening_comp.cases)
  then have "w = {}"
    using matches_ptrs_some(1,7) discardable_not_writable
    by blast
  then show ?case
    using matches_ptrs_some
    by (auto simp: weakening_def empty_def)
qed (auto simp: weakening_def empty_def
          elim: weakening_comp.cases
          dest: discardable_not_writable)


lemma matches_ptrs_proj_consumed:
assumes "list_all2 (kinding []) \<tau>s K"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "K \<turnstile> \<Gamma> consumed"
shows   "w = {}"
using assms by (auto dest:   instantiate_ctx_weaken
                     intro!: matches_ptrs_proj_consumed')

lemma matches_ptrs_proj_single:
assumes "list_all2 (kinding []) \<tau>s K"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "i < length \<Gamma>"
and     "\<Gamma> ! i = Some \<tau>"
shows   "\<exists> r' w'. (r' \<subseteq> r) \<and> (w' \<subseteq> w) \<and> (\<Xi>, \<sigma> \<turnstile> (\<gamma> ! i) :u instantiate \<tau>s \<tau> \<langle>r', w'\<rangle>)"
using assms by (auto intro!: matches_ptrs_proj_single' [simplified]
                     simp:   instantiate_ctx_def)


section {* procedure environment matches *}
lemma proc_env_matches_ptrs_abstract:
assumes "\<xi> matches-u \<Xi>"
and     "\<Xi> f = (K, \<tau>i, \<tau>o)"
and     "list_all2 (kinding []) \<tau>s K"
and     "\<Xi> , \<sigma> \<turnstile> v   :u instantiate \<tau>s \<tau>i \<langle>r, w\<rangle>"
and     "\<xi> f (\<sigma>, v) (\<sigma>', v')"
shows   "(\<exists>r' w'. (\<Xi> , \<sigma>' \<turnstile> v' :u instantiate \<tau>s \<tau>o \<langle>r', w'\<rangle>)
                \<and> r' \<subseteq> r
                \<and> frame \<sigma> w \<sigma>' w')"
using assms by ( clarsimp simp: proc_env_matches_ptrs_def
               , drule_tac x = f in spec
               , auto)


section {* frame *}

theorem frame_id:
shows "frame \<sigma> w \<sigma> w"
by (simp add: frame_def)

section {* Type Safety *}

theorem u_progress:
assumes "\<Xi>, K, \<Gamma> \<turnstile> c : \<tau>"
and     "\<xi> matches-u \<Xi>"
and     "list_all2 (kinding []) \<tau>s K"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
shows   "\<exists>! st. (\<xi>, \<gamma> \<turnstile> (\<sigma>,c) \<Down>! st)"
oops (* NOT ACTUALLY EVEN TRUE IN THE CURRENT SETUP *)

lemma u_t_map_UPrimD:
  "\<Xi> , \<sigma> \<turnstile>* vs :u map TPrim \<tau>s \<langle>rs, ws\<rangle>
    \<Longrightarrow> \<exists>lits. vs = map UPrim lits \<and> map lit_type lits = \<tau>s"
  apply (induct \<Xi> \<sigma> vs \<tau>s'\<equiv>"map TPrim \<tau>s" rs ws
        arbitrary: \<tau>s rule: uval_typing_all.induct, simp_all)
  apply (clarsimp simp: Cons_eq_map_conv)
  apply (erule uval_typing.cases, simp_all)
  apply (erule meta_allE, drule meta_mp, rule refl, clarsimp)
  apply (rule exI[where x="x # xs" for x xs], simp)
  done

lemma eval_prim_u_preservation:
assumes "prim_op_type p = (\<tau>s, \<tau>)"
and     "\<Xi> , \<sigma> \<turnstile>* vs :u map TPrim \<tau>s \<langle>{}, {}\<rangle>"
shows   "\<Xi> , \<sigma> \<turnstile>  eval_prim_u p vs :u TPrim \<tau> \<langle>{}, {}\<rangle>"
using assms u_t_prim[where \<Xi>=\<Xi> and l="case eval_prim_u p vs of UPrim v \<Rightarrow> v"]
by (clarsimp simp add: eval_prim_u_def o_def eval_prim_op_lit_type dest!: u_t_map_UPrimD)

lemma uval_typing_valid:
  assumes "p \<in> (r \<union> w)"
  shows   "\<Xi> , \<sigma> \<turnstile> u :u t \<langle> r , w \<rangle> \<Longrightarrow> \<sigma> p \<noteq> None"
    and   "\<Xi> , \<sigma> \<turnstile>* us :ur ts \<langle> r , w \<rangle> \<Longrightarrow> \<sigma> p \<noteq> None"
  using assms
proof (induct rule: uval_typing_uval_typing_record.inducts)
  case (u_t_p_abs_ro a n ts r \<sigma> l \<Xi> ptrl)
  then show ?case
    using abs_typing_valid by fast
next
  case (u_t_p_abs_w a n ts r w \<sigma> l \<Xi> ptrl)
  then show ?case
    using abs_typing_valid by (fast dest: abs_typing_valid)
qed (auto dest: abs_typing_valid)

lemma matches_ptrs_valid:
assumes "\<Xi> , \<sigma> \<turnstile> u matches t \<langle> r , w \<rangle>"
and     "p \<in> (r \<union> w)"
shows   "\<sigma> p \<noteq> None"
using assms proof (induct arbitrary: p rule: matches_ptrs.induct)
case matches_ptrs_some then show ?case using uval_typing_valid by blast
qed auto

lemma uval_typing_frame:
assumes "frame \<sigma> w1 \<sigma>' w2"
and     "w \<inter> w1 = {}"
and     "r \<inter> w1 = {}"
shows   "\<Xi> , \<sigma> \<turnstile>  u  :u  t  \<langle> r , w \<rangle> \<Longrightarrow> \<Xi> , \<sigma>' \<turnstile>  u  :u t   \<langle> r , w \<rangle>"
and     "\<Xi> , \<sigma> \<turnstile>* us :ur ts \<langle> r , w \<rangle> \<Longrightarrow> \<Xi> , \<sigma>' \<turnstile>* us :ur ts \<langle> r , w \<rangle>"
using assms  proof(induct  rule:uval_typing_uval_typing_record.inducts)
     case u_t_prim     then show ?case by (auto simp add: uval_typing_uval_typing_record.u_t_prim)
next case u_t_product  then show ?case by (fastforce intro!: uval_typing_uval_typing_record.intros)
next case u_t_sum      then show ?case by (fastforce intro!: uval_typing_uval_typing_record.intros)
next case u_t_struct   then show ?case by (fastforce intro!: uval_typing_uval_typing_record.intros)
next case u_t_abstract then show ?case by (simp add: uval_typing_uval_typing_record.u_t_abstract abs_typing_frame)
next case u_t_function then show ?case by (simp add: uval_typing_uval_typing_record.u_t_function)
next case u_t_unit     then show ?case by (simp add: uval_typing_uval_typing_record.u_t_unit)
next case u_t_r_empty  then show ?case by (simp add: uval_typing_uval_typing_record.u_t_r_empty)
next case u_t_r_cons1  then show ?case by (force simp: frame_def
                                                 intro!: uval_typing_uval_typing_record.u_t_r_cons1)
next case u_t_r_cons2  then show ?case by (simp add: uval_typing_uval_typing_record.u_t_r_cons2)
next case u_t_p_abs_ro then show ?case by (auto simp: frame_def abs_typing_frame
                                                intro!: uval_typing_uval_typing_record.u_t_p_abs_ro)
next case u_t_p_abs_w then show ?case by (auto simp: frame_def abs_typing_frame
                                                intro!: uval_typing_uval_typing_record.u_t_p_abs_w)
qed (fastforce simp:   frame_def
               intro!: uval_typing_uval_typing_record.intros)+

lemma matches_ptrs_frame:
assumes "\<Xi> , \<sigma> \<turnstile> u matches t \<langle> r , w \<rangle>"
and     "frame \<sigma> w1 \<sigma>' w2"
and     "w1 \<inter> w = {}"
and     "w1 \<inter> r = {}"
shows   "\<Xi> , \<sigma>' \<turnstile> u matches t \<langle> r , w \<rangle>"
using assms proof (induct rule: matches_ptrs.induct)
     case matches_ptrs_empty then show ?case by (simp add: matches_ptrs.matches_ptrs_empty)
next case matches_ptrs_none  then show ?case by (auto)
next case matches_ptrs_some  then show ?case by (fast dest:   uval_typing_frame(1) [rotated -1]
                                                      intro!: matches_ptrs.intros)
qed

lemma frame_single_update:
shows  "frame \<sigma> {l} (\<sigma>(l \<mapsto> v)) {l}"
by (simp add: frame_def)

lemma frame_noalias_uval_typing :
assumes "frame \<sigma> u \<sigma>' u'"
and     "\<Xi>, \<sigma> \<turnstile> v :u \<tau> \<langle>r, w\<rangle>"
shows   "u  \<inter> w = {} \<Longrightarrow> u' \<inter> w = {}"
and     "u  \<inter> r = {} \<Longrightarrow> u' \<inter> r = {}"
using assms by (auto iff:  set_eq_iff
                     simp: frame_def
                     dest: uval_typing_valid [rotated 1])

lemma frame_noalias_matches_ptrs :
assumes "frame \<sigma> u \<sigma>' u'"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>"
shows   "u  \<inter> w = {} \<Longrightarrow> u' \<inter> w = {}"
and     "u  \<inter> r = {} \<Longrightarrow> u' \<inter> r = {}"
using assms by (auto simp: frame_def
                     dest: matches_ptrs_valid
                     iff:  set_eq_iff)

lemma frame_noalias_uval_typing' :
assumes "frame \<sigma> u \<sigma>' u'"
and     "\<Xi>, \<sigma> \<turnstile> v :u \<tau> \<langle>r, w\<rangle>"
shows   "w \<inter> u = {} \<Longrightarrow> w \<inter> u' = {}"
and     "r \<inter> u = {} \<Longrightarrow> r \<inter> u' = {}"
using assms by (auto simp: frame_def
                     dest: uval_typing_valid [rotated 1]
                     iff:  set_eq_iff)


lemma frame_noalias_2 :
assumes "frame \<sigma>  u \<sigma>'  u'"
and     "frame \<sigma>' w \<sigma>'' w'"
and     "\<Xi>, \<sigma>  \<turnstile> \<gamma>  matches \<Gamma>  \<langle>r , w\<rangle>"
and     "\<Xi>, \<sigma>' \<turnstile> v :u \<tau> \<langle>r', u'\<rangle>"
and     "u \<inter> w = {}"
shows   "u' \<inter> w' = {}"
proof -
from assms(1,3,5) have "u' \<inter> w = {}"by (rule frame_noalias_matches_ptrs)
with assms(2,4)   show ?thesis      by (rule frame_noalias_uval_typing')
qed

lemma frame_let:
assumes "frame \<sigma> w \<sigma>' w'"
and     "frame \<sigma>' (u \<union> w') \<sigma>'' u''"
shows   "frame \<sigma> (w \<union> u) \<sigma>'' u''"
using assms apply -
  apply (simp add: frame_def)
  apply (clarsimp)
  apply (drule_tac x = p in spec)
  apply (drule_tac x = p in spec)
  apply (clarsimp)
  apply (auto)
done

lemma frame_app:
assumes "frame \<sigma> w \<sigma>' w'"
and     "frame \<sigma>' u \<sigma>'' u'"
shows   "frame \<sigma> (w \<union> u) \<sigma>'' (w' \<union> u')"
using assms apply -
  apply (simp add: frame_def)
  apply (clarsimp)
  apply (drule_tac x = p in spec)
  apply (drule_tac x = p in spec)
  apply (clarsimp)
  apply (auto)
done


lemma frame_trans:
assumes "frame \<sigma>  w  \<sigma>'  w'"
and     "frame \<sigma>' w' \<sigma>'' w''"
shows   "frame \<sigma>  w  \<sigma>'' w''"
using assms by (rule frame_let [where u = "{}", simplified])

lemma subset_helper:
assumes "x \<inter> y = {}"
and     "x' \<subseteq> x"
and     "y' \<subseteq> y"
shows   "x' \<inter> y' = {}"
using assms by (blast)

lemma subset_helper2:
assumes "x \<union> y = z"
shows   "x \<subseteq> z"
using assms by blast

lemma subset_helper2':
assumes "x \<union> y = z"
shows   "y \<subseteq> z"
using assms by blast


lemma uval_typing_record_nth:
assumes "\<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s \<langle>r, {}\<rangle>"
and     "\<tau>s ! f = (n, \<tau>, Present)"
and     "f < length \<tau>s"
shows "\<exists>r' \<subseteq> r. \<Xi>, \<sigma> \<turnstile> fst (fs ! f) :u \<tau> \<langle>r', {}\<rangle>"
using assms proof (induct fs arbitrary: f r \<tau>s)
     case Nil  then show ?case by force
next case Cons then show ?case
  proof (cases f)
       case 0   with Cons(2-) show ?thesis by (force elim!: u_t_r_consE)
  next case Suc with Cons(2-) show ?thesis by (elim u_t_r_consE, auto dest!: Cons(1))
  qed
qed

lemma sum_downcast_u:
  assumes uval_tsum_ts: "\<Xi>, \<sigma> \<turnstile> USum tag v xs :u TSum ts \<langle>r, w\<rangle>"
    and   tag_neq_tag': "tag \<noteq> tag'"
    and   tag'_in_ts  : "(tag', \<tau>, Unchecked) \<in> set ts"
  shows "\<Xi>, \<sigma> \<turnstile> USum tag v xs :u TSum (tagged_list_update tag' (\<tau>, Checked) ts) \<langle>r, w\<rangle>"
  using uval_tsum_ts
proof -
  from uval_tsum_ts
  obtain k \<tau>1
    where uval_elim_lemmas:
      "\<Xi>, \<sigma> \<turnstile> v :u \<tau>1 \<langle>r, w\<rangle>"
      "xs = map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) ts"
      "(tag, \<tau>1, Unchecked) \<in> set ts"
      "distinct (map fst ts)"
      "[] \<turnstile> TSum ts wellformed"
    by fastforce
  moreover obtain i
    where tag_at:
      "i < length ts"
      "ts ! i = (tag', \<tau>, Unchecked)"
    using tag'_in_ts
    by (metis in_set_conv_nth)
  ultimately show ?thesis
    using assms 
  proof (intro u_t_sum)
    have "map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) (ts[i := (tag', \<tau>, Checked)]) = map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) ts"
      by (metis (mono_tags, lifting) list_update_id map_update old.prod.case tag_at(2))
    then show "xs = map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) (tagged_list_update tag' (\<tau>, Checked) ts)"
      using uval_elim_lemmas tag_at
      by (clarsimp simp add: tagged_list_update_distinct)
  next
    show "(tag, \<tau>1, Unchecked) \<in> set (tagged_list_update tag' (\<tau>, Checked) ts)"
      using uval_elim_lemmas tag_neq_tag' tagged_list_update_different_tag_preserves_values2
      by metis
  next
    show "[] \<turnstile> TSum (tagged_list_update tag' (\<tau>, Checked) ts) wellformed"
      using uval_elim_lemmas tag'_in_ts prod_in_set(1)
      by (fastforce intro!: variant_tagged_list_update_wellformedI simp add: list_all_iff)
  qed simp+
qed

lemma list_all2_helper2:
assumes "map fst tsa = map fst rs"
and     "list_all2 (\<lambda>t. (=) (type_repr t)) (map snd tsa) (map snd rs)"
shows   "map (\<lambda>(a,b). (a,type_repr b)) tsa = rs"
using assms(2,1) by ( induct "map snd tsa" "map snd rs"
                      arbitrary: tsa rs
                      rule: list_all2_induct
                    , auto)

lemma type_repr_uval_repr:
shows"\<Xi>, \<sigma> \<turnstile> v :u t \<langle>r, w\<rangle> \<Longrightarrow> uval_repr v = type_repr t"
and  "\<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r, w\<rangle> \<Longrightarrow> map snd fs = map (type_repr \<circ> fst \<circ> snd) ts"
  by (induct rule: uval_typing_uval_typing_record.inducts,
      (force dest: abs_typing_repr intro: list_all2_helper2 [symmetric])+)

lemma type_repr_uval_repr_deep:
shows"\<Xi>, \<sigma> \<turnstile> v :u t \<langle>r, w\<rangle> \<Longrightarrow> uval_repr_deep v = type_repr t"
and  "\<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r, w\<rangle> \<Longrightarrow> map uval_repr_deep (map fst fs) = map (type_repr \<circ> fst \<circ> snd) ts"
  by (induct rule: uval_typing_uval_typing_record.inducts,
      (force dest: abs_typing_repr intro: list_all2_helper2 [symmetric])+)


lemma uval_typing_record_take:
assumes "\<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s \<langle>r, w\<rangle>"
and     "\<tau>s ! f = (n, \<tau>, Present)"
and     "[] \<turnstile> \<tau> wellformed"
and     "f < length \<tau>s"
shows   "\<exists>r' w' r'' w''. (\<Xi>, \<sigma> \<turnstile> fst (fs ! f) :u  \<tau>                     \<langle>r' , w' \<rangle>)
                       \<and> (\<Xi>, \<sigma> \<turnstile>* fs          :ur (\<tau>s [f := (n, \<tau>, Taken)]) \<langle>r'', w''\<rangle>)
                       \<and> r = r' \<union> r''
                       \<and> w = w' \<union> w''
                       \<and> w' \<inter> w'' = {}"
using assms proof (induct fs arbitrary: f r w \<tau>s)
     case Nil  then show ?case by force
next case Cons then show ?case
  proof (cases f)
       case 0   with Cons(2-) show ?thesis by ( clarsimp, elim u_t_r_consE
                                              , auto intro!: exI
                                                             uval_typing_uval_typing_record.intros
                                                       elim: type_repr_uval_repr type_repr_uval_repr_deep)
  next case Suc with Cons(2-) show ?thesis
    apply (clarsimp)
    apply (erule u_t_r_consE)
     apply (clarsimp, frule(2) Cons(1) [OF _ _ assms(3)])
     apply (blast intro: uval_typing_uval_typing_record.intros)
    apply (clarsimp, frule(2) Cons(1) [OF _ _ assms(3)])
    apply (fastforce intro!: uval_typing_uval_typing_record.intros)
  done
  qed
qed

lemma uval_typing_record_put_taken:
assumes "\<Xi>, \<sigma> \<turnstile>  e' :u  t  \<langle>r'b, w'b\<rangle>"
and     "\<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r'a, w'a\<rangle>"
and     "ts ! f = (n, t, Taken)"
and     "w'b \<inter> r'a = {}"
and     "w'a \<inter> r'b = {}"
and     "w'a \<inter> w'b = {}"
and     "f < length ts"
shows   "\<Xi>, \<sigma> \<turnstile>* fs[f := (e', snd (fs ! f))] :ur (ts[f := (n, t, Present)]) \<langle>r'a \<union> r'b, w'a \<union> w'b\<rangle>"
using assms proof (induct fs arbitrary: f r'a w'a ts)
case Nil then show ?case by auto
next case Cons then show ?case
  proof (cases f)
       case 0   with Cons(2-) show ?thesis
         apply (clarsimp)
         apply (elim u_t_r_consE, simp)
         apply (rule pointerset_helper_record, (fastforce intro!: u_t_r_cons2 u_t_r_cons1)+)
       done
  next case Suc with Cons(2-) show ?thesis
         apply (clarsimp)
         apply (elim u_t_r_consE)
          apply (frule(1) Cons(1), simp, blast,blast,blast ,simp)
          apply (clarsimp, rule pointerset_helper_record, force intro!: u_t_r_cons1, blast, blast)
         apply (frule(1) Cons(1), simp, blast,blast,blast ,simp)
         apply (clarsimp, rule pointerset_helper_record, force intro!: u_t_r_cons2, blast, blast)
       done
  qed
qed

lemma uval_typing_record_put_discardable:
assumes "\<Xi>, \<sigma> \<turnstile>  e' :u  t  \<langle>r'b, w'b\<rangle>"
and     "\<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r'a, w'a\<rangle>"
and     "ts ! f = (n, t, Present)"
and     "[] \<turnstile> t :\<kappa> k"
and     "D \<in> k"
and     "w'b \<inter> r'a = {}"
and     "w'a \<inter> r'b = {}"
and     "w'a \<inter> w'b = {}"
and     "f < length ts"
shows   "\<exists>r''a\<subseteq> r'a. \<Xi>, \<sigma> \<turnstile>* fs[f := (e', snd (fs ! f))] :ur (ts[f := (n, t, Present)]) \<langle>r''a \<union> r'b, w'a \<union> w'b\<rangle>"
  using assms
proof (induct fs arbitrary: f r'a w'a ts)
  case (Cons f' fs')

  have w'b_empty: "w'b = {}"
    using Cons.prems discardable_not_writable
    by metis

  show ?case
  proof (cases f)
    case 0 with Cons(2-) show ?thesis
      apply (clarsimp)
      apply (frule(2) discardable_not_writable)
      apply (elim u_t_r_consE, simp)
       apply (rotate_tac 3, frule(2) discardable_not_writable)
       apply (rule_tac x = r' in exI)
       apply (rule, blast)
       apply (rule pointerset_helper_record,(fastforce intro!:  u_t_r_cons2 u_t_r_cons1)+)
      done
  next
    case (Suc fa)
    
    show ?thesis
      using Cons(3)
    proof (cases rule: uval_typing_record.cases)
      case (u_t_r_cons1 x t' r w ts' r' w' rp n')

      obtain r''a
        where IHresults:
          "r''a \<subseteq> r'"
          "\<Xi>, \<sigma> \<turnstile>* fs'[fa := (e', snd (fs' ! fa))] :ur ts'[fa := (n, t, Present)] \<langle>r''a \<union> r'b, w' \<union> w'b\<rangle>"
        using u_t_r_cons1 Cons Suc
        by (clarsimp simp add: w'b_empty Int_Un_distrib2, meson)
      then have "\<Xi>, \<sigma> \<turnstile>* (x, rp) # fs'[fa := (e', snd (fs' ! fa))] :ur (n', t', Present) # ts'[fa := (n, t, Present)] \<langle>r \<union> (r''a \<union> r'b), w \<union> (w' \<union> w'b)\<rangle>"
        using u_t_r_cons1 Cons.prems
        by (auto intro!: uval_typing_uval_typing_record.u_t_r_cons1 simp add: Int_Un_distrib Int_Un_distrib2)
      then show ?thesis
        using IHresults
        by (auto intro!: exI[where x="r \<union> r''a"] simp add: u_t_r_cons1 Suc Cons Un_assoc)
    next
      case (u_t_r_cons2 ts' t' rp x n')
      then obtain r''a
        where "r''a \<subseteq> r'a"
          and "\<Xi>, \<sigma> \<turnstile>* fs'[fa := (e', snd (fs' ! fa))] :ur ts'[fa := (n, t, Present)] \<langle>r''a \<union> r'b, w'a \<union> w'b\<rangle>"
        using Cons Suc
        by (clarsimp simp add: w'b_empty Int_Un_distrib2, meson)
      then show ?thesis
        by (simp add: u_t_r_cons2(1-3) Suc,
            metis u_t_r_cons2(4-7) uval_typing_uval_typing_record.u_t_r_cons2)
    qed
  qed
qed fastforce


lemma uval_typing_record_put:
assumes "\<Xi>, \<sigma> \<turnstile>  e' :u  t  \<langle>r'b, w'b\<rangle>"
and     "\<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r'a, w'a\<rangle>"
and     "ts ! f = (n, t, taken)"
and     "D \<in> k \<or> taken = Taken"
and     "w'b \<inter> r'a = {}"
and     "w'a \<inter> r'b = {}"
and     "w'a \<inter> w'b = {}"
and     "f < length ts"
and     "[] \<turnstile> t :\<kappa> k"
shows   "\<exists>r''a\<subseteq> r'a. \<Xi>, \<sigma> \<turnstile>* fs[f := (e', snd (fs ! f))] :ur (ts[f := (n, t, Present)]) \<langle>r''a \<union> r'b, w'a \<union> w'b\<rangle>"
using assms proof (cases taken)
     case Present with assms show ?thesis by (fastforce intro!: uval_typing_record_put_discardable)
next case Taken  with assms show ?thesis by (fastforce intro!: uval_typing_record_put_taken)
qed




lemma value_subtyping:
  shows "\<Xi>, \<sigma> \<turnstile> v :u t \<langle>r, w\<rangle> \<Longrightarrow> [] \<turnstile> t \<sqsubseteq> t'
           \<Longrightarrow> \<exists>r'. r' \<subseteq> r \<and> \<Xi>, \<sigma> \<turnstile> v :u t' \<langle>r', w\<rangle>"
    and "\<Xi>, \<sigma> \<turnstile>* vs :ur ts \<langle>r, w\<rangle> \<Longrightarrow> [] \<turnstile> TRecord ts s \<sqsubseteq> TRecord ts' s
           \<Longrightarrow> \<exists>r'. r' \<subseteq> r \<and> \<Xi>, \<sigma> \<turnstile>* vs :ur ts' \<langle>r', w\<rangle>"
(* Casting to a supertype can make the read set smaller, because record fields will be dropped.
   The write set will be equal though, because fields with write sets cannot be dropped *)
proof (induct arbitrary: t' and ts' rule: uval_typing_uval_typing_record.inducts)
  case (u_t_product \<Xi> \<sigma> a ta ra wa b tb rb wb)
  obtain ta' tb' where elims:
    "t' = TProduct ta' tb'"
    "[] \<turnstile> ta \<sqsubseteq> ta'"
    "[] \<turnstile> tb \<sqsubseteq> tb'"
    using u_t_product by (auto elim: subtyping.cases)

  obtain ra' rb' where r_elims:
    "ra' \<subseteq> ra"
    "\<Xi>, \<sigma> \<turnstile> a :u ta' \<langle>ra', wa\<rangle>"
    "rb' \<subseteq> rb"
    "\<Xi>, \<sigma> \<turnstile> b :u tb' \<langle>rb', wb\<rangle>"
    using u_t_product elims by meson

  have "\<Xi>, \<sigma> \<turnstile> UProduct a b :u t' \<langle>ra' \<union> rb', wa \<union> wb\<rangle>"
    using u_t_product elims r_elims
    by (auto intro!: uval_typing_uval_typing_record.intros)
  moreover have "ra' \<union> rb' \<subseteq> ra \<union> rb"
    using r_elims by blast
  ultimately show ?case
    by blast

next
  case (u_t_sum \<Xi> \<sigma> a ta r w n ts1 rs)
  obtain ts2 where elims:
    "t' = TSum ts2"
    "map fst ts1 = map fst ts2"
    "list_all2 (\<lambda>p1 p2. [] \<turnstile> fst (snd p1) \<sqsubseteq> fst (snd p2)) ts1 ts2"
    "list_all2 variant_kind_subty ts1 ts2"
    "distinct (map fst ts1)"
    using u_t_sum
    by (auto elim: subtyping.cases intro: uval_typing_uval_typing_record.intros)

  obtain i where n_in_ts_ix:
    "(n, ta, Unchecked) = ts1 ! i"
    "i < length ts1"
    using u_t_sum
    by (metis in_set_conv_nth)

  obtain n' ta' ba' where n'_in_ts2: "(n', ta', ba') = ts2 ! i"
    by (metis prod_cases3)

  have sat_ts1_ts2: "variant_kind_subty (ts1 ! i) (ts2 ! i)"
    using elims n_in_ts_ix n'_in_ts2 list_all2_nthD
    by blast

  have sat_unroll:
    "n = n'"
    "[] \<turnstile> ta \<sqsubseteq> ta'"
    "ba' = Unchecked"
    using n_in_ts_ix n'_in_ts2 sat_ts1_ts2
      apply (metis elims(2) fst_conv length_map nth_map)
    apply (metis elims(3) eq_snd_iff fst_conv list_all2_conv_all_nth n'_in_ts2 n_in_ts_ix(1) n_in_ts_ix(2))
    by (metis eq_snd_iff less_eq_variant_state.elims(2) n'_in_ts2 n_in_ts_ix(1) sat_ts1_ts2)
  obtain r' where sup_a: "\<Xi>, \<sigma> \<turnstile> a :u ta' \<langle>r', w\<rangle>"
      "r' \<subseteq> r"
    using u_t_sum sat_unroll
    by auto
  have n_in_ts2:
      "(n, ta', Unchecked) \<in> set ts2"
    using n_in_ts_ix n'_in_ts2 sat_unroll elims
    by (auto simp add: list_all2_lengthD)

  have ts2_wf: "[] \<turnstile> TSum ts2 wellformed"
    using u_t_sum elims
    by (auto dest: subtyping_wellformed_preservation)

  have repr_same: "map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) ts1 = map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) ts2"
    using elims(3) elims(2)
    by (induct rule: list_all2_induct; auto simp add: subtyping_preserves_type_repr)

  show ?case
    using elims sup_a n_in_ts2 ts2_wf repr_same u_t_sum
    by (metis uval_typing_uval_typing_record.u_t_sum)
next
  case (u_t_struct \<Xi> \<sigma> fs ts r w)
  obtain ts' where elims:
    "t' = TRecord ts' Unboxed"
    "distinct (map fst ts')"
    using u_t_struct by (auto elim: subtyping.cases intro: uval_typing_uval_typing_record.intros)

  obtain r' where "\<Xi>, \<sigma> \<turnstile>* fs :ur ts' \<langle>r', w\<rangle>"
      "r' \<subseteq> r"
    using elims subty_trecord subtyping_simps(6) u_t_struct by meson

  then show ?case
    using elims
    by (blast intro: uval_typing_uval_typing_record.intros)
next
  case (u_t_abstract a n ts r w \<Xi> \<sigma>)
  then show ?case
    by (fastforce elim!: subtyping.cases intro: uval_typing_uval_typing_record.intros)
next
  case (u_t_afun \<Xi> f ks a b ts a' b' \<sigma>)
  show ?case
    using u_t_afun.prems
    apply (cases rule: subtyping.cases)
    using u_t_afun by (fastforce simp add: subtyping_trans uval_typing_uval_typing_record.intros)
next
  case (u_t_function \<Xi> K t f u ts t' u' \<sigma>)
  show ?case
    using u_t_function.prems apply (cases rule: subtyping.cases)
    using u_t_function by (fastforce simp add: subtyping_trans uval_typing_uval_typing_record.intros)
next
  case (u_t_p_rec_ro \<Xi> \<sigma> fs ts r l ptrl)
  obtain ts' where elims:
    "t' = TRecord ts' (Boxed ReadOnly ptrl)"
    "map fst ts = map fst ts'"
    "list_all2 (\<lambda>p1 p2. [] \<turnstile> fst (snd p1) \<sqsubseteq> fst (snd p2)) ts ts'"
    "list_all2 (record_kind_subty []) ts ts'"
    "distinct (map fst ts')"
    using u_t_p_rec_ro
    by (auto elim: subtyping.cases intro: uval_typing_uval_typing_record.intros)

  obtain r' where fields: "\<Xi>, \<sigma> \<turnstile>* fs :ur ts' \<langle>r', {}\<rangle>"
      "r' \<subseteq> r"
    using elims subty_trecord subtyping_simps(6) u_t_p_rec_ro by meson
  have repr_same: "map (type_repr \<circ> fst \<circ> snd) ts = map (type_repr \<circ> fst \<circ> snd) ts'"
    using elims(3)
    by (induct rule: list_all2_induct; auto simp add: subtyping_preserves_type_repr)

  show ?case
    using u_t_p_rec_ro elims fields repr_same uval_typing_uval_typing_record.u_t_p_rec_ro
    by (metis (no_types, lifting) insert_mono)
next
  case (u_t_p_rec_w \<Xi> \<sigma> fs ts r w l ptrl)
  obtain ts' where elims:
    "t' = TRecord ts' (Boxed Writable ptrl)"
    "map fst ts = map fst ts'"
    "list_all2 (\<lambda>p1 p2. [] \<turnstile> fst (snd p1) \<sqsubseteq> fst (snd p2)) ts ts'"
    "list_all2 (record_kind_subty []) ts ts'"
    "distinct (map fst ts')"
    using u_t_p_rec_w
    by (auto elim: subtyping.cases intro: uval_typing_uval_typing_record.intros)

  obtain r' where fields: "\<Xi>, \<sigma> \<turnstile>* fs :ur ts' \<langle>r', w\<rangle>"
      "r' \<subseteq> r"
    using elims subty_trecord subtyping_simps(6) u_t_p_rec_w by meson
  have repr_same: "map (type_repr \<circ> fst \<circ> snd) ts = map (type_repr \<circ> fst \<circ> snd) ts'"
    using elims(3)
    by (induct rule: list_all2_induct; auto simp add: subtyping_preserves_type_repr)

  show ?case
    using u_t_p_rec_w elims fields repr_same uval_typing_uval_typing_record.u_t_p_rec_w
    by (metis (no_types, lifting) UnI1 Un_assoc subset_Un_eq)
next
  case (u_t_r_cons1 \<Xi> \<sigma> x t1 r w xs ts r' w' rp n)

  obtain t2 b2 ts2' where field_is: "ts' = (n,t2,b2) # ts2'"
    using u_t_r_cons1 subtyping_simps by auto

  have field_is':
    "([] \<turnstile> t1 \<sqsubseteq> t2)"
    "(if [] \<turnstile> t1 :\<kappa> {D} then Present \<le> b2 else Present = b2)"
    using field_is subtyping_simps(6) u_t_r_cons1.prems by auto

  have trec_subty: "[] \<turnstile> TRecord ts s \<sqsubseteq> TRecord ts2' s"
    using u_t_r_cons1(9) field_is
    apply (cases rule: subtyping.cases)
    by (auto intro: subtyping.intros)

  obtain ra' where field_reads:
      "ra'\<subseteq>r"
      "\<Xi>, \<sigma> \<turnstile> x :u t2 \<langle>ra', w\<rangle>"
    using u_t_r_cons1 field_is' by meson

  obtain rts2' where field_rest:
    "\<Xi>, \<sigma> \<turnstile>* xs :ur ts2' \<langle>rts2', w'\<rangle>"
    "rts2' \<subseteq> r'"
    using u_t_r_cons1 trec_subty by blast

  have t2_wf: "type_wellformed 0 t2"
    using field_is' local.u_t_r_cons1(1) subtyping_wellformed_preservation(1) uval_typing_to_wellformed(1) by fastforce

  have repr_same:
    "type_repr t2 = rp"
    "uval_repr x = type_repr t2"
    "uval_repr_deep x = type_repr t2"
    using u_t_r_cons1 field_is'
    using subtyping_preserves_type_repr type_repr_uval_repr type_repr_uval_repr_deep
    by (metis)+

  then show ?case
  proof (cases b2)
    case Taken
    moreover have w_empty: "w = {}"
      using discardable_not_writable field_is' u_t_r_cons1
      by (metis calculation record_state.distinct(1) singletonI)
    moreover have "\<Xi>, \<sigma> \<turnstile>* (x, rp) # xs :ur (n, t2, Taken) # ts2' \<langle>rts2', w'\<rangle>"
      using field_rest repr_same t2_wf
      by (auto intro: uval_typing_uval_typing_record.u_t_r_cons2)
    ultimately show ?thesis
      apply clarsimp
      apply (rule exI[where x="rts2'"])
      apply rule
      using field_rest apply blast
      using field_is Taken by auto
  next case Present
    then show ?thesis
      apply -
      apply (rule exI[where x="ra' \<union> rts2'"])
      apply rule
      using field_rest field_reads apply blast
      using repr_same field_reads field_rest field_is u_t_r_cons1
      by (auto intro!: uval_typing_uval_typing_record.u_t_r_cons1)
  qed
next
  case (u_t_r_cons2 \<Xi> \<sigma> xs ts r w t1 rp x n)

  obtain t2 b2 ts2' where field_is: "ts' = (n,t2,b2) # ts2'"
    using u_t_r_cons2 subtyping_simps by auto

  have field_is':
    "([] \<turnstile> t1 \<sqsubseteq> t2)"
    "(if [] \<turnstile> t1 :\<kappa> {D} then Taken \<le> b2 else Taken = b2)"
    using field_is subtyping_simps(6) u_t_r_cons2.prems by auto

  have trec_subty: "[] \<turnstile> TRecord ts s \<sqsubseteq> TRecord ts2' s"
    using u_t_r_cons2(7) field_is
    apply (cases rule: subtyping.cases)
    by (auto intro: subtyping.intros)

  obtain rts2' where field_rest:
    "\<Xi>, \<sigma> \<turnstile>* xs :ur ts2' \<langle>rts2', w\<rangle>"
    "rts2' \<subseteq> r"
    using u_t_r_cons2 trec_subty by blast

  have t2_wf: "type_wellformed 0 t2"
    using field_is' local.u_t_r_cons2 subtyping_wellformed_preservation(1) uval_typing_to_wellformed(1) by fastforce

  have repr_same:
    "type_repr t2 = rp"
    "uval_repr x = type_repr t2"
    "uval_repr_deep x = type_repr t2"
    using u_t_r_cons2 field_is'
    using subtyping_preserves_type_repr type_repr_uval_repr type_repr_uval_repr_deep
    by (metis)+

  have field_taken: "b2 = Taken"
    by (metis field_is' less_eq_record_state.elims(2))

  show ?case
    apply (rule exI[where x="rts2'"])
    apply rule
    using field_rest apply blast
    using field_is field_rest u_t_r_cons2 field_taken t2_wf repr_same
    by (auto intro: uval_typing_uval_typing_record.u_t_r_cons2)
next
  case (u_t_p_abs_ro s ptrl a n ts r \<sigma> l \<Xi>)
  then show ?case
    apply -
    apply (rule exI[where x = "insert l r"], rule, blast)
    by (auto elim!: subtyping.cases intro: uval_typing_uval_typing_record.intros)
next
  case (u_t_p_abs_w s ptrl a n ts r w \<sigma> l \<Xi>)
  then show ?case
    apply -
    apply (rule exI[where x = "r"], rule, blast)
    by (auto elim!: subtyping.cases intro: uval_typing_uval_typing_record.intros)
qed (auto elim: subtyping.cases intro: uval_typing_uval_typing_record.intros)


lemma list_helper:
assumes "ls ! x = y"
shows   "ls[x := y] = ls"
using assms by auto


lemma list_all2_helper:
shows "list_all2 (\<lambda>t. (=) (type_repr t))
                 (map (instantiate \<tau>s \<circ> snd) list)
                 (map (snd \<circ> ((\<lambda>(n, t). (n, type_repr t)) \<circ> (\<lambda>(c, t). (c, instantiate \<tau>s t)))) list)"
by (induct list, (simp+, (case_tac a)?)+)

lemma u_t_p_rec_w':
  assumes "\<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r, w\<rangle>"
    and "\<sigma> l = Some (URecord fs)"
    and "l \<notin> w \<union> r"
    and "rp = (RRecord (map (type_repr \<circ> fst \<circ> snd) ts)) "
    and "distinct (map fst ts)"
  shows "\<Xi>, \<sigma> \<turnstile> UPtr l rp :u TRecord ts (Boxed Writable ptrl) \<langle> r, insert l w \<rangle>"
  using assms
  by (auto intro: u_t_p_rec_w)


theorem preservation:
assumes "list_all2 (kinding []) \<tau>s K"
and     "proc_ctx_wellformed \<Xi>"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "\<xi> matches-u \<Xi>"
shows   "\<lbrakk> \<xi>, \<gamma> \<turnstile>  (\<sigma>, specialise \<tau>s e) \<Down>! (\<sigma>', v)
         ; \<Xi>, K, \<Gamma> \<turnstile> e : \<tau>
         \<rbrakk> \<Longrightarrow> \<exists>r' w'. (\<Xi> , \<sigma>' \<turnstile> v :u instantiate \<tau>s \<tau> \<langle>r', w'\<rangle>)
                     \<and> r' \<subseteq> r
                     \<and> frame \<sigma> w \<sigma>' w'"
and     "\<lbrakk> \<xi>, \<gamma> \<turnstile>* (\<sigma>, map (specialise \<tau>s) es) \<Down>! (\<sigma>', vs)
         ; \<Xi>, K, \<Gamma> \<turnstile>* es : \<tau>s'
         \<rbrakk> \<Longrightarrow> \<exists>r' w'. (\<Xi>, \<sigma>' \<turnstile>* vs :u map (instantiate \<tau>s) \<tau>s' \<langle>r', w'\<rangle>)
                     \<and> r' \<subseteq> r
                     \<and> frame \<sigma> w \<sigma>' w'"
  using assms
proof (induct "(\<sigma>, specialise \<tau>s e)" "(\<sigma>', v )"
                      and "(\<sigma>, map (specialise \<tau>s) es)" "(\<sigma>', vs)"
                      arbitrary:  e  \<tau>s K \<tau>   \<Gamma> r w v  \<sigma>' \<sigma>
                             and  es \<tau>s K \<tau>s' \<Gamma> r w vs \<sigma>' \<sigma>
                      rule: u_sem_u_sem_all.inducts)
     case u_sem_var       then show ?case by ( cases e, simp_all
                                             , fastforce elim!:  typing_varE
                                                         dest!:  matches_ptrs_proj
                                                         intro:  frame_id)
next case u_sem_prim      then show ?case by ( cases e, simp_all
                                             , auto      elim!:  typing_primE
                                                         dest!:  u_sem_prim(2)
                                                         intro!: exI map_tprim_no_pointers'
                                                         intro:  eval_prim_u_preservation
                                                         dest:   map_tprim_no_pointers)
next case u_sem_lit       then show ?case by ( cases e, simp_all
                                             , fastforce dest:   matches_ptrs_proj_consumed
                                                         intro!: uval_typing_uval_typing_record.intros
                                                                 frame_id)
next case u_sem_afun      then show ?case by ( cases e, simp_all
                                             , fastforce intro: u_t_afun_instantiate
                                                                frame_id
                                                         dest:  matches_ptrs_proj_consumed
                                                         simp add: kinding_simps)
next
  case (u_sem_fun \<xi> \<gamma> \<sigma> f ts_inst)
  then show ?case
  proof (cases e)
    case (Fun f' ts)

    have f'_is: "f' = f"
      and ts_inst_is: "ts_inst = map (instantiate \<tau>s) ts"
      using u_sem_fun Fun
      by simp+
    then obtain K' t u
      where \<tau>_is: "\<tau> = TFun (instantiate ts t) (instantiate ts u)"
        and typing_f': "\<Xi>, K', [Some t] \<turnstile> f' : u"
        and \<Gamma>consumed: "K \<turnstile> \<Gamma> consumed"
        and "list_all2 (kinding K) ts K'"
        and t_wellformed: "K' \<turnstile> t wellformed"
      using u_sem_fun Fun is_consumed_def
      by auto
    then have "\<Xi>, \<sigma> \<turnstile> UFunction f' (map (instantiate \<tau>s) ts) :u TFun (instantiate \<tau>s (instantiate ts t)) (instantiate \<tau>s (instantiate ts u)) \<langle>{}, {}\<rangle>"
      using u_t_function_instantiate typing_f' u_sem_fun(3) t_wellformed
      by fast
    moreover have w_is: "w = {}"
      using matches_ptrs_proj_consumed u_sem_fun \<Gamma>consumed
      by blast
    ultimately show ?thesis
      using frame_id
      by (auto simp add: ts_inst_is \<tau>_is f'_is)
  qed simp+
next case (u_sem_app \<xi> \<gamma> \<sigma> x \<sigma>' f ts y \<sigma>'' a e \<tau>s v \<sigma>''' K \<tau> \<Gamma> r w)
  note IH1  = u_sem_app(2)
  and  IH2  = u_sem_app(4)
  and  IH3  = u_sem_app(6)
  and  rest = u_sem_app(1,3,5,7-)

  obtain efun earg where e_def: "e = App efun earg"
      "x = specialise \<tau>s efun"
      "y = specialise \<tau>s earg"
    using u_sem_app by (cases e, auto)

  obtain \<Gamma>1 \<Gamma>2 targ where app_elims:
    "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    "\<Xi>, K, \<Gamma>1 \<turnstile> efun : TFun targ \<tau>"
    "\<Xi>, K, \<Gamma>2 \<turnstile> earg : targ"
    using u_sem_app e_def by auto

  obtain r' w' r'' w'' where match_elims:
   "r = r' \<union> r''" 
   "w = w' \<union> w''"
   "w' \<inter> w'' = {}"
   "\<Xi>, \<sigma> \<turnstile> \<gamma> matches instantiate_ctx \<tau>s \<Gamma>1 \<langle>r', w'\<rangle>"
   "\<Xi>, \<sigma> \<turnstile> \<gamma> matches instantiate_ctx \<tau>s \<Gamma>2 \<langle>r'', w''\<rangle>"
    using rest e_def app_elims
    by (auto elim!: typing_appE dest: matches_ptrs_noalias matches_ptrs_split)

  obtain r'f w'f where vfun_ty:
    "\<Xi>, \<sigma>' \<turnstile> UFunction f ts :u instantiate \<tau>s (TFun targ \<tau>) \<langle>r'f,w'f\<rangle>"
    "r'f \<subseteq> r'"
    "frame \<sigma> w' \<sigma>' w'f"
    using app_elims e_def rest match_elims
    by (auto dest: IH1)

  obtain r'a w'a where varg_ty:
    "\<Xi>, \<sigma>'' \<turnstile> a :u instantiate \<tau>s targ \<langle>r'a, w'a\<rangle>"
    "r'a \<subseteq> r''"
    "frame \<sigma>' w'' \<sigma>'' w'a"
    using rest match_elims vfun_ty  app_elims e_def
    apply (clarsimp)
    apply (frule(7) IH2 [OF _ _ _ _ matches_ptrs_frame, rotated -1])
     apply (metis matches_ptrs_noalias subset_helper subset_helper2 subset_helper2')
    by auto

  obtain Kfun t u where vfun_ty_elims:
      "w'f = {}"
      "r'f = {}"
      "\<Xi>, Kfun, [Some t] \<turnstile> f : u"
      "type_wellformed (length Kfun) t"
      "list_all2 (kinding []) ts Kfun"
      "[] \<turnstile> TFun (instantiate ts t) (instantiate ts u) \<sqsubseteq> TFun (instantiate \<tau>s targ) (instantiate \<tau>s \<tau>)"
    using vfun_ty by (auto elim!: u_t_functionE)

  obtain r'a' where varg_subty:
    "r'a' \<subseteq> r'a"
    "\<Xi>, \<sigma>'' \<turnstile> a :u instantiate ts t \<langle>r'a', w'a\<rangle>"
    using varg_ty vfun_ty_elims
    by (auto elim: subtyping.cases dest: value_subtyping)

  obtain r'r w'r where vres_subty:
    "\<Xi>, \<sigma>''' \<turnstile> v :u instantiate ts u \<langle>r'r, w'r\<rangle>"
    "r'r \<subseteq> r'a'"
    "frame \<sigma>'' w'a \<sigma>''' w'r"
    using rest vfun_ty_elims varg_subty
    apply -
    apply (frule IH3 [OF refl, rotated -1])
    by (auto intro!:  matches_ptrs.intros simp: instantiate_ctx_def)

  obtain r'r' where
    "\<Xi>, \<sigma>''' \<turnstile> v :u instantiate \<tau>s \<tau> \<langle>r'r', w'r\<rangle>"
    "r'r' \<subseteq> r'r"
    using varg_subty vfun_ty_elims varg_ty vfun_ty vres_subty
    by (auto elim: subtyping.cases dest: value_subtyping)

  moreover have "r'r' \<subseteq> r"
    using calculation varg_subty varg_ty vres_subty match_elims by fastforce

  moreover have "frame \<sigma> w \<sigma>''' w'r"
    by (metis frame_let frame_trans match_elims(2) sup_bot.right_neutral varg_ty(3) vfun_ty(3) vfun_ty_elims(1) vres_subty(3))

  ultimately show ?case
    by auto

next case (u_sem_abs_app \<xi> \<gamma> \<sigma> efun \<sigma>' fun_name ts earg \<sigma>'' varg  \<sigma>''' vres efull \<tau>s K \<tau> \<Gamma> r w)
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)

  obtain efun' earg' where e_def: "efull = App efun' earg'"
      "efun = specialise \<tau>s efun'"
      "earg = specialise \<tau>s earg'"
    using rest by (cases efull, auto)

  obtain \<Gamma>1 \<Gamma>2 targ where app_elims:
    "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    "\<Xi>, K, \<Gamma>1 \<turnstile> efun' : TFun targ \<tau>"
    "\<Xi>, K, \<Gamma>2 \<turnstile> earg' : targ"
    using rest e_def by auto

  obtain r' w' r'' w'' where match_elims:
   "r = r' \<union> r''" 
   "w = w' \<union> w''"
   "w' \<inter> w'' = {}"
   "\<Xi>, \<sigma> \<turnstile> \<gamma> matches instantiate_ctx \<tau>s \<Gamma>1 \<langle>r', w'\<rangle>"
   "\<Xi>, \<sigma> \<turnstile> \<gamma> matches instantiate_ctx \<tau>s \<Gamma>2 \<langle>r'', w''\<rangle>"
    using rest e_def app_elims
    by (auto elim!: typing_appE dest: matches_ptrs_noalias matches_ptrs_split)

  obtain r'f w'f where vfun_ty:
    "\<Xi>, \<sigma>' \<turnstile> UAFunction fun_name ts :u instantiate \<tau>s (TFun targ \<tau>) \<langle>r'f,w'f\<rangle>"
    "r'f \<subseteq> r'"
    "frame \<sigma> w' \<sigma>' w'f"
    using app_elims e_def rest match_elims
    by (auto dest: IH1)

  obtain r'a w'a where varg_ty:
    "\<Xi>, \<sigma>'' \<turnstile> varg :u instantiate \<tau>s targ \<langle>r'a, w'a\<rangle>"
    "r'a \<subseteq> r''"
    "frame \<sigma>' w'' \<sigma>'' w'a"
    using rest match_elims vfun_ty  app_elims e_def
    apply (clarsimp)
    apply (frule(7) IH2 [OF _ _ _ _ matches_ptrs_frame, rotated -1])
     apply (metis matches_ptrs_noalias subset_helper subset_helper2 subset_helper2')
    by auto

  obtain Kfun t u where vfun_ty_elims:
      "w'f = {}"
      "r'f = {}"
      "\<Xi> fun_name = (Kfun, t, u)"
      "type_wellformed (length Kfun) t"
      "type_wellformed (length Kfun) u"
      "list_all2 (kinding []) ts Kfun"
      "[] \<turnstile> TFun (instantiate ts t) (instantiate ts u) \<sqsubseteq> TFun (instantiate \<tau>s targ) (instantiate \<tau>s \<tau>)"
    using vfun_ty by (auto elim!: u_t_afunE)

  obtain r'a' where varg_subty:
    "r'a' \<subseteq> r'a"
    "\<Xi>, \<sigma>'' \<turnstile> varg :u instantiate ts t \<langle>r'a', w'a\<rangle>"
    using varg_ty vfun_ty_elims
    by (auto elim: subtyping.cases dest: value_subtyping)

  obtain r'r w'r where vres_subty:
    "\<Xi>, \<sigma>''' \<turnstile> vres :u instantiate ts u \<langle>r'r, w'r\<rangle>"
    "r'r \<subseteq> r'a'"
    "frame \<sigma>'' w'a \<sigma>''' w'r"
    using rest vfun_ty_elims varg_subty
    apply -
    by (frule(4) proc_env_matches_ptrs_abstract, clarsimp)

  obtain r'r' where
    "\<Xi>, \<sigma>''' \<turnstile> vres :u instantiate \<tau>s \<tau> \<langle>r'r', w'r\<rangle>"
    "r'r' \<subseteq> r'r"
    using varg_subty vfun_ty_elims varg_ty vfun_ty vres_subty
    by (auto elim: subtyping.cases dest: value_subtyping)
  moreover have "r'r' \<subseteq> r"
    using calculation varg_subty varg_ty vres_subty match_elims by fastforce
  moreover have "frame \<sigma> w \<sigma>''' w'r"
    by (metis frame_let frame_trans match_elims(2) sup_bot.right_neutral varg_ty(3) vfun_ty(3) vfun_ty_elims(1) vres_subty(3))
  ultimately show ?case
    by auto
next case (u_sem_con \<xi> \<gamma> \<sigma> x_spec \<sigma>' x' ts_inst tag)
  then show ?case
  proof (cases e)
    have f1: "(\<lambda>(n, t, _). (n, type_repr t)) \<circ> (\<lambda>(n, t, b). (n, instantiate \<tau>s t, b)) = (\<lambda>(n, t, b). (n, type_repr (instantiate \<tau>s t)))"
      by fastforce

    case (Con ts tag' x)
    then have spec_simps:
      "ts_inst = map (\<lambda>(c,t,b). (c, instantiate \<tau>s t, b)) ts"
      "tag' = tag"
      "x_spec = specialise \<tau>s x"
      using u_sem_con.hyps by simp+
    then obtain t k
      where typing_elims:
        "\<tau> = TSum ts"
        "\<Xi>, K, \<Gamma> \<turnstile> x : t"
        "(tag, t, Unchecked) \<in> set ts"
        "distinct (map fst ts)"
        "K \<turnstile> TSum ts wellformed"
      using Con u_sem_con.prems
      by fastforce

    obtain r' w'
      where uval_x': "\<Xi>, \<sigma>' \<turnstile> x' :u instantiate \<tau>s t \<langle>r', w'\<rangle>"
        and r'_sub_r: "r' \<subseteq> r"
        and frame_w_w': "frame \<sigma> w \<sigma>' w'"
      using u_sem_con.prems spec_simps typing_elims u_sem_con.hyps(2)
      by blast
    then have "\<Xi>, \<sigma>' \<turnstile> USum tag x' (map (\<lambda>(n,t,_). (n, type_repr t)) (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts)) :u TSum (map ((\<lambda>(c, t, b). (c, instantiate \<tau>s t, b))) ts) \<langle>r', w'\<rangle>"
      using u_sem_con.hyps(2) u_sem_con.prems typing_elims spec_simps
    proof (intro u_t_sum)
      have "(tag, t, Unchecked) \<in> set ts"
        using variant_elem_preservation typing_elims
        by (metis dual_order.antisym less_eq_variant_state.simps(1))
      then show "(tag, instantiate \<tau>s t, Unchecked) \<in> set (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts)"
        by force
    next
      show "[] \<turnstile> TSum (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts) wellformed"
        using typing_elims u_sem_con.prems Con
        using instantiate_wellformed list_all2_kinding_wellformedD
        by (metis expr.inject(6) instantiate.simps(6) spec_simps(1) specialise.simps(6) type_wellformed_pretty_def u_sem_con.hyps(3))
    qed simp+
    then show ?thesis
      using r'_sub_r frame_w_w' spec_simps typing_elims
      by auto
   qed simp+
next case u_sem_let
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (clarsimp elim!: typing_letE)
    apply (frule matches_ptrs_noalias)
    apply (frule(2) matches_ptrs_split, clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule(4) IH2 [rotated -1], clarsimp)
    apply (rule, force)
        apply (force intro: matches_ptrs_frame)
       apply (force dest: frame_noalias_matches_ptrs(1))
      apply (force dest!: frame_noalias_matches_ptrs(2))
     apply (blast)
    apply (fastforce intro: frame_let simp: Un_commute)
  done

next case u_sem_letbang
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (clarsimp elim!: typing_letbE)
    apply (frule matches_ptrs_noalias)
    apply (frule(2) matches_ptrs_split_bang, clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule(3) escapable_no_readers(1) [OF _ _ substitutivity(1)], clarsimp)
    apply (frule(4) IH2 [rotated -1], clarsimp)
     apply (rule, force)
        apply (force intro: matches_ptrs_frame)
       apply (rule frame_noalias_matches_ptrs(1), simp+, blast)
      apply (rule frame_noalias_matches_ptrs(2), simp+, blast)
     apply (simp)
    apply (clarsimp)
    apply (auto intro!: exI
                simp:   Un_assoc
                intro:  frame_let
                intro:  pointerset_helper_frame [OF _ _ refl])
  done
next case u_sem_unit      then show ?case by ( cases e, simp_all
                                             , auto elim!:  typing_unitE
                                                    intro!: exI
                                                    dest!:  matches_ptrs_proj_consumed
                                                    intro:  frame_id
                                                            uval_typing_uval_typing_record.intros)
next case u_sem_cast      then show ?case by ( cases e, simp_all
                                             , fastforce elim:   upcast_valid_cast_to
                                                         intro!: u_t_prim')
next case u_sem_tuple
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (clarsimp elim!: typing_tupleE)
    apply (frule matches_ptrs_noalias)
    apply (frule(2) matches_ptrs_split, clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule(2) matches_ptrs_frame, blast)
    apply (frule(5) IH2, clarsimp)
    apply (frule(1) frame_app)

    apply (frule(2) frame_noalias_matches_ptrs(2) [where u = "w \<union> w'" for w and w'])
    apply (frule(4) uval_typing_frame [rotated -1, OF _ _ frame_noalias_matches_ptrs(1)], blast)
    apply (frule(4) frame_noalias_2)
    apply (blast intro!: uval_typing_uval_typing_record.intros)
    done
next
  case (u_sem_esac \<xi> \<gamma> \<sigma> spec_a \<sigma>' tag v rs)
  then show ?case
  proof (cases e, simp_all)
    case (Esac a)

    have spec_simps: "spec_a = specialise \<tau>s a"
      using Esac u_sem_esac.hyps
      by force

    obtain ts tag'
      where typing_elims:
        "\<Xi>, K, \<Gamma> \<turnstile> a : TSum ts"
        "[(tag', \<tau>, Unchecked)] = filter ((=) Unchecked \<circ> snd \<circ> snd) ts"
      using u_sem_esac.prems Esac
      by blast

    obtain r' w'
      where ih_results:
        "\<Xi>, \<sigma>' \<turnstile> USum tag v rs :u instantiate \<tau>s (TSum ts) \<langle>r', w'\<rangle>"
        "r' \<subseteq> r"
        "frame \<sigma> w \<sigma>' w'"
      using u_sem_esac.hyps u_sem_esac.prems spec_simps typing_elims
      by blast
    then obtain instt
      where ih_elims:
        "\<Xi>, \<sigma>' \<turnstile> v :u instt \<langle>r', w'\<rangle>"
        "(tag, instt, Unchecked) \<in> (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ` set ts"
      using u_t_sumE[OF ih_results(1)[simplified]]
      by auto
    moreover obtain us vs
      where
        "ts = us @ (tag', \<tau>, Unchecked) # vs"
        "\<forall>u\<in>set us. Unchecked \<noteq> snd (snd u)"
        "\<forall>u\<in>set vs. Unchecked \<noteq> snd (snd u)"
      using typing_elims
      by (force simp add: filter_eq_singleton_iff2)
    ultimately have "(tag, instt, Unchecked) = (tag', instantiate \<tau>s \<tau>, Unchecked)"
      using typing_elims by auto
    then have "\<Xi>, \<sigma>' \<turnstile> v :u instantiate \<tau>s \<tau> \<langle>r', w'\<rangle>"
      using spec_simps ih_elims by blast
    then show ?thesis
      using ih_results
      by fastforce
  qed
next
  case (u_sem_case_nm \<xi> \<gamma> \<sigma> x \<sigma>'' tag' va rs tag n m)
  then show ?case
  proof (cases e, simp_all)
    case (Case e' tag'' a b)
    have x_is: "x = specialise \<tau>s e'"
      and tag''_is: "tag'' = tag"
      and m_is: "m = specialise \<tau>s a"
      and n_is: "n = specialise \<tau>s b"
      using Case u_sem_case_nm.hyps(6)
      by simp+

    obtain \<Gamma>1 \<Gamma>2 t ts
      where \<Gamma>_split: "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
        and e'_typing: "\<Xi>, K, \<Gamma>1 \<turnstile> e' : TSum ts"
        and tag''_in_ts: "(tag'', t, Unchecked) \<in> set ts"
        and "\<Xi>, K, Some t # \<Gamma>2 \<turnstile> a : \<tau>"
        and b_typing: "\<Xi>, K, Some (TSum (tagged_list_update tag'' (t, Checked) ts)) # \<Gamma>2 \<turnstile> b : \<tau>"
      using  u_sem_case_nm.prems(1) Case
      by (force elim!: typing_caseE)

    obtain r1 w1 r2 w2
      where r_as_un: "r = r1 \<union> r2"
        and w_as_un: "w = w1 \<union> w2"
        and w1_w2_disjoint: "w1 \<inter> w2 = {}"
        and matches_split1: "\<Xi>, \<sigma> \<turnstile> \<gamma> matches instantiate_ctx \<tau>s \<Gamma>1 \<langle>r1, w1\<rangle>"
        and matches_split2: "\<Xi>, \<sigma> \<turnstile> \<gamma> matches instantiate_ctx \<tau>s \<Gamma>2 \<langle>r2, w2\<rangle>"
      using matches_ptrs_split \<Gamma>_split u_sem_case_nm.prems
      by metis
    then have w2_r1_disjoint: "w2 \<inter> r1 = {}"
         and w1_r2_disjoint: "w1 \<inter> r2 = {}"
      using matches_ptrs_noalias u_sem_case_nm.prems
      by blast+

    obtain r1' w1'
      where "\<Xi>, \<sigma>'' \<turnstile> USum tag' va rs :u instantiate \<tau>s (TSum ts) \<langle>r1', w1'\<rangle>"
        and sub1: "r1' \<subseteq> r1"
        and frame1: "frame \<sigma> w1 \<sigma>'' w1'"
      using u_sem_case_nm.hyps(2) x_is e'_typing u_sem_case_nm.prems matches_split1
      by blast
    then have usem_instantiate_under: "\<Xi>, \<sigma>'' \<turnstile> USum tag' va rs :u TSum (tagged_list_update tag (instantiate \<tau>s t, Checked) (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts)) \<langle>r1', w1'\<rangle>"
      using u_sem_case_nm.hyps(3) tag''_in_ts tag''_is
      by (intro sum_downcast_u, (simp add: rev_image_eqI)+)

    have "\<Xi>, \<sigma>'' \<turnstile> USum tag' va rs :u instantiate \<tau>s (TSum (tagged_list_update tag (t, Checked) ts)) \<langle>r1', w1'\<rangle>"
    proof -
      have f1: "(\<And>tag b'. (case (tag, b') of (c, t, b) \<Rightarrow> (c, instantiate \<tau>s t, b)) = (tag, case b' of (t, b) \<Rightarrow> (instantiate \<tau>s t, b)))"
        by force

      obtain i where "ts ! i = (tag, t, Unchecked)"
                 and "i < length ts"
        using tag''_in_ts tag''_is in_set_conv_nth
        by metis
      then have "tagged_list_update tag (instantiate \<tau>s t, Checked) (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts)
            = map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) (tagged_list_update tag (t, Checked) ts)"
        by (simp add: tagged_list_update_map_over2[where f="\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)"
                                                     and b'="(t, Checked)"
                                                     and g="\<lambda>(t,b). (instantiate \<tau>s t, b)",
                                                   simplified f1, simplified])
      then show ?thesis
        using usem_instantiate_under
        by simp
    qed
    moreover have "\<Xi>, \<sigma>'' \<turnstile> \<gamma> matches instantiate_ctx \<tau>s \<Gamma>2 \<langle>r2, w2\<rangle>"
      using matches_ptrs_frame matches_split2 frame1 w1_r2_disjoint w1_w2_disjoint
      by blast
    moreover have "w1' \<inter> r2 = {}"
      by (meson frame1 frame_noalias_matches_ptrs(2) matches_split2 w1_r2_disjoint)
    moreover have "w1' \<inter> w2 = {}"
      by (meson frame1 frame_noalias_matches_ptrs(1) matches_split2 w1_w2_disjoint)
    moreover have "w2 \<inter> r1' = {}"
      by (meson sub1 subset_eq subset_helper w2_r1_disjoint)
    ultimately have "\<Xi>, \<sigma>'' \<turnstile> USum tag' va rs # \<gamma> matches instantiate_ctx \<tau>s (Some (TSum (tagged_list_update tag (t, Checked) ts)) # \<Gamma>2) \<langle>r2 \<union> r1', w2 \<union> w1'\<rangle>"
      by (metis Un_commute matches_ptrs_cons u_sem_case_nm.prems(2))
    then obtain r' w'
      where "\<Xi>, \<sigma>' \<turnstile> v :u instantiate \<tau>s \<tau> \<langle>r', w'\<rangle>"
      and r'_sub: "r' \<subseteq> r2 \<union> r1'"
      and "frame \<sigma>'' (w2 \<union> w1') \<sigma>' w'"
      using u_sem_case_nm.hyps(5) n_is b_typing u_sem_case_nm.prems(2-3,5) tag''_is
      by blast
    moreover then have "frame \<sigma> w \<sigma>' w'"
      using frame_let frame1 w_as_un
      by simp
    moreover have "r' \<subseteq> r"
      using r_as_un sub1 r'_sub
      by blast
    ultimately show ?thesis
      by force
  qed
next case u_sem_case_m
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (erule typing_caseE)
    apply (frule matches_ptrs_noalias)
    apply (frule(2) matches_ptrs_split, clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (frule(2) matches_ptrs_frame, blast)
    apply (erule u_t_sumE, clarsimp)
     apply (drule(1) distinct_fst [rotated 1],simp,simp)
    apply (frule(4) IH2 [rotated -1])
     apply (force intro!: matches_ptrs_some)
    apply (clarsimp, force intro!: exI simp: Un_commute intro: frame_let)
  done
next case (u_sem_if _ _ _ _ _ b)
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (frule matches_ptrs_noalias)
    apply (erule typing_ifE)
    apply (frule(2) matches_ptrs_split, clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (erule u_t_primE, clarsimp)
    \<comment>\<open>Instantiate the expression in the specialisation of @{thm IH2} with
      @{term \<open>if b then e2 else e3\<close>} for some term @{term e2} and @{term e3}.
      Instantiated using ''of'' instead of ''where'' since the naming is unstable.\<close>
    apply (frule(4) IH2 [ of _ "if b then e2 else e3" for e2 and e3
                        , rotated 2
                        , OF _ _ matches_ptrs_frame ])
        apply (blast, simp, cases b, simp, simp, cases b, simp, simp)
    apply (fastforce intro: frame_let)
  done
next case u_sem_struct    then show ?case by ( cases e, simp_all
                                             , fastforce intro!: uval_typing_uval_typing_record.intros
                                                         intro:  uval_typing_all_record
                                                                 [where ts = "map (instantiate \<tau>s) ts"
                                                                    for ts, simplified])
next case u_sem_member
 then show ?case
   apply ( cases e
         , simp_all )
   apply ( clarsimp elim!: typing_memberE)
   apply ( frule(5) u_sem_member(2)
         , clarsimp )
   apply ( frule(1) shareable_not_writable
         , fastforce simp add: kinding_simps
                     intro!: substitutivity
         , clarsimp elim!: u_t_recE)
   apply ( auto dest!: uval_typing_record_nth
         , fastforce )
 done
next case u_sem_memb_b
 then show ?case
   apply ( cases e
         , simp_all )
   apply ( clarsimp elim!: typing_memberE)
   apply ( frule(5) u_sem_memb_b(2)
         , clarsimp )
   apply ( frule(1) shareable_not_writable
         , fastforce simp add: kinding_simps
                     intro!: substitutivity
         , clarsimp)
   apply ( erule u_t_p_recE)
   apply ( auto dest!: uval_typing_record_nth
         , fastforce )
 done
next
  case (u_sem_take \<xi> \<gamma> \<sigma> x_spec \<sigma>'' pa ra fs f ea_spec)
  then show ?case
  proof (cases e)
    case (Take x f' ea)

    have case_simps:
      "x_spec = specialise \<tau>s x"
      "f = f'"
      "ea_spec = specialise \<tau>s ea"
      using Take u_sem_take.hyps by auto

    obtain \<Gamma>1 \<Gamma>2 ts s t k taken n
      where typing_e_elim_lemmas:
        "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
        "\<Xi>, K, \<Gamma>1 \<turnstile> x : TRecord ts s"
        "\<And>l. s \<noteq> Boxed ReadOnly l"
        "f' < length ts"
        "ts ! f' = (n, t, Present)"
        "K \<turnstile> t :\<kappa> k"
        "S \<in> k \<or> taken = Taken"
        "\<Xi>, K, Some t # Some (TRecord (ts[f' := (n, t, taken)]) s) # \<Gamma>2 \<turnstile> ea : \<tau>"
      using Take u_sem_take.prems
      by fastforce

    obtain r1 w1 r2 w2
      where ptrs_split_lemmas:
        "r = r1 \<union> r2"
        "w = w1 \<union> w2"
        "w1 \<inter> w2 = {}"
        "\<Xi>, \<sigma> \<turnstile> \<gamma> matches instantiate_ctx \<tau>s \<Gamma>1 \<langle>r1, w1\<rangle>"
        "\<Xi>, \<sigma> \<turnstile> \<gamma> matches instantiate_ctx \<tau>s \<Gamma>2 \<langle>r2, w2\<rangle>"
        "(w1 \<union> w2) \<inter> (r1 \<union> r2) = {}"
      using u_sem_take.prems matches_ptrs_split matches_ptrs_noalias typing_e_elim_lemmas 
      by metis

    obtain r1' w1pa'
      where IH1_lemmas:
        "\<Xi>, \<sigma>'' \<turnstile> UPtr pa ra :u instantiate \<tau>s (TRecord ts s) \<langle>r1', w1pa'\<rangle>"
        "r1' \<subseteq> r1"
        "frame \<sigma> w1 \<sigma>'' w1pa'"
      using u_sem_take.hyps(2) u_sem_take.prems ptrs_split_lemmas typing_e_elim_lemmas case_simps
      by blast

    obtain w1' ptrl
      where IH1_uptr_elim_lemmas:
        "w1pa' = insert pa w1'"
        "\<Xi>, \<sigma>'' \<turnstile>* fs :ur map (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y)) ts \<langle>r1', w1'\<rangle>"
        "\<sigma>'' pa = Some (URecord fs)"
        "distinct (map fst ts)"
        "ra = RRecord (map (type_repr \<circ> fst \<circ> snd \<circ> (\<lambda>(n, t, b). (n, instantiate \<tau>s t, b))) ts)"
        "s = Boxed Writable ptrl"
        "pa \<notin> w1'"
        "pa \<notin> r1'"
      using IH1_lemmas typing_e_elim_lemmas
      by (force elim!: u_t_p_recE simp add: u_sem_take.hyps)

    have pointer_noalias_lemmas1:
      "w1pa' \<inter> w2 = {}"
      "w1pa' \<inter> r1 = {}"
      "w1pa' \<inter> r2 = {}"
      using frame_noalias_matches_ptrs[OF IH1_lemmas(3)] ptrs_split_lemmas[simplified Int_Un_distrib Int_Un_distrib2 Un_empty]
      by meson+

    have inst_t_wellformed: "[] \<turnstile> instantiate \<tau>s t wellformed"
      using substitutivity(1) typing_e_elim_lemmas u_sem_take.prems kinding_to_wellformedD
      by blast
    then obtain r1'' w1'' r1''' w1'''
      where utype_record_take_lemmas:
        "\<Xi>, \<sigma>'' \<turnstile> fst (fs ! f') :u instantiate \<tau>s t \<langle>r1'', w1''\<rangle>"
        "\<Xi>, \<sigma>'' \<turnstile>* fs :ur (map (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y)) ts)[f' := (n, instantiate \<tau>s t, Taken)] \<langle>r1''', w1'''\<rangle>"
        "r1' = r1'' \<union> r1'''"
        "w1' = w1'' \<union> w1'''"
        "w1'' \<inter> w1''' = {}"
      using typing_e_elim_lemmas IH1_uptr_elim_lemmas kinding_to_wellformedD
      by (force dest!: uval_typing_record_take[where f="f'" and \<tau>s="map (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y)) ts"])

    have pointers_disjoint: "({pa} \<union> w1'' \<union> w1''' \<union> w2) \<inter> (r1'' \<union> r1''' \<union> r2) = {}"
      using utype_record_take_lemmas(3,4) ptrs_split_lemmas(6) IH1_lemmas IH1_uptr_elim_lemmas
        pointer_noalias_lemmas1
      by (clarsimp simp add: Int_Un_distrib Int_commute,
          meson equalityE subset_helper)

    have \<sigma>''_matches2: "\<Xi>, \<sigma>'' \<turnstile> \<gamma> matches instantiate_ctx \<tau>s \<Gamma>2 \<langle>r2, w2\<rangle>"
      using matches_ptrs_frame ptrs_split_lemmas IH1_lemmas
      by blast

    have "map ((type_repr \<circ> fst \<circ> snd) \<circ> (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y))) ts ! f' = type_repr (instantiate \<tau>s t)"
      by (simp add: typing_e_elim_lemmas(4) typing_e_elim_lemmas(5))
    then have type_repr_inst_ts_taken_same:
      "map ((type_repr \<circ> fst \<circ> snd) \<circ> (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y))) (ts[f' := (n, t, taken)])
        = map ((type_repr \<circ> fst \<circ> snd) \<circ> (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y))) ts"
      by (simp add: map_update list_helper)

    show ?thesis
    proof (cases taken)
      case Taken

      have "\<Xi>, \<sigma>'' \<turnstile> fst (fs ! f') # UPtr pa ra # \<gamma>
            matches Some (instantiate \<tau>s t)
              # Some (TRecord ((map (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y)) ts)[f' := (n, instantiate \<tau>s t, Taken)]) (Boxed Writable ptrl))
              # instantiate_ctx \<tau>s \<Gamma>2
            \<langle>r1'' \<union> (r1''' \<union> r2), w1'' \<union> (insert pa w1''' \<union> w2)\<rangle>"
        using utype_record_take_lemmas u_sem_take.hyps(3) \<sigma>''_matches2
      proof (intro matches_ptrs_some[OF _ matches_ptrs_some[OF u_t_p_rec_w']])
        show "ra = RRecord (map (type_repr \<circ> fst \<circ> snd) ((map (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y)) ts)[f' := (n, instantiate \<tau>s t, Taken)]))"
          using type_repr_inst_ts_taken_same IH1_uptr_elim_lemmas
          by (simp add: map_update)
      next
        show "pa \<notin> w1''' \<union> r1'''"
          and "insert pa w1''' \<inter> w2 = {}"
          and "w1'' \<inter> (insert pa w1''' \<union> w2) = {}"
          using IH1_uptr_elim_lemmas utype_record_take_lemmas pointer_noalias_lemmas1
          by blast+

        show "insert pa w1''' \<inter> r2 = {}"
          and "w2 \<inter> r1''' = {}"
          and "w1'' \<inter> (r1''' \<union> r2) = {}"
          and "(insert pa w1''' \<union> w2) \<inter> r1'' = {}"
          using pointers_disjoint
          by blast+
      next
        show "distinct (map fst ((map (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y)) ts)[f' := (n, instantiate \<tau>s t, Taken)]))"
          using IH1_uptr_elim_lemmas typing_e_elim_lemmas
          by (auto simp add: distinct_map map_update intro: distinct_list_update)
      qed clarsimp+
      then have "\<exists>r' w'. \<Xi>, \<sigma>' \<turnstile> v :u instantiate \<tau>s \<tau> \<langle>r', w'\<rangle> \<and> r' \<subseteq> r1'' \<union> (r1''' \<union> r2) \<and> frame \<sigma>'' (insert pa (w1'' \<union> (w1''' \<union> w2))) \<sigma>' w'"
        using u_sem_take.hyps(5) typing_e_elim_lemmas(8) u_sem_take.prems Taken IH1_uptr_elim_lemmas case_simps
        by (simp add: map_update)
      then obtain r' w'
        where
          "\<Xi>, \<sigma>' \<turnstile> v :u instantiate \<tau>s \<tau> \<langle>r', w'\<rangle>"
          "r' \<subseteq> r1'' \<union> r1''' \<union> r2"
          "frame \<sigma>'' (insert pa (w1'' \<union> w1''' \<union> w2)) \<sigma>' w'"
        by (force simp add: Un_assoc)
      moreover then have "r' \<subseteq> r"
        and "frame \<sigma>'' (w2 \<union> w1pa') \<sigma>' w'"
        using ptrs_split_lemmas(1) utype_record_take_lemmas(3) IH1_lemmas
         apply blast
        apply (metis IH1_uptr_elim_lemmas(1) Un_insert_right calculation(3) inf_sup_aci(5) utype_record_take_lemmas(4))
        done
      ultimately show ?thesis
        using frame_let ptrs_split_lemmas(2) IH1_lemmas(3)
        by blast
    next
      case Present
      then have w1''_empty: "w1'' = {}"
        using u_sem_take.prems typing_e_elim_lemmas inst_t_wellformed utype_record_take_lemmas(1)
        by (fast dest: substitutivity shareable_not_writable(1))
      then have w1'''_is: "w1''' = w1'"
        by (simp add: utype_record_take_lemmas(4))

      have "\<Xi>, \<sigma>'' \<turnstile> fst (fs ! f') # UPtr pa ra # \<gamma>
            matches Some (instantiate \<tau>s t)
              # Some (TRecord (map (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y)) ts) (Boxed Writable ptrl))
              # instantiate_ctx \<tau>s \<Gamma>2
            \<langle>r1'' \<union> (r1' \<union> r2), {} \<union> (insert pa w1' \<union> w2)\<rangle>"
        using utype_record_take_lemmas u_sem_take.hyps(3) \<sigma>''_matches2 w1''_empty IH1_uptr_elim_lemmas
      proof (intro matches_ptrs_some[OF _ matches_ptrs_some[OF u_t_p_rec_w']])
        show "pa \<notin> w1' \<union> r1'"
          and "insert pa w1' \<inter> w2 = {}"
          using IH1_uptr_elim_lemmas utype_record_take_lemmas pointer_noalias_lemmas1 
          by blast+

        show "w2 \<inter> r1' = {}"
          and "insert pa w1' \<inter> r2 = {}"
          and "(insert pa w1' \<union> w2) \<inter> r1'' = {}"
          using pointers_disjoint utype_record_take_lemmas(3) IH1_uptr_elim_lemmas(1)
            pointer_noalias_lemmas1(3) w1'''_is
          by blast+

        show "{} \<inter> (insert pa w1' \<union> w2) = {}"
          and "{} \<inter> (r1' \<union> r2) = {}"
          by simp+
      qed simp+
      moreover have "ts[f' := (n, t, Present)] = ts"
        by (metis list_update_id typing_e_elim_lemmas(5))
      ultimately have "\<exists>r' w'. \<Xi>, \<sigma>' \<turnstile> v :u instantiate \<tau>s \<tau> \<langle>r', w'\<rangle> \<and> r' \<subseteq> r1'' \<union> (r1' \<union> r2) \<and> frame \<sigma>'' (insert pa (w1' \<union> w2)) \<sigma>' w'"
        using u_sem_take.hyps(5) typing_e_elim_lemmas(8) u_sem_take.prems Present IH1_uptr_elim_lemmas case_simps
        by (simp add: map_update)
      then obtain r' w'
        where "\<Xi>, \<sigma>' \<turnstile> v :u instantiate \<tau>s \<tau> \<langle>r', w'\<rangle>"
          and "r' \<subseteq> r1'' \<union> (r1' \<union> r2)"
          and "frame \<sigma>'' (insert pa (w1' \<union> w2)) \<sigma>' w'"
        by blast
      moreover then have "r' \<subseteq> r"
        and "frame \<sigma> (w1 \<union> w2) \<sigma>' w'"
        using IH1_lemmas IH1_uptr_elim_lemmas ptrs_split_lemmas(1) utype_record_take_lemmas(3) 
        by (auto simp add: frame_let sup_commute)
      ultimately show ?thesis
        using ptrs_split_lemmas(2) by blast
    qed
  qed simp+
next
  case (u_sem_take_ub \<xi> \<gamma> \<sigma> x \<sigma>'' fs f ea)
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  have HELP: "\<forall> ts f \<tau> n. (f < length ts \<and> (ts ! f = (n, \<tau>, Present))
          \<longrightarrow> (map (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y)) ts ! f = (n, instantiate \<tau>s \<tau>, Present)))"
    apply (rule allI, induct_tac ts, simp)
    apply (simp split: prod.split)
    apply (clarsimp)
    apply (case_tac f, simp, simp)
  done
  from rest show ?case
    apply (cases e, simp_all)
    apply (erule typing_takeE)
    apply (frule matches_ptrs_noalias)
    apply (frule(2) matches_ptrs_split,clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (erule u_t_recE, simp_all)
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (clarsimp)
    apply (frule list_all2_kinding_wellformedD)
    apply (frule kinding_to_wellformedD)
    apply (frule uval_typing_record_take [ where \<tau>s = "map (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y)) ts" for ts
          , simplified
          , OF _ HELP [rule_format]], force, force intro: instantiate_wellformed, force)
    apply (elim exE conjE)
    apply (frule(2) matches_ptrs_frame, blast)
    apply (simp, erule disjE)
     apply (clarsimp)
     apply (frule(3) shareable_not_writable(1) [OF _ _ substitutivity(1)], clarsimp)
     apply (frule(4) IH2 [rotated -1], simp)
      apply (case_tac taken)
       apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
               apply (simp)
              apply (force simp add: distinct_map map_update intro: u_t_struct distinct_list_update)
             apply (simp)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (clarsimp)
      apply (rule pointerset_helper_matches_ptrs)
        apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
                apply (simp)
               apply (force intro!: u_t_struct simp: list_helper)
              apply (simp)
             apply (blast)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (blast)
     apply (clarsimp, intro exI conjI, simp, blast, force simp: Un_commute intro: frame_let)
    apply (clarsimp)
    apply (frule(4) IH2 [rotated -1], simp)
     apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
             apply (simp)
            apply (force simp add: distinct_map map_update intro: u_t_struct distinct_list_update)
           apply (simp)
          apply (blast)
         apply auto[1]
        apply auto[1]
       apply blast
      apply fast
     apply fast
    apply (clarsimp, auto intro!: exI intro: frame_let pointerset_helper_frame)
    done
next case u_sem_put
  note IH1  = this(2)
    and  IH2  = this(5)
    and  rest = this(1,3-4,6-)
  have HELP: "\<forall> ts f \<tau> taken n. (f < length ts \<longrightarrow> (ts ! f = (n, \<tau>, taken)
              \<longrightarrow> (map (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y)) ts ! f = (n, instantiate \<tau>s \<tau>, taken))))"
    apply (rule allI, induct_tac ts, simp)
    apply (simp split: prod.split)
    apply (clarsimp)
    apply (case_tac f, simp, simp)
    done
  have HELP2: "\<forall> \<tau>s. (type_repr \<circ> fst \<circ> snd \<circ> (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y)))
                   = (\<lambda>(n, t, y). type_repr (instantiate \<tau>s t))"
    by (force split: prod.split)
  from rest show ?case
    apply (cases e, simp_all)
    apply (erule typing_putE)
    apply (frule matches_ptrs_noalias)
    apply (clarsimp)
    apply (frule(2) matches_ptrs_split,clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule(2) matches_ptrs_frame,blast )
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (frule(5) IH2, clarsimp)
    apply (frule(1) frame_noalias_uval_typing, blast)
    apply (frule(1) frame_noalias_uval_typing(2), blast)
    apply (erule u_t_p_recE)
     apply force
    apply clarsimp
    apply (drule(1) frame_app)
    apply (drule(2) uval_typing_frame(2) [rotated -1], blast)
    apply (drule(1) uval_typing_frame(1) [OF frame_single_update, simplified, rotated -1], blast)
    apply (drule(2) uval_typing_frame(2) [OF frame_single_update, simplified, rotated -1])

    apply (frule(5) uval_typing_record_put [ where ts = "map (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y)) ts" for ts
          , OF _ _ HELP [rule_format]
          , simplified
          ])
        apply auto[1]
       apply auto[1]
      apply blast
     apply (fastforce intro: substitutivity)
    apply (clarsimp, intro conjI exI, rule u_t_p_rec_w')
          apply (simp add: map_update)
         apply simp
        apply force
       apply (force intro!: list_helper[symmetric] simp: HELP2 map_update)
      apply (force simp add: distinct_map map_update intro: u_t_struct distinct_list_update)
     apply (auto simp: frame_def)
    done
next case u_sem_put_ub
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  have HELP: "\<forall> ts f \<tau> taken n. (f < length ts \<longrightarrow> (ts ! f = (n, \<tau>, taken)
              \<longrightarrow> (map (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y)) ts ! f = (n, instantiate \<tau>s \<tau>, taken))))"
    apply (rule allI, induct_tac ts, simp)
    apply (simp split: prod.split)
    apply (clarsimp)
    apply (case_tac f, simp, simp)
  done
  from rest show ?case
    apply (cases e, simp_all)
    apply (erule typing_putE)
    apply (frule matches_ptrs_noalias)
    apply (clarsimp)
    apply (frule(2) matches_ptrs_split,clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule(2) matches_ptrs_frame,blast )
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (frule(5) IH2, clarsimp)
    apply (frule(1) frame_noalias_uval_typing, blast)
    apply (frule(1) frame_noalias_uval_typing(2), blast)
    apply (erule u_t_recE, simp,clarsimp)
    apply (drule(1) frame_app)
    apply (drule(2) uval_typing_frame(2) [rotated -1], blast)

    apply (frule(5) uval_typing_record_put [ where ts = "map (\<lambda>(n, t, y). (n, instantiate \<tau>s t, y)) ts" for ts
          , OF _ _ HELP [rule_format]
          , simplified
          ])
        apply blast
       apply auto[1]
      apply blast
     apply (fastforce intro: substitutivity)
    apply (clarsimp simp add: map_update)
    apply (intro conjI exI u_t_struct)
       apply blast
      apply (force simp add: distinct_map map_update intro: u_t_struct distinct_list_update)
     apply (auto simp add: frame_def)
    done
next case u_sem_split
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (erule typing_splitE)
    apply (frule matches_ptrs_noalias)
    apply (frule(2) matches_ptrs_split,clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (erule u_t_productE)
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (frule(3) IH2)
      apply (simp)
      apply (rule matches_ptrs_some, simp, rule matches_ptrs_some, simp)
            apply (rule matches_ptrs_frame, simp, simp)
             apply fast
            apply fast
           apply auto[1]
          apply auto[1]
         apply blast
        apply auto[1]
       apply auto[1]
      apply blast
     apply blast
    apply (clarsimp, auto intro!: exI intro: frame_let pointerset_helper_frame)
    done
next
  case (u_sem_promote \<xi> \<gamma> \<sigma> specx)
  then show ?case
  proof (cases e)
  next
    case (Promote \<tau>a xa)
    moreover then obtain x \<tau>'
      where typing_elims:
        "\<tau>a = \<tau>"
        "xa = x"
        "e = Promote \<tau> x"
        "\<Xi>, K, \<Gamma> \<turnstile> x : \<tau>'"
        "K \<turnstile> \<tau>' \<sqsubseteq> \<tau>"
      using u_sem_promote.prems by blast
    moreover have specx_is: "specx = specialise \<tau>s x"
      using typing_elims u_sem_promote.hyps
      by simp
    moreover have "[] \<turnstile> instantiate \<tau>s \<tau>' \<sqsubseteq> instantiate \<tau>s \<tau>"
      using
        u_sem_promote.prems specialisation_subtyping subtyping_wellformed_preservation
        typing_elims typing_to_wellformed
      by blast
    moreover obtain r' w'
      where
        "\<Xi>, \<sigma>' \<turnstile> v :u instantiate \<tau>s \<tau>' \<langle>r', w'\<rangle>"
        "r' \<subseteq> r"
        "frame \<sigma> w \<sigma>' w'"
      using u_sem_promote specx_is typing_elims
      by blast
    ultimately show ?thesis
      by (meson order.trans value_subtyping)
  qed force+
next case u_sem_all_empty then show ?case
    by ( cases es, simp_all, fastforce intro!: frame_id
                                               uval_typing_all.intros
                                       dest: matches_ptrs_empty_env(2))
next case u_sem_all_cons
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases es, simp_all)
    apply (erule typing_all_consE, clarsimp)
    apply (frule(2) matches_ptrs_split, clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule matches_ptrs_noalias)
    apply (frule(7) IH2 [OF _ _ _ _ matches_ptrs_frame, rotated -1], blast, clarsimp)
    apply (frule(1) frame_app)
    apply (frule(2) frame_noalias_matches_ptrs(2) [where u = "w \<union> w'" for w and w'])
    apply (frule(4) uval_typing_frame [rotated -1, OF _ _ frame_noalias_matches_ptrs(1)], blast)
    apply (frule(4) frame_noalias_2)
    apply (blast intro!: uval_typing_all.intros)
  done

qed
inductive_cases u_t_productE': "\<Xi>, \<sigma> \<turnstile> UProduct a b :u t \<langle>r,w\<rangle>"
inductive_cases u_t_sumE': "\<Xi>, \<sigma> \<turnstile> USum c p ts :u t \<langle>r,w\<rangle>"
inductive_cases u_t_absE: "\<Xi>, \<sigma> \<turnstile> UAbstract v :u t \<langle>r,w\<rangle>"
inductive_cases u_t_funE': "\<Xi>, \<sigma> \<turnstile> UFunction f ts :u t \<langle>r,w\<rangle>"
inductive_cases u_t_ptrE: "\<Xi>, \<sigma> \<turnstile> UPtr p rp :u t \<langle>r,w\<rangle>"

lemma type_repr_heap:
shows "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  v  :u  t  \<langle>r, w\<rangle>; \<Xi>, \<sigma> \<turnstile>  v  :u  t'  \<langle>r', w'\<rangle> \<rbrakk> \<Longrightarrow> type_repr t = type_repr t'"
and   "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r, w\<rangle>
       ; \<Xi>, \<sigma> \<turnstile>* fs :ur ts' \<langle>r', w'\<rangle>
       \<rbrakk> \<Longrightarrow> (map (type_repr \<circ> fst \<circ> snd) ts) = (map (type_repr \<circ> fst \<circ> snd) ts')"
by (auto dest!: type_repr_uval_repr)


lemmas preservation_mono = preservation [where \<tau>s = "[]", simplified, OF refl, simplified]


(* Lemma bucket. *)
lemma matches_ptrs_some_some:
  "\<lbrakk>\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r'', w''\<rangle>;
   \<Xi>, \<sigma> \<turnstile> a :u ta \<langle>ra, wa\<rangle>;
   \<Xi>, \<sigma> \<turnstile> b :u tb \<langle>rb, wb\<rangle>;
    wb \<inter> w'' = {};
    wb \<inter> r'' = {};
    w'' \<inter> rb = {};
     wa \<inter> (wb \<union> w'') = {};
     wa \<inter> (rb \<union> r'') = {};
     (wb \<union> w'') \<inter> ra = {}\<rbrakk> \<Longrightarrow>
  \<Xi>, \<sigma> \<turnstile>
    (a # b # \<gamma>) matches
    (Some ta # Some tb # \<Gamma>)
    \<langle>ra \<union> (rb \<union> r''), wa \<union> (wb \<union> w'')\<rangle>"
  by (fastforce intro!: matches_ptrs_some)

lemma uval_typing_taken_field':
  assumes "\<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s \<langle>r, w\<rangle>"
  assumes "f < length \<tau>s"
  assumes "\<tau>s!f = (n, t, Present)"
  assumes "[] \<turnstile>  t :\<kappa>  k"
  shows "\<exists>r'. \<exists>w'. \<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s[f := (n, t, taken)] \<langle>r', w'\<rangle> \<and> r' \<subseteq> r \<and> w'\<subseteq> w"
  proof (cases taken)
   case Present show ?thesis
   by (rule_tac x="r" in exI,rule_tac x="w" in exI, simp)
      (metis(full_types) Present list_update_id assms(1,3))
  next
   case Taken thus ?thesis using assms
   proof (induct fs arbitrary: f r w \<tau>s)
    case Cons then show ?case
    proof (cases f)
      case 0  with Cons(2-) show ?thesis
        by (fastforce intro!: u_t_r_cons2 elim!: u_t_r_consE dest: kinding_to_wellformedD
            elim: type_repr_uval_repr type_repr_uval_repr_deep)
    next
     case Suc with Cons(2-) show ?thesis
     apply (elim u_t_r_consE)
      apply clarsimp
      apply (frule(4) Cons(1), simp)
      apply (blast intro!: u_t_r_cons1)
     apply clarsimp
     apply (frule(4) Cons(1), simp)
     by (fastforce intro!: u_t_r_cons2)
   qed
  qed fastforce
qed

lemma uval_typing_taken_field:
  assumes "\<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s \<langle>r, w\<rangle>"
  assumes "f < length \<tau>s"
  assumes "\<tau>s!f = (n, t, Present)"
  assumes "[] \<turnstile>  t :\<kappa>  k"
  shows "\<exists>r' \<subseteq> r. \<exists>w'\<subseteq> w. \<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s[f := (n, t, taken)] \<langle>r', w'\<rangle>"
  by (meson uval_typing_taken_field'[OF assms])

lemma uval_typing_record_nth':
  assumes "\<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s \<langle>r , w\<rangle>"
  assumes "\<tau>s ! f = (n, \<tau>, Present)"
  assumes "f < length \<tau>s"
  shows "\<exists> r'\<subseteq>r. \<exists>w'\<subseteq>w. \<Xi>, \<sigma> \<turnstile>  fst (fs!f)  :u  \<tau>  \<langle>r' , w'\<rangle>"
using assms proof (induct fs arbitrary: f r w \<tau>s)
     case Nil  then show ?case by force
next case Cons then show ?case
  proof (cases f)
       case 0   with Cons(2-) show ?thesis  by (fastforce elim!: u_t_r_consE)
  next case Suc with Cons(2-) show ?thesis
    apply (elim u_t_r_consE)
     apply (drule Cons(1), simp, simp, clarsimp)
     apply (rename_tac r'' w'')
      apply (rule_tac x=r'' in exI)
      apply (rule conjI)
       apply blast
      apply (rule_tac x=w'' in exI)
      apply blast
    by (drule Cons(1), auto)
  qed
qed

end

end
