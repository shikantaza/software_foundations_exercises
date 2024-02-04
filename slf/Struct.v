Set Implicit Arguments.
From SLF Require Import LibSepReference LibSepTLCbuffer.
(* #[global] *)

Hint Rewrite conseq_cons' : rew_listx.

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.
Implicit Type p q : loc.
Implicit Type k : nat.
Implicit Type i n : int.
Implicit Type v : val.
Implicit Type L : list val.
Implicit Types z : nat.

Fixpoint hcells (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[]
  | x::L' => (p ~~> x) \* (hcells L' (p+1)%nat)
  end.

Parameter hcells_concat_eq : forall p L1 L2,
  hcells (L1++L2) p = (hcells L1 p \* hcells L2 (length L1 + p)%nat).

Parameter hheader : forall (k:nat) (p:loc), hprop.

Parameter hheader_not_null : forall p k,
  hheader k p ==> hheader k p \* \[p <> null].

Definition harray (L:list val) (p:loc) : hprop :=
  hheader (length L) p \* hcells L (p+1)%nat.

Parameter val_alloc : prim.

Check val_uninit : val.

Parameter triple_alloc_nat : forall k,
  triple (val_alloc k)
    \[]
    (funloc p => harray (LibList.make k val_uninit) p).

Parameter triple_alloc : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (funloc p => harray (LibList.make (abs n) val_uninit) p).

Parameter triple_alloc_array : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (funloc p => \exists L, \[n = length L] \* harray L p).

Parameter val_dealloc : prim.

Parameter triple_dealloc : forall L p,
  triple (val_dealloc p)
    (harray L p)
    (fun _ => \[]).

Parameter val_array_get : val.

Parameter triple_array_get : forall L p i,
  0 <= i < length L ->
  triple (val_array_get p i)
    (harray L p)
    (fun r => \[r = LibList.nth (abs i) L] \* harray L p).

Parameter val_array_set : val.

Parameter triple_array_set : forall L p i v,
  0 <= i < length L ->
  triple (val_array_set p i v)
    (harray L p)
    (fun _ => harray (LibList.update (abs i) v L) p).

Parameter val_array_length : val.

Parameter triple_array_length : forall L p,
  triple (val_array_length p)
    (harray L p)
    (fun r => \[r = length L] \* harray L p).

Parameter triple_array_length_header : forall k p,
  triple (val_array_length p)
    (hheader k p)
    (fun r => \[r = (k:int)] \* hheader k p).

#[global] Hint Resolve triple_array_get triple_array_set triple_array_length : triple.

Definition field : Type := nat.

Definition hfield (p:loc) (k:field) (v:val) : hprop :=
  (p+1+k)%nat ~~> v.

Notation "p `. k '~~>' v" := (hfield p k v)
  (at level 32, k at level 0, no associativity,
   format "p `. k '~~>' v").

Definition hrecord_field : Type := (field * val).

Definition hrecord_fields : Type := list hrecord_field.

Implicit Types kvs : hrecord_fields.

Notation "`{ k1 := v1 }" :=
  ((k1,(v1:val))::nil)
  (at level 0, k1 at level 0, only parsing).

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  ((k1,(v1:val))::(k2,(v2:val))::nil)
  (at level 0, k1, k2 at level 0, only parsing).
  
Notation "`{ k1 := v1 ; k2 := v2 ; k3 := v3 }" :=
  ((k1,(v1:val))::(k2,(v2:val))::(k3,(v3:val))::nil)
  (at level 0, k1, k2, k3 at level 0, only parsing).

Notation "`{ k1 := v1 }" :=
  ((k1,v1)::nil)
  (at level 0, k1 at level 0, only printing).

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  ((k1,v1)::(k2,v2)::nil)
  (at level 0, k1, k2 at level 0, only printing).

Notation "`{ k1 := v1 ; k2 := v2 ; k3 := v3 }" :=
  ((k1,v1)::(k2,v2)::(k3,v3)::nil)
  (at level 0, k1, k2, k3 at level 0, only printing).

Open Scope val_scope.

Fixpoint hfields (kvs:hrecord_fields) (p:loc) : hprop :=
  match kvs with
  | nil => \[]
  | (k,v)::kvs' => (p`.k ~~> v) \* (hfields kvs' p)
  end.

Definition maps_all_fields (nb:nat) (kvs:hrecord_fields) : Prop :=
  LibList.map fst kvs = nat_seq 0 nb.

Definition hrecord (kvs:hrecord_fields) (p:loc) : hprop :=
  \exists z, hheader z p \* hfields kvs p \* \[maps_all_fields z kvs].

Lemma hrecord_not_null : forall p kvs,
  hrecord kvs p ==> hrecord kvs p \* \[p <> null].
Proof using.
  (*
  intros. unfold himpl. intros.
  rewrite hstar_hpure_r. split.
  - auto.
  - unfold "~". intros.
    rewrite H0 in H. 
    inversion H. destruct H1. destruct H1. destruct H1. 
    apply hheader_not_null in H1. destruct H1. destruct H1. destruct H1. destruct H3.
    destruct H3. unfold  "~" in x4. apply x4. auto.
  *)
  (* book version *)
  intros. unfold hrecord. xpull. intros z M.
  xchanges* hheader_not_null. 
Qed.

Notation "p '~~~>' kvs" := (hrecord kvs p)
  (at level 32).

Definition head : field := 0%nat.
Definition tail : field := 1%nat.

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p ~~~>`{ head := x; tail := q}) \* (MList L' q)
  end.

Lemma MList_if : forall (p:loc) (L:list val),
      (MList L p)
  ==> (If p = null
        then \[L = nil]
        else \exists x q L', \[L = x::L']
             \* (p ~~~> `{ head := x ; tail := q }) \* (MList L' q)).
Proof using.
  intros. destruct L.
  - simpl. xsimpl. intros. case_if. xsimpl. auto.
  - simpl. apply himpl_hexists_l.
    intros. xchanges* hrecord_not_null.
    intros. case_if.
    xsimpl. auto.
Qed.

Global Opaque MList.

Declare Scope trm_scope_ext.

Parameter val_get_field : field -> val.

Notation "t1 '`.' k" :=
  (val_get_field k t1)
  (in custom trm at level 56, k at level 0, format "t1 '`.' k" )
  : trm_scope_ext.

Parameter triple_get_field : forall p k v,
  triple (val_get_field k p)
    (p`.k ~~> v)
    (fun r => \[r = v] \* (p`.k ~~> v)).

Fixpoint hfields_lookup (k:field) (kvs:hrecord_fields) : option val :=
  match kvs with
  | nil => None
  | (ki,vi)::kvs' => if Nat.eq_dec k ki
                       then Some vi
                       else hfields_lookup k kvs'
  end.

Parameter triple_get_field_hfields : forall kvs p k v,
  hfields_lookup k kvs = Some v ->
  triple (val_get_field k p)
    (hfields kvs p)
    (fun r => \[r = v] \* hfields kvs p).

Parameter triple_get_field_hrecord : forall kvs p k v,
  hfields_lookup k kvs = Some v ->
  triple (val_get_field k p)
    (hrecord kvs p)
    (fun r => \[r = v] \* hrecord kvs p).

Parameter val_set_field : field -> val.

Notation "t1 '`.' k ':=' t2" :=
  (val_set_field k t1 t2)
  (in custom trm at level 56, k at level 0, format "t1 '`.' k ':=' t2")
  : trm_scope_ext.

Parameter triple_set_field : forall v p k v',
  triple (val_set_field k p v)
    (p`.k ~~> v')
    (fun _ => p`.k ~~> v).

Fixpoint hfields_update (k:field) (v:val) (kvs:hrecord_fields)
                        : option hrecord_fields :=
  match kvs with
  | nil => None
  | (ki,vi)::kvs' => if Nat.eq_dec k ki
                       then Some ((k,v)::kvs')
                       else match hfields_update k v kvs' with
                            | None => None
                            | Some LR => Some ((ki,vi)::LR)
                            end
  end.

Parameter triple_set_field_hfields : forall kvs kvs' k p v,
  hfields_update k v kvs = Some kvs' ->
  triple (val_set_field k p v)
    (hfields kvs p)
    (fun _ => hfields kvs' p).

Parameter triple_set_field_hrecord : forall kvs kvs' k p v,
  hfields_update k v kvs = Some kvs' ->
  triple (val_set_field k p v)
    (hrecord kvs p)
    (fun _ => hrecord kvs' p).

Definition val_alloc_hrecord (ks:list field) : trm :=
  val_alloc (length ks).

Parameter triple_alloc_hrecord : forall ks,
  ks = nat_seq 0 (LibListExec.length ks) ->
  triple (val_alloc_hrecord ks)
    \[]
    (funloc p => hrecord (LibListExec.map (fun k => (k,val_uninit)) ks) p).

#[global] Hint Resolve triple_alloc_hrecord : triple.

Lemma triple_alloc_mcons :
  triple (val_alloc_hrecord (head::tail::nil))
    \[]
    (funloc p => p ~~~> `{ head := val_uninit ; tail := val_uninit }).
Proof using.
  apply triple_alloc_hrecord. simpl. reflexivity.
Qed.

Definition val_dealloc_hrecord : val :=
  val_dealloc.

Parameter triple_dealloc_hrecord : forall kvs p,
  triple (val_dealloc_hrecord p)
    (hrecord kvs p)
    (fun _ => \[]).

#[global] Hint Resolve triple_dealloc_hrecord : triple.

Notation "'delete'" :=
  (trm_val val_dealloc_hrecord)
  (in custom trm at level 0) : trm_scope_ext.

Lemma triple_dealloc_mcons : forall p x q,
  triple (val_dealloc_hrecord p)
    (p ~~~> `{ head := x ; tail := q })
    (fun _ => \[]).
Proof using.
  intros. apply triple_dealloc_hrecord.
Qed.

Module RecordInit.
Import ProgramSyntax.
Open Scope trm_scope_ext.

Definition val_new_hrecord_2 (k1:field) (k2:field) : val :=
  <{ fun 'x1 'x2 =>
       let 'p = {val_alloc_hrecord (k1::k2::nil)} in
       'p`.k1 := 'x1;
       'p`.k2 := 'x2;
       'p }>.

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  (val_new_hrecord_2 k1 k2 v1 v2)
  (in custom trm at level 65,
   k1, k2 at level 0,
   v1, v2 at level 65) : trm_scope_ext.

Lemma triple_new_hrecord_2 : forall k1 k2 v1 v2,
  k1 = 0%nat ->
  k2 = 1%nat ->
  triple <{ `{ k1 := v1; k2 := v2 } }>
    \[]
    (funloc p => p ~~~> `{ k1 := v1 ; k2 := v2 }).
Proof using.
  intros. subst. 
  unfold val_new_hrecord_2. eapply triple_app_fun2.
  - reflexivity.
  - unfold "~". intros. inversion H.
  - simpl. eapply triple_let.
    -- apply triple_alloc_mcons.
    -- intros. simpl. apply triple_hexists.
       intros. apply triple_hpure.
       intros. subst.
       apply triple_seq with (H1 := (x ~~~>
                                      `{ 0%nat := v1; 1%nat := val_uninit})).
       + apply triple_set_field_hrecord. simpl. reflexivity.
       + apply triple_seq with (H1 := (x ~~~>
                                      `{ 0%nat := v1; 1%nat := v2})).
         ++ apply triple_set_field_hrecord. simpl. reflexivity.
         ++ apply triple_val. xsimpl. auto.
Qed.

Definition mcons : val :=
  val_new_hrecord_2 head tail.

Lemma triple_mcons : forall (x q:val),
  triple (mcons x q)
    \[]
    (funloc p => p ~~~> `{ head := x ; tail := q }).
Proof using.
  intros. unfold mcons. apply triple_new_hrecord_2. auto. auto.
Qed.

End RecordInit.

  
       
       
       
