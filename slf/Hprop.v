Set Implicit Arguments.
From SLF Require Export LibSepReference.
Import ProgramSyntax.

Arguments Fmap.single {A} {B}.
Arguments Fmap.union {A} {B}.
Arguments Fmap.disjoint {A} {B}.
Arguments Fmap.union_comm_of_disjoint {A} {B}.
Arguments Fmap.union_empty_l {A} {B}.
Arguments Fmap.union_empty_r {A} {B}.
Arguments Fmap.union_assoc {A} {B}.
Arguments Fmap.disjoint_empty_l {A} {B}.
Arguments Fmap.disjoint_empty_r {A} {B}.
Arguments Fmap.disjoint_union_eq_l {A} {B}.
Arguments Fmap.disjoint_union_eq_r {A} {B}.

Definition example_val : val :=
  val_fun "x" (trm_if (trm_var "x")
                (trm_val (val_int 0))
                (trm_val (val_int 1))).

Definition example_val' : trm :=
  <{ fun "x" =>
       if "x" then 0 else 1 }>.

Definition state : Type := fmap loc val.

Definition heap : Type := state.

Definition hprop := heap -> Prop.

Implicit Type H : hprop.

Definition hempty : hprop :=
  fun (h:heap) => (h = Fmap.empty).

Notation "\[]" := (hempty) (at level 0).

Definition hpure (P:Prop) : hprop :=
  fun (h:heap) => (h = Fmap.empty) /\ P.

Notation "\[ P ]" := (hpure P) (at level 0, format "\[ P ]").

Definition hsingle (p:loc) (v:val) : hprop :=
  fun (h:heap) => (h = Fmap.single p v).

Notation "p '~~>' v" := (hsingle p v) (at level 32).

Definition hstar (H1 H2 : hprop) : hprop :=
  fun (h:heap) => exists h1 h2, H1 h1
                             /\ H2 h2
                             /\ Fmap.disjoint h1 h2
                             /\ h = Fmap.union h1 h2.

Notation "H1 '\*' H2" := (hstar H1 H2) (at level 41, right associativity).

Definition hexists (A:Type) (J:A->hprop) : hprop :=
  fun (h:heap) => exists x, J x h.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ ' x1 .. xn , '/ ' H ']'").

Parameter hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).

Axiom predicate_extensionality : forall (A:Type) (P Q:A->Prop),
  (forall x, P x <-> Q x) ->
  P = Q.

Lemma hprop_eq : forall (H1 H2:hprop),
  (forall (h:heap), H1 h <-> H2 h) ->
  H1 = H2.
Proof using. apply predicate_extensionality. Qed.

Implicit Type Q : val -> hprop.

Notation "Q \*+ H" := (fun x => hstar (Q x) H) (at level 40).

Axiom functional_extensionality : forall A B (f g:A->B),
  (forall x, f x = g x) ->
  f = g.

Lemma qprop_eq : forall (Q1 Q2:val->hprop),
  (forall (v:val), Q1 v = Q2 v) ->
  Q1 = Q2.
Proof using. apply functional_extensionality. Qed.

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (s:state), H s ->
  exists (s':state) (v:val), eval s t s' v /\ Q v s'.

Lemma hoare_conseq : forall t H Q H' Q',
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using.
  intros.
  unfold hoare in *.
  intros.
  pose proof (H0 s).
  unfold "==>" in H1.
  apply H1 in H3.
  pose proof (H4 H3).
  destruct H5.
  destruct H5.
  destruct H5.
  exists x x0.
  split.
  - auto.
  - unfold "===>" in H2. apply H2 in H6. auto.
Qed.

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoare t (H \* H') (Q \*+ H').

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using.
  intros. unfold triple in *.
  intros. unfold hoare in *.
  intros. pose proof (H0 (H' \* H'0)).
  pose proof (H2 s).
  assert ((H \* H' \* H'0) = ((H \* H') \* H'0)). { rewrite hstar_assoc. auto. }
  rewrite H4 in H3.
  pose proof (H3 H1).
  destruct H5. destruct H5. destruct H5.
  exists x x0.
  split.
  - auto.
  - rewrite hstar_assoc. auto.
Qed.

Parameter incr : val.

Lemma incr_applied : forall (p:loc) (n:int),
    trm_app (trm_val incr) (trm_val (val_loc p))
  = incr p.
Proof using. reflexivity. Qed.

Parameter triple_incr : forall (p:loc) (n:int),
  triple (incr p)
    (p ~~> n)
    (fun r => p ~~> (n+1)).
    
   