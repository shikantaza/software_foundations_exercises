Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

Definition relation (X: Type) := X -> X -> Prop.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.
  
Print next_nat.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
unfold partial_function.
intros.
inversion H.
inversion H0.
reflexivity.
Qed.

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
unfold not.
intros.
unfold partial_function in H.
pose proof (H 0 0 1) as H1.
discriminate H1.
- reflexivity.
- apply le_S. apply le_n.
Qed.

(* copied from IndProp.v *)
Inductive total_relation : nat -> nat -> Prop :=
  | tr m n (H: m = n \/ ~(m = n)) : total_relation m n.

Theorem total_rel_not_a_partial_function:
  ~ (partial_function total_relation).
Proof.
unfold partial_function.
unfold not.
intros.
pose proof (H 0 1 2) as H1.
discriminate H1.
- apply tr.
  right.
  unfold not.
  intros.
  discriminate H0.
- apply tr.
  right.
  unfold not.
  intros.
  discriminate H0.
Qed.

(* copied form IndProp.v *)
Inductive empty_relation : nat -> nat -> Prop :=
  | er m n (H: m = n /\ ~(m = n)) : empty_relation m n.
  
Theorem empty_rel_is_partial_function:
 partial_function empty_relation.
Proof.
unfold partial_function.
intros.
induction H.
induction H0.
destruct H.
destruct H0.
rewrite <- H.
assumption.
Qed.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.
  
Theorem le_reflexive :
  reflexive le.
Proof.
unfold reflexive.
intros.
apply le_n.
Qed.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Lemma le_trans_helper: forall m n, S m <= n -> m <= n.
Proof.
intros.
induction H.
apply le_S.
apply le_n.
apply le_S.
apply IHle.
Qed.

Theorem le_trans :
  transitive le. 
Proof.
unfold transitive.
intros.
induction H.
- assumption.
- apply IHle.
  apply le_trans_helper.
  assumption.
Qed.

(* book version *) 
Theorem le_trans' :
  transitive le. 
Proof.
unfold transitive.
intros.
induction H0.
- apply H.
- apply le_S. assumption.
Qed.

Lemma lt_ge_cases_helper1: forall n m,
  n < m -> n < S m.
Proof.
intros.
destruct H.
apply le_S.
apply le_n.
apply le_S.
apply le_S.
apply H.
Qed.

Theorem lt_trans:
  transitive lt. 
Proof.
unfold transitive.
intros.
induction H0.
- apply lt_ge_cases_helper1. assumption.
- apply lt_ge_cases_helper1. assumption.
Qed.

(* book version *) 
Theorem lt_trans_book:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo.
Qed.

Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that m is less than o. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o]. 
  -- apply le_S. assumption.
  -- apply le_S. assumption.
Qed.

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  - apply le_S in Hnm.
    pose proof (le_trans (S n) (S m) 0) as H1.
    apply ((H1 Hnm) Hmo).
  - apply le_S in Hnm.
    pose proof (le_trans (S n) (S m) (S o')) as H1.
    apply ((H1 Hnm) Hmo).
Qed.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
intros.
induction H.
- apply le_S. apply le_n.
- apply le_S. assumption.
Qed.

(* book version *)
Theorem le_Sn_le' : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
intros.
inversion H.
- apply le_n.
- apply le_Sn_le. assumption.
Qed.

(* informal proof of
   forall n, ~ (S n <= n)

   Assume (S n) <= n for some n.
   Then, according to the inductive definition of le (le_S in particular),
   (S n) <= n - 1.
   Repeated applications of le_S leads to (S n) <= 0, which is not true. Qed.
 *)
 
Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
intros.
unfold not.
intros.
induction n.
- inversion H.
- apply le_S_n in H.
  apply (IHn H).
Qed.

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
unfold not.
unfold symmetric.
intros.
pose proof (H 0 1) as H1.
pose proof (le_S 0 0) as H2.
pose proof (le_n 0) as H3.
pose proof (H1 (H2 H3)) as H4.
inversion H4.
Qed.

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
unfold antisymmetric.
intros.
inversion H0.
- reflexivity.
- pose proof (le_trans a b m) as H3.
  pose proof ((H3 H) H1) as H4.
  rewrite <- H2 in H4.
  exfalso.
  pose proof (le_Sn_n m) as H5.
  apply (H5 H4).
Qed.

Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
intros.
unfold lt in H.
pose proof (le_trans (S n) m (S p)) as H1.
pose proof ((H1 H) H0) as H2.
apply le_S_n.
assumption.
Qed.

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).
  
Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).
  
Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).
  
Theorem le_order :
  order le.   
Proof.
unfold order.
split.
- apply le_reflexive.
- split.
  -- apply le_antisymmetric.
  -- apply le_trans.
Qed.

  
Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
  | rt_step x y (H : R x y) : clos_refl_trans R x y
  | rt_refl x : clos_refl_trans R x x
  | rt_trans x y z
        (Hxy : clos_refl_trans R x y)
        (Hyz : clos_refl_trans R y z) :
        clos_refl_trans R x z.

Print le_ind.

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
intros.
split.
- intros.
  induction H.
  -- apply rt_refl.
  -- assert (clos_refl_trans next_nat m (S m)). 
     { apply rt_step. apply nn. }
     apply (rt_trans next_nat n m (S m) IHle H0).
- intros. 
  induction H.
  inversion H.
  -- apply le_S. apply le_n.
  -- apply le_n.
  -- apply (le_trans  x y z).
     --- assumption.
     --- assumption.
Qed.

(* book version *)
Theorem next_nat_closure_is_le' : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  - (* -> *)
    intro H. induction H.
    + (* le_n *) apply rt_refl.
    + (* le_S *)
      apply rt_trans with m. apply IHle. apply rt_step.
      apply nn.
  - (* <- *)
    intro H. induction H.
    + (* rt_step *) inversion H. apply le_S. apply le_n.
    + (* rt_refl *) apply le_n.
    + (* rt_trans *)
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2. Qed.
  
Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.  
  
Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
  R x y -> clos_refl_trans_1n R x y.
Proof.
intros.
apply (rt1n_trans R x y).
- assumption.
- apply rt1n_refl.
Qed.  

Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
    clos_refl_trans_1n R x y ->
    clos_refl_trans_1n R y z ->
    clos_refl_trans_1n R x z.
Proof.  
intros X R x y z Hxy Hyz.
induction Hxy.
- assumption.
- pose proof (IHHxy Hyz) as H1.
  apply (rt1n_trans R x y).
  -- assumption.
  -- assumption.
Qed.

Theorem rtc_rsc_coincide :
  forall (X:Type) (R: relation X) (x y : X),
    clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
intros.
split.
- intros.
  induction H.
  -- apply rsc_R. assumption.
  -- apply rt1n_refl.
  -- apply (rsc_trans X R x y z).
    --- assumption.
    --- assumption. 
- intros.
  induction H.
  -- apply rt_refl.
  -- apply (rt_trans R x y).
     + apply rt_step. assumption.
     + assumption.
Qed.
