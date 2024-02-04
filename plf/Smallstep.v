Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.

Definition FILL_IN_HERE := <{True}>.

Inductive tm : Type :=
  | C : nat -> tm (* Constant *)
  | P : tm -> tm -> tm. (* Plus *)
  
Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.
  
Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n ==> n
  | E_Plus : forall t1 t2 v1 v2,
      t1 ==> v1 ->
      t2 ==> v2 ->
      P t1 t2 ==> (v1 + v2)

where " t '==>' n " := (eval t n).

Module SimpleArith1.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      t2 --> t2' ->
      P (C v1) t2 --> P (C v1) t2'

  where " t '-->' t' " := (step t t').
  
Example test_step_1 :
      P
        (P (C 1) (C 3))
        (P (C 2) (C 4))
      -->
      P
        (C 4)
        (P (C 2) (C 4)).
Proof.
apply ST_Plus1.
apply ST_PlusConstConst.
Qed.

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 1) (C 3)))
      -->
      P
        (C 0)
        (P
          (C 2)
          (C 4)).
Proof.
apply ST_Plus2.
apply ST_Plus2.
apply ST_PlusConstConst.
Qed.

End SimpleArith1.

Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic:
  deterministic step.
Proof.
unfold deterministic.
intros x y1 y2 Hy1 Hy2.
generalize dependent y2.
induction Hy1; intros y2 Hy2.
- inversion Hy2; subst.
  -- reflexivity.
  -- inversion H2.
  -- inversion H2.
- inversion Hy2; subst.
  -- inversion Hy1. 
  -- apply IHHy1 in H2. rewrite H2. reflexivity.
  -- inversion Hy1.
- inversion Hy2; subst.
  -- inversion Hy1.
  -- inversion H2.
  -- apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith2.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.
  
Ltac solve_by_invert :=
  solve_by_inverts 1.
  
Module SimpleArith3.
Import SimpleArith1.

Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try solve_by_invert.
  - (* ST_PlusConstConst *) reflexivity.
  - (* ST_Plus1 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
  - (* ST_Plus2 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).  

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
          P (C v1) (C v2)
      --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 -> (* <--- n.b. *)
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').
  
Theorem step_deterministic :
  deterministic step.
Proof.
unfold deterministic.
intros.
generalize dependent y2.
induction H; intros.
- inversion H0; subst; try solve_by_invert.
  -- reflexivity.
- inversion H0; subst; try solve_by_invert.
  -- apply IHstep in H4. rewrite H4. reflexivity.
  -- inversion H3. rewrite <- H1 in H. inversion H.
- inversion H1; subst; try solve_by_invert.
  -- inversion H. rewrite <- H2 in H5. inversion H5.
  -- apply IHstep in H6. rewrite H6. reflexivity.
Qed.

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
intros.
induction t.
- left. apply v_const.
- destruct IHt1.
  destruct IHt2.
  -- right.
     inversion H. inversion H0.
     exists (C (n + n0)).
     apply ST_PlusConstConst.
  -- destruct H0.
     right.
     exists (P t1 x).
     apply ST_Plus2. assumption. assumption.
  -- destruct H.
     right.
     destruct IHt2.
     --- exists (P x t2).
         apply ST_Plus1.
         assumption.
     --- exists (P x t2). apply ST_Plus1. assumption.
Qed.  
  
Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.
  
Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
intros.
unfold normal_form.
unfold not.
intros.
destruct H0.
inversion H.
rewrite <- H1 in H0.
inversion H0.  
Qed.  
  
Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof.
intros.
unfold normal_form in H.
unfold not in H.
induction t.
- apply v_const.
- exfalso.
  apply H.
  assert (H1: value t1). { 
    apply IHt1.
    intros.
    destruct H0.
    assert (H1: (P t1 t2) --> (P x t2)). { apply ST_Plus1. assumption. }
    apply H.
    exists (P x t2). assumption.
  }
  assert (H2: value t2). { 
    apply IHt2.
    intros.
    destruct H0.
    assert (H2: (P t1 t2) --> (P t1 x)). { apply ST_Plus2. assumption. assumption. }
    apply H.
    exists (P t1 x). assumption.
  }
  inversion H1. inversion H2.
  exists (C (n + n0)).
  apply ST_PlusConstConst. 
Qed.

(* book version *)
Lemma nf_is_value' : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of strong_progress... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t --> t').
  { apply strong_progress. }
  destruct G as [G | G].
  - (* l *) apply G.
  - (* r *) contradiction.
Qed.  

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
split.
- apply nf_is_value.
- apply value_is_nf.
Qed.

Module Temp1.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_funny : forall t1 v2,
                value (P t1 (C v2)). (* <--- *)
                
Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
unfold normal_form.
exists (P (C 0) (C 0)).
split.
- apply v_funny.
- unfold not.
  intros.
  apply H.
  exists (C 0).
  apply ST_PlusConstConst.
Qed.

End Temp1.

Module Temp2.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n). (* Original definition *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,
      C n --> P (C n) (C 0) (* <--- NEW *)
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
unfold normal_form.
exists (C 0).
split.
- apply v_const.
- unfold not.
  intros.
  apply H.
  exists (P (C 0) (C 0)).
  apply ST_Funny.  
Qed.  
  
End Temp2.

Module Temp3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).
  
Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
(* Note that ST_Plus2 is missing. *)

  where " t '-->' t' " := (step t t').
  
Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
unfold normal_form.
exists (P (C 0) (P (C 0) (C 0))).
split.
- unfold not. intros. inversion H.
- unfold not. intros. destruct H.
  inversion H. subst. inversion H3.
Qed.  

End Temp3.  

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
                    
Notation " t '-->*' t' " := (multi step t t') (at level 40).

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
intros.
eapply multi_step.
- apply H.
- apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
intros.
induction H.
- assumption.
- pose proof (IHmulti H0) as H2.
  apply multi_step with y. assumption. assumption.
Qed.

Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   -->*
      C ((0 + 3) + (2 + 4)).
Proof.
eapply multi_step.
- apply ST_Plus1.
  apply ST_PlusConstConst.
- eapply multi_step.
  -- apply ST_Plus2.
     --- apply v_const.
     --- apply ST_PlusConstConst.
  -- eapply multi_step.
     --- apply ST_PlusConstConst.
     --- apply multi_refl.
Qed.     

Lemma test_multistep_2:
  C 3 -->* C 3.
Proof.
apply multi_refl.
Qed.

Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  -->*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
eapply multi_step.
- apply ST_Plus2.
  -- apply v_const.
  -- apply ST_Plus2.
     --- apply v_const.
     --- apply ST_PlusConstConst.
- eapply multi_step.
  -- apply ST_Plus2.
     --- apply v_const.
     --- apply ST_PlusConstConst.
  -- apply multi_refl.
Qed.

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t -->* t' /\ step_normal_form t').

(* not needed *)
Lemma normal_forms_unique_helper :
  forall x y, x -->* y -> x --> y \/ exists y', x -->* y' /\ y' -->* y.
Proof.
intros.
right.
exists y.
split.
assumption.
apply multi_refl.
Qed.

Lemma normal_forms_unique_helper1 :
  forall x y, x -->* y -> x = y \/ x --> y \/ exists y', x --> y' /\ y' -->* y.
Proof.
intros.
inversion H.
- left. reflexivity.
- right. right. exists y0. split. assumption. assumption.
Qed.
  
Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  (* We recommend using this initial setup as-is! *)
  unfold deterministic. unfold normal_form_of.
  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12].
  destruct P2 as [P21 P22].
  generalize dependent y2.
  induction P11.
  - intros.
    unfold step_normal_form in P12, P22.
    unfold normal_form in P12, P22.
    unfold not in P12.
    inversion P21.
    -- reflexivity.
    -- exfalso. apply P12. exists y. assumption.
  - intros.
    apply IHP11.
    -- assumption.
    -- pose proof (normal_forms_unique_helper1 x y2) as H1.
       pose proof (H1 P21) as H2. clear H1.
       destruct H2.
       --- rewrite <- H0 in P22.
           unfold step_normal_form in P22.
           unfold normal_form in P22.
           unfold not in P22.
           exfalso.
           apply P22.
           exists y.
           assumption. 
       --- destruct H0.
           + pose proof (step_deterministic x y y2) as H1.
             pose proof ((H1 H) H0) as H2.
             rewrite H2.
             apply multi_refl.
           + destruct H0.
             destruct H0.
             pose proof (step_deterministic x y x0) as H2.
             pose proof ((H2 H) H0) as H2.
             rewrite H2.
             assumption.
    -- assumption.
Qed.

Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.
    
Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 -->* t1' ->
     P t1 t2 -->* P t1' t2.
Proof.
intros.
induction H.
- apply multi_refl.
- assert (H1: P x t2 --> P y t2). { apply ST_Plus1. assumption. }
  assert (H2: P x t2 -->* P y t2). { apply multi_R. assumption. }
  apply multi_trans with (P y t2). assumption. assumption.
Qed.

Lemma multistep_congr_2 : forall v1 t2 t2',
     value v1 ->
     t2 -->* t2' ->
     P v1 t2 -->* P v1 t2'.
Proof.
intros.
induction H0.
- apply multi_refl.
- assert (H2: P v1 x --> P v1 y). { apply ST_Plus2. assumption. assumption. }
  assert (H3: P v1 x -->* P v1 y). { apply multi_R. assumption. }
  apply multi_trans with (P v1 y). assumption. assumption.
Qed.

Theorem step_normalizing :
  normalizing step.
Proof.
unfold normalizing.
intros.
destruct t.
- exists (C n).
  split.
  apply multi_refl.
  rewrite nf_same_as_value.
  apply v_const.
- induction (P t1 t2).
  -- exists (C n). split.
     --- apply multi_refl.
     --- rewrite nf_same_as_value. apply v_const.
  -- destruct IHt1.
     destruct IHt2.
     destruct H.
     destruct H0.
     rewrite nf_same_as_value in H1, H2.
     inversion H1. inversion H2.
     exists (C (n+n0)).
     split.
     --- rewrite <- H3 in H. clear H3. 
         rewrite <- H4 in H0. clear H4.
         clear H1 H2. clear x x0.
         pose proof (multistep_congr_1 t3 (C n) t4) as H1.
         assert (H2: value (C n)) by (apply v_const).
         pose proof (multistep_congr_2 (C n) t4 (C n0) H2) as H6.
         pose proof (H1 H) as H7.
         pose proof (H6 H0) as H8.
         assert (H9: P t3 t4 -->* P (C n) (C n0)).
         {  
           apply multi_trans with (P (C n) t4).
           assumption. assumption.
         }
         assert (H10: P (C n) (C n0) -->* C (n + n0)).
         {
           apply multi_R. apply ST_PlusConstConst.
         }
         apply multi_trans with (P (C n) (C n0)).
         assumption.
         assumption.
     --- rewrite nf_same_as_value. apply v_const.
Qed.         

Theorem eval__multistep : forall t n,
  t ==> n -> t -->* C n.
Proof.
intros.
induction H.
- apply multi_refl.
- assert (H1: P t1 t2 -->* P (C v1) t2).
  {
    apply multistep_congr_1. apply IHeval1.
  }
  assert (H2: P (C v1) t2 -->* P (C v1) (C v2)).
  {
    apply multistep_congr_2.
    -- apply v_const.
    -- apply IHeval2.
  }
  assert (H3: P t1 t2 -->* P (C v1) (C v2)).
  {
    apply multi_trans with (P (C v1) t2). assumption. assumption.
  }
  assert (H4: P (C v1) (C v2) -->* C (v1 + v2)).
  {
    apply multi_R. apply ST_PlusConstConst.
  }
  apply multi_trans with (P (C v1) (C v2)).
  assumption. assumption.
Qed.

(* 

Informal proof of eval__multistep:

Two cases arise if t evaluates n:

1. t is of the form 'C n'. In which case, we need to prove C n -->* C n
   which follows from multi_refl.
   
2. t is of the form '(P t1 t2)'.

   We have two induction hypotheses:
   
   t1 ==> v1 -> t1 -->* C v1
   t2 ==> v2 -> t2 -->* C v2

   We need to prove P t1 t2 -->* C (v1 + v2)
   
   We can show that P t1 t2 -> P (C v1) t2 by multistep_congr_1
   We can show that P (C v1) t2 -> P (C v1) (C v2) by multistep_congr_2
   
   By multi_trans, we can thus show that P t1 t2 --> P (C v1) (C v2)
   Also, P (C v1) (C v2) -->* C (v1 + v2) by ST_PlusConstConst
   
   Thus, by applying multi_trans again, we can show that 
   P t1 t2 -->* C (v1 + v2)
   
   Qed.
*)

Lemma step__eval : forall t t' n,
     t --> t' ->
     t' ==> n ->
     t ==> n.
Proof.
  intros t t' n Hs. generalize dependent n.
  induction Hs.
  - intros. inversion H. apply E_Plus.
    -- apply E_Const.
    -- apply E_Const.
  - intros. inversion H. subst.
    apply E_Plus.
    apply (IHHs v1).
    -- assumption.
    -- assumption.
  - intros. inversion H. subst. inversion H0. subst.
    pose proof (IHHs v2) as H6.
    pose proof (H6 H5) as H7.
    apply E_Plus.
    -- assumption.
    -- assumption.
Qed.

Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t ==> n.
Proof.
intros.
unfold normal_form_of in H.
destruct H.
induction H.
- unfold step_normal_form in H0.
  apply nf_same_as_value in H0.
  inversion H0.
  exists n.
  split.
  -- reflexivity.
  -- apply E_Const.
- unfold step_normal_form in H0.
  apply nf_same_as_value in H0.
  inversion H0.
  exists n.
  split.
  -- reflexivity.
  -- unfold step_normal_form in IHmulti.
     rewrite nf_same_as_value in IHmulti.
     pose proof (IHmulti H0) as H3.
     destruct H3.
     destruct H3.
     rewrite <- H2 in H3.
     inversion H3.
     rewrite <- H6.
     pose proof (step__eval x y n) as H7.
     apply H7.
     --- assumption. 
     --- rewrite <- H6 in H4. assumption.
Qed.

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).
  
Reserved Notation " a '/' st '-->a' a' "
                  (at level 40, st at level 39).
                  
Inductive astep (st : state) : aexp -> aexp -> Prop :=
  | AS_Id : forall (i : string),
      i / st -->a (st i)
  | AS_Plus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 + a2 }> / st -->a <{ a1' + a2 }>
  | AS_Plus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 + a2 }> / st -->a <{ v1 + a2' }>
  | AS_Plus : forall (v1 v2 : nat),
      <{ v1 + v2 }> / st -->a (v1 + v2)
  | AS_Minus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 - a2 }> / st -->a <{ a1' - a2 }>
  | AS_Minus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 - a2 }> / st -->a <{ v1 - a2' }>
  | AS_Minus : forall (v1 v2 : nat),
      <{ v1 - v2 }> / st -->a (v1 - v2)
  | AS_Mult1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 * a2 }> / st -->a <{ a1' * a2 }>
  | AS_Mult2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 * a2 }> / st -->a <{ v1 * a2' }>
  | AS_Mult : forall (v1 v2 : nat),
      <{ v1 * v2 }> / st -->a (v1 * v2)

    where " a '/' st '-->a' a' " := (astep st a a').
    
Reserved Notation " b '/' st '-->b' b' "
                  (at level 40, st at level 39).     
                  
Inductive bstep (st : state) : bexp -> bexp -> Prop :=
| BS_Eq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 = a2 }> / st -->b <{ a1' = a2 }>
| BS_Eq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 = a2 }> / st -->b <{ v1 = a2' }>
| BS_Eq : forall (v1 v2 : nat),
    <{ v1 = v2 }> / st -->b
    (if (v1 =? v2) then <{ true }> else <{ false }>)
| BS_LtEq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 <= a2 }> / st -->b <{ a1' <= a2 }>
| BS_LtEq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 <= a2 }> / st -->b <{ v1 <= a2' }>
| BS_LtEq : forall (v1 v2 : nat),
    <{ v1 <= v2 }> / st -->b
    (if (v1 <=? v2) then <{ true }> else <{ false }>)
| BS_NotStep : forall b1 b1',
    b1 / st -->b b1' ->
    <{ ~ b1 }> / st -->b <{ ~ b1' }>
| BS_NotTrue : <{ ~ true }> / st -->b <{ false }>
| BS_NotFalse : <{ ~ false }> / st -->b <{ true }>
| BS_AndStep : forall b1 b1' b2,
    b1 / st -->b b1' ->
    <{ b1 && b2 }> / st -->b <{ b1' && b2 }>
| BS_AndTrueStep : forall b2 b2',
    b2 / st -->b b2' ->
    <{ true && b2 }> / st -->b <{ true && b2' }>
| BS_AndFalse : forall b2,
    <{ false && b2 }> / st -->b <{ false }>
| BS_AndTrueTrue : <{ true && true }> / st -->b <{ true }>
| BS_AndTrueFalse : <{ true && false }> / st -->b <{ false }>

where " b '/' st '-->b' b' " := (bstep st b b').

Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).
                  
     Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).
  
Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com. (* <--- NEW *)
  
Notation "x || y" :=
         (CPar x y)
           (in custom com at level 90, right associativity).
Notation "'skip'" :=
         CSkip (in custom com at level 0).
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).
            
Inductive cstep : (com * state) -> (com * state) -> Prop :=
    (* Old part: *)
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st --> c1' / st' ->
      <{ c1 || c2 }> / st --> <{ c1' || c2 }> / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st --> c2' / st' ->
      <{ c1 || c2 }> / st --> <{ c1 || c2' }> / st'
  | CS_ParDone : forall st,
      <{ skip || skip }> / st --> <{ skip }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep.

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).
   
Definition par_loop : com :=
  <{
      Y := 1
    ||
      while (Y = 0) do X := X + 1 end
   }>.
   
Example par_loop_example_0:
  exists st',
       par_loop / empty_st -->* <{skip}> / st'
    /\ st' X = 0.
unfold par_loop.
exists (Y !-> 1).
split.
- eapply multi_step.
  -- eapply CS_Par1.
     apply CS_Asgn.
  -- eapply multi_step.
     --- eapply CS_Par2.
         apply CS_While.
     --- eapply multi_step.
         + eapply CS_Par2.
           ++ apply CS_IfStep.
              apply BS_Eq1.
              apply AS_Id.
         + eapply multi_step.
           ++ eapply CS_Par2.
              rewrite t_update_eq.
              apply CS_IfStep.
              apply BS_Eq.
           ++ eapply multi_step.
              +++ eapply CS_Par2.
                  simpl.
                  apply CS_IfFalse.
              +++ eapply multi_step.
                  ++++ apply CS_ParDone.
                  ++++ apply multi_refl.
- rewrite t_update_neq.
  -- reflexivity.
  -- unfold not.
     intros.
     inversion H. 
Qed.

Ltac par_loop_par1_execute :=
eapply multi_step;
  try (apply CS_Par1;
       apply CS_Asgn);
  try (eapply multi_step;
       try (apply CS_Par2;
            apply CS_While);
       try (eapply multi_step;
            try (apply CS_Par2;
                 apply CS_IfStep;
                 apply BS_Eq1;
                 apply AS_Id);
            try (eapply multi_step;
                 try (apply CS_Par2;
                      apply CS_IfStep;
                      apply BS_Eq);
                 try (eapply multi_step;
                      try (simpl;
                           eapply CS_Par2;
                           apply CS_IfFalse);
                      try (eapply multi_step; 
                           try (apply CS_ParDone);
                           try (apply multi_refl)))))).

Ltac par_loop_par2_execute :=
eapply multi_step;
  try (apply CS_Par2;
       apply CS_While);
  try (eapply multi_step;
       try (apply CS_Par2;
            apply CS_IfStep;
            apply BS_Eq1;
            apply AS_Id);
       try (eapply multi_step;
            try (apply CS_Par2;
                 apply CS_IfStep;
                 apply BS_Eq);
            try (eapply multi_step;
                 try (apply CS_Par2;
                      simpl;
                      apply CS_IfTrue);
                 try (eapply multi_step;
                      try (apply CS_Par2;
                           apply CS_SeqStep;
                           apply CS_AsgnStep;
                           apply AS_Plus1;
                           apply AS_Id));
                 try (eapply multi_step;
                      try (apply CS_Par2;
                           apply CS_SeqStep;
                           apply CS_AsgnStep;
                           apply AS_Plus);
                      try (eapply multi_step;
                           try (apply CS_Par2;
                                simpl;
                                apply CS_SeqStep;
                                apply CS_Asgn));
                           try (eapply multi_step;
                                try (apply CS_Par2;
                                     apply CS_SeqFinish)))))).

Example par_loop_example_2:
  exists st',
       par_loop / empty_st -->* <{skip}> / st'
    /\ st' X = 2.
unfold par_loop.
eexists.
split.
- par_loop_par2_execute.
  par_loop_par2_execute.
  par_loop_par1_execute.
- reflexivity.
Qed.

Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st -->* par_loop / (X !-> S n ; st).
Proof.
intros.
destruct H.
unfold par_loop.
eapply multi_step.
- apply CS_Par2.
  apply CS_While.
- eapply multi_step.
  -- apply CS_Par2.
     apply CS_IfStep.
     apply BS_Eq1.
     apply AS_Id.
  -- eapply multi_step.
     --- apply CS_Par2.
         rewrite H0.
         apply CS_IfStep.
         apply BS_Eq.
     --- eapply multi_step.
         ---- apply CS_Par2.
              simpl.
              apply CS_IfTrue.
         ---- eapply multi_step.
              + apply CS_Par2.
                apply CS_SeqStep.
                apply CS_AsgnStep.
                apply AS_Plus1.
                apply AS_Id.
              + rewrite H.
                eapply multi_step.
                ++ apply CS_Par2.
                   apply CS_SeqStep.
                   apply CS_AsgnStep.
                   apply AS_Plus.
                ++ eapply multi_step.
                   +++ apply CS_Par2.
                       apply CS_SeqStep.
                       apply CS_Asgn.
                   +++ eapply multi_step.
                       ++++ apply CS_Par2.
                            apply CS_SeqFinish.
                       ++++ assert (n + 1 = S n) by lia.
                            rewrite H1.
                            apply multi_refl.
Qed.

Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st -->* par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
induction n.
- intros.
  eexists.
  split.
  -- apply multi_refl.
  -- assumption.
- intros.
  pose proof (IHn st) as H1.
  pose proof (H1 H) as H2. clear IHn H1.
  destruct H2. destruct H0. destruct H1.
  pose proof (par_body_n__Sn n x) as H3.
  assert (H4: x X = n -> x Y = 0 -> x X = n /\ x Y = 0). { split. assumption. assumption. }
  pose proof ((H4 H1) H2) as H5. clear H4.
  pose proof (H3 H5) as H6. clear H3 H5.
  pose proof (multi_trans (com * state)
                          cstep 
                          (par_loop , st)
                          (par_loop , x)
                          (par_loop , (X !-> S n; x))) as H7.
  pose proof ((H7 H0) H6) as H8.
  exists (X !-> S n; x).
  split.
  -- apply H8.
  -- split.
     --- rewrite t_update_eq. reflexivity.
     --- rewrite t_update_neq. 
         ---- assumption.
         ---- unfold not. intros. inversion H3.
Qed.

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / empty_st -->* <{skip}> / st'
    /\ st' X = n.
Proof.
intros.
pose proof (par_body_n n empty_st) as H1.
assert (H2: empty_st X = 0 /\ empty_st Y = 0). { split. reflexivity. reflexivity. }
pose proof (H1 H2) as H3. clear H1 H2.
destruct H3. destruct H. destruct H0.
assert (H2: par_loop / x -->* <{ skip }> / (Y !-> 1; x)) by par_loop_par1_execute.
pose proof (multi_trans (com * state)
                        cstep
                        (par_loop, empty_st)
                        (par_loop , x)
                        (<{ skip }>, (Y !-> 1; x))) as H3.
pose proof ((H3 H) H2) as H4.
eexists.
split.
- apply H4.
- rewrite <- H0.
  reflexivity.
Qed.

End CImp.

Definition stack := list nat.
Definition prog := list sinstr.

Inductive stack_step (st : state) : prog * stack -> prog * stack -> Prop :=
  | SS_Push : forall stk n p,
    stack_step st (SPush n :: p, stk) (p, n :: stk)
  | SS_Load : forall stk i p,
    stack_step st (SLoad i :: p, stk) (p, st i :: stk)
  | SS_Plus : forall stk n m p,
    stack_step st (SPlus :: p, n::m::stk) (p, (m+n)::stk)
  | SS_Minus : forall stk n m p,
    stack_step st (SMinus :: p, n::m::stk) (p, (m-n)::stk)
  | SS_Mult : forall stk n m p,
    stack_step st (SMult :: p, n::m::stk) (p, (m*n)::stk).
 
Theorem stack_step_deterministic : forall st,
  deterministic (stack_step st).
Proof.
unfold deterministic.
intros.
induction H; try (intros; inversion H0; reflexivity).
Qed.

Definition stack_multistep st := multi (stack_step st).

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
match prog with
| SPush n :: rest => s_execute st (n :: stack) rest
| SLoad x :: rest => s_execute st ((st x) :: stack) rest
| SPlus :: rest => match stack with
                   | n1 :: n2 :: rest1 => s_execute st ((n1 + n2) :: rest1) rest
                   | _ => (s_execute st stack rest)
                   end
| SMinus :: rest => match stack with
                   | n1 :: n2 :: rest1 => s_execute st ((n2 - n1) :: rest1) rest
                   | _ => (s_execute st stack rest)
                   end
| SMult :: rest => match stack with
                   | n1 :: n2 :: rest1 => s_execute st ((n1 * n2) :: rest1) rest
                   | _ => (s_execute st stack rest)
                   end
| [] => stack
end.

Compute (s_execute empty_st [] [SPush 5; SPush 3; SPush 1]).

Example s_execute1 :
     s_execute empty_st []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
Proof. reflexivity. Qed.

Example s_execute2 :
     s_execute (X !-> 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof. reflexivity. Qed.

Fixpoint s_compile (e : aexp) : list sinstr :=
match e with
| AId x => (SLoad x) :: nil
| ANum n => (SPush n) :: nil
| APlus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SPlus]
| AMinus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SMinus]
| AMult e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SMult]
end.

Example s_compile1 :
  s_compile <{ X - (2 * Y) }>
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. reflexivity. Qed.

Definition compiler_is_correct_statement : Prop :=
 forall (st : state) (e : aexp) (st1 : stack) (p1 : prog),
   stack_multistep st ((s_compile e) ++ p1, st1) (p1, (aeval st e) :: st1). 
   
Theorem compiler_is_correct : compiler_is_correct_statement.
Proof.
unfold compiler_is_correct_statement.
intros st e.
induction e.
- intros. simpl. apply multi_R. apply SS_Push.
- intros. simpl. apply multi_R. apply SS_Load.
- intros. simpl.
  pose proof (IHe1 st1 ((s_compile e2) ++ [SPlus] ++ p1)) as H1.
  pose proof (IHe2 (aeval st e1 :: st1) ([SPlus] ++ p1)) as H2.
  assert (H3: stack_step st
                         ([SPlus] ++ p1, (aeval st e2 :: aeval st e1 :: st1))
                         (p1 , aeval st e1 + aeval st e2 :: st1))
    by (apply SS_Plus).
  apply multi_R in H3.
  pose proof (multi_trans (prog * stack)
                          (stack_step st)
                          (s_compile e1 ++ s_compile e2 ++ [SPlus] ++ p1, st1)
                          (s_compile e2 ++ [SPlus] ++ p1, aeval st e1 :: st1)
                          ([SPlus] ++ p1, aeval st e2 :: aeval st e1 :: st1)) as H4.
  pose proof ((H4 H1) H2) as H5.
  pose proof (multi_trans (prog * stack)
                          (stack_step st)
                          (s_compile e1 ++ s_compile e2 ++ [SPlus] ++ p1, st1)
                          ([SPlus] ++ p1, aeval st e2 :: aeval st e1 :: st1)
                          (p1, aeval st e1 + aeval st e2 :: st1)) as H6.
  pose proof ((H6 H5) H3) as H7.
  unfold stack_multistep.
  assert (H8: s_compile e1 ++ s_compile e2 ++ [SPlus] ++ p1 = 
              (s_compile e1 ++ s_compile e2 ++ [SPlus]) ++ p1). { repeat (rewrite app_assoc). reflexivity. }
  rewrite <- H8.
  assumption.
- intros. simpl.
  pose proof (IHe1 st1 ((s_compile e2) ++ [SMinus] ++ p1)) as H1.
  pose proof (IHe2 (aeval st e1 :: st1) ([SMinus] ++ p1)) as H2.
  assert (H3: stack_step st
                         ([SMinus] ++ p1, (aeval st e2 :: aeval st e1 :: st1))
                         (p1 , aeval st e1 - aeval st e2 :: st1))
    by (apply SS_Minus).
  apply multi_R in H3.
  pose proof (multi_trans (prog * stack)
                          (stack_step st)
                          (s_compile e1 ++ s_compile e2 ++ [SMinus] ++ p1, st1)
                          (s_compile e2 ++ [SMinus] ++ p1, aeval st e1 :: st1)
                          ([SMinus] ++ p1, aeval st e2 :: aeval st e1 :: st1)) as H4.
  pose proof ((H4 H1) H2) as H5.
  pose proof (multi_trans (prog * stack)
                          (stack_step st)
                          (s_compile e1 ++ s_compile e2 ++ [SMinus] ++ p1, st1)
                          ([SMinus] ++ p1, aeval st e2 :: aeval st e1 :: st1)
                          (p1, aeval st e1 - aeval st e2 :: st1)) as H6.
  pose proof ((H6 H5) H3) as H7.
  unfold stack_multistep.
  assert (H8: s_compile e1 ++ s_compile e2 ++ [SMinus] ++ p1 = 
              (s_compile e1 ++ s_compile e2 ++ [SMinus]) ++ p1). { repeat (rewrite app_assoc). reflexivity. }
  rewrite <- H8.
  assumption.
- intros. simpl.
  pose proof (IHe1 st1 ((s_compile e2) ++ [SMult] ++ p1)) as H1.
  pose proof (IHe2 (aeval st e1 :: st1) ([SMult] ++ p1)) as H2.
  assert (H3: stack_step st
                         ([SMult] ++ p1, (aeval st e2 :: aeval st e1 :: st1))
                         (p1 , aeval st e1 * aeval st e2 :: st1))
    by (apply SS_Mult).
  apply multi_R in H3.
  pose proof (multi_trans (prog * stack)
                          (stack_step st)
                          (s_compile e1 ++ s_compile e2 ++ [SMult] ++ p1, st1)
                          (s_compile e2 ++ [SMult] ++ p1, aeval st e1 :: st1)
                          ([SMult] ++ p1, aeval st e2 :: aeval st e1 :: st1)) as H4.
  pose proof ((H4 H1) H2) as H5.
  pose proof (multi_trans (prog * stack)
                          (stack_step st)
                          (s_compile e1 ++ s_compile e2 ++ [SMult] ++ p1, st1)
                          ([SMult] ++ p1, aeval st e2 :: aeval st e1 :: st1)
                          (p1, aeval st e1 * aeval st e2 :: st1)) as H6.
  pose proof ((H6 H5) H3) as H7.
  unfold stack_multistep.
  assert (H8: s_compile e1 ++ s_compile e2 ++ [SMult] ++ p1 = 
              (s_compile e1 ++ s_compile e2 ++ [SMult]) ++ p1). { repeat (rewrite app_assoc). reflexivity. }
  rewrite <- H8.
  assumption.
Qed.

Example step_example1 :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  apply multi_step with (P (C 3) (C 7)).
    apply ST_Plus2.
      apply v_const.
      apply ST_PlusConstConst.
  apply multi_step with (C 10).
    apply ST_PlusConstConst.
  apply multi_refl.
Qed.

Example step_example1_my_version :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
eapply multi_step.
- apply ST_Plus2.
  -- apply v_const.
  -- apply ST_PlusConstConst.
- simpl.
  apply multi_R.
  apply ST_PlusConstConst.
Qed.

Hint Constructors step value : core.
Example step_example1' :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.
  
Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; simpl)]);
  apply multi_refl.
  
Example step_example1'' :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  normalize.
Qed.
  
Example step_example1''' : exists e',
  (P (C 3) (P (C 3) (C 4)))
  -->* e'.
Proof.
  eexists. normalize.
Qed.

Theorem normalize_ex : exists e',
  (P (C 3) (P (C 2) (C 1)))
  -->* e' /\ value e'.
Proof.
eexists.
split.
- normalize.
- apply v_const.
Qed.

Theorem normalize_ex' : exists e',
  (P (C 3) (P (C 2) (C 1)))
  -->* e' /\ value e'.
Proof.
exists (C 6).
split.
- apply multi_step with (P (C 3) (C 3)).
  -- apply ST_Plus2.
     --- apply v_const.
     --- apply ST_PlusConstConst.
  -- apply multi_R.
     apply ST_PlusConstConst.
- apply v_const.
Qed.

