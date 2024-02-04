Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

Hint Constructors multi : core.

Module TM.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | ite : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.
  
Declare Custom Entry tm.
Declare Scope tm_scope.
Notation "'true'" := true (at level 1): tm_scope.
Notation "'true'" := (tru) (in custom tm at level 0): tm_scope.
Notation "'false'" := false (at level 1): tm_scope.
Notation "'false'" := (fls) (in custom tm at level 0): tm_scope.
Notation "<{ e }>" := e (e custom tm at level 99): tm_scope.
Notation "( x )" := x (in custom tm, x at level 99): tm_scope.
Notation "x" := x (in custom tm at level 0, x constr at level 0): tm_scope.
Notation "'0'" := (zro) (in custom tm at level 0): tm_scope.
Notation "'0'" := 0 (at level 1): tm_scope.
Notation "'succ' x" := (scc x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'pred' x" := (prd x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'iszero' x" := (iszro x) (in custom tm at level 80, x custom tm at level 70): tm_scope.
Notation "'if' c 'then' t 'else' e" := (ite c t e)
                 (in custom tm at level 90, c custom tm at level 80,
                  t custom tm at level 80, e custom tm at level 80): tm_scope.
Local Open Scope tm_scope.

Inductive bvalue : tm -> Prop :=
  | bv_True : bvalue <{ true }>
  | bv_false : bvalue <{ false }>.
  
Inductive nvalue : tm -> Prop :=
  | nv_0 : nvalue <{ 0 }>
  | nv_succ : forall t, nvalue t -> nvalue <{ succ t }>.
  
Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue : core.
Hint Unfold value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | ST_Pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | ST_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> --> v
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | ST_Iszero0 :
      <{ iszero 0 }> --> <{ true }>
  | ST_IszeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> --> <{ false }>
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.
  
Hint Unfold stuck : core.

Example some_term_is_stuck :
  exists t, stuck t.
Proof.
unfold stuck.
exists (scc tru).
split.
- unfold step_normal_form.
  unfold not.
  intros.
  destruct H.
  inversion H.
  inversion H1.
- unfold not.
  intros.
  inversion H.
  -- inversion H0.
  -- inversion H0.
     inversion H2.
Qed.

(* approach 1 *)
Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
intros.
induction H.
- unfold step_normal_form.
  unfold not. intros.
  inversion H.
  -- destruct H0.
     rewrite <- H1 in H0.
     inversion H0.
  -- destruct H0.
     rewrite <- H1 in H0.
     inversion H0.
- unfold step_normal_form.
  unfold not. intros.
  induction H.
  -- destruct H0.
     inversion H.
  -- apply IHnvalue.
     destruct H0.
     inversion H0.
     subst.
     exists t1'.
     assumption.
Qed.

(* approach 2 *)
Lemma value_is_nf' : forall t,
  value t -> step_normal_form t.
Proof.
intros.
induction H.
- unfold step_normal_form.
  unfold not. intros.
  inversion H.
  -- destruct H0.
     rewrite <- H1 in H0.
     inversion H0.
  -- destruct H0.
     rewrite <- H1 in H0.
     inversion H0.
- unfold step_normal_form.
  unfold not. intros.
  induction t.
  -- destruct H0. inversion H0.
  -- destruct H0. inversion H0.
  -- inversion H.
  -- destruct H0. inversion H0.
  -- destruct H0. apply IHt.
     --- inversion H. assumption.
     --- inversion H0. exists t1'. assumption.
  -- destruct H0. apply IHt.
     --- inversion H.
     --- inversion H.
  -- inversion H.
Qed.

Lemma nvalue_impl_value :
  forall v, nvalue v -> value v.
Proof.
intros.
unfold value.
right.
assumption.
Qed.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
unfold deterministic.
intros.
generalize dependent y2.
induction H; intros.
- inversion H0; subst.
  -- reflexivity.
  -- exfalso. inversion H4.
- inversion H0; subst.
  -- reflexivity.
  -- exfalso. inversion H4.
- inversion H0; subst.
  -- exfalso. inversion H.
  -- exfalso. inversion H.
  -- pose proof (IHstep c'0) as H6.
     pose proof (H6 H5) as H7.
     rewrite H7. reflexivity.
- inversion H0. subst. pose proof (IHstep t1'0) as H3.
  pose proof (H3 H2) as H4. rewrite H4. reflexivity.
- inversion H0.
  -- reflexivity.
  -- subst. exfalso. inversion H1.
- assert (H1: value v). { apply nvalue_impl_value. assumption. }
  pose proof (value_is_nf v H1) as H2.
  unfold step_normal_form in H2.
  unfold not in H2.
  inversion H0; subst.
  -- reflexivity.
  -- inversion H4. subst. exfalso. apply H2. exists t1'0. assumption.
- inversion H0; subst.
  -- exfalso. inversion H.
  -- inversion H. subst.
     assert (H4: value y2). { apply nvalue_impl_value. assumption. }
     pose proof (value_is_nf y2 H4) as H5.
     unfold step_normal_form in H5.
     unfold not in H5.
     exfalso.
     apply H5.
     exists t1'0.
     assumption.
  -- pose proof (IHstep t1'0) as H3.
     pose proof (H3 H2) as H4.
     rewrite H4.
     reflexivity.
- inversion H0.
  -- reflexivity.
  -- exfalso. inversion H1.
- inversion H0.
  -- reflexivity.
  -- exfalso.
     inversion H2. 
     assert (H7: value v). { apply nvalue_impl_value. assumption. }
     pose proof (value_is_nf v H7) as H8.
     unfold step_normal_form in H8.
     unfold not in H8.
     exfalso.
     apply H8.
     exists t1'0.
     assumption.
- inversion H0; subst.
  -- exfalso. inversion H.
  -- exfalso.
     inversion H. 
     assert (H5: value v). { apply nvalue_impl_value. assumption. }
     pose proof (value_is_nf v H5) as H6.
     unfold step_normal_form in H6.
     unfold not in H6.
     exfalso.
     apply H6.
     exists t1'0.
     assumption.
  -- pose proof (IHstep t1'0) as H3.
     pose proof (H3 H2) as H4.
     rewrite H4.
     reflexivity.
Qed.

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.
  
Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |- <{ true }> \in Bool
  | T_False :
       |- <{ false }> \in Bool
  | T_If : forall t1 t2 t3 T,
       |- t1 \in Bool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- <{ if t1 then t2 else t3 }> \in T
  | T_0 :
       |- <{ 0 }> \in Nat
  | T_Succ : forall t1,
       |- t1 \in Nat ->
       |- <{ succ t1 }> \in Nat
  | T_Pred : forall t1,
       |- t1 \in Nat ->
       |- <{ pred t1 }> \in Nat
  | T_Iszero : forall t1,
       |- t1 \in Nat ->
       |- <{ iszero t1 }> \in Bool

where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type : core.

Example has_type_1 :
  |- <{ if false then 0 else (succ 0) }> \in Nat.
Proof.
apply T_If.
- apply T_False.
- apply T_0.
- apply T_Succ.
  apply T_0.
Qed.

Example has_type_not :
  ~ ( |- <{ if false then 0 else true}> \in Bool ).
Proof.
unfold not.
intros.
inversion H.
inversion H5.
Qed.

Example succ_hastype_nat__hastype_nat : forall t,
  |- <{succ t}> \in Nat ->
  |- t \in Nat.
Proof.
intros.
inversion H.
assumption.
Qed.

Lemma bool_canonical : forall t,
  |- t \in Bool -> value t -> bvalue t.
Proof.
intros.
inversion H.
- apply bv_True.
- apply bv_false.
- subst. exfalso. inversion H0. inversion H4. inversion H4.
- rewrite <- H2 in H0. inversion H0. inversion H3. inversion H3.
Qed.

Lemma nat_canonical : forall t,
  |- t \in Nat -> value t -> nvalue t.
Proof.
intros.
inversion H0. clear H0.
- inversion H1.
  -- rewrite <- H0 in H. exfalso. inversion H.
  -- rewrite <- H0 in H. exfalso. inversion H.
- assumption.
Qed.

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t --> t'.
Proof.
intros.
induction H.
- left. unfold value. left. apply bv_True.
- left. unfold value. left. apply bv_false.
- destruct IHhas_type1.
  -- pose proof (bool_canonical t1 H H2) as H3.
     inversion H3.
     --- right. exists t2. apply ST_IfTrue.
     --- right. exists t3. apply ST_IfFalse.
  -- destruct H2. right. exists <{ if x then t2 else t3 }>. apply ST_If. assumption.
- left. unfold value. right. apply nv_0.
- destruct IHhas_type.
  -- left. pose proof (nat_canonical t1 H H0) as H1.
     unfold value. right. apply nv_succ. assumption.
  -- right. destruct H0. exists <{ succ x }>. apply ST_Succ. assumption.
- destruct IHhas_type.
  -- pose proof (nat_canonical t1 H H0) as H1.
     inversion H1.
     --- right. exists <{ 0 }>. apply ST_Pred0.
     --- right. exists t. apply ST_PredSucc. assumption.
  --  destruct H0. right. exists <{ pred x }>. apply ST_Pred. assumption.
- destruct IHhas_type.
  -- pose proof (nat_canonical t1 H H0) as H1.
     inversion H1.
     --- right. exists <{ true }>. apply ST_Iszero0.
     --- right. exists <{ false }>. apply ST_IszeroSucc. assumption.
  -- destruct H0. right. exists <{ iszero x }>. apply ST_Iszero. assumption.
Qed.

(* Informal proof of progress (completing what's already given in the book) *)
(*
   - t is a Nat by virtue of T_0, i.e., t is <{ 0 }>:
     <{ 0 }> is a value, so we're done
     
   - t is a Nat by virtue of T_Succ, i.e., given that the proposition holds for t1,
     we need to show that it holds for (succ t1):
     since the prop holds for t1, two cases arise:
     1) t1 is a value 
        - t1 is also an nvalue (by lemma)
        - we need to show that succ t1 is a value, i.e., it is a bvalue or an nvalue. obviously it
          cannot be a bvalue. by nv_succ, the successor of an nvalue is also an nvalue, and
          we are done.
     2) there exists a term t' to which t1 steps.
        - we propose to show that there exists a term to which (succ t1) steps
        - let t1 step to x. then, (succ t1) steps to (succ x), by ST_Succ.
        - thus, (succ x) is a term to which (succ t1) steps, and we are done
        
   - t is a Nat by virtue of T_Pred, i.e., given that the proposition holds for t1,
     we need to show that it holds for (pred t1):
     two cases arise:
     1) t1 is a value 
        - t1 is also an nvalue (by lemma)
        - two cases arise:
          1) t1 is <{ 0 }>
             - we propose to show that there exists a term <{ pred 0 }> steps to - which is <{ 0 }>
               by virtue of ST_Pred0, and we are done.
          2) t1 is of the form (succ t)
             - we propose to show that there exists a term <{ pred (succ t) }> steps to - which is t
               itself, by virtue of ST_PredSucc, and we are done 
     2) there exists a term t' to which t1 steps.
        - we propose to show that there exists a term to which (pred t1) steps
        - let t1 step to x. then, (pred t1) steps to (pred x), by ST_Pred.
        - thus, (pred x) is a term to which (pred t1) steps, and we are done
        
   - t is a Nat by virtue of T_Iszero, i.e., given that the proposition holds for t1,
     we need to show that it holds for (iszero t1):
     two cases arise:
     1) t1 is a value 
        - t1 is also an nvalue (by lemma)
        - two cases arise:
          1) t1 is <{ 0 }>
             - we propose to show that there exists a term <{ iszero 0 }> steps to - which is <{ true }>
               by virtue of ST_Iszero0, and we are done.
          2) t1 is of the form (succ t)
             - we propose to show that there exists a term <{ iszero (succ t) }> steps to - which is t
               <{ false }>, by virtue of ST_IszeroSucc, and we are done
     2) there exists a term t' to which t1 steps.
        - we propose to show that there exists a term to which (iszero t1) steps
        - let t1 step to x. then, (iszero t1) steps to (iszero x), by ST_Iszero
        - thus, (iszero x) is a term to which (pred t1) steps, and we are done
*)

Theorem preservation : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.
Proof.
intros.
generalize dependent t'.
induction H.
- intros. exfalso. inversion H0.
- intros. exfalso. inversion H0.
- intros. inversion H2.
  -- subst. eauto.
  -- subst. eauto.
  -- apply T_If.
     --- apply IHhas_type1. assumption.
     --- assumption.
     --- assumption.
- intros. exfalso. inversion H0.
- intros. inversion H0.
  subst. pose proof (IHhas_type t1') as H3.
  pose proof (H3 H2) as H4.
  apply T_Succ. assumption.
- intros. inversion H0.
  -- apply T_0.
  -- subst. inversion H. assumption.
  -- subst. eauto.
- intros. inversion H0.
  -- apply T_True.
  -- apply T_False.
  -- eauto.
Qed.

Theorem preservation' : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.
Proof with eauto.  
intros.
generalize dependent T.
induction H0; intros; inversion H; subst.
- eauto.
- eauto.
- pose proof (IHstep Bool) as H8.
  pose proof (H8 H4) as H9.
  apply T_If.
  -- assumption.
  -- assumption.
  -- assumption.
- pose proof (IHstep Nat) as H3.
  pose proof (H3 H2) as H4.
  apply T_Succ.
  assumption.
- apply T_0.
- inversion H0. apply T_0.
- inversion H0. apply T_Succ. inversion H3. inversion H6. assumption.
- eauto.
- apply T_True.
- inversion H0. apply T_False.
- inversion H0. apply T_False.
- apply T_Iszero. eauto.
Qed.  

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness_helper : forall t t' T,
  |- t \in T ->
  t -->* t' ->
  |- t' \in T.
Proof.
intros.
generalize dependent T.
induction H0.
- intros. assumption.
- intros.
  pose proof (preservation x y T H1 H) as H2.
  eauto.
Qed.  

Corollary soundness : forall t t' T,
  |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
intros.
unfold stuck.
unfold not.
intros.
destruct H1.
assert (H3: |- t' \in T).
{
  apply soundness_helper with (t := t) (t' := t') (T := T).
  assumption. assumption.
}
unfold step_normal_form in H1.
unfold not in H1.
apply H1.
pose (progress t' T H3) as H4.
destruct H4.
- exfalso. eauto.
- assumption.
Qed.

(* book version *)
Corollary soundness' : forall t t' T,
  |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  - apply progress in HT. destruct HT; auto.
  - apply IHP.
    + apply preservation with (t := x); auto.
    + unfold stuck. split; auto.
Qed.

End TM.
