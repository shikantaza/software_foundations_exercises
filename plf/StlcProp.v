Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Stlc.
From PLF Require Import Smallstep.

Module STLCProp.
Import STLC.

Lemma canonical_forms_bool : forall t,
  empty |- t \in Bool ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof.
intros.
inversion H0; subst.
- exfalso. inversion H.
- left. reflexivity.
- right. reflexivity.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (T1 -> T2) ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
intros.
inversion H0; subst.
- inversion H; subst.
  exists x0, t1.
  reflexivity.
- exfalso. inversion H.
- exfalso. inversion H.
Qed.

Theorem progress : forall t T,
  empty |- t \in T ->
  value t \/ exists t', t --> t'.
Proof.
intros.
remember empty as Gamma.
induction H. 
- rewrite HeqGamma in H. inversion H.  
- left. apply v_abs.
- destruct IHhas_type1.
  -- apply HeqGamma.
  -- destruct IHhas_type2.
     --- apply HeqGamma.
     --- destruct H1.
         + right. exists <{ [x0:=t2]t1 }>.
           apply ST_AppAbs. assumption.
         + inversion H.
         + inversion H.
     --- destruct H2. 
         right. exists <{t1 x0 }>.
         apply ST_App2. assumption. assumption.
  -- destruct H1. right.
     exists <{x0 t2}>.
     apply ST_App1. assumption.
- left. apply v_true.
- left. apply v_false.
- right.
  destruct IHhas_type1.
  -- apply HeqGamma. 
  -- inversion H2; subst.
     --- inversion H.
     --- exists t2. apply ST_IfTrue.
     --- exists t3. apply ST_IfFalse.
  -- destruct H2. exists <{ if x0 then t2 else t3 }>. apply ST_If. assumption.
Qed.

Theorem progress' : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof.
intros t.
induction t; intros T Ht; auto.
- inversion Ht. inversion H1.
- inversion Ht; subst. clear Ht.
  right.
  pose proof ((IHt1 (Ty_Arrow T2 T)) H2) as H5. clear IHt1.
  pose proof ((IHt2 T2) H4) as H6. clear IHt2.
  destruct H5.
  destruct H6.
  destruct H.
  destruct H0.
  -- exists <{[x0:= (\ x1 : T1, t0)]t1}>. apply ST_AppAbs. apply v_abs.
  -- exists <{[x0:= true]t1}>. apply ST_AppAbs. apply v_true.
  -- exists <{[x0:= false]t1}>. apply ST_AppAbs. apply v_false.
  -- inversion H2.
  -- inversion H2.
  -- destruct H0.
     exists <{t1 x0}>. apply ST_App2. assumption. assumption.
  -- destruct H6. destruct H.
     --- exists <{x0 t2}>. apply ST_App1. assumption.
     --- destruct H. exists <{x0 t2}>. apply ST_App1. assumption.
 - right. inversion Ht; subst.
   pose proof ((IHt1 Ty_Bool) H3) as H7.
   destruct H7.
   -- destruct H.
      --- inversion H3.
      --- exists t2. apply ST_IfTrue.
      --- exists t3. apply ST_IfFalse.
   -- destruct H. exists <{ if x0 then t2 else t3 }>.
      apply ST_If. assumption.
Qed.

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma |- t \in T ->
     Gamma' |- t \in T.
Proof.
intros.
generalize dependent Gamma'.
induction H0; eauto. (* can also simply do eauto using includedin_update *)
intros.
apply T_Abs.
pose proof (IHhas_type (x0 |-> T2; Gamma')) as H1.
apply H1.
apply includedin_update.
assumption.
Qed.

Lemma weakening_empty : forall Gamma t T,
     empty |- t \in T ->
     Gamma |- t \in T.
Proof.
intros.
assert (H1: includedin empty Gamma).
{ 
  unfold includedin.
  intros.
  exfalso. inversion H0.
}
eapply weakening.
- apply H1.
- assumption.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  x |-> U ; Gamma |- t \in T ->
  empty |- v \in U ->
  Gamma |- [x:=v]t \in T.
Proof.
intros.
generalize dependent Gamma.
generalize dependent T.
induction t.
- intros.
  destruct (eqb x0 s) eqn: Heq.
  -- rewrite eqb_eq in Heq.
     rewrite Heq in H.
     inversion H. subst.
     rewrite update_eq in H3. inversion H3.
     unfold subst. rewrite eqb_refl.
     apply weakening_empty. rewrite H2 in H0. assumption.
  -- rewrite eqb_neq in Heq.
     inversion H. subst.
     rewrite update_neq in H3.
     --- unfold subst.
         apply String.eqb_neq in Heq.
         rewrite Heq. apply T_Var. assumption.
     --- assumption.
- intros.
  simpl.
  inversion H. subst.
  pose proof (IHt1 (Ty_Arrow T2 T) Gamma) as H7.
  pose proof (H7 H4) as H8.
  pose proof (IHt2 T2 Gamma) as H9.
  pose proof (H9 H6) as H10.
  apply T_App with (T2 := T2).
  assumption. assumption.
- intros. inversion H. subst.
  destruct (eqb x0 s) eqn: Heq.
  -- rewrite eqb_eq in Heq.
     rewrite Heq. simpl.
     rewrite eqb_refl.
     apply T_Abs.
     pose proof (IHt T1 Gamma) as H7. subst.
     rewrite update_shadow in H6.
     assumption.
  -- rewrite eqb_neq in Heq.
     simpl.
     apply String.eqb_neq in Heq.
     rewrite Heq.
     apply T_Abs.
     pose proof (IHt T1 (s |->t; Gamma)) as H7.
     apply H7.
     assert (H8: (s |-> t; x0 |-> U; Gamma) = (x0 |-> U; s |-> t; Gamma)).
     {
       rewrite update_permute. reflexivity. apply eqb_neq. assumption.
     }
     rewrite <- H8. assumption.
- intros. simpl.
  induction T.
  -- apply T_True.
  -- exfalso. inversion H.
- intros. simpl.
  induction T.
  -- apply T_False.
  -- exfalso. inversion H.
- intros.
  simpl.
  apply T_If.
  inversion H.
  -- pose proof (IHt1 Ty_Bool Gamma) as Hthen. eauto.
  -- inversion H. eauto.
  -- inversion H. eauto.
Qed.

Lemma substitution_preserves_typing_from_typing_ind : forall Gamma x U t v T,
  x |-> U ; Gamma |- t \in T ->
  empty |- v \in U ->
  Gamma |- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
  - destruct (eqb x x0) eqn: Heq.
    -- rewrite eqb_eq in Heq.
       rewrite <- Heq in H.
       rewrite G in H.
       rewrite update_eq in H.
       inversion H.
       rewrite <- H1.
       apply weakening_empty. assumption.
    -- rewrite eqb_neq in Heq.
       rewrite G in H.
       rewrite update_neq in H.
       --- apply T_Var. assumption.
       --- assumption.
  - destruct (eqb x x0) eqn: Heq.
    -- rewrite eqb_eq in Heq.
       apply T_Abs.
       rewrite G in Ht.
       rewrite Heq in Ht.
       rewrite update_shadow in Ht.
       assumption.
    -- rewrite eqb_neq in Heq.
       apply T_Abs.
       pose proof (IHHt (x0 |-> T2; Gamma')) as H1.
       apply H1.
       rewrite G.
       apply update_permute.
       assumption.
Qed.


(* to verify that abstractions with free
   variables are also considered as values *)
Definition x1mm : string := "x1".
Definition x2mm : string := "x2".

Example e1 : value <{ \x1mm: Bool, x2mm }>.
Proof. apply v_abs.
Qed.


Theorem preservation : forall t t' T,
  empty |- t \in T ->
  t --> t' ->
  empty |- t' \in T.
Proof.
intros.
remember empty as Gamma.
generalize dependent t'.
induction H.
- intros. inversion H0.
- intros. inversion H0.
- intros. 
  inversion H1; subst.
  -- apply substitution_preserves_typing with (U := T2).
     --- inversion H. assumption.
     --- assumption.
  -- apply T_App with (T2 := T2).
     + apply IHhas_type1.
       ++ reflexivity. 
       ++ assumption. 
     + assumption.
  -- apply T_App with (T2 := T2).
     + assumption.
     + apply IHhas_type2.
       ++ reflexivity.
       ++ assumption.
- intros. inversion H0.
- intros. inversion H0.
- intros.
  inversion H2; subst.
  -- assumption.
  -- assumption.
  -- apply T_If.
     + apply IHhas_type1.
       ++ reflexivity.
       ++ assumption.
     + assumption.
     + assumption.
Qed.      
   
Theorem not_subject_expansion:
  exists t t' T, t --> t' /\ (empty |- t' \in T) /\ ~ (empty |- t \in T).
Proof.
exists <{ (\x:Bool, x) (\x:Bool, x) }>, 
       <{ \x:Bool, x }>, 
       (Ty_Arrow Ty_Bool Ty_Bool).
split.
- apply ST_AppAbs. apply v_abs.
- split.
  -- apply T_Abs. apply T_Var. apply update_eq.
  -- unfold not.
     intros.
     inversion H. clear H.
     subst.
     inversion H5. subst.
     inversion H6. subst. clear H6.
     rewrite update_eq in H1.
     inversion H1. clear H1.
     rewrite <- H0 in H3.
     inversion H3.
Qed.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness_helper : forall t t' T,
  empty |- t \in T ->
  t -->* t' ->
  empty |- t' \in T.
Proof.
intros.
generalize dependent T.
induction H0.
- intros. assumption.
- intros.
  pose proof (preservation x0 y0 T) as H2.
  eauto.
Qed.  

Corollary type_soundness : forall t t' T,
  empty |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
intros.
unfold not.
intros.
unfold stuck in H1.
destruct H1.
unfold normal_form in H1.
assert (empty |- t' \in T).
{ 
  apply soundness_helper with (t := t) (t' := t') (T := T).
  - assumption.
  - assumption.
}
pose proof (progress t' T) as H4.
pose proof (H4 H3) as H5.
destruct H5.
- apply (H2 H5).
- apply (H1 H5).
Qed.

Theorem unique_types : forall Gamma e T T',
  Gamma |- e \in T ->
  Gamma |- e \in T' ->
  T = T'.
Proof.
intros.
generalize dependent T'.
induction H.
- intros.
  inversion H0. subst. rewrite H3 in H. inversion H. reflexivity.
- intros. inversion H0. subst.
  pose proof (IHhas_type T0) as H7.
  pose proof (H7 H6) as H8.
  inversion H8. reflexivity.
- intros. inversion H1. subst.
  pose proof (IHhas_type1 (Ty_Arrow T3 T')) as H8.
  pose proof (H8 H5) as H9.
  inversion H9. reflexivity.
- intros. inversion H0. reflexivity.
- intros. inversion H0. reflexivity.
- intros. inversion H2. subst.
  pose proof (IHhas_type2 T') as H11.
  eauto.
Qed.

 
