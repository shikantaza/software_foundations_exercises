Set Warnings "-deprecated-hint-without-locality,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From PLF Require Import Hoare.

Hint Constructors ceval : core.

Definition valid (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st ->
     Q st'.

Inductive derivable : Assertion -> com -> Assertion -> Type :=
  | H_Skip : forall P,
      derivable P <{skip}> P
  | H_Asgn : forall Q V a,
      derivable (Q [V |-> a]) <{V := a}> Q
  | H_Seq : forall P c Q d R,
      derivable P c Q -> derivable Q d R -> derivable P <{c;d}> R
  | H_If : forall P Q b c1 c2,
    derivable (fun st => P st /\ bassn b st) c1 Q ->
    derivable (fun st => P st /\ ~(bassn b st)) c2 Q ->
    derivable P <{if b then c1 else c2 end}> Q
  | H_While : forall P b c,
    derivable (fun st => P st /\ bassn b st) c P ->
    derivable P <{while b do c end}> (fun st => P st /\ ~ (bassn b st))
  | H_Consequence : forall (P Q P' Q' : Assertion) c,
    derivable P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    derivable P c Q.
    
Lemma H_Consequence_pre : forall (P Q P': Assertion) c,
    derivable P' c Q ->
    (forall st, P st -> P' st) ->
    derivable P c Q.
Proof.
intros.
apply H_Consequence with (P := P) (Q := Q) (P' := P') (Q' := Q) (c := c).
- assumption.
- assumption.
- intros. assumption.
Qed.

Lemma H_Consequence_post : forall (P Q Q' : Assertion) c,
    derivable P c Q' ->
    (forall st, Q' st -> Q st) ->
    derivable P c Q.
intros.
apply H_Consequence with (P := P) (Q := Q) (P' := P) (Q' := Q') (c := c).
- assumption.
- intros. assumption.
- assumption.
Qed.

Example sample_proof :
  derivable
    ((fun st:state => st X = 3) [X |-> X + 2] [X |-> X + 1])
    <{ X := X + 1; X := X + 2}>
    (fun st:state => st X = 3).
Proof.
eapply H_Seq.
- apply H_Asgn.
- apply H_Asgn.
Qed.

Theorem provable_true_post : forall c P,
    derivable P c True.
Proof.
(* intros. *)
induction c.
- intros.
  apply H_Consequence_post with (P := P) 
                                (Q := assert_of_Prop True) 
                                (Q' := P) 
                                (c := <{skip}>).
  -- apply H_Skip.
  -- intros.
     simpl.
     apply I.
- intros.
  apply H_Consequence_pre with (P := P)
                               (P' := (assert_of_Prop True)[x |->a])
                               (Q := assert_of_Prop True)
                               (c := <{x := a}>).
  -- apply H_Asgn.
  -- intros. reflexivity.
- intros.
  eapply H_Seq.
  -- apply (IHc1 P).
  -- apply (IHc2 (assert_of_Prop True)).
- intros.
  eapply H_If.
  -- apply IHc1.
  -- apply IHc2.
- intros.
  (* explict/verbose version *)
  (*
  assert (H1: P ->> True).
  {
    unfold "->>". intros. simpl. apply I.
  }
  pose proof (IHc (fun st : state => True /\ (bassn b) st)) as H2.
  assert (H3: (fun st : state => True /\ ~(bassn b) st) ->> True).
  {
    unfold "->>". intros. simpl. apply I.
  }
  pose proof (H_While (fun st : state => True) b c) as H4.
  pose proof (H4 H2) as H5.
  apply H_Consequence with (P := P)
                           (P' := assert_of_Prop True)
                           (Q' := (fun st : state => True /\ ~ (bassn b) st))
                           (Q := assert_of_Prop True)
                           (c := <{while b do c end }>).
  -- assumption.
  -- assumption.
  -- assumption.
  *)
  eapply H_Consequence.
  -- eapply H_While.
     apply (IHc (fun st: state => True /\ (bassn b) st)).
  -- intros. simpl. apply I.
  -- intros. simpl. apply I. 
Qed.

Theorem provable_false_pre : forall c Q,
    derivable False c Q.
Proof.
induction c.
- intros.
  eapply H_Consequence_post.
  -- apply H_Skip.
  -- intros. simpl in H. exfalso. assumption.
- intros.
  eapply H_Consequence_pre.
  -- apply H_Asgn.
  -- intros. simpl in H. exfalso. assumption.
- intros.
  eapply H_Seq.
  -- apply IHc1.
  -- apply IHc2.
- intros.
  eapply H_If.
  -- eapply H_Consequence_pre.
     + apply IHc1.
     + intros. destruct H. simpl in H. exfalso. assumption.
  -- eapply H_Consequence_pre.
     + apply IHc2.
     + intros. destruct H. simpl in H. exfalso. assumption.
- intros.
  eapply H_Consequence.
  -- eapply H_Consequence_pre.
     + eapply H_While.
       ++ eapply H_Consequence_pre.
          +++ apply IHc.
          +++ intros. simpl. destruct H. apply H.
     + intros. simpl. apply H.
  -- intros. simpl. simpl in H. assumption.
  -- intros. simpl in H. exfalso. destruct H. assumption.
Qed.

Theorem hoare_sound : forall P c Q,
  derivable P c Q -> valid P c Q.
Proof.
intros.
induction X.
- unfold valid. intros. inversion H. subst. assumption.
- unfold valid. intros. inversion H. subst. assumption.
- unfold valid. intros. inversion H. subst. eauto.
- unfold valid. intros. inversion H.
  -- subst. eauto.
  -- subst. eauto.
- unfold valid in *.  
  intros. remember <{while b do c end }> as cw eqn: Hcw.
  induction H.
  -- discriminate.
  -- discriminate.
  -- discriminate.
  -- discriminate.
  -- discriminate.
  -- inversion Hcw. clear Hcw.
     split.
     --- subst. assumption.
     --- subst. simpl. unfold not. intros. rewrite H in H1. inversion H1.
  -- inversion Hcw. clear Hcw.
     split.
     --- subst.  
         pose proof ((IHX st st') H1) as H3.
         simpl in H3.
         assert (H4: P st') by auto.
         assert (H5: <{ while b do c end }> = <{ while b do c end }>) by reflexivity.
         pose proof ((IHceval2 H5) H4) as H6.
         destruct H6.
         assumption.
     --- subst.  
         pose proof ((IHX st st') H1) as H3.
         simpl in H3.
         assert (H4: P st') by auto.
         assert (H5: <{ while b do c end }> = <{ while b do c end }>) by reflexivity.
         pose proof ((IHceval2 H5) H4) as H6.
         destruct H6.
         assumption.
- unfold valid in *.
  intros. eauto.
Qed.

Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', s =[ c ]=> s' -> Q s'.
  
Hint Unfold wp : core.

Theorem wp_is_precondition : forall c Q,
  {{wp c Q}} c {{Q}}.
Proof.
(* verbose proof *)
(*
intros.
unfold hoare_triple.
intros.
unfold wp in H0.
apply H0.
assumption.
*)
auto.
Qed.

Theorem wp_is_weakest : forall c Q P',
    {{P'}} c {{Q}} ->
    P' ->> (wp c Q).
Proof. 
(* verbose proof *)
(*
intros.
unfold "->>".
intros.
unfold hoare_triple in H.
unfold wp.
intros.
apply (H st s').
- assumption.
- assumption.
*)
eauto. 
Qed.

Lemma wp_seq : forall P Q c1 c2,
    derivable P c1 (wp c2 Q) -> derivable (wp c2 Q) c2 Q -> derivable P <{c1; c2}> Q.
Proof.
intros.
eapply H_Seq.
- apply X.
- apply X0.
Qed.

Lemma wp_invariant : forall b c Q,
  valid (wp <{while b do c end}> Q /\ b) c (wp <{while b do c end}> Q).
(* valid ((fun st : state => wp <{while b do c end}> Q st /\ bassn b st)) c (wp <{while b do c end}> Q).
*)
Proof.
intros.
unfold valid.
intros.
unfold wp in *.
intros.
destruct H0.
apply H0.
eauto.
Qed.

From Coq Require Import Bool.Bool.

Theorem hoare_complete: forall P c Q,
  valid P c Q -> derivable P c Q.
Proof.
  unfold valid. intros P c. generalize dependent P.
  induction c; intros P Q HT.
  - eapply H_Consequence_post.
    -- apply H_Skip.
    -- intros. eauto.
  - eapply H_Consequence_post.
    -- eapply H_Consequence_pre.
       --- apply H_Asgn.
       --- intros.
           pose proof (HT st (x !-> aeval st a; st)) as H1.
           assert (H2: st =[ x := a ]=> (x !-> aeval st a; st)). 
           { 
             apply E_Asgn. reflexivity.
           }
           pose proof (H1 H2) as H3.
           apply (H3 H).
    -- intros. assumption.
  - apply wp_seq.
    -- apply IHc1. eauto.
    -- apply IHc2. eauto.
  - eapply H_If.
    -- eapply H_Consequence_post.
       --- apply IHc1. intros. apply (HT st st').
           + apply E_IfTrue.
             ++ destruct H0. simpl in H1. assumption.
             ++ assumption.
           + destruct H0. assumption.
       --- intros. assumption.
    -- apply IHc2. intros. apply (HT st st').
       + apply E_IfFalse.
         ++ destruct H0. simpl in H1. 
            apply eq_true_not_negb in H1.
            apply negb_true_iff in H1. assumption.
         ++ assumption.
       + destruct H0. assumption.
  - eapply H_Consequence.
    -- apply H_While with (P := (wp <{while b do c end }> Q)).
       apply IHc.
       apply wp_invariant.
    -- intros. unfold wp. intros. eauto.
    -- intros. simpl in H.
       destruct H.
       unfold wp in H.
       apply (H st).
       apply E_WhileFalse.
       apply eq_true_not_negb in H0.
       apply negb_true_iff in H0. assumption.
Qed.
