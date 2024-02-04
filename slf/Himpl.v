Set Implicit Arguments.
From SLF Require LibSepReference.
From SLF Require Export Hprop.

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

Definition himpl (H1 H2:hprop) : Prop :=
  forall (h:heap), H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55).

Lemma himpl_refl : forall H,
  H ==> H.
Proof using.
  intros. unfold "==>". intros. auto.
Qed.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using.
  intros.
  unfold "==>" in *.
  intros.
  apply H0. apply H. auto.
Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  H1 = H2.
Proof using.
  intros.
  apply predicate_extensionality. intros.
  unfold "==>" in *.
  pose proof (H x). pose proof (H0 x).
  split. auto. auto.
Qed.

Lemma comm_conj_helper : forall H1 H2,
  (H1 \* H2) ==> (H2 \* H1).
Proof using.
  intros.
  unfold "==>".
  intros.
  unfold "\*" in *.
  destruct H. destruct H. destruct H. destruct H0. destruct H3.
  exists x0 x. split.
  - auto.
  - split.
    -- auto.
    -- split.
       + unfold Fmap.disjoint in *. apply map_disjoint_sym in H3.
         auto.
       + apply union_comm_of_disjoint in H3.
         rewrite H4. auto.
Qed.

Lemma comm_conj : forall H1 H2,
  (H1 \* H2) = (H2 \* H1).
Proof.
  intros. apply himpl_antisym.
  - apply comm_conj_helper.
  - apply comm_conj_helper.
Qed.

Definition qimpl (Q1 Q2:val->hprop) : Prop :=
  forall (v:val), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55).

Lemma qimpl_refl : forall Q,
  Q ===> Q.
Proof using.
  intros. unfold "===>". intros. unfold "==>". intros. auto.
Qed.

Lemma qimpl_trans : forall Q2 Q1 Q3,
  (Q1 ===> Q2) ->
  (Q2 ===> Q3) ->
  (Q1 ===> Q3).
Proof using.
  intros.
  unfold "===>" in *.
  intros. pose proof (H v). pose proof (H0 v). clear H H0.
  eapply himpl_trans. apply H1. apply H2.
Qed.

Lemma qimpl_antisym : forall Q1 Q2,
  (Q1 ===> Q2) ->
  (Q2 ===> Q1) ->
  (Q1 = Q2).
Proof using.
  intros. unfold "===>" in *.
  apply qprop_eq. intros. pose proof (H v). pose proof (H0 v). clear H H0.
  apply himpl_antisym. auto. auto.
Qed.

Parameter hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).

Parameter hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.

Parameter hstar_hempty_l : forall H,
  \[] \* H = H.

Parameter hstar_hexists : forall A (J:A->hprop) H,
  (\exists x, J x) \* H = \exists x, (J x \* H).

Parameter himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).

Lemma hstar_comm_assoc : forall H1 H2 H3,
  H1 \* H2 \* H3 = H2 \* H1 \* H3.
Proof using.
  intros. assert (H1 \* (H2 \* H3) = (H1 \* H2) \* H3).
  {
     rewrite hstar_assoc. auto.
  }
  rewrite H.    
  assert (H2 \* (H1 \* H3) = (H2 \* H1) \* H3). { rewrite hstar_assoc. auto. }
  rewrite H0.
  assert (H1 \* H2 = H2 \* H1). { rewrite hstar_comm. auto. }
  rewrite H4. auto.
Qed.

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof using.
  intros.
  assert (H2 \* H1 ==> H2' \* H1). { apply himpl_frame_l. auto. }
  assert (H2' \* H1 = H1 \* H2'). { apply hstar_comm. }
  assert (H2 \* H1 = H1 \* H2). { apply hstar_comm. }
  rewrite H3 in H0.
  rewrite H4 in H0.
  auto.
Qed.

Lemma himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1' \* H2').
Proof using.
  intros.  
  assert (H1 \* H2 ==> H1' \* H2). { apply himpl_frame_l. auto. }
  assert (H1' \* H2 ==> H1' \* H2'). { apply himpl_frame_r. auto. }
  eapply himpl_trans. apply H3. apply H4.
Qed.

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof using.
  intros. unfold "==>" in *. intros.
  rewrite hstar_hpure_l.
  split. auto. apply H1. auto.
Qed.

Lemma himpl_hstar_hpure_l : forall (P:Prop) (H H':hprop),
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
Proof using.
  intros. unfold "==>" in *. intros. rewrite hstar_hpure_l in H1. destruct H1.
  apply H0. auto. auto.
Qed.

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (\exists x, J x).
Proof using.
  intros. unfold "==>" in *. intros. pose proof (H0 h). exists x. auto.
Qed.

Lemma himpl_hexists_l : forall (A:Type) (H:hprop) (J:A->hprop),
  (forall x, J x ==> H) ->
  (\exists x, J x) ==> H.
Proof using.
  intros. unfold "==>" in *.
  intros. destruct H1. pose proof (H0 x h). auto.
Qed.

Lemma hstar_hsingle_same_loc : forall (p:loc) (v1 v2:val),
  (p ~~> v1) \* (p ~~> v2) ==> \[False].
Proof using.
  intros. unfold hsingle. intros h (h1 & h2 & E1 & E2 & D & E). false.
  subst. applys Fmap.disjoint_single_single_same_inv D.
Qed.

Parameter triple_conseq : forall t H Q H' Q',
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.

Parameter triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').

Lemma triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.
Proof using.
  intros.
  assert (triple t (H1 \* H2) (Q1 \*+ H2)). { apply triple_frame. auto. }
  eapply triple_conseq.
  - apply H5.
  - auto.
  - auto.
Qed.

Parameter triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.

Parameter triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (\exists x, J x) Q.

