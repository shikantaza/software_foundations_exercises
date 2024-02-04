Set Implicit Arguments.
From SLF Require Export Rules.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

Parameter wp : trm -> (val->hprop) -> hprop.

Parameter wp_equiv : forall t H Q,
  (H ==> wp t Q) <-> (triple t H Q).

Lemma wp_pre : forall t Q,
  triple t (wp t Q) Q.
Proof using.
  intros. rewrite <- wp_equiv. xsimpl.
Qed.

Lemma wp_weakest : forall t H Q,
  triple t H Q ->
  H ==> wp t Q.
Proof using.
  intros. rewrite wp_equiv. auto.
Qed.

Lemma wp_frame : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).
Proof using.
  intros. rewrite wp_equiv.
  apply triple_frame. apply wp_pre.
Qed.

Lemma wp_frame_trans : forall t H1 Q H,
  H1 ==> wp t Q ->
  (H1 \* H) ==> wp t (Q \*+ H).
Proof using.
  intros. assert ((H1 \* H) ==> (wp t Q) \* H).
  { apply himpl_frame_l. auto. }
  assert ((wp t Q) \* H ==> wp t (Q \*+ H)). { apply wp_frame. }
  apply himpl_trans with (H2 := wp t Q \* H). auto. auto.
Qed.

Lemma wp_conseq : forall t Q1 Q2,
  Q1 ===> Q2 ->
  wp t Q1 ==> wp t Q2.
Proof using.
  intros.
  apply wp_weakest with (H := wp t Q1). 
  assert (triple t (wp t Q1) Q1). { apply wp_pre. }
  eapply triple_conseq.
  - apply H0.
  - apply himpl_refl.
  - auto.
Qed.

Lemma wp_conseq_trans : forall t H1 H2 Q1 Q2,
  H1 ==> wp t Q1 ->
  H2 ==> H1 ->
  Q1 ===> Q2 ->
  H2 ==> wp t Q2.
Proof using.
  (*
  intros. rewrite wp_equiv in *.
  eapply triple_conseq.
  - apply H.
  - auto.
  - auto.
  *)
  (* from book *)
  introv M WH WQ. xchange WH. xchange M. applys wp_conseq WQ.
Qed.

Parameter triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.

Lemma triple_hpure_with_wp : forall t H Q (P:Prop),
  (P -> (H ==> wp t Q)) ->
  (\[P] \* H) ==> wp t Q.
Proof using.
  intros. rewrite wp_equiv in *. apply triple_hpure. auto.
Qed.

Parameter triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.

Lemma wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.
Proof using.
  intros. rewrite wp_equiv. apply triple_val. apply himpl_refl.
Qed.

Lemma triple_val_derived_from_wp_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  intros. rewrite <- wp_equiv. apply wp_weakest. apply triple_val. auto.
Qed.

Parameter triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.

Lemma wp_seq : forall t1 t2 Q,
  wp t1 (fun v => wp t2 Q) ==> wp (trm_seq t1 t2) Q.
Proof using.
  intros. rewrite wp_equiv.
  eapply triple_seq.
  - rewrite <- wp_equiv. apply wp_conseq. xsimpl.
  - apply wp_pre.
Qed.

Lemma triple_seq_from_wp_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  intros. eapply triple_seq.
  - apply H0.
  - apply H2.
Qed.

