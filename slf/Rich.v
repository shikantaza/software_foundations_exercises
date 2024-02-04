Set Implicit Arguments.
From SLF Require Import LibSepReference LibSepTLCbuffer.
From SLF Require Basic Repr.

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.
Implicit Type p q : loc.
Implicit Type k : nat.
Implicit Type i n : int.
Implicit Type v : val.
Implicit Types b : bool.
Implicit Types L : list val.

Module Assertions.

Parameter val_assert : prim.

Parameter evaluate_assertions : bool.

Parameter eval_assert_enabled : forall s t s',
  evaluate_assertions = true ->
  eval s t s' (val_bool true) ->
  eval s (val_assert t) s' val_unit.

Parameter eval_assert_disabled : forall s t,
  evaluate_assertions = false ->
  eval s (val_assert t) s val_unit.

Parameter eval_assert_no_effect : forall s t v,
  eval s t s (val_bool true) ->
  eval s (val_assert t) s val_unit.

Lemma hoare_assert : forall t H,
  hoare t H (fun r => \[r = true] \* H) ->
  hoare (val_assert t) H (fun _ => H).  
Proof using.
  intros. unfold hoare in *. intros.
  pose proof (H0 h H1). destruct H2. destruct H2. destruct H2.
  rewrite hstar_hpure_l in H3. destruct H3.
  destruct evaluate_assertions eqn: Heq.
  - exists x val_unit. split.
    apply eval_assert_enabled. auto. subst. auto. auto.
  - exists h val_unit. split.
    apply eval_assert_disabled. auto. auto.
Qed.

Lemma triple_assert : forall t H,
  triple t H (fun r => \[r = true] \* H) ->
  triple (val_assert t) H (fun _ => H).
Proof using.
  intros. unfold triple in *.
  intros. eapply hoare_assert. 
  pose proof (H0 H').
  clear H0. unfold hoare in *.
  intros. pose proof (H1 h H0).
  destruct H2. destruct H2. destruct H2.
  rewrite hstar_assoc in H3.
  exists x x0. split. auto. auto.
Qed.

End Assertions.

Parameter eval_if_trm : forall s1 s2 s3 v0 v t0 t1 t2,
  eval s1 t0 s2 v0 ->
  eval s2 (trm_if v0 t1 t2) s3 v ->
  eval s1 (trm_if t0 t1 t2) s3 v.

Lemma hoare_if_trm : forall Q' t0 t1 t2 H Q,
  hoare t0 H Q' ->
  (forall v, hoare (trm_if v t1 t2) (Q' v) Q) ->
  hoare (trm_if t0 t1 t2) H Q.
Proof using.
  intros. unfold hoare in *. intros.
  pose proof (H0 h H2). clear H0. destruct H3. destruct H0. destruct H0.
  pose proof (H1 x0 x H3). clear H1.
  destruct H4. destruct H1. exists x1 x2.
  destruct H1. split.
  - eapply eval_if_trm.
    -- apply H0.
    -- apply H1.
  - auto.
Qed.  

Lemma triple_if_trm : forall Q' t0 t1 t2 H Q,
  triple t0 H Q' ->
  (forall v, triple (trm_if v t1 t2) (Q' v) Q) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  intros. unfold triple in *.
  intros. eapply hoare_if_trm.
  - apply H0.
  - intros. pose proof (H1 v H'). clear H1.
    eapply hoare_conseq.
    -- apply H2.
    -- apply himpl_refl.
    -- apply qimpl_refl.
Qed.

(* this seems simpler than the book version *)
Lemma wp_if_trm : forall t0 t1 t2 Q,
  wp t0 (fun v => wp (trm_if v t1 t2) Q) ==> wp (trm_if t0 t1 t2) Q.
Proof using.
  intros. rewrite wp_equiv.
  eapply triple_if_trm.
  - rewrite <- wp_equiv. apply himpl_refl.
  - intros. simpl. rewrite <- wp_equiv.
    apply himpl_refl.
Qed.        

Module WhileLoops.

Parameter trm_while : trm -> trm -> trm.

Notation "'while' t1 'do' t2 'done'" :=
  (trm_while t1 t2)
  (in custom trm at level 0,
   t1 custom trm at level 99,
   t2 custom trm at level 99,
   format "'[v' 'while' t1 'do' '/' '[' t2 ']' '/' 'done' ']'")
   : trm_scope.

Parameter eval_while : forall s1 s2 t1 t2 v,
  eval s1 (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) s2 v ->
  eval s1 (trm_while t1 t2) s2 v.

Lemma hoare_while : forall t1 t2 H Q,
  hoare (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) H Q ->
  hoare (trm_while t1 t2) H Q.
Proof using.
  intros. unfold hoare in *.
  intros. pose proof (H0 h H1). clear H0.
  destruct H2. destruct H0. exists x x0.
  destruct H0. split.
  - apply eval_while. auto.
  - auto.
Qed.

Lemma triple_while : forall t1 t2 H Q,
  triple (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) H Q ->
  triple (trm_while t1 t2) H Q.
Proof using.
  intros. unfold triple in *.
  intros. unfold hoare in *.
  intros. pose proof (H0 H' h H1). clear H0.
  destruct H2. destruct H0. destruct H0.
  exists x x0. split.
  - apply eval_while. auto.
  - auto.
Qed.

Lemma wp_while : forall t1 t2 Q,
      wp (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) Q
  ==> wp (trm_while t1 t2) Q.
Proof using.
  intros. rewrite wp_equiv.
  eapply triple_while.
  rewrite <- wp_equiv. apply himpl_refl.
Qed.

(* directly from the book *)
Lemma triple_while_inv_not_framable :
  forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) t1 t2,
  wf R ->
  (forall b X, triple t1 (I b X) (fun r => \exists b', \[r = b'] \* I b' X)) ->
  (forall b X, triple t2 (I b X) (fun _ => \exists b' Y, \[R Y X] \* I b' Y)) ->
  triple (trm_while t1 t2) (\exists b X, I b X) (fun r => \exists Y, I false Y).
Proof using.
  introv WR M1 M2. applys triple_hexists. intros b.
  applys triple_hexists. intros X.
  gen b. induction_wf IH: WR X. intros. applys triple_while.
  applys triple_if_trm (fun (r:val) => \exists b', \[r = b'] \* I b' X).
  { applys M1. }
  { intros v. applys triple_hexists. intros b'. applys triple_hpure. intros ->.
    applys triple_if. case_if.
    { applys triple_seq.
      { applys M2. }
      { applys triple_hexists. intros b''. applys triple_hexists. intros Y.
        applys triple_hpure. intros HR. applys IH HR. } }
    { applys triple_val. xsimpl. } }
Qed. 

Lemma triple_while' : forall t1 t2 H Q,
  (forall t,
     (forall H' Q', triple (trm_if t1 (trm_seq t2 t) val_unit) H' Q' ->
                    triple t H' Q') ->
    triple t H Q) ->
  triple (trm_while t1 t2) H Q.
Proof using.
  intros. pose proof (H0 (trm_while t1 t2)).
  apply H1. intros. apply triple_while. auto.
Qed.

(* directly from the book *)
Lemma triple_while_inv :
  forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) t1 t2,
  let Q := (fun r => \exists Y, I false Y) in
  wf R ->
  (forall t b X,
    (forall b' Y, R Y X -> triple t (I b' Y) Q) ->
    triple (trm_if t1 (trm_seq t2 t) val_unit) (I b X) Q) ->
  triple (trm_while t1 t2) (\exists b X, I b X) Q.
Proof using.
  introv WR M. applys triple_hexists. intros b0.
  applys triple_hexists. intros X0.
  gen b0. induction_wf IH: WR X0. intros. applys triple_while.
  applys M. intros b' Y HR'. applys IH HR'.
Qed.

(* directly from the book *)
Lemma triple_while_inv_conseq_frame :
  forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) H' t1 t2 H Q,
  let Q' := (fun r => \exists Y, I false Y) in
  wf R ->
  (H ==> (\exists b X, I b X) \* H') ->
  (forall t b X,
      (forall b' Y, R Y X -> triple t (I b' Y) Q') ->
      triple (trm_if t1 (trm_seq t2 t) val_unit) (I b X) Q') ->
  Q' \*+ H' ===> Q ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv WR WH M WQ. applys triple_conseq_frame WH WQ.
  applys triple_while_inv WR M.
Qed.

(* directly from the book *)
Lemma wp_while_inv_conseq :
  forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) t1 t2,
  let Q := (fun r => \exists Y, I false Y) in
  wf R ->
     (\exists b X, I b X)
      \* \[forall t b X,
            (forall b' Y, R Y X -> (I b' Y) ==> wp t Q) ->
              (I b X) ==> wp (trm_if t1 (trm_seq t2 t) val_unit) Q]
      ==> wp (trm_while t1 t2) Q.
Proof using.
  introv WR. sets H: (\exists b X, I b X). xpull. intros M.
  rewrite wp_equiv. applys triple_while_inv WR.
  introv N. rewrite <- wp_equiv. applys M.
  introv HR. rewrite wp_equiv. applys N HR.
Qed.

