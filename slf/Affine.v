Set Implicit Arguments.
From SLF Require Rules.
From SLF Require Export LibSepReference.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

Module MotivatingExample.
Export DemoPrograms.

Definition succ_using_incr :=
  <{ fun 'n =>
       let 'p = ref 'n in
       incr 'p;
       ! 'p }>.

Lemma triple_succ_using_incr : forall (n:int),
  triple (succ_using_incr n)
    \[]
    (fun r => \[r = n+1] \* \exists p, (p ~~> (n+1))).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xsimpl. auto.
Qed.

Lemma triple_succ_using_incr' : forall (n:int),
  triple (succ_using_incr n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xsimpl. { auto. } (* stuck here *)
Abort.

End MotivatingExample.

Parameter triple_hany_post : forall t H H' Q,
  triple t H (Q \*+ H') ->
  triple t H Q.

Module MotivatingExampleSolved.
Export MotivatingExample.

Lemma triple_succ_using_incr' : forall (n:int),
  triple (succ_using_incr n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  intros. applys triple_hany_post. applys triple_succ_using_incr.
Qed.

End MotivatingExampleSolved.

Parameter triple_hany_pre : forall t H H' Q,
  triple t H Q ->
  triple t (H \* H') Q.

Module Preview.

Parameter haffine : hprop -> Prop.

Parameter triple_haffine_post : forall t H H' Q,
  haffine H' ->
  triple t H (Q \*+ H') ->
  triple t H Q.

Parameter triple_haffine_pre : forall t H H' Q,
  haffine H' ->
  triple t H Q ->
  triple t (H \* H') Q.
  
End Preview.

Parameter heap_affine : heap -> Prop.

Parameter heap_affine_empty :
  heap_affine Fmap.empty.

Parameter heap_affine_union : forall h1 h2,
  heap_affine h1 ->
  heap_affine h2 ->
  Fmap.disjoint h1 h2 ->
  heap_affine (Fmap.union h1 h2).

Definition haffine (H:hprop) : Prop :=
  forall h, H h -> heap_affine h.

Lemma haffine_hempty :
  haffine \[].
Proof using.
  unfold haffine. intros. inversion H. apply heap_affine_empty.
Qed.

Lemma haffine_hpure : forall P,
  haffine \[P].
Proof using.
  intros. unfold haffine. intros.
  inversion H. inversion H0. apply heap_affine_empty.
Qed.

Lemma haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).
Proof using.
  intros. unfold haffine in *. intros.
  inversion H3. destruct H4. destruct H4. destruct H5. destruct H6.
  rewrite H7. apply heap_affine_union. 
  - apply H. auto.
  - apply H0. auto.
  - auto.
Qed.

Lemma haffine_hexists : forall A (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\exists x, (J x)).
Proof using.
  intros. unfold haffine in *.
  intros. destruct H0. eapply H. apply H0.
Qed.

Lemma haffine_hforall' : forall A (J:A->hprop),
  (exists x, haffine (J x)) ->
  haffine (\forall x, (J x)).
Proof using.
  intros. destruct H.  
  unfold haffine in *. intros. 
  apply H. eapply hforall_inv in H0. apply H0.
Qed.

Lemma haffine_hforall : forall A `{Inhab A} (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\forall x, (J x)).
Proof using.
  intros. unfold haffine in *. intros.
  induction H. destruct Inhab_intro.
  apply H0 with (x := x). eapply hforall_inv in H1. apply H1.
Qed.

Lemma haffine_hstar_hpure_l : forall P H,
  (P -> haffine H) ->
  haffine (\[P] \* H).
Proof using.
  intros. unfold haffine in *. intros.
  rewrite hstar_hpure_l in H1. destruct H1. apply H0.
  - auto.
  - auto.
Qed.

Definition hgc : hprop :=
  \exists H, \[haffine H] \* H.
  
Declare Scope hgc_scope.

Open Scope hgc_scope.

Notation "\GC" := (hgc) : hgc_scope.

Lemma hgc_intro : forall h,
  heap_affine h ->
  \GC h.
Proof using.
  intros. unfold "\GC".
  apply hexists_intro with (x := heap_affine). rewrite hstar_hpure_l.
  split.
  - unfold haffine. intros. auto.
  - auto.
Qed.

Lemma hgc_inv : forall h,
  \GC h ->
  heap_affine h.
Proof using.
  intros. unfold "\GC" in H.
  destruct H. rewrite hstar_hpure_l in H.
  destruct H. unfold haffine in H. auto.
Qed.

Lemma hgc_eq_heap_affine :
  hgc = heap_affine.
Proof using.
  eapply himpl_antisym.
  - unfold "==>". intros. apply hgc_inv. auto.
  - unfold "==>". intros. apply hgc_intro. auto.
Qed.

Arguments Fmap.empty {A} {B}.

Lemma hstar_hgc_hgc' :
  (\GC \* \GC) = \GC.
Proof using.
  rewrite hgc_eq_heap_affine.
  Transparent hstar. unfold hstar.
  apply functional_extensionality.
  intros.
  apply antisym_iff.
  - split.
    -- intros. destruct H. destruct H. destruct H. destruct H0. destruct H1.
       rewrite H2. apply heap_affine_union. auto. auto. auto.
    -- intros. exists x (@Fmap.empty loc val).
       split. auto. split. apply heap_affine_empty. split.
       apply Fmap.disjoint_empty_r. rewrite Fmap.union_empty_r. auto.
  - split.
    -- intros. exists x (@Fmap.empty loc val).
       split. auto. split. apply heap_affine_empty. split.
       apply Fmap.disjoint_empty_r. rewrite Fmap.union_empty_r. auto.
    -- intros. destruct H. destruct H. destruct H. destruct H0. destruct H1.
       rewrite H2. apply heap_affine_union. auto. auto. auto.
Qed.        

(* book version *)
Lemma hstar_hgc_hgc :
  (\GC \* \GC) = \GC.
Proof using.
  unfold hgc. applys himpl_antisym.
  { xpull. intros H1 K1 H2 K2. xsimpl (H1 \* H2). applys* haffine_hstar. }
  { xpull. intros H K. xsimpl H \[]. auto. applys haffine_hempty. }
Qed.

Lemma haffine_hgc :
  haffine \GC.
Proof using.
  (*
  unfold hgc. unfold haffine.
  intros. destruct H. destruct H. destruct H. destruct H. destruct H.
  apply x2. inversion H. subst. destruct H0. destruct H1.
  rewrite Fmap.union_empty_l in H2. rewrite <- H2 in H0. auto.
  *)
  (* book version *)
  applys haffine_hexists. intros H. applys haffine_hstar_hpure_l. auto.
Qed.

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using.
  intros. unfold hgc. xsimpl. auto.
Qed.

Lemma hempty_himpl_hgc :
  \[] ==> \GC.
Proof using.
  apply himpl_hgc_r. apply haffine_hempty.
Qed.

Parameter triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.

Module FullyAffineLogic.

Parameter heap_affine_def : forall h,
  heap_affine h = True.

Lemma heap_affine_empty :
  heap_affine Fmap.empty.
Proof using. rewrite heap_affine_def. exact I. Qed.

Lemma heap_affine_union : forall h1 h2,
  heap_affine h1 ->
  heap_affine h2 ->
  Fmap.disjoint h1 h2 ->
  heap_affine (Fmap.union h1 h2).
Proof using.
  intros. rewrite heap_affine_def. exact I.
Qed.

Lemma haffine_equiv : forall H,
  (haffine H) <-> True.
Proof using.
  intros. split.
  - intros. exact I.
  - intros. unfold haffine. intros. rewrite heap_affine_def. exact I.
Qed.

Definition htop : hprop :=
  \exists H, H.

Lemma hgc_eq_htop : hgc = htop.
Proof using.
  apply himpl_antisym.
  - unfold hgc. xsimpl. intros. unfold htop. xsimpl.
  - unfold hgc. xsimpl. unfold haffine. intros.
    unfold htop in H. rewrite heap_affine_def. exact I.
Qed.

End FullyAffineLogic.

Module FullyLinearLogic.

Parameter heap_affine_def : forall h,
  heap_affine h = (h = Fmap.empty).

Lemma heap_affine_empty :
  heap_affine Fmap.empty.
Proof using.
  rewrite heap_affine_def. auto.
Qed.

Lemma heap_affine_union : forall h1 h2,
  heap_affine h1 ->
  heap_affine h2 ->
  Fmap.disjoint h1 h2 ->
  heap_affine (Fmap.union h1 h2).
Proof using.
  intros. rewrite heap_affine_def in *. subst.
  apply Fmap.union_empty_r.
Qed.

Lemma haffine_equiv : forall H,
  haffine H <-> (H ==> \[]).
Proof using.
  intros. split.
  - intros. unfold haffine in H0.
    unfold himpl.
    intros. pose proof (H0 h H1). rewrite heap_affine_def in H2.
    subst. Transparent hempty. unfold hempty. auto.
  - intros. unfold haffine. intros.
    rewrite heap_affine_def. unfold himpl in H0.
    pose proof (H0 h H1). unfold hempty in H2. auto.
Qed.

Lemma hgc_eq_hempty : hgc = hempty.
Proof using.
  apply himpl_antisym.
  - unfold hgc. unfold himpl. intros.
    apply hexists_inv in H. destruct H.
    rewrite hstar_hpure_l in H. destruct H. unfold haffine in H.
    pose proof (H h H0).
    rewrite heap_affine_def in H1. rewrite H1.
    Transparent hempty. unfold hempty. auto.
  - unfold hgc. unfold himpl. intros.
    apply hexists_intro with (x := hempty).
    rewrite hstar_hpure_l. split.
    -- rewrite haffine_equiv. xsimpl.
    -- auto.
Qed.

End FullyLinearLogic.

Module NewTriples.

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoare t (H \* H') (Q \*+ H' \*+ \GC).

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using.
  intros. unfold triple in *.
  intros. eapply hoare_conseq.
  - apply H0.
  - xsimpl.
  - xsimpl.
Qed.

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  intros. unfold triple in *.
  intros. eapply hoare_conseq.
  - apply H0.
  - xchange H1.
  - xsimpl. xchange H2.
Qed.

Lemma triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  (*
  intros. unfold triple in *. intros.
  unfold hoare. intros.
  inversion H1. destruct H2. destruct H2. destruct H3. destruct H4.
  rewrite hstar_hpure_l in H2. destruct H2.
  pose proof (H0 H2).
  clear H0. unfold hoare in H7.
  apply H7. subst.
  unfold hstar. exists x x0.
  split. auto. split. auto. split. auto. auto.
  *)
  (* book version *)
  introv M. unfolds triple. intros H'.
  rewrite hstar_assoc. applys* hoare_hpure.
Qed.

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (\exists x, J x) Q.
Proof using.
  intros. unfold triple in *. intros.
  rewrite hstar_hexists. apply hoare_hexists. intros. auto.
Qed.

Lemma triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  intros. unfold triple in *. intros.
  eapply hoare_seq.
  - apply H0.
  - rewrite hstar_assoc.
    pose proof (H2 (H' \* \GC)).
    eapply hoare_conseq.
    -- apply H3.
    -- xsimpl.
    -- unfold qimpl. intros. unfold himpl. intros.
       rewrite hstar_assoc in H4. rewrite hstar_assoc in H4.
       rewrite hstar_hgc_hgc in H4. rewrite hstar_assoc. auto.
Qed.

Module Export GCRules.

Lemma triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using.
  intros. unfold triple in *. intros.
  eapply hoare_conseq.
  - apply H0.
  - xsimpl.
  - xchanges hstar_hgc_hgc.
Qed.

Lemma triple_haffine_post : forall t H H' Q,
  haffine H' ->
  triple t H (Q \*+ H') ->
  triple t H Q.
Proof using.
  intros. apply triple_hgc_post.
  unfold triple in *.
  intros. eapply hoare_conseq.
  - apply H1.
  - xsimpl.
  - xsimpl.
    unfold himpl. unfold hgc. intros.
    eapply hexists_intro. rewrite hstar_hpure_l. split. apply H0. auto.
Qed.

Lemma triple_hgc_post_from_triple_haffine_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using.    
  introv. apply triple_haffine_post.
  unfold hgc. unfold haffine. intros. apply hexists_inv in H0.
  destruct H0. destruct H0. destruct H0. destruct H0.
  destruct H0. apply x2. destruct H1. destruct H2. subst.
  inversion H0. subst. rewrite Fmap.union_empty_l. auto.
Qed.

Lemma triple_haffine_pre : forall t H H' Q,
  haffine H' ->
  triple t H Q ->
  triple t (H \* H') Q.
Proof using.
  intros. eapply triple_haffine_post.
  - apply H0.
  - apply triple_frame. auto.
Qed.

Lemma triple_conseq_frame_hgc : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \GC ->
  triple t H Q.
Proof using.
  intros. apply triple_hgc_post.
  eapply triple_conseq.
  - eapply triple_frame. apply H0.
  - apply H3.
  - auto.  
Qed.  

(* this is needed to recognize "\--*" *)
Notation "Q1 \−−∗ Q2" := (qwand Q1 Q2) (at level 43).
 
Lemma triple_ramified_frame_hgc : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \−−∗ (Q \*+ \GC)) ->
  triple t H Q.
Proof using.
  intros. eapply triple_conseq_frame_hgc.
  - apply H0.
  - apply H2.
  - xsimpl.
Qed.

End GCRules.

Definition wp (t:trm) (Q:val->hprop) : hprop :=
  \exists (H:hprop), H \* \[triple t H Q].

Lemma wp_equiv : forall t H1 Q,
  (H1 ==> wp t Q) <-> (triple t H1 Q).
Proof using.
  intros. split.
  - intros. eapply triple_conseq with (H' := wp t Q) (Q' := Q).
    -- unfold wp. apply triple_hexists.
       intros. rewrite hstar_comm. apply triple_hpure. auto.
    -- auto.
    -- auto.
  - intros. unfold wp. Check himpl_hexists_r. 
    apply himpl_hexists_r with (x := H1).
    xsimpl. auto.
Qed.

Lemma wp_hgc_post : forall t Q,
  wp t (Q \*+ \GC) ==> wp t Q.
Proof using.
  intros. rewrite wp_equiv. unfold wp.
  apply triple_hexists. intros.
  rewrite hstar_comm. apply triple_hpure. apply triple_hgc_post.
Qed.

Lemma wp_haffine_pre : forall t H Q,
  haffine H ->
  (wp t Q) \* H ==> wp t Q.
Proof using.
  intros. rewrite wp_equiv.
  unfold wp. rewrite hstar_hexists. apply triple_hexists.
  intros. rewrite hstar_assoc. rewrite hstar_comm.
  rewrite hstar_assoc. apply triple_hpure. intros.
  rewrite hstar_comm. apply triple_haffine_pre. auto. auto.
Qed.

Lemma wp_ramified : forall Q1 Q2 t,
  (wp t Q1) \* (Q1 \−−∗ (Q2 \*+ \GC)) ==> (wp t Q2).
Proof using.
  (* using structural rules associated with triples *)
  (*
  intros.
  unfold wp. xsimpl. intros. 
  rewrite hstar_comm.
  eapply triple_ramified_frame_hgc.
  - apply H.
  - xsimpl.
  *)
  
  (* without using structural rules associated with triples *)
  
  intros. unfold wp. xsimpl. intros.
  unfold triple in *. 
  intros. 
  eapply hoare_conseq.
  - apply H.
  - xsimpl.
  - (* using hgc_eq_hempty *)
    (* xsimpl. rewrite FullyLinearLogic.hgc_eq_hempty. xsimpl. *)    
    (* using hstar_hgc_hgc, as in book version *)
    xchange hstar_hgc_hgc. xsimpl.  
  
  (* book version *)
  (*
  intros. unfold wp. xpull ;=> H M.
  xsimpl (H \* (Q1 \−−∗ Q2 \*+ \GC)).
  unfolds triple. intros H'.
  applys hoare_conseq (M ((Q1 \−−∗ Q2 \*+ \GC) \* H')).
  { xsimpl. } { xchange hstar_hgc_hgc. xsimpl. }
  *)
Qed.

Parameter xwp_lemma : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.
  
Parameter triple_app_fun: forall x v1 v2 t1 H Q,
  v1 = <{ fun x => t1 }> ->
  triple (subst x v2 t1) H Q ->
  triple (v1 v2) H Q.

Lemma xwp_lemma' : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 (Q \*+ \GC) ->
  triple (trm_app v1 v2) H Q.
Proof using.
  intros. apply triple_hgc_post.
  eapply xwp_lemma.
  - apply H0.
  - apply H1.
Qed.
       
Tactic Notation "xwp" :=
  intros; applys xwp_lemma';
  [ reflexivity | simpl; unfold wpgen_var; simpl ].

Module MotivatingExampleWithUpdatedXwp.
Export MotivatingExample.

Parameter haffine_hany : forall (H:hprop),
  haffine H.

Lemma triple_succ_using_incr : forall (n:int),
  triple (succ_using_incr n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  intros. xwp. xapp. intros. xseq. xapp. xapp. xsimpl.
  - math.
  - unfold hgc. xsimpl. apply haffine_hany.
Qed.

End MotivatingExampleWithUpdatedXwp.

    