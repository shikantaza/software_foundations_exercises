Set Implicit Arguments.
From SLF Require Import LibSepReference.

From SLF Require Repr.
Close Scope trm_scope.

Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

Module WandDef.

Definition hwand' (H1 H2:hprop) : hprop :=
  fun h => forall h', Fmap.disjoint h h' -> H1 h' -> H2 (h \u h').

Definition hwand (H1 H2:hprop) : hprop :=
  \exists H0, H0 \* \[ H1 \* H0 ==> H2 ].

Notation "H1 \−∗ H2" := (hwand H1 H2) (at level 43, right associativity).

Lemma hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \−∗ H2) <-> (H1 \* H0 ==> H2).
Proof using.
  intros. split.
  - intros. assert (H1 \* H0 ==> H1 \* (H1 \-* H2)).
    {  apply himpl_frame_r. auto. }
    eapply himpl_trans.
    -- apply H3.
    -- xsimpl.
  - intros. unfold hwand.
    xsimpl. auto.
Qed.

Lemma himpl_hwand_r : forall H0 H1 H2,
  (H1 \* H0) ==> H2 ->
  H0 ==> (H1 \−∗ H2).
Proof using.
  intros. unfold hwand. xsimpl. auto.
Qed.

Lemma himpl_hwand_r_inv : forall H0 H1 H2,
  H0 ==> (H1 \−∗ H2) ->
  (H1 \* H0) ==> H2.
Proof using.
  intros. eapply himpl_trans.
  -- eapply himpl_frame_r. apply H.
  -- unfold hwand. xsimpl. intros. auto.
Qed.

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \−∗ H2) ==> H2.
Proof using.
  intros. unfold hwand. xsimpl. intros. auto.
Qed.

Arguments hwand_cancel : clear implicits.

Lemma hwand_inv : forall h1 h2 H1 H2,
  (H1 \−∗ H2) h2 ->
  H1 h1 ->
  Fmap.disjoint h1 h2 ->
  H2 (h1 \u h2).
Proof using.
  intros. inversion H. clear H. inversion H4. clear H4.
  destruct H. destruct H. destruct H4. destruct H5.
  inversion H4. clear H4. inversion H7. clear H7. subst.
  assert (x0 \u Fmap.empty = x0). { apply Fmap.union_empty_r. }
  rewrite H4 in H3. clear H4.
  assert (h1 \u x0 \u Fmap.empty = h1 \u x0). { rewrite Fmap.union_empty_r. auto. }
  rewrite H4. clear H4.
  clear H5.
  unfold "==>" in x2.
  pose proof (x2 (h1 \u x0)). clear x2.
  apply H4. clear H4.
  Transparent hstar.
  unfold "\*".
  exists h1 x0.
  split. auto. split. auto. split. auto. auto. 
Qed.  

Lemma test : forall Q1 Q2 H,
  (Q1 \*+ H ===> Q2) <-> forall v, (Q1 v \* H ==> Q2 v).
Proof using.
  intros. split.
  - intros. unfold "===>" in H0. auto.
  - intros. unfold "===>". auto. 
Qed.

Definition qwand (Q1 Q2:val->hprop) : hprop :=
  \exists H0, H0 \* \[ Q1 \*+ H0 ===> Q2 ].

Notation "Q1 \−−∗ Q2" := (qwand Q1 Q2) (at level 43).

Lemma qwand_equiv' : forall H Q1 Q2,
  H ==> (Q1 \−−∗ Q2) <-> (Q1 \*+ H) ===> Q2.
Proof using.
  intros. split.
  - intros. unfold qwand in H0.
    unfold "==>" in H0.
    unfold "===>".
    intros.
    unfold "==>".
    intros.
    destruct H1.
    destruct H1. destruct H1. destruct H2. destruct H3.
    pose proof (H0 x0).
    pose proof (H5 H2). clear H5. clear H0 H2. rewrite H4. clear H4.
    destruct H6.
    destruct H0. destruct H0. destruct H0. destruct H2. destruct H4.
    unfold "===>" in H2. destruct H2. inversion H2. subst.
    assert (x2 \u Fmap.empty = x2). { apply Fmap.union_empty_r. } rewrite H5 in H3.
    clear H5. clear H2. clear H4.   
    assert (x \u x2 \u Fmap.empty = x \u x2). { rewrite Fmap.union_empty_r. auto. }
    rewrite H2. clear H2.
    pose proof (x4 v). clear x4.
    unfold "==>" in H2.
    pose proof (H2 (x \u x2)). apply H4. clear H2 H4.
    unfold hstar.
    exists x x2. split. auto. split. auto. split. auto. auto.
  - intros. unfold "===>" in H0. unfold "==>" in H0.
    unfold qwand.
    Transparent hexists. unfold hexists.
    unfold "==>". intros.
    unfold "===>".
    exists H. unfold "==>".
    unfold hstar.
    exists h.
    unfold hstar in H0.
    eexists.
    split. auto.
    split. split. apply H0. Transparent hempty. unfold hempty. reflexivity.
    split. apply Fmap.disjoint_empty_r.
    rewrite Fmap.union_empty_r. auto.
Qed.

(* book version *)
Lemma qwand_equiv : forall H Q1 Q2,
  H ==> (Q1 \−−∗ Q2) <-> (Q1 \*+ H) ===> Q2.
Proof using.
  unfold qwand. iff M.
  { intros v. xchange M. intros H4 N. xchange N. }
  { xsimpl H. xchange M. }
Qed.   
    
Lemma qwand_cancel : forall Q1 Q2,
  Q1 \*+ (Q1 \−−∗ Q2) ===> Q2.
Proof using.
  intros. unfold qwand. xsimpl. intros. xchange H.
Qed.

Lemma qwand_specialize : forall (v:val) (Q1 Q2:val->hprop),
  (Q1 \−−∗ Q2) ==> (Q1 v \−∗ Q2 v).
Proof using.
  intros. unfold qwand. xsimpl. intros. unfold "===>" in H. pose proof (H v).
  apply hwand_equiv. xchange H0.
Qed.   

Lemma triple_ramified_frame : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \−−∗ Q) ->
  triple t H Q.
Proof using.
  intros. eapply triple_conseq_frame.
  - apply H0.
  - apply H2.
  - apply qwand_cancel.
Qed.

Lemma triple_conseq_frame_of_ramified_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.
Proof.
  intros. eapply triple_conseq_frame.
  - apply H0.
  - apply H3.
  - apply H4.
Qed.

Parameter wp_conseq_frame : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 ->
  (wp t Q1) \* H ==> (wp t Q2).
  
Lemma wp_ramified : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \−−∗ Q2) ==> (wp t Q2).
Proof using.
  intros. eapply wp_conseq_frame.
  apply qwand_cancel.
Qed.

Lemma wp_conseq_frame_of_wp_ramified : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 ->
  (wp t Q1) \* H ==> (wp t Q2).
Proof using.
  intros. rewrite <- qwand_equiv in H0.
  xchange H0. rewrite hstar_comm. apply wp_ramified.
Qed.

Lemma wp_ramified_trans' : forall t H Q1 Q2,
  H ==> (wp t Q1) \* (Q1 \−−∗ Q2) ->
  H ==> (wp t Q2).
Proof using.
  intros.
  assert (wp t Q1 \* (Q1 \−−∗ Q2) ==> wp t Q2) by apply wp_ramified.
  apply himpl_trans with (H2 := wp t Q1 \* (Q1 \−−∗ Q2)).
  apply H0. apply H1.
Qed.

(* book version *)
Lemma wp_ramified_trans : forall t H Q1 Q2,
  H ==> (wp t Q1) \* (Q1 \−−∗ Q2) ->
  H ==> (wp t Q2).
Proof using. introv M. xchange M. applys wp_ramified. Qed.

End WandDef.

Module XsimplDemo.

(* this import is needed to recognize "\-*" *)
Import WandDef.

(* these lemmas don't evaluate as mentioned in the text,
in spite of importing LibSepSimpl *)

Lemma xsimpl_demo_hwand_cancel : forall H1 H2 H3 H4 H5,
  H1 \* (H2 \−∗ H3) \* H4 \* H2 ==> H5.
Proof using. intros. xsimpl. Abort.

Lemma xsimpl_demo_hwand_cancel_partial : forall H1 H2 H3 H4 H5 H6,
  ((H1 \* H2 \* H3) \−∗ H4) \* H5 \* H2 ==> H6.
Proof using. intros. xsimpl. Abort.

Lemma xsimpl_demo_himpl_hwand_r : forall H1 H2 H3 H4 H5,
  H1 \* H2 ==> H1 \* (H3 \−∗ (H4 \* H5)).
Proof using. intros. xsimpl. Abort.

Lemma xsimpl_demo_hwand_iter : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* ((H1 \* H3) \−∗ (H4 \−∗ H5)) \* H4 ==> ((H2 \−∗ H3) \−∗ H5).
Proof using. intros. xsimpl. (* Qed. *) Abort.

Lemma xsimpl_demo_qwand_cancel : forall v (Q1 Q2:val->hprop) H1 H2,
  (Q1 \−−∗ Q2) \* H1 \* (Q1 v) ==> H2.
Proof using. intros. xsimpl. Abort.

Lemma xsimpl_hwand_frame : forall H1 H2 H3,
  (H1 \−∗ H2) ==> ((H1 \* H3) \−∗ (H2 \* H3)).
Proof using.
  intros. xsimpl.
  (* xsimpl first step is to turn the goal into:
     (H1 \−∗ H2) \* (H1 \* H3) ==> (H2 \* H3). *)
(* Qed. *)
Abort.

End XsimplDemo.

Module WPgenRec.

(* this import is needed to recognize "\-*" *)
Import WandDef.

Implicit Types vx vf : val.

Parameter triple_app_fun_from_wpgen : forall vf vx x t1 H' Q',
  vf = val_fun x t1 ->
  H' ==> wpgen ((x,vx)::nil) t1 Q' ->
  triple (trm_app vf vx) H' Q'.

Definition wpgen_fun (Fof:val->formula) : formula := fun Q =>
  \forall vf, \[forall vx Q', Fof vx Q' ==> wp (trm_app vf vx) Q'] \−∗ Q vf.

Lemma wpgen_fun_sound : forall x t1 Fof,
  (forall vx, formula_sound (subst x vx t1) (Fof vx)) ->
  formula_sound (trm_fun x t1) (wpgen_fun Fof).
Proof using.
  introv M. intros Q. unfolds wpgen_fun. applys himpl_hforall_l (val_fun x t1).
  xchange hwand_hpure_l.
  { intros. applys himpl_trans_r. { applys* wp_app_fun. } { applys* M. } }
  { applys wp_fun. }
Qed.

Lemma wpgen_fun_proof_obligation : forall E x t1,
  (forall E, formula_sound (isubst E t1) (wpgen E t1)) ->
  formula_sound (trm_fun x (isubst (rem x E) t1))
                (wpgen_fun (fun v => wpgen ((x,v)::E) t1)).
Proof using.
  introv IH. applys wpgen_fun_sound.
  { intros vx. rewrite <- isubst_rem. applys IH. }
Qed.

Notation "'Fun' x ':=' F1" :=
  ((wpgen_fun (fun x => F1)))
  (at level 69, x name, right associativity,
  format "'[v' '[' 'Fun' x ':=' F1 ']' ']'").

Parameter triple_app_fix_from_wpgen : forall vf vx f x t1 H' Q',
  vf = val_fix f x t1 ->
  H' ==> wpgen ((f,vf)::(x,vx)::nil) t1 Q' ->
  triple (trm_app vf vx) H' Q'.

Definition wpgen_fix (Fof:val->val->formula) : formula := fun Q =>
  \forall vf, \[forall vx Q', Fof vf vx Q' ==> wp (trm_app vf vx) Q'] \−∗ Q vf.

Lemma wpgen_fix_sound : forall f x t1 Fof,
  (forall vf vx, formula_sound (subst x vx (subst f vf t1)) (Fof vf vx)) ->
  formula_sound (trm_fix f x t1) (wpgen_fix Fof).
Proof using.
  introv M. intros Q. unfolds wpgen_fix.
  applys himpl_hforall_l (val_fix f x t1). xchange hwand_hpure_l.
  { intros. applys himpl_trans_r. { applys* wp_app_fix. } { applys* M. } }
  { applys wp_fix. }
Qed.

Lemma wpgen_fix_proof_obligation : forall E f x t1,
  (forall E, formula_sound (isubst E t1) (wpgen E t1)) ->
  formula_sound (trm_fix f x (isubst (rem x (rem f E)) t1))
                    (wpgen_fix (fun vf vx => wpgen ((f,vf)::(x,vx)::E) t1)).
Proof using.
  introv IH. applys wpgen_fix_sound.
  { intros vf vx. rewrite <- isubst_rem_2. applys IH. }
Qed.

Notation "'Fix' f x ':=' F1" :=
  ((wpgen_fix (fun f x => F1)))
  (at level 69, f name, x name, right associativity,
  format "'[v' '[' 'Fix' f x ':=' F1 ']' ']'").

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  mkstruct match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_var E x
  | trm_fun x t1 => wpgen_fun (fun v => wpgen ((x,v)::E) t1)
  | trm_fix f x t1 => wpgen_fix (fun vf v => wpgen ((f,vf)::(x,v)::E) t1)
  | trm_if t0 t1 t2 => wpgen_if t0 (wpgen E t1) (wpgen E t2)
  | trm_seq t1 t2 => wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | trm_app t1 t2 => wp (isubst E t)
  end.

Lemma xfun_spec_lemma : forall (S:val->Prop) H Q Fof,
  (forall vf,
    (forall vx H' Q', (H' ==> Fof vx Q') -> triple (trm_app vf vx) H' Q') ->
    S vf) ->
  (forall vf, S vf -> (H ==> Q vf)) ->
  H ==> wpgen_fun Fof Q.
Proof using.
  Admitted. (* error when doing 'applys M2' *)
(*
  introv M1 M2. unfold wpgen_fun. xsimpl. intros vf N.
  applys M2. applys M1. introv K. rewrite <- wp_equiv. xchange K. applys N.
Qed.
*)

Tactic Notation "xfun" constr(S) :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xfun_spec_lemma S.

Lemma xfun_nospec_lemma : forall H Q Fof,
  (forall vf,
     (forall vx H' Q', (H' ==> Fof vx Q') -> triple (trm_app vf vx) H' Q') ->
     (H ==> Q vf)) ->
  H ==> wpgen_fun Fof Q.
Proof using.
  Admitted. (* error when doing 'applys M' *)
(*  
  introv M. unfold wpgen_fun. xsimpl. intros vf N. applys M.
  introv K. rewrite <- wp_equiv. xchange K. applys N.
Qed.
*)

Tactic Notation "xfun" :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xfun_nospec_lemma.


Import DemoPrograms.

Definition myfun : val :=
  <{ fun 'p =>
       let 'f = (fun_ 'u => incr 'p) in
       'f ();
       'f () }>.

Lemma triple_myfun : forall (p:loc) (n:int),
  triple (trm_app myfun p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp.
  xfun (fun (f:val) => forall (m:int),
    triple (f())
      (p ~~> m)
      (fun _ => p ~~> (m+1))); intros f Hf.
  { intros. applys Hf. clear Hf. xapp. (* exploits triple_incr *) xsimpl. }
  xapp. (* exploits Hf. *)
  xapp. (* exploits Hf. *)
  replace (n+1+1) with (n+2); [|math]. xsimpl.
Qed.

Lemma triple_myfun' : forall (p:loc) (n:int),
  triple (trm_app myfun p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp.
  xfun; intros f Hf.
  xapp. (* exploits Hf *)
  xapp. (* exploits triple_incr *)
  xapp. (* exploits Hf *)
  xapp. (* exploits triple_incr *)
  replace (n+1+1) with (n+2); [|math]. xsimpl.
Qed.

End WPgenRec.

