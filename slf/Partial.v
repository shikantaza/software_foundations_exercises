Set Implicit Arguments.
From SLF Require Export Nondet.
Close Scope val_scope.
Close Scope trm_scope.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types s : state.
Implicit Types t : trm.
Implicit Types v : val.
Implicit Types n : int.
Implicit Types p : loc.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

CoInductive evalnp : state -> trm -> (val->state->Prop) -> Prop :=
  | evalnp_val : forall s v Q,
      Q v s ->
      evalnp s (trm_val v) Q
  | evalnp_fix : forall s f x t1 Q,
      Q (val_fix f x t1) s ->
      evalnp s (trm_fix f x t1) Q
  | evalnp_app_fix : forall s1 v1 v2 f x t1 Q,
      v1 = val_fix f x t1 ->
      evalnp s1 (subst x v2 (subst f v1 t1)) Q ->
      evalnp s1 (trm_app v1 v2) Q
  | evalnp_let : forall Q1 s1 x t1 t2 Q,
      evalnp s1 t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> evalnp s2 (subst x v1 t2) Q) ->
      evalnp s1 (trm_let x t1 t2) Q
  | evalnp_if : forall s1 b t1 t2 Q,
      evalnp s1 (if b then t1 else t2) Q ->
      evalnp s1 (trm_if (val_bool b) t1 t2) Q
  | evalnp_add : forall s n1 n2 Q,
      Q (val_int (n1 + n2)) s ->
      evalnp s (val_add (val_int n1) (val_int n2)) Q
  | evalnp_rand : forall s n Q,
      n > 0 ->
      (forall n1, 0 <= n1 < n -> Q n1 s) ->
      evalnp s (val_rand (val_int n)) Q
  | evalnp_ref : forall s v Q,
      (forall p, ~ Fmap.indom s p ->
         Q (val_loc p) (Fmap.update s p v)) ->
      evalnp s (val_ref v) Q
  | evalnp_get : forall s p Q,
      Fmap.indom s p ->
      Q (Fmap.read s p) s ->
      evalnp s (val_get (val_loc p)) Q
  | evalnp_set : forall s p v Q,
      Fmap.indom s p ->
      Q val_unit (Fmap.update s p v) ->
      evalnp s (val_set (val_loc p) v) Q
  | evalnp_free : forall s p Q,
      Fmap.indom s p ->
      Q val_unit (Fmap.remove s p) ->
      evalnp s (val_free (val_loc p)) Q.

Definition hoarenp (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> evalnp s t Q.

Lemma evalnp_conseq : forall s t Q1 Q2,
  evalnp s t Q1 ->
  Q1 ===> Q2 ->
  evalnp s t Q2.
Proof using.
  (* an 'auto' after 'cofix IH' seems to be sufficient *)
  (*
  intros. unfolds qimpl, himpl.
  gen s t Q1 Q2. cofix IH. auto.
  *)
  (* book version *)
  introv M W. unfolds qimpl, himpl.
  gen s t Q1 Q2. cofix IH. intros. inverts M; try solve [ constructors* ].
Qed.

Lemma evalnp_inv_eval : forall s t v s' Q,
  evalnp s t Q ->
  eval s t s' v ->
  Q v s'.
Proof using.
  (* proof copy-pasted from NonDet.v *)
  intros. gen Q. induction H0; subst.
  - intros. inversion H. subst. auto.
  - intros. inversion H. subst. auto.
  - intros. apply IHeval. inversion H. inversion H4. subst. auto.
  - intros. apply IHeval2. inversion H. subst.
    apply H6. pose proof (IHeval1 Q1). apply H0. auto.
  - intros. apply IHeval. inversion H. subst. apply H6.
  - intros. inversion H. auto.
  - intros. inversion H0. 
    -- inversion H4. 
    -- auto.
  - intros. inversion H0.
    -- inversion H4.
    -- auto.
  - intros. inversion H0.
    -- inversion H4.
    -- auto.
  - intros. inversion H0. auto.
  - intros. inversion H0.
    -- inversion H4.
    -- auto.
Qed.

(* book version; straightforward to derive explicitly by 
   ourselves, but quite cumbersome *)
Lemma evalnp_of_evaln : forall s t Q,
  evaln s t Q ->
  evalnp s t Q.
Proof using. introv M. induction M; try solve [ constructors* ]. Qed.

Lemma hoaren_of_cohoare : forall t H Q,
  hoaren t H Q ->
  hoarenp t H Q.
Proof using.
  intros.
  unfold hoaren in H0. unfold hoarenp.
  intros. apply evalnp_of_evaln. auto.
Qed.

Definition Empty : val->state->Prop :=
  fun v s => False.

Definition divn (s:state) (t:trm) : Prop :=
  evalnp s t Empty.

Lemma hoarenp_conseq : forall t H' Q' H Q,
  hoarenp t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoarenp t H Q.
Proof using.
  intros. unfold hoarenp in *.
  intros. eapply evalnp_conseq. auto. auto.
Qed.

Lemma hoarenp_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, hoarenp t (J x) Q) ->
  hoarenp t (hexists J) Q.
Proof using.
  intros. unfold hoarenp in *. intros.
  inversion H0. eapply H. apply H1.
Qed.

Lemma hoarenp_hpure : forall t (P:Prop) H Q,
  (P -> hoarenp t H Q) ->
  hoarenp t (\[P] \* H) Q.
Proof using.
  intros. unfold hoarenp in *. intros.
  rewrite hstar_hpure_l in H1. destruct H1. apply H0. auto. auto.
Qed.

Lemma hoarenp_val : forall v H Q,
  H ==> Q v ->
  hoarenp (trm_val v) H Q.
Proof using.
  intros. unfold hoarenp in *. intros. apply evalnp_val. applys H0. auto.
Qed.

Lemma hoarenp_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  hoarenp (trm_fix f x t1) H Q.
Proof using.
  intros. unfold hoarenp in *. intros. apply evalnp_fix. applys H0. auto.
Qed.

Lemma hoarenp_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  hoarenp (subst x v2 (subst f v1 t1)) H Q ->
  hoarenp (trm_app v1 v2) H Q.
Proof using.
  intros. unfold hoarenp in *. intros. eapply evalnp_app_fix.
  - apply H0.
  - applys H1. auto.
Qed.

Lemma hoarenp_let : forall x t1 t2 H Q Q1,
  hoarenp t1 H Q1 ->
  (forall v1, hoarenp (subst x v1 t2) (Q1 v1) Q) ->
  hoarenp (trm_let x t1 t2) H Q.
Proof using.
  intros. unfold hoarenp in *. intros. eapply evalnp_let.
  - apply H0. auto.
  - apply H1.
Qed.

Lemma hoarenp_if : forall (b:bool) t1 t2 H Q,
  hoarenp (if b then t1 else t2) H Q ->
  hoarenp (trm_if b t1 t2) H Q.
Proof using.
  intros. unfold hoarenp in *. intros. eapply evalnp_if.
  applys H0. auto.
Qed.

Lemma hoarenp_add : forall H n1 n2,
  hoarenp (val_add n1 n2)
    H
    (fun r => \[r = val_int (n1 + n2)] \* H).
Proof using.
  intros. unfold hoarenp. intros. applys evalnp_add.
  rewrite hstar_hpure_l. split. auto. auto.
Qed.
  
Lemma hoarenp_rand : forall n,
  n > 0 ->
  hoarenp (val_rand n)
    \[]
    (fun r => \exists n1, \[0 <= n1 < n] \* \[r = val_int n1]).
Proof using.
  intros. unfold hoarenp. intros. applys evalnp_rand.
  - auto.
  - intros. exists n1. rewrite hstar_hpure_l. split.
    -- auto.
    -- apply hpure_intro_hempty. auto. auto.
Qed.

Lemma hoarenp_ref : forall H v,
  hoarenp (val_ref v)
    H
    (fun r => (\exists p, \[r = val_loc p] \* p ~~> v) \* H).
Proof using.
  intros. unfold hoarenp. intros. applys evalnp_ref. intros.
  rewrite hstar_hexists. exists p.
  rewrite hstar_assoc. rewrite hstar_hpure_l. split.
  - auto.
  - Transparent hstar. unfold hstar.
    exists (Fmap.single p v) s. split.
    -- apply hsingle_intro.
    -- split. 
       + auto.
       + split.
         ++ apply Fmap.disjoint_single_of_not_indom. auto.
         ++ apply Fmap.update_eq_union_single.
Qed.

Lemma hoarenp_get : forall H v p,
  hoarenp (val_get p)
    ((p ~~> v) \* H)
    (fun r => \[r = v] \* (p ~~> v) \* H).
Proof using.
  intros. unfold hoarenp.  intros. apply evalnp_get.
  - unfold hstar in H0. destruct H0. destruct H0. destruct H0. destruct H1.
    destruct H2. rewrite H3.
    inversion H0. apply Fmap.indom_union_l. apply Fmap.indom_single.
  - rewrite hstar_hpure_l. split.
    -- inversion H0. destruct H1. destruct H1. destruct H2. destruct H3.
       rewrite H4. inversion H1. rewrite Fmap.read_union_l.
       + apply read_single.
       + apply indom_single.
    -- auto.
Qed.

Lemma hoarenp_set : forall H w p v,
  hoarenp (val_set (val_loc p) v)
    ((p ~~> w) \* H)
    (fun r => \[r = val_unit] \* (p ~~> v) \* H).
Proof using.
  intros. unfold hoarenp. intros.
  apply evalnp_set.
  - unfold hstar in H0. destruct H0. destruct H0. destruct H0. destruct H1.
    destruct H2. rewrite H3.
    inversion H0. apply Fmap.indom_union_l. apply indom_single.
  - rewrite hstar_hpure_l. split.
    -- auto.
    -- unfold hstar in *.
       destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
       exists (Fmap.single p v) x0. split.
       + apply hsingle_intro.
       + split.
         ++ auto.
         ++ split.
            +++ apply disjoint_single_of_not_indom.
                unfold "~". intros.
                eapply disjoint_inv_not_indom_both.
                ++++ apply H2.
                ++++ rewrite H0. apply indom_single.
                ++++ auto.
            +++ rewrite H3.
                rewrite update_union_l.
                ++++ inversion H0. rewrite update_single. auto.
                ++++ inversion H0. apply indom_single.
Qed.

Lemma hoarenp_free : forall H p v,
  hoarenp (val_free (val_loc p))
    ((p ~~> v) \* H)
    (fun r => \[r = val_unit] \* H).
Proof using.
  intros. unfold hoarenp. intros. apply evalnp_free.
  - inversion H0. destruct H1. destruct H1. destruct H2. destruct H3.
    rewrite H4. apply indom_union_l. inversion H1. apply indom_single.
  - rewrite hstar_hpure_l. split.
    -- auto.
    -- inversion H0. destruct H1. destruct H1. destruct H2. destruct H3.
       rewrite H4. inversion H1. rewrite remove_union_single_l.
       + auto.
       + unfold "~". intros.
         eapply disjoint_inv_not_indom_both.
         ++++ apply H3.
         ++++ inversion H1. apply indom_single.
         ++++ auto.
Qed.

Lemma divn_app_fix : forall s1 v1 v2 f x t1,
  v1 = val_fix f x t1 ->
  divn s1 (subst x v2 (subst f v1 t1)) ->
  divn s1 (trm_app v1 v2).
Proof using.
  intros. unfold divn in *.
  eapply evalnp_app_fix.
  - apply H.
  - apply H0.
Qed.

Lemma divn_let_ctx : forall s1 x t1 t2,
  divn s1 t1 ->
  divn s1 (trm_let x t1 t2).
Proof using.
  intros. unfold divn in *. eapply evalnp_conseq.
  - eapply evalnp_let.
    -- apply H.
    -- intros. inversion H0.
  - apply qimpl_refl.
Qed.

Lemma divn_let : forall s1 x t1 t2 Q1,
  evalnp s1 t1 Q1 ->
  (forall s2 v1, divn s2 (subst x v1 t2)) ->
  divn s1 (trm_let x t1 t2).
Proof using.
  intros. unfold divn in *.
  eapply evalnp_let.
  - apply H.
  - intros. apply H0.
Qed.

Lemma divn_if : forall s1 b t1 t2,
  divn s1 (if b then t1 else t2) ->
  divn s1 (trm_if (val_bool b) t1 t2).
Proof using.
  intros. unfold divn in *. apply evalnp_if. auto.
Qed.

