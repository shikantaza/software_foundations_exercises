Set Implicit Arguments.
From SLF Require Export LibSepReference.
Close Scope val_scope.
Close Scope trm_scope. (* TODO: scope closed by default *)

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

Inductive evaln : state -> trm -> (val->state->Prop) -> Prop :=
  | evaln_val : forall s v Q,
      Q v s ->
      evaln s (trm_val v) Q
  | evaln_fix : forall s f x t1 Q,
      Q (val_fix f x t1) s ->
      evaln s (trm_fix f x t1) Q
  | evaln_app_fix : forall s v1 v2 f x t1 Q,
      v1 = val_fix f x t1 ->
      evaln s (subst x v2 (subst f v1 t1)) Q ->
      evaln s (trm_app v1 v2) Q
  | evaln_let : forall Q1 s x t1 t2 Q,
      evaln s t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> evaln s2 (subst x v1 t2) Q) ->
      evaln s (trm_let x t1 t2) Q
  | evaln_if : forall s b t1 t2 Q,
      evaln s (if b then t1 else t2) Q ->
      evaln s (trm_if (val_bool b) t1 t2) Q
  | evaln_add : forall s n1 n2 Q,
      Q (val_int (n1 + n2)) s ->
      evaln s (val_add (val_int n1) (val_int n2)) Q
  | evaln_rand : forall s n Q,
      n > 0 ->
      (forall n1, 0 <= n1 < n -> Q n1 s) ->
      evaln s (val_rand (val_int n)) Q
  | evaln_ref : forall s v Q,
      (forall p, ~ Fmap.indom s p ->
         Q (val_loc p) (Fmap.update s p v)) ->
      evaln s (val_ref v) Q
  | evaln_get : forall s p Q,
      Fmap.indom s p ->
      Q (Fmap.read s p) s ->
      evaln s (val_get (val_loc p)) Q
  | evaln_set : forall s p v Q,
      Fmap.indom s p ->
      Q val_unit (Fmap.update s p v) ->
      evaln s (val_set (val_loc p) v) Q
  | evaln_free : forall s p Q,
      Fmap.indom s p ->
      Q val_unit (Fmap.remove s p) ->
      evaln s (val_free (val_loc p)) Q.

Lemma evaln_conseq : forall s t Q1 Q2,
  evaln s t Q1 ->
  Q1 ===> Q2 ->
  evaln s t Q2.
Proof using.
  intros. unfold "===>" in H0. unfold "==>" in H0. induction H; subst.
  - apply evaln_val. apply H0. auto.
  - apply evaln_fix. apply H0. auto.
  - eapply evaln_app_fix.
    -- reflexivity.
    -- apply IHevaln. auto.
  - eapply evaln_let.
    -- apply H.
    -- intros. apply H2. auto. auto.
  - apply evaln_if. apply IHevaln. auto.
  - apply evaln_add. apply H0. auto.
  - apply evaln_rand. auto. intros. apply H0. apply H1. auto.
  - apply evaln_ref. intros. pose proof (H p H1).
    apply H0. auto.
  - apply evaln_get. auto. apply H0. auto.
  - apply evaln_set. auto. apply H0. auto.
  - apply evaln_free. auto. apply H0. auto.
  (* book version *)
  (*
  introv M W.
  asserts W': (forall v h, Q1 v h -> Q2 v h). { auto. } clear W.
  induction M; try solve [ constructors* ].
  *)
Qed.

Lemma evaln_let' : forall s1 x t1 t2 Q,
  evaln s1 t1 (fun v1 s2 => evaln s2 (subst x v1 t2) Q) ->
  evaln s1 (trm_let x t1 t2) Q.
Proof using.
  intros. eapply evaln_let.
  - apply H.
  - intros. simpl in H0. auto.
Qed.

Lemma evaln_let_of_evaln_let' : forall Q1 s1 x t1 t2 Q,
  evaln s1 t1 Q1 ->
  (forall v1 s2, Q1 v1 s2 -> evaln s2 (subst x v1 t2) Q) ->
  evaln s1 (trm_let x t1 t2) Q.
Proof using.
  intros. apply evaln_let'.
  eapply evaln_conseq.
  - apply H.
  - unfold qimpl. intros. unfold himpl. intros.
    apply H0. auto.
Qed.

Inductive eval : state -> trm -> state -> val -> Prop :=
  | eval_val : forall s v,
      eval s (trm_val v) s v
  | eval_fix : forall s f x t1,
      eval s (trm_fix f x t1) s (val_fix f x t1)
  | eval_app_fix : forall s1 s2 v1 v2 f x t1 v,
      v1 = val_fix f x t1 ->
      eval s1 (subst x v2 (subst f v1 t1)) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
  | eval_let : forall s1 s2 s3 x t1 t2 v1 r,
      eval s1 t1 s2 v1 ->
      eval s2 (subst x v1 t2) s3 r ->
      eval s1 (trm_let x t1 t2) s3 r
  | eval_if : forall s1 s2 b v t1 t2,
      eval s1 (if b then t1 else t2) s2 v ->
      eval s1 (trm_if (val_bool b) t1 t2) s2 v
  | eval_add : forall s n1 n2,
      eval s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2))
  | eval_rand : forall s n n1,
      0 <= n1 < n ->
      eval s (val_rand (val_int n)) s (val_int n1)
  | eval_ref : forall s v p,
      ~ Fmap.indom s p ->
      eval s (val_ref v) (Fmap.update s p v) (val_loc p)
  | eval_get : forall s p,
      Fmap.indom s p ->
      eval s (val_get (val_loc p)) s (Fmap.read s p)
  | eval_set : forall s p v,
      Fmap.indom s p ->
      eval s (val_set (val_loc p) v) (Fmap.update s p v) val_unit
  | eval_free : forall s p,
      Fmap.indom s p ->
      eval s (val_free (val_loc p)) (Fmap.remove s p) val_unit.

Lemma evaln_inv_eval : forall s t v s' Q,
  evaln s t Q ->
  eval s t s' v ->
  Q v s'.
Proof using.
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

Lemma evaln_inv_exists_eval : forall s t Q,
  evaln s t Q ->
  exists s' v, eval s t s' v /\ Q v s'.
Proof using.
  intros. induction H.
  - exists s v. split.
    -- apply eval_val.
    -- auto.
  - exists s (val_fix f x t1). split.
    -- apply eval_fix.
    -- auto.
  - destruct IHevaln. destruct H1. exists x0 x1. destruct H1. split.
    -- eapply eval_app_fix. apply H. apply H1.
    -- auto.
  - destruct IHevaln. destruct H2. destruct H2.
    pose proof (H1 x1 x0 H3). destruct H4. destruct H4. destruct H4.
    exists x2 x3. split.
    -- eapply eval_let. apply H2. apply H4.
    -- apply H5.
  - destruct IHevaln. destruct H0. destruct H0.
    exists x x0. split.
    -- apply eval_if. auto.
    -- auto.
  - exists s (val_int (n1 + n2)). split.
    -- apply eval_add.
    -- auto.
  - exists s (val_int (n - 1)). split.
    -- apply eval_rand. math.
    -- apply H0. math.
  - forwards* (p&D&N): (exists_fresh null s).
    exists (Fmap.update s p v) (val_loc p). split.
    -- apply eval_ref. auto. 
    -- auto.
  - exists s (Fmap.read s p). split.
    -- apply eval_get. auto.
    -- auto.
  - exists (Fmap.update s p v) val_unit. split.
    -- apply eval_set.  auto.
    -- auto.
  - exists (Fmap.remove s p) val_unit. split.
    -- apply eval_free. auto.
    -- auto.
Qed.

Definition post (s:state) (t:trm) : val->hprop :=
  fun v s' => eval s t s' v.

Lemma evaln_post_of_evaln : forall s t Q,
  evaln s t Q ->
  evaln s t (post s t).
Proof using.
  intros. unfold post. induction H.
  - apply evaln_val. apply eval_val.
  - apply evaln_fix. apply eval_fix.
  - eapply evaln_app_fix.
    -- apply H.
    -- eapply evaln_conseq.
       + apply IHevaln.
       + unfold qimpl. intros. unfold himpl. intros.
         eapply eval_app_fix.
         ++ apply H.
         ++ apply H1.
  - eapply evaln_let.
    -- apply evaln_inv_exists_eval in H.
       destruct H. destruct H. destruct H.
       apply IHevaln.
    -- intros. eapply evaln_conseq.
       + apply H1.  eapply evaln_inv_eval in H.
         ++ apply H.
         ++ simpl in H2. auto.    
       + unfold qimpl. intros. unfold himpl. intros.
         eapply eval_let.
         ++ simpl in H2. apply H2.
         ++ auto.  
  - apply evaln_if. destruct b.
    -- eapply evaln_conseq.
       + apply IHevaln.
       + unfold qimpl. intros. unfold himpl. intros.
         apply eval_if. auto.
    -- eapply evaln_conseq.
       + apply IHevaln.
       + unfold qimpl. intros. unfold himpl. intros.
         apply eval_if. auto.
  - apply evaln_add. apply eval_add.
  - apply evaln_rand. auto. intros. apply eval_rand. auto.
  - apply evaln_ref. intros. apply eval_ref. auto.
  - apply evaln_get. auto. apply eval_get. auto.
  - apply evaln_set. auto. apply eval_set. auto.
  - apply evaln_free. auto. apply eval_free. auto.
Qed.

Lemma evaln_inv_post_qimpl : forall s t Q,
  evaln s t Q ->
  post s t ===> Q.
Proof using.
  intros. unfold post.
  unfold qimpl. intros. unfold himpl. intros.
  eapply evaln_inv_eval.
  - apply H.
  - apply H0.
Qed.

Definition hoaren (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (s:state), H s -> evaln s t Q.

Definition triplen (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (s:state), H s -> evaln s t Q.

Lemma evaln_frame : forall h1 h2 t Q,
  evaln h1 t Q ->
  Fmap.disjoint h1 h2 ->
  evaln (h1 \u h2) t (Q \*+ (= h2)).
Proof using.
  intros. induction H. Transparent hstar. 
  - apply evaln_val. unfold hstar.
    exists s h2. split. auto. split. auto. split. auto. auto.
  - apply evaln_fix. unfold hstar.
    exists s h2. split. auto. split. auto. split. auto. auto.
  - eapply evaln_app_fix.
    -- apply H.
    -- apply IHevaln. auto.
  - eapply evaln_let.
    -- apply IHevaln. auto.
    -- intros. simpl in H3. destruct H3. destruct H3. destruct H3.
       destruct H4. destruct H5.
       pose proof (H2 v1 x0 H3). subst. apply (H7 H5).
  - apply evaln_if. auto.
  - apply evaln_add. unfold hstar. exists s h2.
    split. auto. split. auto. split. auto. auto.
  - apply evaln_rand.
    -- auto.
    -- intros. unfold hstar. exists s h2.
       split. auto. split. auto. split. auto. auto.
  - apply evaln_ref. intros.
    unfold hstar. exists (Fmap.update s p v) h2.
    split.
    -- apply H. unfold "~". intros.
       unfold "~" in H1. apply H1. apply Fmap.indom_union_l. auto.
    -- split.
       + auto.
       + split.
         ++ apply Fmap.disjoint_update_not_r.
            +++ auto.
            +++ unfold "~". unfold "~" in H1. intros. apply H1.
                apply Fmap.indom_union_r. auto.
         ++ apply Fmap.update_union_not_r.
            unfold "~". unfold "~" in H1. intros. apply H1.
            apply Fmap.indom_union_r. auto.
  - apply evaln_get. 
    -- apply Fmap.indom_union_l. auto.
    -- unfold hstar. exists s h2.
       split.
       + rewrite Fmap.read_union_l. auto. auto.
       + split.
         ++ auto.
         ++ split. auto. auto.
  - apply evaln_set.
    -- apply Fmap.indom_union_l. auto.
    -- unfold hstar. exists (Fmap.update s p v) h2.
       split.
       + auto.
       + split.
         ++ auto.
         ++ split.
            +++ apply Fmap.disjoint_update_not_r.
                ++++ auto.
                ++++ unfold "~". eapply Fmap.disjoint_inv_not_indom_both.
                     apply H0. apply H.
            +++ apply Fmap.update_union_not_r.
                unfold "~". eapply Fmap.disjoint_inv_not_indom_both.
                apply H0. apply H.
  - apply evaln_free.
    -- apply Fmap.indom_union_l. auto.
    -- unfold hstar. exists (Fmap.remove s p) h2.
       + split.
         ++ auto.
         ++ split.
            +++ auto.
            +++ split.
                ++++ apply Fmap.disjoint_remove_l. auto.
                ++++ apply Fmap.remove_disjoint_union_l. auto. auto.
Qed.

Lemma triplen_frame : forall t H Q H',
  triplen t H Q ->
  triplen t (H \* H') (Q \*+ H').
Proof.
  intros. unfold triplen in *.
  intros. apply hstar_inv in H1. destruct H1. destruct H1. destruct H1.
  destruct H2. destruct H3. rewrite H4. eapply evaln_conseq.
  - apply evaln_frame.
    -- apply H0. auto.
    -- auto.
  - xsimpl. unfold himpl. intros. rewrite H5. auto.
Qed.

Lemma triplen_conseq : forall t H' Q' H Q,
  triplen t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triplen t H Q.
Proof using.
  intros. unfold triplen in *. intros.
  eapply evaln_conseq.
  -- apply H0. unfold himpl in H1. apply H1. auto.
  -- auto.
Qed.

Lemma triplen_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triplen t (J x) Q) ->
  triplen t (hexists J) Q.
Proof using.
  intros. unfold triplen in *. intros.
  inversion H0. eapply H. apply H1.
Qed.

Lemma triplen_hpure : forall t (P:Prop) H Q,
  (P -> triplen t H Q) ->
  triplen t (\[P] \* H) Q.
Proof using.
  intros. unfold triplen in *. intros.
  rewrite hstar_hpure_l in H1. destruct H1.
  apply H0. auto. auto.
Qed.

Lemma triplen_val : forall v H Q,
  H ==> Q v ->
  triplen (trm_val v) H Q.
Proof using.
  intros. unfold triplen. intros. apply evaln_val.
  unfold himpl in H0. apply H0. auto.
Qed.

Lemma triplen_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triplen (trm_fix f x t1) H Q.
Proof using.
  intros. unfold triplen. intros. apply evaln_fix.
  unfold himpl in H0. apply H0. auto.
Qed.

Lemma triplen_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  triplen (subst x v2 (subst f v1 t1)) H Q ->
  triplen (trm_app v1 v2) H Q.
Proof using.
  intros. unfold triplen in *. intros.
  eapply evaln_app_fix.
  - apply H0.
  - apply H1. auto.
Qed.

Lemma triplen_let : forall x t1 t2 H Q Q1,
  triplen t1 H Q1 ->
  (forall v1, triplen (subst x v1 t2) (Q1 v1) Q) ->
  triplen (trm_let x t1 t2) H Q.
Proof using.
  intros. unfold triplen in *. intros.
  eapply evaln_let.
  - apply H0. auto.
  - intros. apply H1. auto.
Qed.

Lemma triplen_if : forall (b:bool) t1 t2 H Q,
  triplen (if b then t1 else t2) H Q ->
  triplen (trm_if b t1 t2) H Q.
Proof using.
  intros. unfold triplen in *. intros.
  apply evaln_if. apply H0. auto.
Qed.

Lemma triplen_add : forall H n1 n2,
  triplen (val_add n1 n2)
    H
    (fun r => \[r = val_int (n1 + n2)] \* H).
Proof using.
  intros. unfold triplen. intros. applys evaln_add.
  rewrite hstar_hpure_l. split. auto. auto.
Qed.

Lemma triplen_rand : forall n,
  n > 0 ->
  triplen (val_rand n)
    \[]
    (fun r => \exists n1, \[0 <= n1 < n] \* \[r = val_int n1]).
Proof using.
  intros. unfold triplen. intros. applys evaln_rand.
  - auto.
  - intros. exists n1. rewrite hstar_hpure_l. split.
    -- auto.
    -- apply hpure_intro_hempty. auto. auto.
Qed.

Lemma triplen_ref : forall H v,
  triplen (val_ref v)
    H
    (fun r => (\exists p, \[r = val_loc p] \* p ~~> v) \* H).
Proof using.
  intros. unfold triplen. intros. applys evaln_ref. intros.
  rewrite hstar_hexists. exists p.
  rewrite hstar_assoc. rewrite hstar_hpure_l. split.
  - auto.
  - unfold hstar.
    exists (Fmap.single p v) s. split.
    -- apply hsingle_intro.
    -- split. 
       + auto.
       + split.
         ++ apply Fmap.disjoint_single_of_not_indom. auto.
         ++ apply Fmap.update_eq_union_single.
Qed.

Lemma triplen_get : forall H v p,
  triplen (val_get p)
    ((p ~~> v) \* H)
    (fun r => \[r = v] \* (p ~~> v) \* H).
Proof using.
  intros. unfold triplen.  intros. apply evaln_get.
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

Lemma triplen_set : forall H w p v,
  triplen (val_set (val_loc p) v)
    ((p ~~> w) \* H)
    (fun r => \[r = val_unit] \* (p ~~> v) \* H).
Proof using.
  intros. unfold triplen. intros.
  apply evaln_set.
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

Lemma triplen_free : forall H p v,
  triplen (val_free (val_loc p))
    ((p ~~> v) \* H)
    (fun r => \[r = val_unit] \* H).
Proof using.
  intros. unfold triplen. intros. apply evaln_free.
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


   
                
    
    
    
    
    