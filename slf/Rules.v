Set Implicit Arguments.

From SLF Require Export LibSepReference.
From SLF Require Basic.

Module SyntaxAndSemantics.

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_fun : var -> trm -> val
  | val_fix : var -> var -> trm -> val
  | val_ref : val
  | val_get : val
  | val_set : val
  | val_free : val
  | val_add : val
  | val_div : val
with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fun : var -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm.

Coercion val_loc : loc >-> val.
Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.

Definition state : Type := fmap loc val.

Global Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Qed.

Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if_y_eq x (trm_val w) t
  | trm_fun x t1 => trm_fun x (if_y_eq x t1 (aux t1))
  | trm_fix f x t1 => trm_fix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_seq t1 t2 => trm_seq (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (if_y_eq x t2 (aux t2))
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  end.

Implicit Types b : bool.
Implicit Types v r : val.
Implicit Types t : trm.
Implicit Types s : state.

Coercion trm_val : val >-> trm.

Coercion trm_app : trm >-> Funclass.

Inductive eval : state -> trm -> state -> val -> Prop :=
  | eval_val : forall s v,
      eval s (trm_val v) s v
  | eval_fun : forall s x t1,
      eval s (trm_fun x t1) s (val_fun x t1)
  | eval_fix : forall s f x t1,
      eval s (trm_fix f x t1) s (val_fix f x t1)
  | eval_app_fun : forall s1 s2 v1 v2 x t1 v,
      v1 = val_fun x t1 ->
      eval s1 (subst x v2 t1) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
  | eval_app_fix : forall s1 s2 v1 v2 f x t1 v,
      v1 = val_fix f x t1 ->
      eval s1 (subst x v2 (subst f v1 t1)) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
  | eval_seq : forall s1 s2 s3 t1 t2 v1 v,
      eval s1 t1 s2 v1 ->
      eval s2 t2 s3 v ->
      eval s1 (trm_seq t1 t2) s3 v
  | eval_let : forall s1 s2 s3 x t1 t2 v1 r,
      eval s1 t1 s2 v1 ->
      eval s2 (subst x v1 t2) s3 r ->
      eval s1 (trm_let x t1 t2) s3 r
  | eval_if : forall s1 s2 b v t1 t2,
      eval s1 (if b then t1 else t2) s2 v ->
      eval s1 (trm_if (val_bool b) t1 t2) s2 v
  | eval_add : forall s n1 n2,
      eval s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2))
  | eval_div : forall s n1 n2,
      n2 <> 0 ->
      eval s (val_div (val_int n1) (val_int n2)) s (val_int (Z.quot n1 n2))
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

End SyntaxAndSemantics.

Implicit Types x f : var.
Implicit Types b : bool.
Implicit Types p : loc.
Implicit Types n : int.
Implicit Types v w r : val.
Implicit Types t : trm.
Implicit Types h : heap.
Implicit Types s : state.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

Parameter triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').

Parameter triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.

Parameter triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

Parameter triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.

Parameter triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall (x:A), triple t (J x) Q) ->
  triple t (\exists (x:A), J x) Q.

Lemma triple_hpure' : forall t (P:Prop) Q,
  (P -> triple t \[] Q) ->
  triple t \[P] Q.
Proof using.
  intros. apply triple_hpure in H.
  assert (\[P] \* \[] = \[P]).
  {
    xsimpl. auto. auto.
  }
  rewrite H0 in H. auto.
Qed.

Parameter triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.

Parameter triple_let : forall x t1 t2 Q1 H Q,
  triple t1 H Q1 ->
  (forall v1, triple (subst x v1 t2) (Q1 v1) Q) ->
  triple (trm_let x t1 t2) H Q.

Parameter triple_if_case : forall b t1 t2 H Q,
  (b = true -> triple t1 H Q) ->
  (b = false -> triple t2 H Q) ->
  triple (trm_if (val_bool b) t1 t2) H Q.

Parameter triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.

Lemma triple_val_minimal : forall v,
  triple (trm_val v) \[] (fun r => \[r = v]).
Proof using.
  intros. apply triple_val. xsimpl. auto.
Qed.

Lemma triple_val' : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  intros.
  assert (H ==> H \* \[]). { xsimpl. }
  assert (Q \*+ \[] ===> Q). { xsimpl. }
  pose proof (triple_val_minimal v).
  eapply triple_conseq_frame.
  - apply H3.
  - xsimpl.
  - xsimpl. intros. rewrite H4. auto.
Qed.


(* not convinced about this *)
Lemma triple_let_val : forall x v1 t2 H Q,
  triple v1 H (fun r => \[r = v1] \* H) ->
  (forall v, triple (subst x v t2) ((fun r => \[r = v1] \* H) v) Q) ->
  triple (trm_let x v1 t2) H Q.
Proof using.
  intros. eapply triple_let.
  - apply H0.
  - (* can also do just eauto *) intros. pose proof (H1 v0). auto.
Qed.

Parameter triple_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  triple (trm_fun x t1) H Q.

Parameter triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.

Parameter triple_add : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).

Parameter triple_div' : forall n1 n2,
  triple (val_div n1 n2)
    \[n2 <> 0]
    (fun r => \[r = val_int (Z.quot n1 n2)]).

Parameter triple_div : forall n1 n2,
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun r => \[r = val_int (Z.quot n1 n2)]).

Parameter triple_get : forall v p,
  triple (val_get (val_loc p))
    (p ~~> v)
    (fun r => \[r = v] \* (p ~~> v)).

Parameter triple_set : forall w p v,
  triple (val_set (val_loc p) w)
    (p ~~> v)
    (fun _ => p ~~> w).

Parameter triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun (r:val) => \exists (p:loc), \[r = val_loc p] \* p ~~> v).

Parameter triple_ref' : forall v,
  triple (val_ref v)
    \[]
    (funloc p => p ~~> v).

Parameter triple_free : forall p v,
  triple (val_free (val_loc p))
    (p ~~> v)
    (fun _ => \[]).

Module ExamplePrograms.
Export ProgramSyntax.

Definition incr : val :=
  val_fun "p" (
    trm_let "n" (trm_app val_get (trm_var "p")) (
    trm_let "m" (trm_app (trm_app val_add
                             (trm_var "n")) (val_int 1)) (
    trm_app (trm_app val_set (trm_var "p")) (trm_var "m")))).

Definition incr' : val :=
  <{ fun 'p =>
       let 'n = ! 'p in
       let 'm = 'n + 1 in
       'p := 'm }>.

Lemma incr_eq_incr' :
  incr = incr'.
Proof using. reflexivity. Qed.

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  (* initialize the proof *)
  intros. applys triple_app_fun. { reflexivity. } simpl.
  (* reason about let n = .. *)
  applys triple_let.
  (* reason about !p *)
  { apply triple_get. }
  (* name n' the result of !p *)
  intros n'. simpl.
  (* substitute away the equality n' = n *)
  apply triple_hpure. intros ->.
  (* reason about let m = .. *)
  applys triple_let.
  (* apply the frame rule to put aside p ~~> n *)
  { applys triple_conseq_frame.
    (* reason about n+1 in the empty state *)
    { applys triple_add. }
    { xsimpl. }
    { xsimpl. } }
  (* name m' the result of n+1 *)
  intros m'. simpl.
  (* substitute away the equality m' = m *)
  apply triple_hpure. intros ->.
  (* reason about p := m *)
  { applys triple_set. }
Qed.

Definition succ_using_incr : val :=
  <{ fun 'n =>
       let 'r = val_ref 'n in
       incr 'r;
       let 'x = ! 'r in
       val_free 'r;
       'x }>.

Lemma triple_succ_using_incr : forall (n:int),
  triple (trm_app succ_using_incr n)
    \[]
    (fun v => \[v = val_int (n+1)]).
Proof using.
  intros. eapply triple_app_fun.
  - reflexivity.
  - simpl. eapply triple_let.
    -- apply triple_ref.
    -- intros. simpl. apply triple_hexists.
       intros. apply triple_hpure.
       intros. eapply triple_seq.
       + assert (triple (incr x) (x ~~> n) (fun _ => (x ~~> (n+1)))).
         { apply triple_incr. }
         rewrite <- H in H0. apply H0.
       + rewrite H. apply triple_let with (Q1 := fun r => \[r = (n+1)]  \* (x ~~> (n+1))).
         ++ apply triple_get.
         ++ intros. simpl. apply triple_hpure. intros. eapply triple_seq.
            +++ eapply triple_conseq.
                ++++ rewrite H. apply triple_free.
                ++++ xsimpl.
                ++++ xsimpl.
            +++ rewrite H0. apply triple_val. xsimpl. auto.
Qed.

Import Basic.Facto.

Definition factorec : val :=
  <{ fix 'f 'n =>
       let 'b = ('n <= 1) in
       if 'b
         then 1
         else let 'x = 'n - 1 in
              let 'y = 'f 'x in
              'n * 'y }>.

Lemma cps_facto_helper1 : forall n : int, n >= 0 -> n <= 1 -> n = 0 \/ n = 1.
Proof.
  induction n; intros.
  - left. auto.
  - induction p.
    -- right. math.
    -- right. math.
    -- right. auto.
  - induction p.
    -- left. math.
    -- left. math.
    -- left. math.
Qed.

Lemma cps_facto_helper2 : forall n : int, ~ n <= 1 -> n > 1.
Proof.
  intros.
  unfold "~" in H.
  math. 
Qed.

Lemma triple_factorec : forall n,
  n >= 0 ->
  triple (factorec n)
    \[]
    (fun r => \[r = facto n]).
Proof using.
  intros n. induction_wf IH: (downto 0) n. intros.
  eapply triple_app_fix.
  - reflexivity.
  - simpl. eapply triple_let.
    -- eapply triple_le.
    -- intros. simpl. apply triple_hpure'.
       intros. rewrite H0. applys triple_if. case_if as C.
       + apply triple_val. xsimpl. 
         assert (n = 0 \/ n = 1). { apply cps_facto_helper1. auto. auto. }
         destruct H1.
         ++ rewrite H1. rewrite facto_init. auto. math.
         ++ rewrite H1. rewrite facto_init. auto. math.
       + apply triple_let with (Q1 := (fun r => \[r = (n-1)])).
         ++ apply triple_sub.
         ++ intros. simpl. apply triple_hpure'.
            intros. rewrite H1.  
            assert (n > 1). { apply cps_facto_helper2. auto. }
            rewrite (@facto_step n).
            +++ eapply triple_let with (Q1 := (fun r => \[r = facto (n-1)])).
                ++++ xapp.
                     +++++ math.
                     +++++ math.
                     +++++ xsimpl. auto.
                ++++ intros. simpl. apply triple_hpure'. intros. rewrite H3.
                     eapply triple_mul.
            +++ auto.
Qed.
              
            