Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

Hint Constructors multi : core.

(*
   Where do we fail if we attempt to prove normalization by a 
   straightforward induction on the size of a well-typed term?

   Application - this could lead to the size not reducing (revisit this
   later; the reasoning seems incorrect)
*)

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Prod : ty -> ty -> ty.
  
Inductive tm : Type :=
    (* pure STLC *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
    (* booleans *)
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
    (* pairs *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm.  
  
Declare Custom Entry stlc.

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "{ x }" := x (in custom stlc at level 1, x constr).

Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := tm_true (in custom stlc at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := tm_false (in custom stlc at level 0).

Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc at level 2, X custom stlc, Y custom stlc at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 0).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 0).

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{ \ y : T, t1 }> =>
      if String.eqb x y then t else <{ \y:T, [x:=s] t1 }>
  | <{t1 t2}> =>
      <{ ([x:=s]t1) ([x:=s]t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  | <{(t1, t2)}> =>
      <{( ([x:=s] t1), ([x:=s] t2) )}>
  | <{t0.fst}> =>
      <{ ([x:=s] t0).fst}>
  | <{t0.snd}> =>
      <{ ([x:=s] t0).snd}>
  end

  where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).
  
Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{(v1, v2)}>.
      
Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1 t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
  | ST_Pair1 : forall t1 t1' t2,
        t1 --> t1' ->
        <{ (t1,t2) }> --> <{ (t1' , t2) }>
  | ST_Pair2 : forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        <{ (v1, t2) }> --> <{ (v1, t2') }>
  | ST_Fst1 : forall t0 t0',
        t0 --> t0' ->
        <{ t0.fst }> --> <{ t0'.fst }>
  | ST_FstPair : forall v1 v2,
        value v1 ->
        value v2 ->
        <{ (v1,v2).fst }> --> v1
  | ST_Snd1 : forall t0 t0',
        t0 --> t0' ->
        <{ t0.snd }> --> <{ t0'.snd }>
  | ST_SndPair : forall v1 v2,
        value v1 ->
        value v2 ->
        <{ (v1,v2).snd }> --> v2

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Notation step_normal_form := (normal_form step).

Lemma value__normal : forall t, value t -> step_normal_form t.
Proof.
intros.
unfold step_normal_form.
unfold not.
intros.
destruct H0.
induction H0; try solve_by_invert.
- inversion H. eauto.
- inversion H. eauto.
Qed.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc at level 0).
                                          
Inductive has_type : context -> tm -> ty -> Prop :=
  (* Same as before: *)
  (* pure STLC *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
    (x |-> T2 ; Gamma) |- t1 \in T1 ->
      Gamma |- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (T2 -> T1) ->
      Gamma |- t2 \in T2 ->
      Gamma |- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |- true \in Bool
  | T_False : forall Gamma,
       Gamma |- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T1 ->
       Gamma |- t3 \in T1 ->
       Gamma |- if t1 then t2 else t3 \in T1
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in T2 ->
      Gamma |- (t1, t2) \in (T1 * T2)
  | T_Fst : forall Gamma t0 T1 T2,
      Gamma |- t0 \in (T1 * T2) ->
      Gamma |- t0.fst \in T1
  | T_Snd : forall Gamma t0 T1 T2,
      Gamma |- t0 \in (T1 * T2) ->
      Gamma |- t0.snd \in T2

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Hint Extern 2 (has_type _ (app _ _) _) => eapply T_App; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.

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
pose proof (IHhas_type (x |-> T2; Gamma')) as H1.
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
  (x |-> U ; Gamma) |- t \in T ->
  empty |- v \in U ->
  Gamma |- [x:=v]t \in T.     
Proof.
intros.
generalize dependent Gamma.
generalize dependent T.
induction t.
- intros.
  destruct (eqb x s) eqn: Heq.
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
  destruct (eqb x s) eqn: Heq.
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
     assert (H8: (s |-> t; x |-> U; Gamma) = (x |-> U; s |-> t; Gamma)).
     {
       rewrite update_permute. reflexivity. apply eqb_neq. assumption.
     }
     rewrite <- H8. assumption.
- intros. simpl.
  inversion H.
  apply T_True.
- intros. simpl.
  inversion H.
  apply T_False.
- intros.
  simpl.
  apply T_If.
  inversion H.
  -- pose proof (IHt1 Ty_Bool Gamma) as Hthen. eauto.
  -- inversion H. eauto.
  -- inversion H. eauto.
- intros. simpl.
  inversion H; subst. eauto.
- intros. simpl.
  inversion H. subst. eauto.
- intros. simpl.
  inversion H. subst. eauto.  
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
- intros. inversion H1; subst.
  -- apply T_Pair.
     + eauto.
     + assumption.
  -- apply T_Pair.
     + assumption.
     + eauto.
- intros. inversion H0; subst.
  -- eapply T_Fst. eauto.
  -- inversion H. assumption.
- intros.  inversion H0; subst.
  -- eapply T_Snd. eauto.
  -- inversion H. assumption.
Qed.      

Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall (x : string),
      appears_free_in x <{ x }>
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x <{ t1 t2 }>
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x <{ t1 t2 }>
  | afi_abs : forall x y T11 t12,
        y <> x ->
        appears_free_in x t12 ->
        appears_free_in x <{ \y : T11, t12 }>
  (* booleans *)
  | afi_test0 : forall x t0 t1 t2,
      appears_free_in x t0 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  | afi_test1 : forall x t0 t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  | afi_test2 : forall x t0 t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  (* pairs *)
  | afi_pair1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{ (t1, t2) }>
  | afi_pair2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{ (t1 , t2) }>
  | afi_fst : forall x t,
      appears_free_in x t ->
      appears_free_in x <{ t.fst }>
  | afi_snd : forall x t,
      appears_free_in x t ->
      appears_free_in x <{ t.snd }>.
      
Hint Constructors appears_free_in : core.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.
  
Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in S.
Proof.
intros.
generalize dependent Gamma'.
induction H.
- intros. apply T_Var. rewrite <- (H0 x). assumption. apply afi_var.
- intros. apply T_Abs.
  apply (IHhas_type (x |-> T2; Gamma')).
  intros.
  destruct (String.eqb x x0) eqn: Heq.
  -- rewrite eqb_eq in Heq. rewrite Heq. rewrite update_eq. rewrite update_eq. reflexivity.
  -- rewrite eqb_neq in Heq. rewrite update_neq.
     + rewrite update_neq.
       ++ apply H0. apply afi_abs. assumption. assumption.
       ++ assumption.
     + assumption.
- intros. eapply T_App.
  -- eauto.
  -- eauto.
- intros. apply T_True.
- intros. apply T_False.
- intros. apply T_If.
  -- eauto.
  -- eauto.
  -- eauto.
- intros. apply T_Pair.
  -- eauto.
  -- eauto.
- intros. eapply T_Fst. eauto.
- intros. eapply T_Snd. eauto.  
Qed.  
  
Theorem false_eqb_string : forall x y : string,
   x <> y -> String.eqb x y = false.
Proof.
intros.
unfold not in H.
apply eqb_neq in H. assumption.
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof.
intros.
generalize dependent T.
generalize dependent Gamma.
induction H; intros.
- exists T. inversion H0. assumption.
- inversion H0. subst. apply IHappears_free_in in H4. assumption.
- inversion H0. subst. apply IHappears_free_in in H6. assumption.
- inversion H1. subst. apply IHappears_free_in in H7.
  destruct H7. rewrite update_neq in H2.
  -- exists x0. assumption.
  -- assumption.
- inversion H0. subst. apply IHappears_free_in in H5. assumption.
- inversion H0. subst. apply IHappears_free_in in H7. assumption.
- inversion H0. subst. apply IHappears_free_in in H8. assumption.
- inversion H0. subst. apply IHappears_free_in in H4. assumption.
- inversion H0. subst. apply IHappears_free_in in H6. assumption.
- inversion H0. subst. apply IHappears_free_in in H3. assumption.
- inversion H0. subst. apply IHappears_free_in in H3. assumption.
Qed.

(* basically reinvented free_in_context unknowingly! *)
Lemma ctx_for_term_with_free_var : forall Gamma x t T,
  appears_free_in x t ->
  Gamma |- t \in T ->
  exists T1, Gamma x = Some T1.
Proof.
intros.
induction H0; subst.
- inversion H. subst. exists T1. assumption.
- inversion H. subst.
  destruct (IHhas_type H6).
  rewrite update_neq in H1. exists x1. assumption. assumption.
- inversion H; subst.
  -- destruct (IHhas_type1 H2). exists x0. assumption.
  -- destruct (IHhas_type2 H2). exists x0. assumption.
- inversion H.
- inversion H.
- inversion H; subst.
  -- destruct (IHhas_type1 H2). exists x0. assumption.
  -- destruct (IHhas_type2 H2). exists x0. assumption.
  -- destruct (IHhas_type3 H2). exists x0. assumption.
- inversion H; subst.
  -- destruct (IHhas_type1 H2). exists x0. assumption.
  -- destruct (IHhas_type2 H2). exists x0. assumption.
- inversion H; subst.
  destruct (IHhas_type H3). exists x0. assumption.
- inversion H; subst.
  destruct (IHhas_type H3). exists x0. assumption.
Qed.

Corollary typable_empty__closed : forall t T,
    empty |- t \in T ->
    closed t.
Proof.
intros t.
induction t; intros.
- inversion H. inversion H2.
- inversion H. subst.
  apply (IHt1 <{T2 -> T}>) in H3.
  apply (IHt2 T2) in H5.
  unfold closed in *.
  intros.  
  pose proof (H3 x) as H6.
  pose proof (H5 x) as H7.
  unfold not in *.
  intros.
  inversion H0.
  -- eauto.
  -- eauto.
- unfold closed.
  intros. unfold not. intros.
  inversion H0. subst.
  inversion H. subst.
  clear IHt H H0.
  destruct (ctx_for_term_with_free_var (s |-> t) x t0 T1 H6 H8).
  rewrite update_neq in H.
  -- inversion H.
  -- assumption.
- unfold closed. intros. unfold not. intros. inversion H0.
- unfold closed. intros. unfold not. intros. inversion H0.
- inversion H. subst.
  unfold closed in *.
  intros. unfold not. intros.
  inversion H0. subst.
  -- apply (((IHt1 <{Bool}>) H4) x). assumption.
  -- apply (((IHt2 T) H6) x). assumption.
  -- apply (((IHt3 T) H7) x). assumption.
- inversion H. subst.
  unfold closed in *. intros. unfold not. intros.
  inversion H0; subst.
  -- pose proof (((IHt1 T1) H3) x) as H6. eauto.
  -- pose proof (((IHt2 T2) H5) x) as H7. eauto.
- inversion H. subst.
  unfold closed in *. intros. unfold not. intros.
  inversion H0; subst.
  pose proof (((IHt <{T * T2}>) H2) x) as H5. eauto.
- inversion H. subst.
  unfold closed in *. intros. unfold not. intros.
  inversion H0; subst.
  pose proof (((IHt <{T1 * T}>) H2) x) as H5. eauto.
Qed.

(* book version *)
Corollary typable_empty__closed' : forall t T,
    empty |- t \in T ->
    closed t.
Proof.
  intros. unfold closed. intros x H1.
  destruct (free_in_context _ _ _ _ H1 H) as [T' C].
  discriminate C.
Qed.

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
intros.
induction H.
- unfold step_normal_form.
  unfold not. intros.
  destruct H.
  inversion H.
- unfold step_normal_form.
  unfold not. intros.
  destruct H.
  inversion H.
- unfold step_normal_form.
  unfold not. intros.
  destruct H.
  inversion H.
- unfold step_normal_form in *.
  unfold not in *.
  intros.
  destruct H1.
  inversion H1.
  -- apply IHvalue1. exists t1'. assumption.
  -- apply IHvalue2. exists t2'. assumption.  
Qed.  

(* could have used value__normal defined earlier
   instead of value_is_normal *)
Lemma step_deterministic :
   deterministic step.
Proof.
unfold deterministic.
intros.
generalize dependent y2.
induction H; intros.
- inversion H0; subst.
  -- reflexivity.
  -- inversion H4.
  -- apply value_is_nf in H.
     unfold step_normal_form in H.
     exfalso. apply H. exists t2'. assumption.
- inversion H0; subst.
  -- inversion H.
  -- apply (IHstep t1'0) in H4. rewrite H4. reflexivity.     
  -- apply value_is_nf in H3.
     unfold step_normal_form in H3.
     exfalso. apply H3. exists t1'. assumption.
- inversion H1; subst.
  -- apply value_is_nf in H5.
     unfold step_normal_form in H5.
     exfalso. apply H5. exists t2'. assumption.
  -- apply value_is_nf in H.
     unfold step_normal_form in H.
     exfalso. apply H. exists t1'. assumption.
  -- rewrite ((IHstep t2'0) H6). reflexivity.
- inversion H0.
  -- reflexivity.
  -- subst. inversion H4.
- inversion H0.
  -- reflexivity.
  -- subst. inversion H4.
- inversion H0; subst.
  -- inversion H.
  -- inversion H.
  -- rewrite ((IHstep t1'0) H5). reflexivity.
- inversion H0; subst.
  -- rewrite ((IHstep t1'0) H4). reflexivity.
  -- apply value_is_nf in H3.
     unfold step_normal_form in H3.
     exfalso. apply H3. exists t1'. assumption.
- inversion H1; subst.
  -- apply value_is_nf in H.
     unfold step_normal_form in H.
     exfalso. apply H. exists t1'. assumption.
  -- rewrite ((IHstep t2'0) H6). reflexivity.
- inversion H0; subst.
  -- rewrite ((IHstep t0'0) H2). reflexivity.
  -- inversion H; subst. 
     + apply value_is_nf in H2.
       unfold step_normal_form in H2.
       exfalso. apply H2. exists t1'. assumption.
     + apply value_is_nf in H3.
       unfold step_normal_form in H3.
       exfalso. apply H3. exists t2'. assumption.
- inversion H1. subst.
  -- inversion H3; subst.
     + apply value_is_nf in H.
       unfold step_normal_form in H.
       exfalso. apply H. exists t1'. assumption.
     + apply value_is_nf in H0.
       unfold step_normal_form in H0.
       exfalso. apply H0. exists t2'. assumption.
  -- reflexivity.
- inversion H0; subst.
  -- rewrite ((IHstep t0'0) H2). reflexivity.
  -- inversion H; subst. 
     + apply value_is_nf in H2.
       unfold step_normal_form in H2.
       exfalso. apply H2. exists t1'. assumption.
     + apply value_is_nf in H3.
       unfold step_normal_form in H3.
       exfalso. apply H3. exists t2'. assumption. 
- inversion H1. subst.
  -- inversion H3; subst.
     + apply value_is_nf in H.
       unfold step_normal_form in H.
       exfalso. apply H. exists t1'. assumption.
     + apply value_is_nf in H0.
       unfold step_normal_form in H0.
       exfalso. apply H0. exists t2'. assumption.
  -- reflexivity.
Qed.

Definition halts (t:tm) : Prop := exists t', t -->* t' /\ value t'.

Lemma value_halts : forall v, value v -> halts v.
Proof.
intros.
unfold halts.
inversion H.
- exists v. rewrite <- H0. split. apply multi_refl. apply v_abs.
- exists v. rewrite <- H0. split. apply multi_refl. apply v_true.
- exists v. rewrite <- H0. split. apply multi_refl. apply v_false.
- exists v. rewrite <- H2. split. apply multi_refl. apply v_pair. assumption. assumption.
Qed.

Fixpoint R (T:ty) (t:tm) : Prop :=
  empty |- t \in T /\ halts t /\
  (match T with
   | <{ Bool }> => True
   | <{ T1 -> T2 }> => (forall s, R T1 s -> R T2 <{t s}> )

   (* ... edit the next line when dealing with products *)
   (*| <{ T1 * T2 }> => R T1 <{t.fst}> /\ R T2 <{t.snd}> *)
   | <{ T1 * T2 }> => (exists s1 s2, t -->* <{(s1, s2)}> /\ R T1 s1 /\ R T2 s2)
   end).

Lemma R_halts : forall {T} {t}, R T t -> halts t.
Proof.
intros.
destruct T; simpl R in H.
- destruct H. destruct H0. assumption.
- destruct H. destruct H0. assumption.
- destruct H. destruct H0. assumption.
Qed.

Lemma R_typable_empty : forall {T} {t}, R T t -> empty |- t \in T.
Proof.
intros. destruct T; simpl R in H; destruct H as [H [_ _]]; assumption.
Qed.

Lemma normal_forms_unique_helper :
  forall x y, x -->* y -> x --> y \/ exists y', x -->* y' /\ y' -->* y.
Proof.
intros.
right.
exists y.
split.
assumption.
apply multi_refl.
Qed.

Lemma helper_lemma : forall t t',
  t -->* t' ->
  t = t' \/ t --> t' \/ (exists t1, t --> t1 /\ t1 -->* t').
Proof.
intros.
inversion H.
- left. reflexivity.
- subst. right. right. exists y. split. assumption. assumption.
Qed.
  
Lemma step_preserves_halting :
  forall t t', (t --> t') -> (halts t <-> halts t').
Proof.
intros.
split.
- intros. unfold halts in *.
  destruct H0. destruct H0.
  exists x. split.
  -- destruct (helper_lemma t x H0).
     + subst.
       apply value_is_nf in H1.
       unfold step_normal_form in H1.
       exfalso. apply H1. exists t'. assumption.
     + destruct H2.
       ++ rewrite (step_deterministic t t' x H H2). apply multi_refl.
       ++ destruct H2. destruct H2.
          rewrite <- (step_deterministic t t' x0 H H2) in H3. assumption.
  -- assumption.
- intros. unfold halts in *.
  destruct H0. destruct H0.
  exists x. split.
  -- eapply multi_step. apply H. apply H0.
  -- assumption.
Qed.

(* book version *)
Lemma step_preserves_halting' :
  forall t t', (t --> t') -> (halts t <-> halts t').
Proof.
 intros t t' ST. unfold halts.
 split.
 - (* -> *)
  intros [t'' [STM V]].
  destruct STM.
   + exfalso; apply value__normal in V; eauto.
   + rewrite (step_deterministic _ _ _ ST H). exists z. split; assumption.
 - (* <- *)
  intros [t'0 [STM V]].
  exists t'0. split; eauto.
Qed.  
 
(*     
Lemma step_preserves_R : forall T t t', (t --> t') -> R T t -> R T t'.
Proof.
intros.
generalize dependent t'.
generalize dependent t.
induction T; intros.
- unfold R in *.
  destruct H0. destruct H1.
  split.
  -- apply preservation with (t := t). assumption. assumption.
  -- split.
     + apply step_preserves_halting with (t := t). assumption. assumption.
     + assumption.
- simpl in *.
  destruct H0. destruct H1.
  split.
  -- apply preservation with (t := t). assumption. assumption.
  -- split.
     + apply step_preserves_halting with (t := t). assumption. assumption.
     + intros. eauto.
- simpl in *.
  destruct H0. destruct H1. destruct H2. destruct H2. destruct H2. destruct H3.
  split.
  -- apply preservation with (t := t).  assumption. assumption.
  -- split.
     + apply step_preserves_halting with (t := t). assumption. assumption.
     + exists x, x0. split.
       ++  
                
Qed.       
*)

Lemma step_preserves_R : forall T t t', (t --> t') -> R T t -> R T t'.
Proof.
 induction T;  intros t t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [typable_empty_t [halts_t RRt]].
  (* TBool *)
  split. eapply preservation; eauto.
  split. apply (step_preserves_halting _ _ E); eauto.
  auto.
  (* TArrow *)
  split. eapply preservation; eauto.
  split. apply (step_preserves_halting _ _ E); eauto.
  intros.
  eapply IHT2.
  apply  ST_App1. apply E.
  apply RRt; auto.
  destruct RRt as [s1 [s2 [H0 [H1 H2]]]].
  inversion H0; subst. inversion E; subst;
  split; try eapply preservation; eauto;
  split; try apply (step_preserves_halting _ _ E); eauto.
  exists t1'; eauto.
  exists s1; eauto.
  assert (t' = y) by (eapply step_deterministic; eauto).
  subst. split. eapply preservation; eauto.
  split. apply (step_preserves_halting _ _ E); eauto.
  exists s1; eauto.
Qed.
       
Lemma multistep_preserves_R : forall T t t',
  (t -->* t') -> R T t -> R T t'.
Proof.
intros.
induction H.
- assumption.
- apply IHmulti. apply step_preserves_R with (t := x). assumption. assumption.
Qed.

(*
Lemma step_preserves_R' : forall T t t',
  empty |- t \in T -> (t --> t') -> R T t' -> R T t.
intros.
generalize dependent t'.
generalize dependent t.
induction T; intros.
- unfold R in *.
  destruct H1. destruct H2.
  split.
  -- assumption.
  -- split.
     + rewrite step_preserves_halting. apply H2. assumption.
     + assumption.
- simpl in *.
  destruct H1. destruct H2.
  split.
  -- assumption.
  -- split.
     + rewrite step_preserves_halting. apply H2. assumption.
     + intros. pose proof ((H3 s) H4) as H5.
       pose proof (IHT2 <{t s}>) as H6.
       apply H6 in H5. 
       ++ assumption.
       ++ eapply T_App. apply H. apply R_typable_empty. assumption.
       ++ apply ST_App1. assumption.
- simpl in *.
  destruct H1. destruct H2.
  split.
  -- assumption.
  -- split.
     + rewrite step_preserves_halting. apply H2. assumption.
     + intros. eauto.
Qed.
*)

Lemma step_preserves_R' : forall T t t',
  has_type empty t T -> (t --> t') -> R T t' -> R T t.
Proof with eauto.
 induction T;  intros t t' Ha E Rt; unfold R; fold R; unfold R in Rt;
 fold R in Rt; destruct Rt as [typable_empty_t [halts_t RRt]]; split...
 split... eapply step_preserves_halting...
 split. eapply step_preserves_halting... intros.
 remember H. clear Heqr.
 apply R_typable_empty in H.
 apply RRt in r. eapply IHT2...
 destruct RRt as [s1 [s2 [H1 [H2 H3]]]].
 split. eapply step_preserves_halting...
 inversion H1; subst; exists s1...
Qed.

Lemma multistep_preserves_R' : forall T t t',
  empty |- t \in T -> (t -->* t') -> R T t' -> R T t.
Proof.
intros.
induction H0.
- assumption.
- pose proof (preservation x y T H H0) as H3.
  apply IHmulti in H3. 
  -- eapply step_preserves_R'. assumption. apply H0. assumption.
  -- assumption.        
Qed.     

Definition env := list (string * tm).

Fixpoint msubst (ss:env) (t:tm) : tm :=
match ss with
| nil => t
| ((x,s)::ss') => msubst ss' <{ [x:=s]t }>
end.

Definition tass := list (string * ty).

Fixpoint mupdate (Gamma : context) (xts : tass) :=
  match xts with
  | nil => Gamma
  | ((x,v)::xts') => update (mupdate Gamma xts') x v
  end.
  
Fixpoint lookup {X:Set} (k : string) (l : list (string * X))
              : option X :=
  match l with
    | nil => None
    | (j,x) :: l' =>
      if String.eqb j k then Some x else lookup k l'
  end.
  
Fixpoint drop {X:Set} (n:string) (nxs:list (string * X))
            : list (string * X) :=
  match nxs with
    | nil => nil
    | ((n',x)::nxs') =>
        if String.eqb n' n then drop n nxs'
        else (n',x)::(drop n nxs')
  end.
  
Inductive instantiation : tass -> env -> Prop :=
| V_nil :
    instantiation nil nil
| V_cons : forall x T v c e,
    value v -> R T v ->
    instantiation c e ->
    instantiation ((x,T)::c) ((x,v)::e).

Lemma vacuous_substitution : forall t x,
     ~ appears_free_in x t ->
     forall t', <{ [x:=t']t }> = t.
Proof.
intros.
induction t.
- simpl. destruct (String.eqb x s) eqn: Heq.
  -- rewrite eqb_eq in Heq. rewrite Heq in H. exfalso. unfold not in H.
     apply H. apply afi_var.
  -- reflexivity.
- simpl.
  assert (H1: ~ appears_free_in x t1 /\ ~ appears_free_in x t2).
  {
    intros. split.
    - unfold not in H. unfold not. intros. apply H. apply afi_app1. assumption.
    - unfold not in H. unfold not. intros. apply H. apply afi_app2. assumption.  
  }
  destruct H1. rewrite (IHt1 H0). rewrite (IHt2 H1). reflexivity.
- simpl. destruct (String.eqb x s) eqn: Heq.
  -- reflexivity. 
  -- rewrite eqb_neq in Heq.
     assert (H1: s <> x). { unfold not in *. intros. rewrite H0 in Heq. apply Heq. reflexivity. }
     assert (H2: ~ appears_free_in x t0).
     {
       intros. unfold not in H. unfold not. intros. apply H. apply afi_abs. 
       - assumption.
       - assumption.
     }
     rewrite (IHt H2). reflexivity.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl.
  assert (H1: ~ appears_free_in x t1 /\ ~ appears_free_in x t2 /\ ~ appears_free_in x t3).
  {
    intros. split.
    - unfold not in H. unfold not. intros. apply H. apply afi_test0. assumption.
    - split. 
      -- unfold not in H. unfold not. intros. apply H. apply afi_test1. assumption.
      -- unfold not in H. unfold not. intros. apply H. apply afi_test2. assumption.
  }
  destruct H1. destruct H1.
  rewrite (IHt1 H0). rewrite (IHt2 H1). rewrite (IHt3 H2). reflexivity.
- simpl.
  assert (H1: ~ appears_free_in x t1 /\ ~ appears_free_in x t2).
  {
    intros. split.
    - unfold not in H. unfold not. intros. apply H. apply afi_pair1. assumption.
    - unfold not in H. unfold not. intros. apply H. apply afi_pair2. assumption.  
  }
  destruct H1. rewrite (IHt1 H0). rewrite (IHt2 H1). reflexivity.
- simpl.
  assert (H1: ~ appears_free_in x t).
  {     
    intros. unfold not in H. unfold not. intros. apply H. apply afi_fst. assumption. 
  }
  rewrite (IHt H1). reflexivity.
- simpl.
  assert (H1: ~ appears_free_in x t).
  {     
    intros. unfold not in H. unfold not. intros. apply H. apply afi_snd. assumption. 
  }
  rewrite (IHt H1). reflexivity.
Qed.

Lemma subst_closed: forall t,
     closed t ->
     forall x t', <{ [x:=t']t }> = t.
Proof.
intros.
unfold closed in H.
pose proof (H x) as H1.
generalize t'.
generalize dependent H1.
generalize t x.
apply vacuous_substitution.
Qed.

Lemma subst_not_afi : forall t x v,
    closed v -> ~ appears_free_in x <{ [x:=v]t }>.
intros.
unfold not.
intros.
unfold closed in H.
induction t.
- simpl in H0.
  destruct (String.eqb x s) eqn: Heq.
  -- apply (H x). assumption.
  -- rewrite eqb_neq in Heq.
     unfold not in Heq. apply Heq.
     inversion H0. reflexivity.
- simpl in H0.
  inversion H0; subst.
  -- apply (IHt1 H3).
  -- apply (IHt2 H3).
- simpl in H0.
  destruct (String.eqb x s) eqn: Heq.
  -- rewrite eqb_eq in Heq. rewrite Heq in H0. inversion H0.
     unfold not in H4. apply H4. reflexivity.
  -- rewrite eqb_neq in Heq.
     inversion H0. subst.
     apply IHt. assumption.
- simpl in H0. inversion H0.
- simpl in H0. inversion H0.
- inversion H0; subst.
  -- apply (IHt1 H3).
  -- apply (IHt2 H3).
  -- apply (IHt3 H3).
- inversion H0; subst.
  -- apply (IHt1 H3).
  -- apply (IHt2 H3).
- inversion H0; subst.
  apply (IHt H3).
- inversion H0; subst.
  apply (IHt H3).
Qed.

Lemma duplicate_subst : forall t' x t v,
  closed v -> <{ [x:=t]([x:=v]t') }> = <{ [x:=v]t' }>.
Proof.
intros.
apply subst_not_afi with (t:=t') (x:=x) in H.
pose proof (vacuous_substitution <{ [x := v] t' }> x H) as H1.
apply H1.
Qed.

Lemma swap_subst : forall t x x1 v v1,
    x <> x1 ->
    closed v -> closed v1 ->
    <{ [x1:=v1]([x:=v]t) }> = <{ [x:=v]([x1:=v1]t) }>.
Proof.      
intros.
induction t.
- destruct (String.eqb x s) eqn: Heqx.
  -- rewrite eqb_eq in Heqx. rewrite Heqx.
     simpl.
     assert (H2: (s =? s)%string  = true). { rewrite eqb_eq. reflexivity. }
     rewrite H2. 
     destruct (String.eqb x1 s) eqn: Heqx1.
     + rewrite eqb_eq in Heqx1.
       rewrite <- Heqx1 in Heqx.
       exfalso. apply (H Heqx).
     + simpl.
       rewrite H2.
       rewrite subst_closed.
       ++ reflexivity.
       ++ assumption.
  -- rewrite eqb_neq in Heqx. 
     simpl.
     assert (H2: (x =? s)%string  = false). { rewrite eqb_neq. assumption. }
     rewrite H2.
     destruct (String.eqb x1 s) eqn: Heqx1.
     + rewrite eqb_eq in Heqx1. rewrite Heqx1.
       simpl.
       assert (H3: (s =? s)%string  = true). { rewrite eqb_eq. reflexivity. }
       rewrite H3. 
       rewrite subst_closed.
       ++ reflexivity.
       ++ assumption.
     + simpl.
       assert (H3: (x =? s)%string  = false). { rewrite eqb_neq. assumption. }
       rewrite H3.
       assert (H4: (x1 =? s)%string  = false). { assumption. }
       rewrite H4.
       reflexivity.
- simpl. rewrite IHt1. rewrite IHt2. reflexivity.
- simpl.
  destruct (String.eqb x s) eqn: Heqx.
  -- rewrite eqb_eq in Heqx. rewrite Heqx.
     simpl.
     destruct (String.eqb x1 s) eqn: Heqx1.
     + simpl.
       assert (H2: (s =? s)%string  = true). { rewrite eqb_eq. reflexivity. }
       rewrite H2. reflexivity.
     + simpl.
       assert (H2: (s =? s)%string  = true). { rewrite eqb_eq. reflexivity. }
       rewrite H2. reflexivity.
  -- rewrite eqb_neq in Heqx.
     simpl.
     destruct (String.eqb x1 s) eqn: Heqx1.
     + simpl.
       assert (H2: (x =? s)%string  = false). { rewrite eqb_neq. assumption. }
       rewrite H2. reflexivity.
     + simpl.
       assert (H2: (x =? s)%string  = false). { rewrite eqb_neq. assumption. }
       rewrite H2.
       rewrite IHt. reflexivity.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl.
  rewrite IHt1.
  rewrite IHt2.
  rewrite IHt3.
  reflexivity.
- simpl.
  rewrite IHt1.
  rewrite IHt2.
  reflexivity.
- simpl. rewrite IHt. reflexivity.
- simpl. rewrite IHt. reflexivity.
Qed.

Lemma msubst_closed: forall t, closed t -> forall ss, msubst ss t = t.
Proof.
intros.
induction ss.
- simpl. reflexivity.
- destruct a. simpl.
  apply subst_closed with (x:=s) (t':=t0) in H. rewrite H.
  assumption.
Qed.

Fixpoint closed_env (env:env) :=
  match env with
  | nil => True
  | (x,t)::env' => closed t /\ closed_env env'
  end.
  
Lemma subst_msubst: forall env x v t, closed v -> closed_env env ->
    msubst env <{ [x:=v]t }> = <{ [x:=v] { msubst (drop x env) t } }> .
Proof.
intros.
generalize t.
induction env0; intros.
- reflexivity.
- destruct a. simpl.
  destruct (String.eqb s x) eqn: Heq.
  -- rewrite eqb_eq in Heq. rewrite Heq.
     rewrite duplicate_subst.
     apply IHenv0.
     + inversion H0. assumption.
     + assumption.
  -- rewrite eqb_neq in Heq.
     simpl. 
     inversion H0.
     pose proof (IHenv0 H2) as H3.
     rewrite swap_subst.
     + eauto.
     + unfold not in Heq. unfold not. intros. apply Heq. eauto.
     + assumption.
     + assumption.
Qed.

Lemma msubst_var: forall ss x, closed_env ss ->
   msubst ss (tm_var x) =
   match lookup x ss with
   | Some t => t
   | None => tm_var x
  end.
Proof.
intros.
induction ss.
- reflexivity.
- destruct a. simpl.
  destruct (eqb_spec s x).
  -- inversion H. apply msubst_closed. assumption.
  -- inversion H. apply IHss in H1. assumption.
Qed.

Lemma msubst_abs: forall ss x T t,
  msubst ss <{ \ x : T, t }> = <{ \x : T, {msubst (drop x ss) t} }>.
Proof.
intros.
generalize t.
induction ss; intros.
- reflexivity.
- destruct a. simpl.
  destruct (eqb_spec s x).
  -- apply IHss.
  -- simpl. apply IHss. 
Qed.

Lemma msubst_app : forall ss t1 t2,
    msubst ss <{ t1 t2 }> = <{ {msubst ss t1} ({msubst ss t2}) }>.
Proof.
intros.
generalize t2. generalize t1.
induction ss; intros.
- reflexivity.
- destruct a. simpl. eauto.
Qed.  
  
Lemma msubst_true : forall ss,
  msubst ss <{ true }> = <{ true }>.
Proof.
intros.
induction ss.
- reflexivity.
- destruct a. simpl. assumption.
Qed.
  
Lemma msubst_false : forall ss,
  msubst ss <{ false }> = <{ false }>.
Proof.
intros.
induction ss.
- reflexivity.
- destruct a. simpl. assumption.
Qed.

Lemma msubst_if : forall ss t1 t2 t3,
    msubst ss <{ if t1 then t2 else t3}> = 
      <{ if {msubst ss t1} then {msubst ss t2} else {msubst ss t3} }>.
Proof.
intros.
generalize t3. generalize t2. generalize t1.
induction ss; intros.
- reflexivity.
- destruct a. simpl. eauto.
Qed.  

Lemma msubst_pair : forall ss t1 t2,
    msubst ss <{ (t1, t2) }> = <{ ({msubst ss t1}, {msubst ss t2}) }>.
Proof.
intros.
generalize t2. generalize t1.
induction ss; intros.
- reflexivity.
- destruct a. simpl. eauto.
Qed.  
  
Lemma msubst_fst : forall ss t,
    msubst ss <{ t.fst }> = <{ {msubst ss t}.fst }>.
intros.
generalize t.
induction ss; intros.
- reflexivity.
- destruct a. simpl. eauto.
Qed.

Lemma msubst_snd : forall ss t,
    msubst ss <{ t.snd }> = <{ {msubst ss t}.snd }>.
intros.
generalize t.
induction ss; intros.
- reflexivity.
- destruct a. simpl. eauto.
Qed.

Lemma mupdate_lookup : forall (c : tass) (x:string),
    lookup x c = (mupdate empty c) x.            
Proof.
intros.
induction c.
- reflexivity.
- destruct a. simpl.
  destruct (eqb_spec s x).
  -- rewrite e. rewrite update_eq. reflexivity.
  -- rewrite update_neq.
     + assumption.
     + assumption.
Qed.

Lemma mupdate_drop : forall (c: tass) Gamma x x',
      mupdate Gamma (drop x c) x'
    = if String.eqb x x' then Gamma x' else mupdate Gamma c x'.
Proof.
intros.
destruct (eqb_spec x x').
- rewrite e.
  induction c.
  -- reflexivity.
  -- destruct a. simpl.
     destruct (eqb_spec s x').
     + assumption.
     + simpl. rewrite update_neq. assumption. assumption.
      
- induction c.
  -- reflexivity.
  -- destruct a. simpl. 
     destruct (eqb_spec s x').
     + destruct (eqb_spec s x).
       ++ rewrite <- e in n. rewrite <- e0 in n. exfalso. unfold not in n. apply n. reflexivity.
       ++ rewrite e. simpl. rewrite update_eq. rewrite update_eq. reflexivity. 
     + destruct (eqb_spec s x).
       ++ rewrite update_neq. assumption. assumption.
       ++ simpl. rewrite update_neq.
          +++ rewrite update_neq. assumption. assumption.
          +++ assumption.
Qed.

Lemma instantiation_domains_match: forall {c} {e},
    instantiation c e ->
    forall {x} {T},
      lookup x c = Some T -> exists t, lookup x e = Some t.
Proof.
intros.
induction H.
- inversion H0.
- destruct (String.eqb x0 x) eqn: Heq.
  -- rewrite eqb_eq in Heq. rewrite Heq. simpl.
     assert (H3: (x =? x)%string = true). { rewrite eqb_eq. reflexivity. }
     rewrite H3. exists v. reflexivity.
  -- simpl. rewrite Heq.
     apply IHinstantiation.
     simpl in H0. rewrite Heq in H0. assumption.
Qed.

Lemma instantiation_env_closed : forall c e,
  instantiation c e -> closed_env e.
Proof.
intros.
induction H.
- reflexivity.
- simpl. split.
  -- eapply typable_empty__closed. apply R_typable_empty. apply H0.
  -- assumption.
Qed.

Lemma instantiation_R : forall c e,
    instantiation c e ->
    forall x t T,
      lookup x c = Some T ->
      lookup x e = Some t -> R T t.
Proof.
intros.
induction H.
- inversion H0.
- destruct (String.eqb x0 x) eqn: Heq.
  -- rewrite eqb_eq in Heq. rewrite Heq in H0, H1. simpl in H0. simpl in H1.
     assert (H4: (x =? x)%string = true). { apply eqb_eq. reflexivity.  }
     rewrite H4 in H0, H1. inversion H0. inversion H1.
     rewrite H6 in H2. rewrite H7 in H2. assumption.
  -- simpl in H0. simpl in H1. rewrite Heq in H0, H1. eauto.
Qed.

Lemma instantiation_drop : forall c env,
    instantiation c env ->
    forall x, instantiation (drop x c) (drop x env).
Proof.
intros.
induction H.
- simpl. apply V_nil.
- simpl.
  destruct (String.eqb x0 x) eqn: Heq.
  -- assumption.
  -- apply V_cons.
     + assumption.
     + assumption.
     + assumption.
Qed.

Lemma multistep_App2 : forall v t t',
  value v -> (t -->* t') -> <{ v t }> -->* <{ v t' }>.
Proof.
intros.
induction H0.
- apply multi_refl.
- subst.
  eapply multi_step.
  -- apply ST_App2. assumption. apply H0.
  -- assumption.
Qed.

Lemma multistep_Pair1 : forall t1 t2 v,
  t1 -->* v -> (tm_pair t1 t2) -->* (tm_pair v t2).  
Proof with eauto.
  intros. induction H...
Qed.

Lemma multistep_Pair2 : forall t t' v,
  value v -> (t -->* t') -> (tm_pair v t) -->* (tm_pair v t').  
Proof with eauto.
  intros. induction H0...
Qed.

Lemma multistep_Fst : forall t t',
  t -->* t' -> (tm_fst t -->* tm_fst t').
Proof with eauto.
  intros. induction H...
Qed.

Lemma multistep_Snd : forall t t',
  t -->* t' -> (tm_snd t -->* tm_snd t').
Proof with eauto.
  intros. induction H...
Qed.

Lemma multistep_If : forall t1 t1' t2 t3,
  t1 -->* t1' -> <{if t1 then t2 else t3 }> -->* <{if t1' then t2 else t3 }>.
Proof with eauto.
  intros. induction H...
Qed.
  

Lemma test_drop : forall s c Gamma t,
  (s |-> t; mupdate Gamma c) = (s |-> t; mupdate Gamma (drop s c)).
Proof.
intros.
induction c.
- reflexivity.
- destruct a. simpl.
  destruct (eqb_spec s0 s).
  -- rewrite e. rewrite update_shadow. assumption.
  -- simpl. rewrite update_permute.
     + rewrite IHc. rewrite update_permute. 
       ++ reflexivity.
       ++ unfold not in *. intros. apply n. auto.
     + assumption.
Qed.

Lemma msubst_preserves_typing' : forall c e,
     instantiation c e ->
     forall Gamma t S, (mupdate Gamma c) |- t \in S ->
     Gamma |- { (msubst e t) } \in S.
Proof.
intros.
generalize dependent Gamma.
generalize dependent S.
induction t; intros.
- induction H.
  -- simpl in *. assumption.
  -- simpl in *.
     destruct (eqb_spec x s).
     + rewrite e0 in H0. inversion H0. subst.
       rewrite update_eq in H5. inversion H5.
       rewrite <- H4.
       pose proof (R_typable_empty H1) as H3.
       pose proof (typable_empty__closed v T H3) as H6.
       apply msubst_closed with (ss := e) in H6.
       rewrite H6.
       apply weakening_empty. assumption.
     + inversion H0. subst.
       rewrite update_neq in H5.
       ++ apply IHinstantiation. apply T_Var. assumption.
       ++ assumption.
- rewrite msubst_app.
  inversion H0. subst.
  apply T_App with (T2:=T2).
  -- apply IHt1. assumption.
  -- apply IHt2. assumption.
  
- admit. 
- rewrite msubst_true. inversion H0. apply T_True.  
- rewrite msubst_false. inversion H0. apply T_False.
- rewrite msubst_if.
  inversion H0. subst.
  apply T_If.
  -- apply IHt1. assumption.   
  -- apply IHt2. assumption.   
  -- apply IHt3. assumption.
- rewrite msubst_pair.
  inversion H0. subst.
  apply T_Pair.
  -- apply IHt1. assumption.   
  -- apply IHt2. assumption.   
- rewrite msubst_fst.
  inversion H0. subst.
  eapply T_Fst. apply IHt. apply H3.
- rewrite msubst_snd.
  inversion H0. subst.
  eapply T_Snd. apply IHt. apply H3.
Admitted.

(* book version *)
Lemma msubst_preserves_typing : forall c e,
     instantiation c e ->
     forall Gamma t S, (mupdate Gamma c) |- t \in S ->
     Gamma |- { (msubst e t) } \in S.
Proof.
    intros c e H. induction H; intros.
    simpl in H. simpl. auto.
    simpl in H2. simpl.
    apply IHinstantiation.
    eapply substitution_preserves_typing; eauto.
    apply (R_typable_empty H0).
Qed.

(* my version (incomplete *)
(*
Lemma msubst_R' : forall c env t T,
    (mupdate empty c) |- t \in T ->
    instantiation c env ->
    R T (msubst env t).
Proof.
intros c env T.
induction T.
- intros. rewrite msubst_var.
  -- inversion H. subst. rewrite <- mupdate_lookup in H3.
     pose proof (instantiation_domains_match H0 H3) as H4.
     destruct H4. rewrite H1.
     apply instantiation_R with (c:=c) (e:=env) (x:=s). assumption. assumption. assumption.
  -- apply instantiation_env_closed in H0. assumption.
- intros. rewrite msubst_app.
  inversion H. subst.
  apply IHT1 in H4.
  apply IHT2 in H6.
  -- inversion H4. destruct H2. pose proof (H3 (msubst env T2)) as H7. eauto.
  -- assumption.
  -- assumption.
- admit.
- intros. rewrite msubst_true. inversion H. simpl. split.
  -- apply T_True.
  -- split.
     ++ apply value_halts. apply v_true.
     ++ apply I.
- intros. rewrite msubst_false. inversion H. simpl. split.
  -- apply T_False.
  -- split.
     ++ apply value_halts. apply v_false.
     ++ apply I.
- intros. rewrite msubst_if.
  inversion H. subst.
  apply IHT1 in H5.
  apply IHT2 in H7.
  apply IHT3 in H8.
  admit. assumption. assumption. assumption.
- intros. rewrite msubst_pair. inversion H. subst.
  simpl. split.
  -- apply T_Pair.
     + eapply msubst_preserves_typing. apply H0. assumption.
     + eapply msubst_preserves_typing. apply H0. assumption.
  -- split.
     + apply IHT1 in H4.
       apply IHT2 in H6.
       apply R_halts in H4.
       apply R_halts in H6.
       destruct H4. destruct H1.
       destruct H6. destruct H3.
       unfold halts.
       ++ exists <{(x, x0)}>. split.
          +++ admit.
          +++ admit.
       ++ assumption.
       ++ assumption.
     + admit.      
- intros. rewrite msubst_fst. inversion H. subst.
  apply IHT in H3.
  -- simpl in H3. destruct H3. destruct H2. destruct H3. destruct H3. destruct H3. destruct H4. 
     admit. 
  -- assumption.     
- intros. rewrite msubst_snd. inversion H. subst.
  apply IHT in H3.
  -- simpl in H3. destruct H3. destruct H2. destruct H3. destruct H3. destruct H3. destruct H4. 
     admit. 
  -- assumption.             
Admitted.
*)

From Coq Require Import FunctionalExtensionality.

(* book version; completed by me *) 
Lemma msubst_R : forall c env t T,
    (mupdate empty c) |- t \in T ->
    instantiation c env ->
    R T (msubst env t).
Proof.
  intros c env0 t T HT V.
  generalize dependent env0.
  (* We need to generalize the hypothesis a bit before setting up the induction. *)
  remember (mupdate empty c) as Gamma.
  assert (forall x, Gamma x = lookup x c).
    intros. rewrite HeqGamma. rewrite mupdate_lookup. auto.
  clear HeqGamma.
  generalize dependent c.
  induction HT; intros.
  - (* T_Var *)
   rewrite H0 in H. destruct (instantiation_domains_match V H) as [t P].
   eapply instantiation_R; eauto.
   rewrite msubst_var. rewrite P. auto. eapply instantiation_env_closed; eauto.
  - (* T_Abs *)
    rewrite msubst_abs.
    (* We'll need variants of the following fact several times, so its simplest to
       establish it just once. *)
    assert (WT : empty |- \x : T2, {msubst (drop x env0) t1 } \in (T2 -> T1) ).
    { eapply T_Abs. eapply msubst_preserves_typing.
      { eapply instantiation_drop; eauto. }
      eapply context_invariance.
      { apply HT. }
      intros.
      unfold update, t_update. rewrite mupdate_drop. destruct (eqb_spec x x0).
      + auto.
      + rewrite H.
        clear - c n. induction c.
        simpl. rewrite false_eqb_string; auto.
        simpl. destruct a. unfold update, t_update.
        destruct (String.eqb s x0); auto. }
    unfold R. fold R. split.
       auto.
     split. apply value_halts. apply v_abs.
     intros.
     destruct (R_halts H0) as [v [P Q]].
     pose proof (multistep_preserves_R _ _ _ P H0).
     apply multistep_preserves_R' with (msubst ((x,v)::env0) t1).
       eapply T_App. eauto.
       apply R_typable_empty; auto.
       eapply multi_trans. eapply multistep_App2; eauto.
       eapply multi_R.
       simpl. rewrite subst_msubst.
       eapply ST_AppAbs; eauto.
       eapply typable_empty__closed.
       apply (R_typable_empty H1).
       eapply instantiation_env_closed; eauto.
       eapply (IHHT ((x,T2)::c)).
          intros. unfold update, t_update, lookup. destruct (String.eqb x x0); auto.
       constructor; auto.
  - (* T_App *)
    rewrite msubst_app.
    destruct (IHHT1 c H env0 V) as [_ [_ P1]].
    pose proof (IHHT2 c H env0 V) as P2. auto. (* fold R in P1. auto. *)
    
  - simpl. split.
    -- rewrite msubst_true. apply T_True.
    -- rewrite msubst_true.  split. apply value_halts. apply v_true. apply I.       
  - simpl. split.
    -- rewrite msubst_false. apply T_False.
    -- rewrite msubst_false.  split. apply value_halts. apply v_false. apply I.

  - rewrite msubst_if.
    destruct (IHHT1 c H env0 V) as [HT [Halts _]].
    pose proof (IHHT1 c H env0 V).
    pose proof (IHHT2 c H env0 V).
    pose proof (IHHT3 c H env0 V).
    destruct Halts as [bool [STM value]].
    assert (has_type empty <{if {msubst env0 t1} then {msubst env0 t2} else {msubst env0 t3} }> T1).
    {
      apply T_If. auto. apply (R_typable_empty H1). apply (R_typable_empty H2).
    }
    eapply multistep_preserves_R'. auto.
    apply multistep_If. apply STM.
    assert (has_type empty bool <{Bool}>).
    apply R_typable_empty.
    apply multistep_preserves_R with (msubst env0 t1); eauto.
    destruct bool; try solve_by_invert.
    eapply step_preserves_R'.
    apply T_If. auto. apply (R_typable_empty H1). apply (R_typable_empty H2).
    apply ST_IfTrue.
    auto.
    eapply step_preserves_R'.
    apply T_If. auto. apply (R_typable_empty H1). apply (R_typable_empty H2).
    apply ST_IfFalse.
    auto.        
  - rewrite msubst_pair. simpl. split.
    -- apply T_Pair.
       + eapply msubst_preserves_typing. apply V.
         pose proof (mupdate_lookup c) as H1.
         assert (H2: forall x, mupdate empty c x = Gamma x).
           intros. rewrite H. rewrite H1. reflexivity.
         apply functional_extensionality in H2.
         rewrite H2.
         assumption.
       + eapply msubst_preserves_typing. apply V.
         pose proof (mupdate_lookup c) as H1.
         assert (H2: forall x, mupdate empty c x = Gamma x).
           intros. rewrite H. rewrite H1. reflexivity.
         apply functional_extensionality in H2.
         rewrite H2.
         assumption.
    -- split.
       + unfold halts.
         pose proof (IHHT1 c H env0 V) as H1.
         pose proof (IHHT2 c H env0 V) as H2.
         apply R_halts in H1.
         apply R_halts in H2.
         destruct H1. destruct H0.
         destruct H2. destruct H2.
         exists <{ (x, x0) }>. split.
         assert (H4: <{ ({msubst env0 t1}, {msubst env0 t2}) }> -->* <{ (x, {msubst env0 t2} )}>).
         { apply multistep_Pair1. assumption. }
         assert (H5: <{ (x, {msubst env0 t2}) }> -->* <{ (x, x0 )}>).
         { apply multistep_Pair2. assumption. assumption. }
         eapply multi_trans.
         apply H4.
         apply H5.
         apply v_pair. assumption. assumption.
       + pose proof (IHHT1 c H env0 V) as H1.
         pose proof (IHHT2 c H env0 V) as H2.
         exists (msubst env0 t1), (msubst env0 t2). split.
         ++ apply multi_refl.
         ++ split. assumption. assumption.
  - rewrite msubst_fst.
    pose proof (IHHT c H env0 V) as H1. 
    destruct H1. destruct H1. destruct H2. destruct H2.  destruct H2.  destruct H3.
    destruct (R_halts H3) as [v1 [H11 H12]].
    destruct (R_halts H4) as [v2 [H21 H22]].
    assert (tm_fst (msubst env0 t0) -->* v1).
    {
      apply multi_trans with (tm_fst (tm_pair v1 v2)); eauto.
      apply multistep_Fst.
      apply multi_trans with (tm_pair x x0); auto.
      apply multi_trans with (tm_pair v1 x0).
      apply multistep_Pair1; auto.
      apply multistep_Pair2; auto.
    }
    assert (R T1 v1).
    {
      apply multistep_preserves_R with x; eauto.
    }
    apply multistep_preserves_R' with v1; eauto.
  - rewrite msubst_snd.
    pose proof (IHHT c H env0 V) as H1. 
    destruct H1. destruct H1. destruct H2. destruct H2.  destruct H2.  destruct H3.
    destruct (R_halts H3) as [v1 [H11 H12]].
    destruct (R_halts H4) as [v2 [H21 H22]].
    assert (tm_snd (msubst env0 t0) -->* v2).
    {
      apply multi_trans with (tm_snd (tm_pair v1 v2)); eauto.
      apply multistep_Snd.
      apply multi_trans with (tm_pair x x0); auto.
      apply multi_trans with (tm_pair v1 x0).
      apply multistep_Pair1; auto.
      apply multistep_Pair2; auto.
    }
    assert (R T2 v2).
    {
      apply multistep_preserves_R with x0; eauto.
    }
    apply multistep_preserves_R' with v2; eauto.
Qed.

Theorem normalization : forall t T, empty |- t \in T -> halts t.
Proof.
  intros.
  replace t with (msubst nil t) by reflexivity.
  apply (@R_halts T).
  apply (msubst_R nil); eauto.
  eapply V_nil.  
Qed.
           
         

                     
          
          
          
  
  
  
  
