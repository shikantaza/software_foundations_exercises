From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.
  
Check string_dec.

Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof.
intros.
unfold eqb_string.
destruct string_dec.
- reflexivity.
- unfold not in n. exfalso. apply n. reflexivity.
Qed.

Theorem eqb_string_true_iff : forall x y : string,
  eqb_string x y = true <-> x = y.
Proof.
intros.
split.
- intros.
  unfold eqb_string in H.
  destruct string_dec in H.
  -- assumption.
  -- exfalso. discriminate H.
- intros.
  rewrite H. symmetry. apply eqb_string_refl.
Qed.

Theorem eqb_string_false_iff : forall x y : string,
  eqb_string x y = false <-> x <> y.
Proof.
intros.
split.
- intros.
  unfold not.
  intros.
  rewrite H0 in H.
  rewrite <- eqb_string_refl in H.
  discriminate H.
- intros.
  unfold eqb_string.
  destruct string_dec.
  -- exfalso. unfold not in H. apply (H e).
  -- reflexivity.
Qed.

(* book version *)
Theorem eqb_string_false_iff' : forall x y : string,
  eqb_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.
  
Definition total_map (A : Type) := string -> A.  

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).  

Compute (t_empty 10) "abc"%string.

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
  
Example example_empty := (_ !-> false).

Compute (example_empty "abc"%string).

Notation "x '!->' v ';' m" := 
  (t_update m x v)
  (at level 100, v at next level, right associativity).
  
Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _ !-> false
  ).
  
Compute (examplemap' "bar"%string).
Compute (examplemap' "foo"%string).
Compute (examplemap' "abc"%string).

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof.
intros.
unfold t_empty. reflexivity.
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
intros.
unfold t_update.
rewrite <- eqb_string_refl.
reflexivity.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
intros.
unfold t_update.
rewrite <- eqb_string_false_iff in H.
rewrite H.
reflexivity.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
intros.
unfold t_update.
apply functional_extensionality.
intros.
unfold eqb_string.
destruct string_dec.
- reflexivity.
- reflexivity.
Qed.

Lemma eqb_stringP : forall x y : string,
  reflect (x = y) (eqb_string x y).
Proof.
intros.
apply iff_reflect.
split.
- rewrite eqb_string_true_iff. intros. assumption.
- rewrite eqb_string_true_iff. intros. assumption.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
intros.
unfold t_update.
apply functional_extensionality.
intros.
destruct (eqb_string x x0) eqn: Heq.
- rewrite eqb_string_true_iff in Heq.
  rewrite Heq. reflexivity.
- reflexivity.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
intros.
unfold t_update.
apply functional_extensionality.
intros.
destruct (eqb_string x1 x) eqn: Heq.
- rewrite eqb_string_true_iff in Heq.
  rewrite Heq in H.
  rewrite <- eqb_string_false_iff in H.
  rewrite H.
  reflexivity.
- reflexivity.
Qed.

Definition partial_map (A : Type) := total_map (option A).
Definition empty {A : Type} : partial_map A :=
  t_empty None.
Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '⊢>' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).  
  
Notation "x '⊢>' v" := (update empty x v)
  (at level 100).  
  
Example examplemap1 :=
  ("Church" ⊢> true ; "Turing" ⊢> false).  

Check examplemap1.
  
Compute (examplemap1 "Church").
Compute (examplemap1 "Turing").
Compute (examplemap1 "abc").

Lemma apply_empty : forall (A : Type) (x : string),
  @empty A x = None.  
intros.
reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x ⊢> v ; m) x = Some v.
intros.
unfold update.
rewrite t_update_eq.
reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 ⊢> v ; m) x1 = m x1.
intros.
unfold update.
rewrite t_update_neq.
- reflexivity.
- assumption.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x ⊢> v2 ; x ⊢> v1 ; m) = (x ⊢> v2 ; m).
Proof.
intros.
unfold update.
apply functional_extensionality.
intros.
rewrite t_update_shadow.
reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v ->
  (x ⊢> v ; m) = m.
Proof.
intros.
unfold update.
rewrite <- H.
rewrite t_update_same.
reflexivity.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 ⊢> v1 ; x2 ⊢> v2 ; m) = (x2 ⊢> v2 ; x1 ⊢> v1 ; m).
Proof.
intros.
unfold update.
apply functional_extensionality.
intros.
unfold t_update.
destruct (eqb_string x2 x1) eqn: Heq.
- rewrite eqb_string_true_iff in Heq.
  exfalso.
  unfold not in H.
  apply (H Heq). 
- destruct (eqb_string x1 x) eqn: Heq1.
  -- rewrite eqb_string_true_iff in Heq1.
     rewrite Heq1 in Heq.
     rewrite Heq.
     reflexivity.
  -- reflexivity.
Qed.

Definition inclusion {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

Lemma inclusion_update : forall (A : Type) (m m' : partial_map A)
                                (x : string) (vx : A),
  inclusion m m' ->
  inclusion (x ⊢> vx ; m) (x ⊢> vx ; m').
Proof.
intros.
unfold inclusion in H.
unfold inclusion.
intros.
unfold update.
unfold t_update.
destruct (eqb_string x x0) eqn: Heq.
- rewrite eqb_string_true_iff in Heq.
  rewrite <- Heq in H0.
  unfold update in H0.
  unfold t_update in H0.
  rewrite <- eqb_string_refl in H0.
  assumption.
- unfold update in H0.
  unfold t_update in H0.
  rewrite Heq in H0.
  pose proof (H x0 v) as H1.
  apply (H1 H0).
Qed.
