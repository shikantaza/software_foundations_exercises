Set Implicit Arguments.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.
From Coq Require Import Lists.List.

(* to prove the properties of doubly linked lists
   from Reynolds' paper *)

Inductive points_to : nat -> nat -> Prop :=
  | pr m n : m <> 0 -> points_to m n.

Inductive dlist : (list nat) -> nat -> nat -> nat -> nat -> Prop :=
  | dl_nil : forall i i' j j', 
               i = j ->
               i' = j' ->
               dlist nil i i' j j'
  | dl_cons : forall i i' k k' a alpha,
                (exists j, (points_to i a) /\ 
                            points_to (i+1) j /\ 
                            points_to (i+2) i' /\
                          (dlist alpha j i k k')) ->
                dlist (a :: alpha) i i' k k'.
                
Example dlist_example1 : forall i i' j j' a,
  (points_to i a) /\
   points_to (i+1) j /\
   points_to (i+2) i'/\
   i = j' <->
   dlist (a :: nil) i i' j j'.
Proof.
intros. split.
- intros. destruct H as [H1 [H2 [H3 H4]]].
  apply dl_cons.
  exists j.
  split.
  -- assumption.
  -- split.
     + assumption.
     + split.
       ++ assumption.
       ++ apply dl_nil. reflexivity. assumption.
- intros.
  inversion H. subst.
  destruct H6. destruct H0 as [H1 [H2 [H3 H4]]].
  inversion H4. subst.
  split.
  -- assumption.
  -- split.
     + assumption.
     + split. assumption. reflexivity.
Qed.

Example dlist_example2 : forall i i' k k' a b,
  dlist (a++b) i i' k k' <-> exists j j', dlist a i i' j j' /\ dlist b j j' k k'.
Proof.
intros.
split.
- intros.
  generalize dependent i'. generalize dependent i.
  induction a.
  -- intros. simpl in H. exists i, i'. split. apply dl_nil. reflexivity. reflexivity. assumption.
  -- intros. assert ((a :: a0) ++ b = a :: (a0 ++ b)). { rewrite app_comm_cons. reflexivity. }
     rewrite H0 in H. inversion H. subst.
     destruct H7.  destruct H1 as [H2 [H3 [H4 H5]]].
     pose proof ((IHa x i) H5) as H6.
     destruct H6. destruct H1. destruct H1.
     exists x0, x1.
     split.
     + apply dl_cons. exists x. split. assumption. split. assumption. split. assumption. assumption.
     + assumption.
- intros. destruct H. destruct H. destruct H.
  generalize dependent i'. generalize dependent i.
  induction a.
  -- intros. simpl in *. inversion H. subst. assumption.
  -- intros. inversion H. subst.
     destruct H7. destruct H1 as [H2 [H3 [H4 H5]]].
     pose proof ((IHa x1 i) H5).
     assert ((a :: a0) ++ b = a :: a0 ++ b). { rewrite app_comm_cons. reflexivity. }
     rewrite H6.
     apply dl_cons.
     exists x1. split. auto. split. auto. split. auto. auto.
Qed.

Example dlist_example3 : forall a b i i' k k',
  dlist (a ++ b::nil) i i' k k' <-> 
    exists j', dlist a i i' k' j' /\ points_to k' b /\ points_to (k'+1) k /\ points_to (k'+2) j'.    
Proof.
intros. split.
- intros. rewrite dlist_example2 in H. destruct H. destruct H. destruct H.
  inversion H0. subst. destruct H7. destruct H1 as [H2 [H3 [H4 H5]]].
  inversion H5. subst. exists x0. split. auto. split. auto. split. auto. auto.
- intros. destruct H. destruct H as [H1 [H2 [H3 H4]]].
  apply dlist_example2. exists k', x. split. auto.
  apply dl_cons. exists k. split. auto. split. auto. split. auto. apply dl_nil. reflexivity. reflexivity.
Qed.

Lemma dlist_example4_lemma : forall a i i' j,
  dlist a i i' j 0 -> a = nil.
Proof.
intros.
generalize dependent i'. generalize dependent i. induction a.
- intros. reflexivity.
- intros. exfalso. inversion H. subst.
  destruct H6. destruct H0 as [H1 [H2 [H3 H4]]].
  pose proof ((IHa x i) H4).
  rewrite H0 in H4. inversion H4. subst. inversion H1. unfold not in H0. apply H0. reflexivity.
Qed.

Example dlist_example4 : forall a i i' j j',
  dlist a i i' j j' ->
    (i = 0 -> (a = nil /\ j = 0 /\ i' = j')) /\
    (j' = 0 -> (a = nil /\ i' = 0 /\ i = j)) /\
    (i <> j -> a <> nil) /\
    (i' <> j' -> a <> nil).
Proof.
intros. split.
- intros. split. inversion H; subst.
  -- reflexivity.
  -- exfalso. destruct H1. destruct H0. inversion H0. unfold not in H2. apply H2. reflexivity.
  -- split.
     + inversion H; subst.
       ++ reflexivity.
       ++ exfalso. destruct H1. destruct H0. inversion H0. unfold not in H2. apply H2. reflexivity.
     + inversion H; subst.
       ++ reflexivity.
       ++ exfalso. destruct H1. destruct H0. inversion H0. unfold not in H2. apply H2. reflexivity.
- split.
  -- intros. subst. split.
     + generalize dependent i'. generalize dependent i. induction a.
       ++ intros. reflexivity.
       ++ intros. exfalso. inversion H. subst.
          destruct H6. destruct H0 as [H1 [H2 [H3 H4]]].
          pose proof ((IHa x i) H4).
          rewrite H0 in H4. inversion H4. subst. inversion H1. unfold not in H0. apply H0. reflexivity.
     + split.
       ++ generalize dependent i'. generalize dependent i. induction a.
          +++ intros. inversion H. auto.
          +++ intros. inversion H. subst. destruct H6. destruct H0 as [H1 [H2 [H3 H4]]].
              pose proof (IHa x i H4). rewrite H0 in H1. inversion H1. unfold not in H5.  exfalso.
              apply H5. reflexivity.
       ++ assert (a = nil). { eapply dlist_example4_lemma. apply H. } (* is there a way to remember proved goals? *)
          rewrite H0 in H. inversion H. auto.
  -- split.
     + intros. unfold not. intros.
       rewrite H1 in H. inversion H. subst. unfold not in H0. apply H0. reflexivity.
     + intros. unfold not in *. intros. rewrite H1 in H. inversion H. subst. apply H0. reflexivity.
Qed.

