Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Tactics.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
intros.
split.
induction m.
rewrite add_0_r in H.
assumption.
apply IHm.
rewrite <- plus_n_Sm in H.
discriminate.
rewrite add_comm in H.
induction n.
rewrite add_0_r in H.
assumption.
apply IHn.
rewrite <- plus_n_Sm in H.
discriminate.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
intros.
apply and_exercise in H.
destruct H.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
intros.
destruct H as [_ Hq].
apply Hq.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  split.
  apply HP.
  apply HQ.
  apply HR.
Qed.

Fact not_implies_our_not : forall (P:Prop),
  not P -> (forall (Q:Prop), P -> Q).
Proof.
intros.
contradiction.
Qed.

Theorem zero_not_one : 0 <> 1.
Proof.
unfold not.
intros contra.
discriminate contra.
Qed.

Theorem not_False :
  not False.
Proof.
unfold not.
intros.
apply H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\  not P) -> Q.
Proof.
intros.
destruct H.
contradiction.
Qed.

(*
  Write an informal proof of double_neg:
  Theorem: P implies ~~P, for any proposition P.

  Let P be true. Then, ~~P is not (not true) = not false = true = P.
  Let P be false. Then, ~~P is not (not false) = not true = false = P
  Qed.
*)

Theorem double_neg : forall (P : Prop), P -> not (not P).
Proof.
intros.
unfold not.
intros.
exact (H0 H).
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (not Q -> not P).
Proof.
intros.
unfold not.
intros.
apply H in H1.
contradiction.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  not (P /\ not P).
Proof.
intros.
unfold not.
intros.
destruct H.
apply H0 in H.
apply H.
Qed.

(*
  Write an informal proof (in English) of the proposition ∀ P : Prop, ~(P ∧ ¬P)

  If P is true, ~P is false, and therefore (P /\ ~P) = (true /\ false) is false.
  If P is false, ~P is true, and therefore, (P /\ ~P) = (false /\ true) is false.
  Qed.

*)

Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.
  
Theorem disc : forall n, not (O = S n).
Proof.
intros.
unfold not.
intros.
assert (H1: disc_fn O). { simpl. apply I. }
rewrite H in H1.
simpl in H1.
apply H1.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
intros.
split.

intros.
split.
destruct H.
left.
apply H.
destruct H.
right.
apply H.
destruct H.
left.
apply H.
destruct H.
right.
apply H0.

intros.
destruct H.
destruct H0.
left.
apply H0.
destruct H.
left.
apply H.
right.
split.
apply H.
apply H0.
Qed.

From Coq Require Import Setoids.Setoid.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> not (exists x, not (P x)).
Proof.
intros.
unfold not.
intros.
destruct H0.
pose proof (H x) as H2.
apply (H0 H2).
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
intros.
split.

intros.
destruct H.
destruct H.
left.
exists x.
apply H.
right.
exists x.
apply H.

intros.
destruct H.
destruct H.
exists x.
left.
apply H.
destruct H.
exists x.
right.
apply H.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  
  intros.
  induction l.
  exfalso.
  cbn in H.
  apply H.
  cbn in H.
  destruct H.
  exists x.
  split.
  apply H.
  cbn.
  left.
  reflexivity.
  pose proof (IHl H) as H1.
  simpl In.
  destruct H1.
  exists x0.
  split.
  destruct H0.
  apply H0.
  right.
  destruct H0.
  apply H1.
  
  intros.
  destruct H.
  destruct H.
  induction l.
  exfalso.
  cbn in H0.
  apply H0.
  cbn in H0.
  destruct H0.
  cbn.
  left.
  rewrite <- H0 in H.
  apply H.
  cbn.
  right.
  apply (IHl H0).
  Qed.
  
Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  intros.
  split.
  cbn.
  intros.
  right.
  apply H.
  intros.
  cbn.
  cbn in H.
  destruct H.
  exfalso.
  apply H.
  apply H.
  
  intros.  
  split.
  intros.
  cbn.
  cbn in H.
  destruct H.
  left.
  left.
  apply H.
  pose proof (IH l'0 a) as H1.
  destruct H1.
  apply H0 in H.
  destruct H.
  left.
  right.
  apply H.
  right.
  apply H.
  
  intros.
  cbn.
  destruct H.
  cbn in H.
  destruct H.
  left.
  apply H.
  right.
  pose proof (IH l'0 a) as H1.
  destruct H1.
  apply H1.
  left.
  apply H.
  pose proof (IH l'0 a) as H1.
  destruct H1.
  right.
  apply H1.
  right.
  apply H.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
match l with
| [] => True
| x :: l' => (P x) /\ All P l'
end. 

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
intros.
split.

intros.
induction l.
simpl.
apply I.
simpl.
split.
pose proof (H x) as H1.
apply H1.
simpl.
left.
reflexivity.
apply IHl.
intros.
pose proof (H x0) as H2.
simpl In in H2.
apply H2.
right.
apply H0.

intros.
induction l.
simpl in H0.
exfalso.
apply H0.
simpl All in H.
simpl In in H0.
destruct H.
destruct H0.
rewrite H0 in H.
apply H.
apply IHl.
apply H1.
apply H0.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun x => if (even x) then (Peven x) else (Podd x).
  
Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
intros.
unfold combine_odd_even.
destruct (even n) eqn: E1.
apply H0.
assert (H1: even n = true -> odd n = false). {
intros.
unfold odd.
rewrite H1.
reflexivity.
}
apply (H1 E1).
assert (H1: even n = false -> odd n = true). {
intros.
unfold odd.
rewrite H1.
reflexivity.
}
apply H.
apply (H1 E1).
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
intros.
unfold combine_odd_even in H.
destruct (even n) eqn: E1.
assert (H1: even n = true -> odd n = false). {
intros.
unfold odd.
rewrite H1.
reflexivity.
}
pose proof (H1 E1) as H2.
rewrite H0 in H2.
discriminate.
apply H.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
intros.
unfold combine_odd_even in H.
destruct (even n) eqn: E1.
apply H.
assert (H1: even n = false -> odd n = true). {
intros.
unfold odd.
rewrite H1.
reflexivity.
}
pose proof (H1 E1) as H2.
rewrite H0 in H2.
discriminate.
Qed.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Theorem app_nil_l : forall (X:Type), forall l:list X,
  [] ++ l = l.
Proof.
intros.
induction l.
simpl.
reflexivity.
cbn.
reflexivity.
Qed.

Lemma rev1 : forall {X : Type} (l l1 l2 : list X),
  rev_append l (l1 ++ l2) = (rev_append l l1) ++ l2.
Proof.
intros.
generalize dependent l1.
induction l.
intros.
cbn.
reflexivity.
intros.
cbn.
pose proof (IHl (x :: l1)) as H.
assert (H2: (x :: l1) ++ l2 = x :: l1 ++ l2). { reflexivity. }
rewrite H2 in H.
rewrite H.
reflexivity.
Qed.

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
intros.
apply functional_extensionality.
unfold tr_rev.
induction x.
simpl.
reflexivity.
cbn.
assert (H: [x] = [ ] ++ [x]). { reflexivity. }
rewrite H.
pose proof (rev1 x0 [] [x]) as H1.
rewrite H1.
rewrite <- IHx.
rewrite app_nil_l.
reflexivity.
Qed.

Lemma even_double : forall k, even (double k) = true.
Proof.
intros.
induction k.
simpl.
reflexivity.
simpl.
apply IHk.
Qed.

Lemma double_plus : forall n, double n = n + n .
Proof.
intros.
induction n.
simpl.
reflexivity.
rewrite <- plus_n_Sm.
rewrite plus_Sn_m.
rewrite <- IHn.
simpl.
reflexivity.
Qed.

Require Import Lia.

Lemma succ_even_not_even: forall n, even n = true -> even (S n) = false.
Proof.
intros.
induction n.
simpl.
reflexivity.
destruct (even n) eqn: E1.
assert (H1: true = true). { reflexivity. }
pose proof (IHn H1) as H2.
rewrite H in H2.
exfalso.
discriminate.
simpl.
apply E1.
Qed.

Lemma succ_not_even_even: forall n, even n = false -> even (S n) = true.
intros.
induction n.
discriminate.
simpl.
destruct (even n) eqn: E1.
reflexivity.
assert (H1: false = false). { reflexivity. }
pose proof (IHn H1) as H2.
rewrite H in H2.
exfalso.
discriminate.
Qed.

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
induction n.
simpl.
exists 0.
simpl.
reflexivity.
destruct IHn.
destruct (even n) eqn: E1.
rewrite H.
pose proof (succ_even_not_even (double x)) as H1.
rewrite H in E1.
pose proof (H1 E1) as H2.
rewrite H2.
exists x.
reflexivity.
pose proof (succ_not_even_even n) as H1.
pose proof (H1 E1) as H2.
rewrite H2.
rewrite H.
exists (x+1).
repeat rewrite double_plus.
lia.
Qed.

Lemma even_double_conv' : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
intros.
induction n.
simpl.
exists 0.
simpl.
reflexivity.
destruct (even n) eqn: E1.
pose proof (even_S n) as H.
rewrite E1 in H.
rewrite H.
simpl.
destruct IHn.
rewrite H0.
exists x.
reflexivity.
pose proof (even_S n) as H.
rewrite E1 in H.
rewrite H.
simpl.
destruct IHn.
rewrite H0.
exists (x+1).
repeat rewrite double_plus.
lia.
Qed.

Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
intros.
split.
intros.
split.
unfold andb in H.
destruct b1.
reflexivity.
discriminate.
unfold andb in H.
destruct b1.
apply H.
discriminate.
intros.
destruct H.
unfold andb.
rewrite H.
apply H0.
Qed.

Theorem orb_true_iff : forall b1 b2, 
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
intros.
split.
intros.
unfold orb in H.
destruct b1.
left.
reflexivity.
right.
apply H.
intros.
destruct H.
unfold orb.
rewrite H.
reflexivity.
unfold orb.
destruct b1.
reflexivity.
apply H.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H. (* note implicit destruct b here *)
  - (* b = true *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
split.

intros H1.
pose proof (eqb_eq x y) as H2.
destruct H2.
pose proof (contrapositive (x = y) ((x =? y) = true)) as H3.
pose proof (H3 H0) as H4.
rewrite <- not_true_iff_false in H1.
pose proof (H4 H1) as H5.
apply H5.

intros.
rewrite <- not_true_iff_false.
intros H1.
apply eqb_eq in H1.
contradiction.
Qed.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
match l1, l2 with
| [], [] => true
| [], _ => false
| _, [] => false
| x1 :: l1', x2 :: l2' => (andb (eqb x1 x2) (eqb_list eqb l1' l2'))
end.

Compute (eqb_list eqb [1;2;3] [1;2;3]).

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
intros b c.
destruct b eqn:Eb.
simpl.
intro H.
reflexivity.
intros.
discriminate.
Qed.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
intros A eqb H.
induction l1.
destruct l2.
simpl.
split.
intros.
reflexivity.
intros.
reflexivity.
simpl.
split.
intros.
discriminate.
intros.
discriminate.
intros.
split.
intros.
destruct l2.
discriminate.
simpl in H0.

pose proof (andb_true_elim1 (eqb x x0) (eqb_list eqb l1 l2)) as H1.
pose proof (H1 H0) as H2.
pose proof (H x x0) as H3.
destruct H3 as [H4 _].
pose proof (H4 H2) as H5.
rewrite H5.
apply f_equal.
clear H1 H2 H4 H5.

pose proof (andb_true_elim2 (eqb x x0) (eqb_list eqb l1 l2)) as H1.
pose proof (H1 H0) as H2.
pose proof (IHl1 l2) as H3.
destruct H3 as [H4 _].
apply (H4 H2).

intros.
rewrite <- H0.
simpl.
pose proof (H x x) as H1.
pose proof (IHl1 l1) as H2.
destruct H1 as [H3 H4].
destruct H2 as [H5 H6].
rewrite H4.
simpl.
rewrite H6.
reflexivity.
reflexivity.
reflexivity.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
intros.
split.
intros.
induction l.
simpl.
apply I.
simpl.
split.
simpl forallb in H.
pose proof (andb_true_elim1 (test x) (forallb test l)) as H1.
apply (H1 H).
apply IHl.
simpl forallb in H.
pose proof (andb_true_elim2 (test x) (forallb test l)) as H1.
apply (H1 H).

intros.
induction l.
simpl.
reflexivity.
simpl.
simpl All in H.
destruct H.
pose proof (IHl H0) as H1.
rewrite H.
rewrite H1.
simpl.
reflexivity.
Qed.

(*
  Q: Are there any important properties of the function forallb which are not captured  
  by this specification?
  A: It doesn't capture the fact that forallb is decidable.
*)

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ not P.
Proof.
intros p [] H.
left.
rewrite H.
reflexivity.
right.
rewrite H.
intros contra.
discriminate contra.
Qed.

Theorem restricted_excluded_middle' : forall P b,
  (P <-> b = true) -> P \/ not P.
Proof.
intros.
destruct b.
left.
rewrite H.
reflexivity.
right.
rewrite H.
intros contra.
discriminate contra.
Qed.

Theorem excluded_middle_irrefutable: forall (P:Prop),
  not (not (P \/ not P)).
Proof.
unfold not.
intros.
apply H.
right.
intros.
destruct H.
left.
apply H0.
Qed.

Definition excluded_middle := forall P : Prop,
  P \/ not P.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    not (exists x, not (P x)) -> (forall x, P x).
Proof.
intros.
unfold excluded_middle in H.
pose proof (H (P x)) as H1.
destruct H1.
apply H1.
unfold not in H0.
elim H0.
unfold not in H1.
exists x.
apply H1.
Qed.

(* to verify transitivity of <-> (needed for next exercise *)
Theorem test: forall P Q R : Prop, (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
intros.
split.
destruct H.
destruct H0.
intros.
exact (H0 (H H3)).
intros.
destruct H.
destruct H0.
exact (H2 (H3 H1)).
Qed.

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P:Prop,
  (not (not P)) -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  not((not P) /\ (not Q)) -> P \/ Q.

Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> ((not P) \/ Q).

Lemma test_cls : forall P Q : Prop,
  (P \/ ~P) -> (P -> Q) -> (~P \/ Q).
Proof.
intros.
destruct H.
right.
apply (H0 H).
left.
apply H.
Qed.

Theorem test1 : forall A B C : Prop, (A -> B -> C) <-> ((A /\ B) -> C).
intros.
split.

intros.
destruct H0.
exact ((H H0) H1).

intros.
apply H.
split.
apply H0.
apply H1.
Qed.

Lemma helper1 : forall A B C D E: Prop,
  (A->B)->(B->C)->(C->D)->(D->E)->(E->A)->((A<->B) /\ (B<->C) /\ (C<->D) /\ (D<->E)).
Proof.
intros.
split.

split.
apply H.
intros.
apply (H3 (H2 (H1 (H0 H4)))).

split.
split.
apply H0.
intros.
apply (H (H3 (H2 (H1 H4)))).

split.
split.
apply H1.
intros.
apply (H0 (H (H3 (H2 H4)))).

split.
apply H2.
intros.
apply (H1 (H0 (H (H3 H4)))).
Qed.

Theorem classical_axioms'':
  (de_morgan_not_and_not -> excluded_middle)-> 
  (excluded_middle -> double_negation_elimination) ->
  (double_negation_elimination -> implies_to_or) ->
  (implies_to_or -> peirce) ->
  (peirce -> de_morgan_not_and_not) ->
  ((de_morgan_not_and_not <-> excluded_middle) /\
   (excluded_middle <-> double_negation_elimination) /\
   (double_negation_elimination <-> implies_to_or) /\
   (implies_to_or <-> peirce)).
Proof.
apply (helper1 de_morgan_not_and_not excluded_middle double_negation_elimination implies_to_or peirce).
Qed.

Theorem classical_axioms':
  (peirce -> double_negation_elimination) ->
  (double_negation_elimination -> de_morgan_not_and_not) ->
  (de_morgan_not_and_not -> implies_to_or) ->
  (implies_to_or -> excluded_middle) ->
  (excluded_middle -> peirce) ->
  ((peirce <-> double_negation_elimination) /\
   (double_negation_elimination <-> de_morgan_not_and_not) /\
   (de_morgan_not_and_not <-> implies_to_or) /\
   (implies_to_or <-> excluded_middle)).
Proof.
apply (helper1 peirce double_negation_elimination de_morgan_not_and_not implies_to_or excluded_middle).
Qed.

Lemma demorgan_to_excluded_middle :
  de_morgan_not_and_not -> excluded_middle.
Proof.
intros.
unfold de_morgan_not_and_not in H.
unfold excluded_middle.
intros.
pose proof (H P (~P)) as H1.
apply H1.
unfold not.
intros.
destruct H0.
apply (H2 H0).
Qed.

Lemma excluded_middle_to_double_neg :
  excluded_middle -> double_negation_elimination.
Proof.
intros.
unfold excluded_middle in H.
unfold double_negation_elimination.
intros.
unfold not in H0.
pose proof (H P) as Hp.
destruct Hp.
apply H1.
exfalso.
unfold not in H1.
apply (H0 H1).
Qed.

Lemma excluded_middle_to_implies:
  excluded_middle -> implies_to_or.
Proof.
intros.
unfold excluded_middle in H.
unfold implies_to_or.
intros.
pose proof (H P) as H1.
destruct H1.
right.
apply (H0 H1).
left.
apply H1.
Qed.

Lemma implies_to_excluded_middle:
  implies_to_or -> excluded_middle.
Proof.
intros.
unfold excluded_middle.
unfold implies_to_or in H.
intros.
pose proof (H P P) as H1.
assert (H2: P->P). { intros. apply H0. }
pose proof (H1 H2) as H3.
destruct H3.
right.
apply H0.
left.
apply H0.
Qed.

Lemma demorgan_to_implies:
  de_morgan_not_and_not -> implies_to_or.
Proof.
intros.
apply excluded_middle_to_implies.
apply demorgan_to_excluded_middle.
apply H.
Qed.

Lemma implies_to_double_neg:
  implies_to_or -> double_negation_elimination.
Proof.
intros.
apply excluded_middle_to_double_neg.
apply implies_to_excluded_middle.
apply H.
Qed.

Lemma implies_to_peirce: 
  implies_to_or -> peirce.
Proof.
intros.
unfold implies_to_or in H.
unfold peirce.
intros.
pose proof (H (P->Q) P) as H1.
pose proof (H1 H0) as H2.
assert (H3: implies_to_or -> excluded_middle). { apply implies_to_excluded_middle. }
unfold implies_to_or in H3.
unfold excluded_middle in H3.
pose proof (H3 H) as H4.
destruct (H4 P).
apply H5.
apply H0.
intros.
exfalso.
apply (H5 H6).
Qed.

Lemma demorgan_to_peirce:
  de_morgan_not_and_not -> peirce.
Proof.
intros.
apply demorgan_to_implies in H.
apply implies_to_peirce in H.
apply H.
Qed.

Lemma demorgan_to_double_neg:
  de_morgan_not_and_not -> double_negation_elimination.
Proof.
intros.
apply demorgan_to_implies in H.
apply implies_to_double_neg.
apply H.
Qed.

Lemma excluded_middle_to_peirce:
  excluded_middle -> peirce.
Proof.
intros.
apply excluded_middle_to_implies in H.
apply implies_to_peirce in H.
apply H.
Qed.

Lemma implies_to_demorgan:
  implies_to_or -> de_morgan_not_and_not.
Proof.
intros.
assert (H1: excluded_middle). { apply implies_to_excluded_middle in H. apply H. }
assert (H2: double_negation_elimination). { apply excluded_middle_to_double_neg. apply H1. }

unfold de_morgan_not_and_not.
unfold implies_to_or in H.
unfold excluded_middle in H1.
unfold double_negation_elimination in H2.

intros.
pose proof (H (~P) Q) as H3.
assert (H4: forall P, P <-> ~~P). { intros. split. apply double_neg. apply (H2 P0). }
pose proof (H4 P) as H5.
rewrite <- H5 in H3.
apply H3.
intros.
pose proof (H1 Q) as H7.
destruct H7.
apply H7.
assert (H8: ~P /\ ~ Q). { split. apply H6.  apply H7. }
exfalso.
apply (H0 H8).
Qed.

Lemma excluded_middle_to_demorgan:
  excluded_middle -> de_morgan_not_and_not.
Proof.
intros.
assert (H1: implies_to_or). { apply excluded_middle_to_implies.  apply H. }
apply implies_to_demorgan in H1.
apply H1.
Qed.

Lemma peirce_to_double_neg:
  peirce -> double_negation_elimination.
Proof.
intros.
unfold peirce in H.
unfold double_negation_elimination.
intros.
pose proof (H P False) as H1.
apply H1.
intros.
unfold not in H0.
exfalso.
apply (H0 H2).
Qed.

Lemma helper : forall P Q : Prop, (P->Q) -> (~Q -> ~P).
Proof.
tauto.
Qed.

Lemma double_neg_to_demorgan:
  double_negation_elimination -> de_morgan_not_and_not.
Proof.
intros.
unfold double_negation_elimination in H.
unfold de_morgan_not_and_not.
intros.
assert (H1: (~(P \/ Q)) -> (~P /\ ~Q)). { tauto. }
pose proof (helper (~(P \/ Q)) (~P /\ ~Q)) as H2.
pose proof (H2 H1) as H3.
pose proof (H3 H0) as H5.
apply (H (P \/ Q)).
apply H5.
Qed.

Theorem classical_axioms:
  (peirce <-> double_negation_elimination) /\
  (double_negation_elimination <-> de_morgan_not_and_not) /\
  (de_morgan_not_and_not <-> implies_to_or) /\
  (implies_to_or <-> excluded_middle).
Proof.
apply (classical_axioms' peirce_to_double_neg double_neg_to_demorgan demorgan_to_implies implies_to_excluded_middle excluded_middle_to_peirce).
Qed.

Lemma test_axioms: peirce <-> excluded_middle.
Proof.
pose proof classical_axioms as H.
destruct H.
destruct H0.
destruct H1.
rewrite H0 in H.
rewrite H1 in H.
rewrite H2 in H.
apply H.
Qed.

