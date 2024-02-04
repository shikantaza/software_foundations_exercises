From LF Require Export Poly.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) -> [n;o] = [m;p].
Proof.
intros.
(* pose proof (H0 H) as H1.
assumption.
 *)
apply H0.
apply H.
Qed.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
intros.
pose proof (H0 n m) as H1.
pose proof (H1 H) as H2.
exact H2.
Qed.

Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
intros.
apply H0.
apply H.
apply H1.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->  l' = rev l.
Proof.
intros.
rewrite H.
rewrite rev_involutive.
reflexivity.
Qed.

(*
Q: Briefly explain the difference between the tactics apply and rewrite. What are the situations where both can usefully be applied?
A: Rewrite - replacing a term in a goal with another term if an hypothesis equating
both terms is available. Apply - If a hypothesis is of the form A->B, and the goal is B, making the goal A (since proving A would prove B, which was the original goal) 
Both can be usefully applied when the hypothesis is not an implication, but a proposition.

*)

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
intros.
rewrite H in H0.
apply H0.
Qed.

Lemma pred_eq : forall (n m : nat), n = m -> pred n = pred m.
Proof.
intros.
rewrite H.
reflexivity.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m -> n = m.
Proof.
intros.
(* pose proof (pred_eq (S n) (S m)) as H1.
pose proof (H1 H) as H2.
simpl pred in H2.
exact H2.
 *)
assert (H1: n = pred (S n)). { reflexivity. }
rewrite H1.
rewrite H.
simpl.
reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m -> n = m.
Proof.
intros.
injection H as Hmn.
apply Hmn.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
intros.
injection H as H1 H2.
rewrite H1.
rewrite H2.
reflexivity.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
intros.
rewrite H0 in H.
injection H as H1 H2.
rewrite H1.
rewrite H2.
reflexivity.
Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
intros.
discriminate.
Qed.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
intros n.
induction n.
destruct m.
intros.
reflexivity.
intros.
discriminate.
destruct m.
intros.
discriminate.
intros.
apply f_equal.
pose proof (IHn m) as H1.
apply H1.
simpl in H.
assumption.
Qed.

(*
   Q: Give a careful informal proof of eqb_true, being as explicit as possible about 
   quantifiers.
   A: 1) We do induction on n
      2) Show that the theorem is true for n=0, for all m
         a) two cases - m = 0, and m <> 0 (i.e., of the form S ..): 
              i) trivial to prove for m = 0
              ii) for m <> 0, we use discriminate (two different constructors can never 
                  create the same object)
      3) Now we assume it true for n, and have to prove that it's true for S n, for all m
         a) Again destruct on m:
              i) for m = 0, we use discrimiate now (comparing to S n)
              ii) for m <> 0,
                    - we need to show that if S n =? S m, then S n = S m, or n = m
                    - we thus assume that S n =? S m (call this hypothesis H)
                    - the goal is thus n = m
                    - we instantiate the induction hypothesis with the value 'm'
                    - this results in the hypothesis that if n =? m, then n = m, 
                    - this means that if we prove that n =? m, we are done
                    - so the goal becomes n =? m 
                    - simplifying the hypothesis H (S n =? S m) - which was the premise of the second goal, it becomes identical to the goal, QED.
   (this just seems to be explaining the steps in the formal proof )
*)

Definition double (n : nat) := n + n.

Require Import Lia.

Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *)
  intros m eq.
  destruct m as [| m'] eqn:E.
    + (* m = O *)
      discriminate eq.
    + (* m = S m' *)
  apply f_equal.
  apply IHn'. 
  simpl in eq. 
  injection eq as goal. 
  assert (Hn: n' + S n' = S (n' + n')). { lia. }
  assert (Hm: m' + S m' = S (m' + m')). { lia. }
  rewrite Hn in goal. rewrite Hm in goal.
  injection goal as H.
  clear Hn Hm.
  assert (Hn: double n' = n' + n'). { reflexivity. }
  assert (Hm: double m' = m' + m'). { reflexivity. }
  rewrite <- Hn in H. rewrite <- Hm in H.
  assumption.
Qed.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
intros.
assert (Hn: double n = n + n). { reflexivity. }
assert (Hm: double m = m + m). { reflexivity. }
rewrite <- Hn in H.
rewrite <- Hm in H.
pose proof (double_injective n m) as H1.
pose proof (H1 H) as H2.
assumption.
Qed.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
intros.
generalize dependent n.
induction l.
intros.
simpl.
reflexivity.
intros.
simpl.
destruct n.
discriminate.
simpl in H.
injection H as H1.
pose proof (IHl n) as H2.
pose proof (H2 H1) as H3.
assumption.
Qed.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
induction l.
intros.
simpl in H.
injection H.
intros.
rewrite <- H0.
rewrite <- H1.
simpl.
reflexivity.

intros.
destruct x as (a, b) eqn: E1 in H.
assert (H1: split ((a, b) :: l) = (a :: (fst (split l)), b :: (snd (split l)))).
{
cbn.
destruct (split l).
simpl.
reflexivity.
}
rewrite H in H1.
injection H1.
intros.
rewrite H0.
rewrite H2.
simpl.
rewrite <- E1.

destruct (split l) as (l1', l2') eqn: E2.
simpl.
pose proof (IHl l1' l2') as H3.
assert (H4: combine l1' l2' = l).
apply H3.
reflexivity.
rewrite H4.
reflexivity.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
induction b.
destruct (f true) eqn: H.
rewrite H.
assumption.
rewrite <- H.
destruct (f true) eqn: H1.
rewrite H1.
assumption.
destruct (f false) eqn: H2.
rewrite H1.
reflexivity.
assumption.
destruct (f false) eqn: H.
destruct (f true) eqn: H1.
assumption.
assumption.
rewrite H.
assumption.
Qed.

Lemma eq_impl_eqb : forall (n m : nat), n = m -> n =? m = true.
Proof.
intros.
rewrite H.
rewrite eqb_refl.
reflexivity.
Qed.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
intros.
destruct (n =? m) eqn: E1.
apply eqb_true in E1.
symmetry in E1.
apply eq_impl_eqb in E1.
symmetry.
assumption.
symmetry.
destruct (m =? n) eqn: E2.
apply eqb_true in E2.
symmetry in E2.
apply eq_impl_eqb in E2.
rewrite <- E1.
rewrite <- E2.
reflexivity.
reflexivity.
Qed.

(*
  Informal proof of above theorem:
  Case 1: 
    Let us assume that (n =? m) = true.
    This implies that n = m (from lemma proved earlier).
    This implies that m = n (by symmetry).
    This implies that m =? n (from lemma proved earlier), which was to be proved.
  Case 2:
    Let us assume that (n =? m) = false.
    Then we need to prove that (m =? n) is also false.
    Case 1:
      Let us assume that (m =? n) is true.
      This implies that m = n (from lemma proved earlier).
      By symmetry, this implies that n = m.
      This implies that (n =? m) is true.
      But this contradicts our assumption that (n =? m) is false.
      Thus, (m =? n) is false, which was to be proved.
    Case 2:
      Let us assume that (m =? n) is false.
      In which case, we are done, as this is what we had to prove.
*)

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
intros.
apply eqb_true in H.
apply eqb_true in H0.
rewrite <-H in H0.
apply eq_impl_eqb in H0.
assumption.
Qed.

Definition split_combine_statement : Prop :=
  forall X Y (l : list (X * Y)) (l1 : list X) (l2 : list Y),
    length l1 = length l2 -> split (combine l1 l2) = (l1, l2).

Lemma len_zero_impl_nil : forall X (l : list X),
  length l = 0 -> l = [ ].
Proof.
induction l.
intros.
reflexivity.
simpl length.
intros.
discriminate.
Qed.

Theorem split_combine : split_combine_statement.
Proof.
unfold split_combine_statement.
induction l1.
intros.
simpl.
simpl in H.
symmetry in H.
apply len_zero_impl_nil in H.
rewrite H.
reflexivity.
intros.
destruct l2.
discriminate.
simpl combine.
simpl in H.
injection H.
intros.
simpl.
pose proof ((IHl1 l2) H0) as H1.
rewrite H1.
reflexivity.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
induction l.
intros.
simpl in H.
discriminate.
intros.
destruct (test x0) eqn: E1.
simpl filter in H.
rewrite E1 in H.
injection H.
intros.
rewrite <- H1.
assumption.
simpl filter in H.
rewrite E1 in H.
pose proof (IHl lf) as H1.
exact (H1 H).
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
match l with
| [] => true
| x :: l' => match (test x) with
             | true => forallb test l'
             | false => false
             end
end.

Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.

Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.

Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.

Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
match l with
| [] => false
| x :: l' => match (test x) with
             | true => true
             | false => existsb test l'
             end
end.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.

Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.

Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.

Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun (x : X) => (negb (test x))) l).

Example test_existsb'_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.

Example test_existsb'_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.

Example test_existsb'_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.

Example test_existsb'_4 : existsb even [] = false.
Proof. reflexivity. Qed.

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl existsb.
destruct (test x) eqn: E1.
unfold existsb'.
simpl forallb.
rewrite E1.
simpl.
reflexivity.
rewrite IHl.
unfold existsb'.
simpl forallb.
rewrite E1.
simpl.
reflexivity.
Qed.

