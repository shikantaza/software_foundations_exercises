Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => (match b2 with
             | true => false
             | false => true
             end)
  | false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof.
simpl.
reflexivity.
Qed.

Example test_nandb2: (nandb false false) = true.
Proof.
simpl.
reflexivity.
Qed.

Example test_nandb3: (nandb false true) = true.
Proof.
simpl.
reflexivity.
Qed.

Example test_nandb4: (nandb true true) = false.
Proof.
simpl.
reflexivity.
Qed.

Definition andb (b1:bool) (b2:bool) : bool :=
match b1 with
| true => b2
| false => false
end.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb b1 (andb b2 b3).

Example test_andb31: (andb3 true true true) = true.
Proof.
simpl.
reflexivity.
Qed.

Example test_andb32: (andb3 false true true) = false.
Proof.
simpl.
reflexivity.
Qed.

Example test_andb33: (andb3 true false true) = false.
Proof.
simpl.
reflexivity.
Qed.

Example test_andb34: (andb3 true true false) = false.
Proof.
simpl.
reflexivity.
Qed.

Definition mult (m n : nat) : nat :=
match m with
| 0 => 0
| S n' => n + (mult n n')
end.

Compute mult 4 3.

Fixpoint factorial (n:nat) : nat :=
match n with
| 0 => 1
| 1 => 1
| (S n') => mult n (factorial n')
end.

Compute factorial 8.

Example test_factorial1: (factorial 3) = 6.
Proof.
simpl.
reflexivity.
Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof.
simpl.
reflexivity.
Qed.

Definition negb (b : bool) : bool :=
match b with
| true => false
| false => true
end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

(* fixpoint version *)
Fixpoint ltb' (n m : nat) : bool :=
match n, m with
| 0, 0 => false
| 0, _ => true
| _, 0 => false
| S n', S m' =>  ltb' n' m'
end.

(* non-fixpoint version, using previously-defined functions *)
Definition ltb (n m : nat) : bool :=
andb (leb n m) (negb (eqb n m)).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof.
simpl.
reflexivity.
Qed.

Example test_ltb2: (ltb 2 4) = true.
Proof.
simpl.
reflexivity.
Qed.

Example test_ltb3: (ltb 4 2) = false.
Proof.
simpl.
reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
intros n m o.
intros H1.
intros H2.
rewrite -> H1.
rewrite <- H2.
reflexivity.
Qed.

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
intros p.
rewrite <- mult_n_Sm.
rewrite <- mult_n_O.
simpl.
reflexivity.
Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
intros n.
destruct n as [|n'] eqn:E.
- reflexivity.
- reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
intros b c.
destruct b eqn:Eb.
simpl.
intro H.
assumption.
simpl.
intro H.
discriminate.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
intros n.
destruct n eqn:En.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
intros f.
intros H.
intros b.
rewrite H with b.
rewrite H with b.
reflexivity.
Qed.

Theorem identity_fn_applied_twice' :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
intros f.
intros H.
intros b.
rewrite H with b.
rewrite H with (negb b).
destruct b.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
intros b c.
intros H.
destruct b.
simpl in H.
rewrite H.
reflexivity.
simpl in H.
assumption.
Qed.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m:bin) : bin :=
match m with
| Z => B1 Z
| B0 n => B1 n
| B1 Z => B0 (B1 Z)
| B1 (B0 n) => B0 (B1 n)
| B1 (B1 n) => B0 (B0 (incr n))
end.

Compute incr Z.
Compute incr (incr Z).
Compute incr (incr (incr Z)).
Compute incr (incr (incr (incr Z))).
Compute incr (incr (incr (incr (incr Z)))).
Compute incr (incr (incr (incr (incr (incr Z))))).
Compute incr (incr (incr (incr (incr (incr (incr Z)))))).
Compute incr (incr (incr (incr (incr (incr (incr (incr Z))))))).

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof.
simpl.
reflexivity.
Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof.
simpl.
reflexivity.
Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof.
simpl.
reflexivity.
Qed.

Fixpoint bin_to_nat (m:bin) : nat :=
match m with
| Z => O
| B0 n => 2 * (bin_to_nat n)
| B1 n => (2 * (bin_to_nat n)) + 1
end.

Compute (bin_to_nat Z).
Compute (bin_to_nat (B1 Z)).
Compute (bin_to_nat (B0 (B1 Z))).
Compute (bin_to_nat (B1 (B1 Z))).
Compute (bin_to_nat (B0 (B0 (B1 Z)))).
Compute (bin_to_nat (B1 (B0 (B1 Z)))).
Compute (bin_to_nat (B0 (B1 (B1 Z)))).
Compute (bin_to_nat (B1 (B1 (B1 Z)))).
Compute (bin_to_nat (B0 (B0 (B0 (B1 Z))))).

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof.
simpl.
reflexivity.
Qed.

Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof.
simpl.
reflexivity.
Qed.

Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof.
simpl.
reflexivity.
Qed.























