From LF Require Export Basics.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
intros n.
induction n.
reflexivity.
rewrite <- IHn.
simpl.
rewrite IHn.
rewrite IHn.
reflexivity.
Qed.

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
intros n.
induction n.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
induction n.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite <- IHn.
reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
intros.
induction n.
simpl.
rewrite add_0_r.
reflexivity.
simpl.
rewrite IHn.
rewrite plus_n_Sm.
reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
intros n.
induction n.
simpl.
reflexivity.
simpl.
rewrite IHn.
rewrite plus_n_Sm.
reflexivity.
Qed.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
intros n.
induction n.
simpl.
reflexivity.
rewrite IHn.
rewrite negb_involutive.
simpl.
reflexivity.
Qed.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
intros.
rewrite add_assoc.
rewrite add_assoc.
assert (H: n + m = m + n).
{rewrite add_comm.
reflexivity.
}
rewrite H.
reflexivity.
Qed.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
intros.
induction n.
simpl.
rewrite <- mult_n_O.
reflexivity.
rewrite <- mult_n_Sm.
rewrite IHn.
simpl.
rewrite add_comm.
reflexivity.
Qed.

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
assumption.
Qed.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
intros.
destruct n.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
intros.
destruct b.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Lemma le_impl_plus_1_le : forall n m : nat,
  n <=? m = true -> S n <=? S m = true.
intros.
assumption.
Qed.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
intros.
induction p.
simpl.
assumption.
assert (H1: S p + n = n + S p). { rewrite add_comm. reflexivity. }
assert (H2: S p + m = m + S p). { rewrite add_comm. reflexivity. }
rewrite H1, H2.
rewrite <- plus_n_Sm.
rewrite <- plus_n_Sm.
assert (H3: p + n = n + p). {rewrite add_comm. reflexivity. }
assert (H4: p + m = m + p). {rewrite add_comm. reflexivity. }
rewrite <- H3, <- H4.
pose proof (le_impl_plus_1_le (p + n) (p + m)) as H5.
pose proof (H5 IHp) as H6.
assumption.
Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
intros.
simpl.
reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
intros.
simpl.
rewrite add_0_r.
reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
intros.
case b.
case c.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem mul_n_Sm : forall m n : nat,
  n * S m = n * m + n.
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite plus_n_Sm.
rewrite IHn.
rewrite plus_n_Sm.
rewrite add_assoc.
reflexivity.
Qed.

Require Import Lia.

(* TODO: see if this can be proved without using lia *)
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
intros.
induction p.
rewrite mul_0_r.
rewrite mul_0_r.
rewrite mul_0_r.
simpl.
reflexivity.
rewrite mul_n_Sm.
rewrite IHp.
rewrite mul_n_Sm.
rewrite mul_n_Sm.
rewrite add_assoc.
rewrite add_assoc.
lia.
Qed.

(* TODO: see if this can be proved without using lia *)
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
intros.
induction p.
repeat rewrite mul_0_r.
reflexivity.
repeat rewrite mul_n_Sm.
lia.
Qed.

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
intros.
induction n.
reflexivity.
assumption.
Qed.

Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
intros.
rewrite add_assoc.
rewrite add_assoc.
replace (n + m) with (m + n).
reflexivity.
rewrite add_comm.
reflexivity.
Qed.

(* copied from basics.v *)
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint equal_bin (a b : bin) : bool :=
match b with
| Z => match a with
       | Z => true
       | _ => false
       end
| B0 b' => match a with
           | Z => false
           | B0 a' => equal_bin a' b'
           | B1 a' => false
           end
| B1 b' => match a with
           | Z => false
           | B0 a' => false
           | B1 a' => equal_bin a' b'
           end
end.

Compute (equal_bin (B1 Z) (B1 Z)).

Definition neq_Z (b : bin) :=
match b with
| Z => false
| _ => true
end.
 
(* copied from basics.v *)
Fixpoint incr (m:bin) : bin :=
match m with
| Z => B1 Z
| B0 n => B1 n
| B1 n => B0 (incr n)
end.

Compute incr Z.
Compute incr (incr Z).
Compute incr (incr (incr Z)).
Compute incr (incr (incr (incr Z))).
Compute incr (incr (incr (incr (incr Z)))).
Compute incr (incr (incr (incr (incr (incr Z))))).
Compute incr (incr (incr (incr (incr (incr (incr Z)))))).
Compute incr (incr (incr (incr (incr (incr (incr (incr Z))))))).

(* copied from basics.v *)
Fixpoint bin_to_nat (m:bin) : nat :=
match m with
| Z => O
| B0 n => 2 * (bin_to_nat n)
| B1 n => (2 * (bin_to_nat n)) + 1
end.

Theorem bin_to_nat_pres_incr : forall m : bin,
  bin_to_nat (incr m) = S (bin_to_nat m).
Proof.
intros.
induction m.
simpl.
reflexivity.
simpl.
repeat rewrite add_0_r.
rewrite plus_n_Sm.
lia.
simpl.
repeat rewrite IHm.
lia.
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
match n with
| 0 => Z
| S n' => incr (nat_to_bin n')
end.

Compute (nat_to_bin 8).

Lemma n_b_incr : forall n : nat, nat_to_bin (S n) = incr (nat_to_bin n).
Proof.
intros.
induction n.
simpl.
reflexivity.
rewrite IHn.
simpl.
reflexivity.
Qed.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
induction n.
simpl.
reflexivity.
rewrite n_b_incr.
pose proof (bin_to_nat_pres_incr (nat_to_bin n)) as H.
rewrite H.
rewrite IHn.
reflexivity.
Qed.

Fixpoint normalize (b : bin) : bin :=
match b with
| Z => Z
| B0 b' => match (normalize b') with
           | Z => Z
           | b'' => B0 b''
           end
| B1 b' => B1 (normalize b')
end.

Compute normalize (B0 (B1 (B0 Z))).
Compute normalize (B0 (B1 (B0 (B0 Z)))).

Lemma norm_incr : forall b, normalize (incr b) = incr (normalize b).
Proof.
induction b.
easy.

assert (H: incr (B0 b) = B1 b). { reflexivity. }
rewrite H. clear H.
assert (H: normalize (B1 b) = B1 (normalize b)). { reflexivity. }
rewrite H. clear H.
assert (H: B1 (normalize b) = incr (B0 (normalize b))). { reflexivity. }
rewrite H. clear H.
simpl (normalize (B0 b)).
destruct (normalize b).
easy.
easy.
easy.

simpl incr.
cbn.
rewrite IHb.
destruct b.
easy.
rewrite <- IHb.
easy.
easy.
Qed.

Lemma twice_n_eq_b0 : forall n, nat_to_bin (2 * n) = normalize (B0 (nat_to_bin n)).
Proof.
induction n.
easy.
rewrite n_b_incr.
assert (H: B0 (incr (nat_to_bin n)) = incr (incr (B0 (nat_to_bin n)))). { reflexivity. }
rewrite H. clear H.
pose proof (norm_incr (incr (B0 (nat_to_bin n)))) as H.
rewrite H. clear H.
pose proof (norm_incr (B0 (nat_to_bin n))) as H.
rewrite H. clear H.
rewrite <- IHn.
rewrite <- n_b_incr.
rewrite <- n_b_incr.
assert (H: 2 * S n = S (S (2 * n))). { lia. }
rewrite H. reflexivity.
Qed.

(* looks like this can be simplified further,
per StackOverflow forum post *)
Lemma norm_idem : forall b, normalize b = normalize (normalize b).
Proof.
induction b; cbn.
- easy.
- destruct b.
  + easy.
  + destruct (normalize (B0 b)).
    * easy.
    * cbn in *.
     now rewrite <- IHb.
    * cbn. now rewrite IHb.
  + cbn in *.
   now rewrite IHb.
- now rewrite <- IHb.
Qed.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
induction b.
simpl.
reflexivity.

simpl bin_to_nat.
rewrite add_0_r.

assert (H: bin_to_nat b + bin_to_nat b = 2 * bin_to_nat b). { lia. }
rewrite H. clear H.
pose proof (twice_n_eq_b0 (bin_to_nat b)) as H.
rewrite H. clear H.
rewrite IHb.
simpl normalize.
rewrite <- norm_idem.
reflexivity.

simpl bin_to_nat.
rewrite add_0_r.
simpl normalize.

assert (H: bin_to_nat b + bin_to_nat b + 1 = S (2 * bin_to_nat b)). { lia. }
rewrite H. clear H.
simpl nat_to_bin.
rewrite add_0_r.

assert (H: bin_to_nat b + bin_to_nat b = 2 * bin_to_nat b). { lia. }
rewrite H. clear H.
pose proof (twice_n_eq_b0 (bin_to_nat b)) as H.
rewrite H. clear H.
rewrite IHb.
simpl normalize.
rewrite <- norm_idem.

destruct (normalize b).
easy.
easy.
easy.
Qed.

