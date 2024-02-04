(*
Lemma bin_add_cancel_left: forall a b c, b = c -> bin_add a b = bin_add a c.
Proof.
intros.
rewrite H. reflexivity.
Qed.
*)

(*
Lemma helper1 : forall a b, bin_add b (B0 a) = bin_add (bin_add b a) a.
Proof.
intros.
pose proof (bplus_assoc b a a) as H.
rewrite H. clear H.
pose proof (bin_add_cancel_left b (B0 a) (bin_add a a)) as H.
apply H. clear H.
exact (B0_eq_bin_add_b_b a).
Qed.

Lemma helper2 : forall a b, bin_add b (B1 a) = bin_add (incr (bin_add b a)) a.
Proof.
intros.
assert (H: B1 a = incr (B0 a)). { reflexivity. }
rewrite H. clear H.
pose proof (b_add_incr b a) as H.
rewrite <- H. clear H.
pose proof (bplus_assoc b (incr a) a) as H.
rewrite H. clear H.
pose proof (b_add_comm (incr a) a) as H.
rewrite H. clear H.
pose proof (b_add_incr a a) as H.
rewrite H. clear H.
pose proof (B0_eq_bin_add_b_b a) as H.
rewrite H. clear H.
reflexivity.
Qed.
*)

(*
Lemma incr_inj': forall a b, incr a = incr b -> a = b.
Admitted.
*)

(*
Lemma bin_add_eq : forall a b c, bin_add b a = bin_add c a -> b = c.
Proof.
induction a.
intros.
rewrite bplus_Z_r in H.
rewrite bplus_Z_r in H.
assumption.

intros.
pose proof (helper1 a b) as H1.
pose proof (helper1 a c) as H2.
rewrite H1 in H. rewrite H2 in H.
clear H1 H2.
pose proof (IHa (bin_add b a) (bin_add c a)) as H1.
pose proof (H1 H) as H2.
pose proof (IHa b c) as H3.
exact (H3 H2).

intros.
pose proof (helper2 a b) as H1.
pose proof (helper2 a c) as H2.
rewrite H1 in H. rewrite H2 in H.
clear H1 H2.
pose proof (IHa (incr (bin_add b a)) (incr (bin_add c a))) as H1.
pose proof (H1 H) as H2.
pose proof (IHa b c) as H3.
pose proof (incr_inj' (bin_add b a) (bin_add c a)) as H4.
exact (H3 (H4 H2)).
Qed.
*)

(*
Lemma incr_inj : forall b c, incr b = incr c -> b = c.
Proof.
intros.
pose proof (bin_add_one b) as H1.
pose proof (bin_add_one c) as H2.
rewrite <- H1 in H. clear H1.
rewrite <- H2 in H. clear H2.
remember (B1 Z) as a.
pose proof (bin_add_eq a b c) as H1.
exact (H1 H).
Qed.
*)

(*
Lemma incr_b_add_b_b : forall b, incr (bin_add b b) = B1 b.
Proof.
intros.
rewrite <- B0_eq_bin_add_b_b.
simpl incr.
reflexivity.
Qed.
*)

(*
Lemma incr_b_add_b_b' : forall b, incr (bin_add b b) = B1 b.
Proof.
induction b.
simpl.
reflexivity.

simpl.
assert (H: B1 b = incr (B0 b)). { reflexivity. }
rewrite H in IHb. clear H.
pose proof (incr_inj' (bin_add b b) (B0 b)) as H.
pose proof (H IHb) as H1.
rewrite H1.
reflexivity.

simpl.
rewrite IHb.
reflexivity.
Qed.
*)

Definition is_normalized (b : bin) : bool := equal_bin (normalize b) b.

Compute (is_normalized Z).

Compute bin_add (B0 Z) (B0 Z).
Compute bin_add (B1 (B0 Z)) (B1 (B0 Z)).

(* Don't think this can be proven. Not needed anyway.
Lemma B0_eq_bin_add_b_b : forall b, B0 b = bin_add b b.
Admitted.
*)

Fixpoint normalize'' (b : bin) : bin :=
match b with
| Z => Z
| B0 Z => Z
| B0 b' => match (normalize'' b') with
           | Z => Z
           | b'' => B0 b''
           end
| B1 b' => B1 (normalize'' b')
end.

(* from StackOverflow forum, for the slightly different
   version of normalize, with B0 Z => Z *) 
Lemma norm_idem' : forall b, normalize'' b = normalize'' (normalize'' b).
Proof.
induction b; cbn.
- easy.
- destruct b.
  + easy.
  + destruct (normalize'' (B0 b)).
    * easy.
    * cbn in *.
     now rewrite <- IHb.
    * cbn. now rewrite IHb.
  + cbn in *.
   now rewrite IHb.
- now rewrite <- IHb.
Qed.

(*
Fixpoint normalize3 (b : bin) : bin :=
match b with
| Z => Z
| B0 b' => match (normalize3 b') with
           | Z => Z
           | b'' => B0 b''
           end
| B1 b' => B1 (normalize3 b')
end.
*)

Lemma eq_impl_incr_eq : forall b c, b = c -> incr b = incr c.
intros. rewrite H. reflexivity. Qed.

Lemma helper1 : forall b, B1 Z = incr b -> normalize b = Z.
destruct b.
intros. reflexivity.
intros.
simpl incr in H.
pose proof (B1_inj Z b) as H1.
pose proof (H1 H) as H2.
rewrite H2.
simpl.
rewrite <- H2.
simpl.
reflexivity.
intros.
simpl incr in H.
exfalso.
discriminate H.
Qed.

Lemma incr_inj : forall b c, incr b = incr c -> normalize b = normalize c.
Proof.
induction b.

destruct c.
intros.
reflexivity.
intros.
simpl.
simpl incr in H.
pose proof ((B1_inj Z c) H) as H1.
rewrite <- H1.
simpl.
reflexivity.
intros.
simpl.
simpl incr in H.
exfalso.
discriminate H.

destruct c.
intros.
simpl incr in H.
pose proof ((B1_inj b Z) H) as H1.
rewrite H1.
simpl.
reflexivity.
intros.
simpl incr in H.
pose proof ((B1_inj b c) H) as H1.
rewrite H1.
reflexivity.
intros.
simpl incr in H.
exfalso.
discriminate H.

destruct c.
intros.
simpl incr in H.
exfalso.
discriminate H.
intros.
simpl incr in H.
exfalso.
discriminate H.
intros.
simpl incr in H.
pose proof ((B0_inj (incr b) (incr c)) H) as H1.
pose proof ((IHb c) H1) as H2.
simpl normalize.
rewrite H2.
reflexivity.
Qed.

Fixpoint bin_add' (b c : bin) : bin :=
match b with
| Z => c
| B0 b' => match c with
           | Z => B0 b'
           | B0 c' => B0 (bin_add' b' c')
           | B1 c' => B1 (bin_add' b' c')
           end
| B1 b' => match c with
           | Z => B1 b'
           | B0 c' => B1 (bin_add' b' c')
           | B1 c' => B0 (incr (bin_add' b' c'))
           end
end.

Definition eq_but_not_Z (b c : bin) : bool :=
match (equal_bin b c) with
| false => false
| true  => match b with
           | Z => false
           | _ => true
           end
end.

Compute eq_but_not_Z (B0 Z) (B1 Z).

Fixpoint bin_add (b c : bin) : bin :=
match (b, c) with
  | (_, Z)         => b 
  | (Z, _)         => c
  | (B0 b', B0 c') => B0 (bin_add b' c')
  | (B0 b', B1 c') => B1 (bin_add b' c')
  | (B1 b', B0 c') => B1 (bin_add b' c')
  | (B1 b', B1 c') => B0 (incr (bin_add b' c'))
end.

Fixpoint normalize' (b : bin) : bin :=
match b with
| Z => Z
| B0 b' => bin_add (normalize' b') (normalize' b')
| B1 b' => B1 (normalize' b')
end.

Compute bin_add (B1 (B1 Z)) (B1 (B0 (B1 Z))).
Compute bin_add (B0 (B1 (B0 Z))) (B1 Z).
Compute bin_add Z Z.
Compute bin_add (B0 Z) Z.

(* testing associativity *)
Compute (bin_add (bin_add (B0 (B1 Z)) (B1 (B1 Z))) (B1 Z)).
Compute (bin_add (B0 (B1 Z)) (bin_add (B1 (B1 Z)) (B1 Z))).

Lemma bplus_Z_r : forall b, bin_add b Z = b.
Proof.
induction b.
reflexivity.
reflexivity.
reflexivity.
Qed.

Lemma bplus_Z_l : forall b, bin_add Z b = b.
Proof.
induction b.
reflexivity.
reflexivity.
reflexivity.
Qed.

Lemma eq_impl_norm_eq: forall b c, b = c -> normalize b = normalize c.
intros. rewrite H. reflexivity. Qed. 

Lemma B0_inj : forall b c, B0 b = B0 c -> b = c.
Proof.
intros.
injection H.
intros.
assumption.
Qed.

Lemma B1_inj : forall b c, B1 b = B1 c -> b = c.
Proof.
intros.
injection H.
intros.
assumption.
Qed.

Lemma B0_eq_impl_eq : forall b c, b = c -> B0 b = B0 c.
Proof.
intros.
destruct b.
rewrite H. reflexivity.
rewrite H. reflexivity.
rewrite H. reflexivity.
Qed.

Lemma B1_eq_impl_eq : forall b c, b = c -> B1 b = B1 c.
Proof.
intros.
destruct b.
rewrite H. reflexivity.
rewrite H. reflexivity.
rewrite H. reflexivity.
Qed.

Lemma bin_add_one : forall b, bin_add b (B1 Z) = incr b.

intros.
induction b.

simpl.
reflexivity.

simpl.
rewrite bplus_Z_r.
reflexivity.

assert (H: bin_add (B1 b) (B1 Z) = B0 (incr (bin_add b Z))). { reflexivity. }
rewrite H. clear H.
rewrite bplus_Z_r.
simpl incr.


assert (H: bin_add (B1 b) (B1 Z) = B0 (incr (bin_add b Z))). {
reflexivity.
}
reflexivity.
Qed.

Lemma b_add_comm: forall b c, bin_add b c = bin_add c b.
Proof.

induction b.
intros.
rewrite bplus_Z_r.
rewrite bplus_Z_l.
reflexivity.

destruct c.
rewrite bplus_Z_r.
rewrite bplus_Z_l.
reflexivity.

assert (H: bin_add (B0 b) (B0 c) = (B0 (bin_add b c))). { reflexivity. }
rewrite H. clear H.
assert (H: bin_add (B0 c) (B0 b) = (B0 (bin_add c b))). { reflexivity. }
rewrite H. clear H.
pose proof (IHb c) as H.
rewrite H. clear H.
reflexivity.

assert (H: bin_add (B0 b) (B1 c) = (B1 (bin_add b c))). { reflexivity. }
rewrite H. clear H.
assert (H: bin_add (B1 c) (B0 b) = (B1 (bin_add c b))). { reflexivity. }
rewrite H. clear H.
pose proof (IHb c) as H.
rewrite H. clear H.
reflexivity.

destruct c.
rewrite bplus_Z_r.
rewrite bplus_Z_l.
reflexivity.

assert (H: bin_add (B1 b) (B0 c) = (B1 (bin_add b c))). { reflexivity. }
rewrite H. clear H.
assert (H: bin_add (B0 c) (B1 b) = (B1 (bin_add c b))). { reflexivity. }
rewrite H. clear H.
pose proof (IHb c) as H.
rewrite H. clear H.
reflexivity.

assert (H: bin_add (B1 b) (B1 c) = (B0 (incr (bin_add b c)))). { reflexivity. }
rewrite H. clear H.
assert (H: bin_add (B1 c) (B1 b) = (B0 (incr (bin_add c b)))). { reflexivity. }
rewrite H. clear H.
pose proof (IHb c) as H.
rewrite H. clear H.
reflexivity.
Qed.

Lemma bplus_assoc : forall a b c, bin_add (bin_add a b) c =
                                  bin_add a (bin_add b c).
Proof.
induction a, b, c.
repeat rewrite bplus_Z_r. reflexivity.
repeat rewrite bplus_Z_r. repeat rewrite bplus_Z_l. reflexivity.
repeat rewrite bplus_Z_l. reflexivity.
repeat rewrite bplus_Z_r. repeat rewrite bplus_Z_l. reflexivity.
repeat rewrite bplus_Z_r. repeat rewrite bplus_Z_l. reflexivity.
repeat rewrite bplus_Z_r. repeat rewrite bplus_Z_l. reflexivity.
repeat rewrite bplus_Z_r. repeat rewrite bplus_Z_l. reflexivity.
repeat rewrite bplus_Z_r. repeat rewrite bplus_Z_l. reflexivity.
repeat rewrite bplus_Z_r. repeat rewrite bplus_Z_l. reflexivity.
repeat rewrite bplus_Z_r. repeat rewrite bplus_Z_l. reflexivity.
repeat rewrite bplus_Z_r. repeat rewrite bplus_Z_l. reflexivity.
repeat rewrite bplus_Z_r. repeat rewrite bplus_Z_l. reflexivity.
repeat rewrite bplus_Z_r. repeat rewrite bplus_Z_l. reflexivity.

simpl bin_add.
pose proof (B0_eq_impl_eq (bin_add (bin_add a b) c) (bin_add a (bin_add b c))) as H.
pose proof (IHa b c) as H1.
exact (H H1).

simpl bin_add.
pose proof (B1_eq_impl_eq (bin_add (bin_add a b) c) (bin_add a (bin_add b c))) as H.
pose proof (IHa b c) as H1.
exact (H H1).

simpl bin_add.
reflexivity.

simpl bin_add.
pose proof (B1_eq_impl_eq (bin_add (bin_add a b) c) (bin_add a (bin_add b c))) as H.
pose proof (IHa b c) as H1.
exact (H H1).

simpl bin_add.
pose proof (B0_eq_impl_eq (incr (bin_add (bin_add a b) c)) (bin_add a (incr (bin_add b c)))) as H.
apply H. clear H.
pose proof (IHa b c) as H.
rewrite H. clear H.
pose proof (bin_add_one (bin_add b c)) as H.
rewrite <- H. clear H.
pose proof (IHa (bin_add b c) (B1 Z)) as H.
rewrite <- H. clear H.
pose proof (bin_add_one (bin_add a (bin_add b c))) as H.
rewrite <- H.
reflexivity.

repeat rewrite bplus_Z_r. reflexivity.
repeat rewrite bplus_Z_r. repeat rewrite bplus_Z_l. reflexivity.
repeat rewrite bplus_Z_r. repeat rewrite bplus_Z_l. reflexivity.
repeat rewrite bplus_Z_r. reflexivity.

simpl bin_add.
pose proof (IHa b c) as H.
rewrite H.
reflexivity.

simpl bin_add.
pose proof (IHa b c) as H.
rewrite H.
reflexivity.

simpl bin_add.
reflexivity.

simpl bin_add.
pose proof (B0_eq_impl_eq (bin_add (incr (bin_add a b)) c) (incr (bin_add a (bin_add b c)))) as H.
apply H. clear H.
Admitted.


Lemma b_add_incr : forall b c, bin_add b (incr c) = incr (bin_add b c).
Proof.
intros.
induction b.
repeat rewrite bplus_Z_l.
reflexivity.

pose proof (bin_add_one c) as H.
rewrite <- H. clear H.
pose proof (b_add_comm c (B1 Z)) as H.
rewrite H. clear H.
pose proof (bplus_assoc (B0 b) (B1 Z) c) as H.
rewrite <- H. clear H.
assert (H: bin_add (B0 b) (B1 Z) = B1 (bin_add b Z)). { reflexivity. }
rewrite bplus_Z_r in H.
rewrite H. clear H.
pose proof (bin_add_one (bin_add (B0 b) c)) as H.
rewrite <- H. clear H.
pose proof (bplus_assoc (B0 b) c (B1 Z)) as H.
rewrite H. clear H.
pose proof (b_add_comm c (B1 Z)) as H.
rewrite H. clear H.
pose proof (bplus_assoc (B0 b) (B1 Z) c) as H.
rewrite <- H. clear H.
assert (H: bin_add (B0 b) (B1 Z) = B1 (bin_add b Z)). { reflexivity. }
rewrite H. clear.
rewrite bplus_Z_r.
reflexivity.

pose proof (bin_add_one c) as H.
rewrite <- H. clear H.
pose proof (b_add_comm c (B1 Z)) as H.
rewrite H. clear H.
pose proof (bplus_assoc (B1 b) (B1 Z) c) as H.
rewrite <- H. clear H.
assert (H: bin_add (B1 b) (B1 Z) = B0 (incr (bin_add b Z))). { reflexivity. }
rewrite bplus_Z_r in H.
rewrite H. clear H.
pose proof (bin_add_one (bin_add (B1 b) c)) as H.
rewrite <- H. clear H.
pose proof (bplus_assoc (B1 b) c (B1 Z)) as H. 
rewrite H. clear H.
pose proof (b_add_comm c (B1 Z)) as H.
rewrite H. clear H.
pose proof (bplus_assoc (B1 b) (B1 Z) c) as H.
rewrite <- H. clear H.
assert (H: bin_add (B1 b) (B1 Z) = B0 (incr (bin_add b Z))). { reflexivity. }
rewrite bplus_Z_r in H.
rewrite H. clear H.
reflexivity.
Qed.

Lemma n_to_b_add : forall m n, 
  bin_add (nat_to_bin m) (nat_to_bin n) = nat_to_bin (m + n).
Proof.
intros.
induction n.
rewrite add_0_r.
simpl.
rewrite bplus_Z_r.
reflexivity.
rewrite <- plus_n_Sm.
repeat rewrite n_b_incr.
rewrite <- IHn.

pose proof (bin_add_one (nat_to_bin n)) as H.
rewrite <- H. clear H.
pose proof (bplus_assoc (nat_to_bin m) (nat_to_bin n) (B1 Z)) as H.
rewrite <- H. clear H.
pose proof (bin_add_one (bin_add (nat_to_bin m) (nat_to_bin n))) as H.
rewrite H. clear H.
reflexivity.

(*
rewrite b_add_incr.
rewrite IHn.
reflexivity.
*)

Qed.
