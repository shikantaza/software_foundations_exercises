Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.
From Coq Require Import Lia.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
  
Theorem ev_4 : ev 4.
apply ev_SS.
apply ev_SS.
apply ev_0.
Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
intros.
apply ev_SS.
apply ev_SS.
apply H.
Qed.

Theorem ev_double : forall n,
  ev (double n).
Proof.
intros.
induction n.
simpl.
apply ev_0.
simpl.
apply ev_SS.
apply IHn.
Qed.

Theorem ev_inversion :
  forall (n : nat), ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
intros.
destruct H.
left.
reflexivity.
right.
destruct H.
exists 0.
split.
reflexivity.
apply ev_0.
exists (S (S n)).
split.
reflexivity.
apply ev_SS.
apply H.
Qed.

(* as done in the text *)
Theorem ev_inversion' :
  forall (n : nat), ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.
  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
intros.
destruct H.
simpl.
apply ev_0.
simpl.
apply H.
Qed.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
intros.
pose proof (ev_minus2 (S (S n))).
pose proof (H0 H) as H1.
simpl pred in H1.
apply H1.
Qed.

Theorem evSS_ev_remember : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. remember (S (S n)) as k eqn:Hk.
  destruct E as [|n' E'] eqn:EE.
  - (* E = ev_0 *)
    (* Now we do have an assumption, in which k = S (S n) has been
       rewritten as 0 = S (S n) by destruct. That assumption
       gives us a contradiction. *)
    discriminate Hk.
  - (* E = ev_S n' E' *)
    (* This time k = S (S n) has been rewritten as S (S n') = S (S n). *)
    injection Hk as Heq. rewrite <- Heq. apply E'.
Qed.

Theorem one_not_even : not (ev 1).
Proof.
unfold not.
intros.
apply ev_inversion in H.
destruct H.
discriminate H.
case H.
intros.
destruct H0.
discriminate H0.
Qed.

(* as in text *)
Theorem one_not_even' : not (ev 1).
intros H.
apply ev_inversion in H.
destruct H as [| [m [Hm _]]].
discriminate.
discriminate Hm.
Qed.

(* as in text *)
Theorem one_not_even'' : not (ev 1).
Proof.
  intros H. inversion H. Qed.
  
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
intros.
pose proof (evSS_ev (S (S n))) as H1.
pose proof (H1 H) as H2.
apply (evSS_ev n).
apply H2.
Qed.

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
intros.
apply ev_minus2 in H.
simpl pred in H.
apply ev_minus2 in H.
simpl pred in H.
apply one_not_even in H.
exfalso.
apply H.
Qed.

Theorem ev5_nonsense' :
  ev 5 -> 2 + 2 = 9.
Proof.
intros.
inversion H.
apply ev_minus2 in H1.
simpl pred in H1.
apply one_not_even in H1.
exfalso.
apply H1.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
intros.
inversion H.
reflexivity.
Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
intros.
inversion H.
Qed.

Lemma test: forall n, 
  (double n) = 0 \/ (exists n', ((double n) = S (S n')) /\ ev n').
Proof.
intros.
apply (ev_inversion (double n)).
apply ev_double.
Qed.

Lemma test2: forall n, double n = 0 -> n = 0.
intros.
destruct n.
reflexivity.
discriminate.
Qed.

Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
intros n E.
unfold Even.
inversion E as [EQ' | n' E' EQ'].
exists 0.
reflexivity.
assert (H: (exists k', n' = double k') -> (exists n0, S (S n') = double n0)).
{ intros [k' EQ''].
exists (S k').
simpl.
rewrite <- EQ''.
reflexivity.
}
apply H.
generalize dependent E'.
Abort.

Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
intros.
induction H.
unfold Even.
exists 0.
reflexivity.
unfold Even in IHev.
elim IHev.
intros.
unfold Even.
exists (S x).
rewrite H0.
simpl.
reflexivity.
Qed.

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
intros.
split.
apply ev_Even.
intros.
unfold Even in H.
elim H.
intros.
rewrite H0.
apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
intros.
induction H.
simpl.
apply H0.
assert (S (S n) + m = S (S (n + m))). { lia. }
rewrite H1.
apply ev_SS.
apply IHev.
Qed.

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
intros.
split.
intros.
induction H.
apply ev_0.
apply ev_SS.
apply ev_0.
apply ev_sum.
apply IHev'1.
apply IHev'2.
intros.
induction H.
apply ev'_0.
assert (H1: S (S n) = n + 2).  { lia. }
rewrite H1.
apply (ev'_sum n 2).
apply IHev.
apply ev'_2.
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
intros.
induction H0.
simpl in H.
apply H.
apply IHev.
apply ev_inversion in H.
destruct H.
exfalso.
discriminate H.
inversion H.
destruct H1.
assert (H3: S (S n) + m = S (S x) -> x = n + m). { lia. }
pose proof (H3 H1) as H4.
rewrite H4 in H2.
apply H2.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
intros.
pose proof (ev_sum (n+m) (n+p)) as H1.
pose proof (H1 H) as H2.
pose proof (H2 H0) as H3.
assert (H4: n + m + (n + p) = (double n) + (m + p)) . { 
assert (H5: double n = n + n). { apply double_plus. }
rewrite H5.
lia.
}
rewrite H4 in H3.
pose proof (ev_ev__ev (double n) (m+p)) as H5.
pose proof (H5 H3) as H6.
apply H6.
apply ev_double.
Qed.

Module Playground.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

Theorem test_le1 :
  3 <= 3.
Proof.
apply (le_n 3).
Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
apply (le_S 3 5).
apply (le_S 3 4).
apply (le_S 3 3).
apply (le_n 3).
Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
intros.
inversion H.
inversion H2.
Qed.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

End Playground.

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).
  
Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).
  
Inductive next_ev : nat -> nat -> Prop :=
  | ne_1 n (H: ev (S n)) : next_ev n (S n)
  | ne_2 n (H: ev (S (S n))) : next_ev n (S (S n)).
  
(*
Define an inductive binary relation total_relation that holds between every pair of natural numbers.
*)
Inductive total_relation : nat -> nat -> Prop :=
  | tr m n (H: m = n \/ ~(m = n)) : total_relation m n.

(*
Define an inductive binary relation empty_relation (on numbers) that never holds.
*)
Inductive empty_relation : nat -> nat -> Prop :=
  | er m n (H: m = n /\ ~(m = n)) : empty_relation m n.

Lemma le_trans_helper: forall m n, S m <= n -> m <= n.
Proof.
intros.
induction H.
apply le_S.
apply le_n.
apply le_S.
apply IHle.
Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
intros.
induction H.
apply H0.
apply IHle.
pose proof (le_trans_helper m0 o) as H1.
apply (H1 H0).
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
intros.
induction n.
apply le_n.
apply le_S.
apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
intros.
induction H.
apply le_n.
apply le_S.
apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
intros.
inversion H.
apply le_n.
pose proof (le_trans_helper n m) as H2.
apply (H2 H1).
Qed.

Lemma lt_ge_cases_helper1: forall n m,
  n < m -> n < S m.
Proof.
intros.
destruct H.
apply le_S.
apply le_n.
apply le_S.
apply le_S.
apply H.
Qed.

Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
induction m.
right.
apply O_le_n.
destruct IHm.
left.
unfold lt.
apply n_le_m__Sn_le_Sm.
unfold lt in H.
apply le_S in H.
apply Sn_le_Sm__n_le_m in H.
apply H.
inversion H.
left.
unfold lt.
apply le_n.
right.
apply n_le_m__Sn_le_Sm.
apply H0.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
induction b.
rewrite add_0_r.
apply le_n.
rewrite <- plus_n_Sm.
apply le_S.
apply IHb.
Qed.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
intros.
split.

induction n2.
rewrite add_0_r in H.
apply H.
rewrite <- plus_n_Sm in H.
apply le_S in H.
apply Sn_le_Sm__n_le_m in H.
apply (IHn2 H).

induction n1.
cbn in H.
apply H.
rewrite plus_Sn_m in H.
apply le_S in H.
apply Sn_le_Sm__n_le_m in H.
apply (IHn1 H).

Qed.

Lemma add_le_cases_helper: forall a b c,
  a + b <= a + c -> b <= c.
Proof.
intros.
induction a.
cbn in H.
apply H.
rewrite plus_Sn_m in H.
rewrite plus_Sn_m in H.
apply Sn_le_Sm__n_le_m in H.
apply (IHa H).
Qed.
 
Theorem add_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
intros.
induction n.
left.
apply O_le_n.
rewrite plus_Sn_m in H.
apply le_S in H.
apply Sn_le_Sm__n_le_m in H.
pose proof (IHn H) as H1.
destruct H1.
inversion H0.
rewrite H1 in H.
pose proof (add_le_cases_helper p m q) as H2.
right.
apply (H2 H).
left.
apply n_le_m__Sn_le_Sm.
apply H1.
right.
apply H0.
Qed.

Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
intros.
induction p.
cbn.
apply H.
repeat rewrite plus_Sn_m.
apply n_le_m__Sn_le_Sm.
apply IHp.
Qed.

Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
intros.
pose proof (plus_le_compat_l n m p) as H1.
pose proof (H1 H) as H2.
assert (H3: p+n = n+p). { rewrite add_comm. reflexivity. }
assert (H4: p+m = m+p). { rewrite add_comm. reflexivity. }
rewrite <- H3.
rewrite <- H4.
apply H2.
Qed.

Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
intros.
induction p.
rewrite add_0_r.
apply H.
rewrite <- plus_n_Sm.
apply le_S.
apply IHp.
Qed.

Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
intros.
unfold lt in H.
apply le_S in H.
apply Sn_le_Sm__n_le_m in H.
apply H.
Qed.

Lemma plus_lt_helper: forall n m, S n < m -> n < m.
Proof.
intros.
unfold lt in H.
apply le_S in H.
apply Sn_le_Sm__n_le_m in H.
unfold lt.
apply H.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
intros.
split.

induction n2.
rewrite add_0_r in H.
apply H.
rewrite <- plus_n_Sm in H.
unfold lt in H.
apply plus_lt_helper in H.
apply (IHn2 H).

induction n1.
cbn in H.
apply H.
rewrite plus_Sn_m in H.
apply plus_lt_helper in H.
apply (IHn1 H).

Qed.

Lemma S_leb_impl_leb: forall n m,
  S n <=? S m = true -> n <=? m = true.
Proof.
intros.
apply H.
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
intros n.
induction n.
intros.
apply O_le_n.
intros.
destruct m.
discriminate.
apply n_le_m__Sn_le_Sm.
pose proof (S_leb_impl_leb n m) as H1.
pose proof (H1 H) as H2.
pose proof (IHn m) as H3.
apply (H3 H2).
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
intros n.
induction n.
intros.
reflexivity.
intros.
destruct m.
inversion H.
apply Sn_le_Sm__n_le_m in H.
pose proof ((IHn m)H) as H1.
apply H1.
Qed.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
intros.
apply leb_complete in H.
apply leb_complete in H0.
pose proof (le_trans n m o) as H1.
pose proof (H1 H) as H2.
pose proof (H2 H0) as H3.
apply leb_correct.
apply H3.
Qed.

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
split.
intros.
apply leb_complete.
apply H.
intros.
apply leb_correct.
apply H.
Qed.

Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o ) : R (S m) n (S o)
  | c3 m n o (H : R m n o ) : R m (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
  | c5 m n o (H : R m n o ) : R n m o.

Example e1 : R 1 1 2.
Proof.
apply c2.
apply c3.
apply c1.
Qed.

Example e2: R 2 2 6.
Proof.
repeat (apply c3).
apply c4.
repeat (apply c2).
apply c4.
repeat (apply c3).
apply c2.
Abort.

(* Dropping constructor c5 wouldn't make any difference because it only swaps
  the first and the second arguments, which we are anyway able to make zero in the     
  second proposition, and the first proposition can be proved without c5 *)
  
(* Dropping c4 also wouldn't make a difference because the first proposition can be     
   proved without it, and in the second proposition the goal would start diverging if we
   apply c4 *)
   
Definition fR : nat -> nat -> nat := fun m n => m + n.

Compute fR 1 1.

Lemma R_equiv_fR_helper : forall m n,
  m = n -> S m = S n.
intros.
rewrite H.
reflexivity.
Qed.

Lemma R_equiv_fR_helper2 : forall m n,
  S m = S n -> m = n.
Proof.
intros.
apply succ_inj.
apply H.
Qed.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
intros.
split.

intros.
unfold fR.
induction H.
simpl.
reflexivity.
rewrite plus_Sn_m.
pose proof (R_equiv_fR_helper (m+n) o) as H1.
apply (H1 IHR).
rewrite <- plus_n_Sm.
pose proof (R_equiv_fR_helper (m+n) o) as H1.
apply (H1 IHR).
assert (H1: S m + S n = S (S (m+n))). { lia. }
rewrite H1 in IHR.
repeat (apply R_equiv_fR_helper2 in IHR).
apply IHR.
rewrite add_comm.
apply IHR.

intros.
unfold fR in H.
induction H.
induction n.
induction m.
simpl.
apply c1.
simpl.
rewrite add_0_r.
rewrite add_0_r in IHm.
apply c2.
apply IHm.
rewrite <- plus_n_Sm.
apply c3.
apply IHn.
Qed.

Fixpoint is_subseq (l1 l2 : list nat) : bool :=
  match l1,l2 with
    | [], _          => true
    | _, []          => false
    | h1::t1, h2::t2 => (if h1 =? h2 
                         then (is_subseq t1 t2)
                         else (is_subseq l1 t2))
  end.

Compute (is_subseq [] []).
Compute (is_subseq [] [1;2;3]).  
Compute (is_subseq [1;2;3] [1;2;3]).
Compute (is_subseq [1;2;3] [1;1;1;2;2;3]).
Compute (is_subseq [1;2;3] [1;2;7;3]).
Compute (is_subseq [1;2;3] [5;6;1;9;9;2;7;3;8]).
Compute (is_subseq [1;2;3] [1;2]).
Compute (is_subseq [1;2;3] [1;3]).
Compute (is_subseq [1;2;3] [5;6;2;1;7;3;8]).

Definition head (T : Type) (l : list T) : option T :=
  match l with
  | [] => None
  | h :: t => Some h
  end.

Arguments head {T}.

Definition tail (T : Type) (l : list T) : list T :=
  match l with
  | [] => []
  | h :: t => t
  end.

Arguments tail {T}.

(* Inductive subseq : list nat -> list nat -> Prop :=
  | subseq1 l : subseq [] l
  | subseq2 l1 l2 (H1 : head l1 = head l2) (H2: subseq (tail l1) (tail l2)) : subseq l1 l2
  | subseq3 l1 l2 (H1 : head l1 <> head l2) (H2: subseq l1 (tail l2)) : subseq l1 l2.
 *)  

Inductive subseq : list nat -> list nat -> Prop :=
  | subseq1 l2 : subseq [] l2
  | subseq2 (h : nat) (l1 l2 : list nat) (H: subseq l1 l2) : subseq (h :: l1) (h :: l2)
  | subseq3 (h : nat) (l1 l2 : list nat) (H: subseq l1 l2) : subseq l1 (h :: l2).
  
Theorem  subseq_refl : forall l : list nat,
  subseq l l.
Proof.
intros.
induction l.
apply subseq1.
apply subseq2.
apply IHl.
Qed.

Lemma append_nil_r (T : Type): forall s : list T, s ++ [] = s.
intros.
induction s.
simpl.
reflexivity.
simpl.
rewrite IHs.
reflexivity.
Qed.

Lemma append_nil_l (T : Type): forall s : list T, [] ++ s = s.
intros.
induction s.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Lemma subseq_trans_helper : forall l, subseq l [] -> l = [].
Proof.
intros.
induction l.
reflexivity.
inversion H.
Qed.

Lemma subseq_nil_true : forall l, is_subseq [] l = true.
Proof.
intros.
destruct l.
reflexivity.
reflexivity.
Qed.

Lemma subseq_nil_impl_nil : forall l, is_subseq l [] = true -> l = [].
Proof.
intros.
unfold is_subseq in H.
destruct l.
reflexivity.
discriminate H.
Qed.

(* first try to prove using function version *)
(* solution is possible if we generalize IHl2 as 
  'forall l2, is_subseq l2 l3 ...' and instantiate with (x :: l2) *)
(*
Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  is_subseq l1 l2 = true ->
  is_subseq l2 l3 = true ->
  is_subseq l1 l3 = true.
Proof.
intros.
generalize dependent l1.
generalize dependent l2.
induction l2.
intros.
apply subseq_nil_impl_nil in H.
rewrite H.
apply subseq_nil_true.
intros. *)

(***)
(* sample from Stack Overflow *) 
Inductive InL {A:Type} (y:A) : list A -> Prop := 
  | InHead : forall xs:list A, InL y (cons y xs) 
  | InTail : forall (x:A) (xs:list A), InL y xs -> InL y (cons x xs).

Inductive SubSeq {A:Type} : list A -> list A -> Prop :=
 | SubNil : forall l:list A, SubSeq [] l
 | SubCons1 : forall (x:A) (l1 l2:list A), SubSeq l1 l2 -> SubSeq l1 (x::l2)
 | SubCons2 : forall (x:A) (l1 l2:list A), SubSeq l1 l2 -> SubSeq (x::l1) (x::l2).

Lemma proof1: forall (A:Type) (x:A) (l1 l2:list A), 
  SubSeq l1 l2 -> InL x l1 -> InL x l2.
Proof.
(* first introduce your hypothesis, but put back x and In foo
   inside the goal, so that your induction hypothesis are correct*)
intros. 
revert x H0. induction H; intros.
(* x In [] is not possible, so inversion will kill the subgoal *)
inversion H0.

(* here it is straitforward: just combine the correct hypothesis *)
apply InTail; apply IHSubSeq; trivial.

(* x0 in x::l1 has to possible sources: x0 == x or x0 in l1 *)
inversion H0; subst; clear H0.
apply InHead.
apply InTail; apply IHSubSeq; trivial.
Qed.

Lemma proof2: forall (A:Type) (x:A) (l1 l2:list A), 
  SubSeq l1 l2 -> InL x l1 -> InL x l2.
Proof.
intros.
revert x H0.

induction H.
intros.
inversion H0.
intros.
apply InTail.
apply IHSubSeq.
apply H0.

intros.
inversion H0.
apply InHead.
apply InTail.
apply IHSubSeq.
apply H2.
Qed.
(***)

Theorem subseq_app : forall l1 l2 l3 : list nat,
  subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
intros.
induction H.
apply subseq1.
assert ((h :: l2) ++ l3 = h :: (l2 ++ l3)). { reflexivity. }
rewrite H0.
clear H0.
apply subseq2.
apply IHsubseq.
assert ((h :: l2) ++ l3 = h :: (l2 ++ l3)). { reflexivity. }
rewrite H0.
clear H0.
apply subseq3.
apply IHsubseq.
Qed.

Theorem subseq_app_front : forall l1 l2 l3 : list nat,
  subseq l1 l2 -> subseq l1 (l3 ++ l2).
Proof.
intros.
induction l3.
rewrite append_nil_l.
apply H.
assert (H1: (x :: l3) ++ l2 = x :: (l3 ++ l2)). { reflexivity. }
rewrite H1.
apply subseq3.
apply IHl3.
Qed.

Lemma subseq_app_helper : forall l1 l2, subseq l1 (l1 ++ l2).
Proof.
intros.
induction l1.
apply subseq1.
assert (H: (x :: l1) ++ l2 = x :: (l1 ++ l2)). { reflexivity. }
rewrite H.
clear H.
apply subseq2.
apply IHl1.
Qed.

(* alternate proof that depends on subseq_trans *)
(* Theorem subseq_app' : forall l1 l2 l3 : list nat,
  subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
intros.
pose proof (subseq_app_helper l2 l3) as H1.
pose proof (subseq_trans l1 l2 (l2 ++ l3)) as H2.
apply ((H2 H) H1).
Qed. *)

Lemma subseq_tail : forall l1 l2, subseq l1 (tail l2) -> subseq l1 l2.
Proof.
intros.
destruct l2.
simpl in H.
apply H.
simpl in H.
apply subseq3.
apply H.
Qed.

Theorem subseq_inversion : forall (l1 l2 : list nat),
   subseq l1 l2 -> l1 = [] \/
                   subseq l1 (tail l2) \/
                   (head l1 = head l2 /\ subseq (tail l1) (tail l2)).
Proof.
intros.
inversion H.
left.
reflexivity.
right.
right.
simpl.
split.
reflexivity.
apply H0.
right.
left.
simpl.
apply H0.
Qed.

Theorem subseq_impl_tail: forall l1 l2,
  subseq l1 l2 -> subseq (tail l1) l2.
Proof.
intros.
induction H.
simpl.
apply subseq1.
simpl.
apply (subseq3 h).
apply H.
apply (subseq3 h).
apply IHsubseq.
Qed.

Theorem subseq_head_impl : forall h l1 l2,
  subseq (h :: l1) l2 -> subseq l1 l2.
Proof.
intros.
apply subseq_impl_tail in H.
simpl in H.
apply H.
Qed.

Theorem subseq_h_h_implies : forall h l1 l2,
  subseq (h :: l1) (h :: l2) -> subseq l1 l2.
Proof.
intros.
inversion H.
apply H1.
apply subseq_impl_tail in H2.
simpl in H2.
apply H2.
Qed.

Fixpoint pos_in_list_internal (x acc : nat) (l : list nat) : option nat :=
  match l with
  |  []      => None
  |  h :: l' => match (x =? h) with
                | true  => Some acc 
                | false => (pos_in_list_internal x (acc + 1) l')
                end
  end.

Definition pos_in_list (x : nat) (l : list nat) : option nat :=
  pos_in_list_internal x 0 l.

Compute pos_in_list 42 [1;2;3;4].

Lemma opt_injection : forall n1 n2 : nat,
  Some n1 = Some n2 -> n1 = n2.
intros.
injection H.
intros.
apply H0.
Qed.

Lemma subseq_h1_h2 : forall h1 h2 l1 l2,
  subseq (h1 :: l1) (h2 :: l2) ->
  h1 <> h2 ->
  subseq (h1 :: l1) l2.
Proof.
intros.
apply subseq_inversion in H.
destruct H.
discriminate H.
destruct H.
simpl in H.
apply H.
destruct H.
simpl in H.
apply opt_injection in H.
unfold not in H0.
exfalso.
apply (H0 H).
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
intros.
generalize dependent l3.
induction H.

intros.
apply subseq1.

intros.
generalize H0.

induction l3.
intros.
apply subseq_trans_helper in H1.
discriminate H1.

intros.
destruct (eqb h x) eqn:H2.

rewrite eqb_eq in H2.
rewrite H2.
apply subseq2.
rewrite H2 in H0.
apply (subseq_h_h_implies x l2 l3) in H0.
apply ((IHsubseq l3) H0).

rewrite eqb_neq in H2.
pose proof (subseq_h1_h2 h x l2 l3) as H3.
pose proof ((H3 H1) H2) as H4.
pose proof ((IHl3 H4) H4) as H5.
apply (subseq3 x) in H5.
apply H5.

intros.
apply subseq_impl_tail in H0.
simpl in H0.
apply ((IHsubseq l3) H0).

Qed.


(* Suppose we give Coq the following definition: *)

Inductive R' : nat -> list nat -> Prop :=
  | c1'                     : R' 0     []
  | c2' n l (H: R' n     l) : R' (S n) (n :: l)
  | c3' n l (H: R' (S n) l) : R' n     l.

(* Which of the following propositions are provable?

  R' 2 [1;0]           <- provable 
  R' 1 [1;2;1;0]       <- not provable (application of c3' keeps incrementing first arg;
                          get stuck if we try to apply either c1' or c2')            
  R' 6 [3;2;1;0]       <- not provable (can only keep applying c3' indefinitely)

*)

Example R'_example1 : R' 2 [1; 0].
Proof.
apply c2'.
apply c2'.
apply c1'.
Qed.

Example R'_example2 : R' 1 [1;2;1;0].
Proof.
apply c3'.
apply c2'.
apply c3'.
Abort.

Example R'_example3 : R' 6 [3;2;1;0].
Proof.
apply c3'.
apply c3'.
Abort.

(* Regular expressions *)

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

Example reg_exp_ex1 : [1] =~ Char 1.
apply MChar.
Qed.  

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
(* apply (MApp [1] (Char 1) [2] (Char 2) (MChar 1) (MChar 2)). *)
apply (MApp [1]).
- apply MChar.
- apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
unfold not.
intros.
inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.
  
Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
unfold reg_exp_of_list.
apply (MApp [1]).
apply MChar.
apply (MApp [2]).
apply MChar.
apply (MApp [3]).
apply MChar.
apply MEmpty.
Qed.

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
intros.
pose proof (MStar0 re) as H1.
pose proof (MStarApp s [] re H H1) as H2.
rewrite (append_nil_r T) in H2.
apply H2.
Qed.

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
intros.
unfold not.
intros.
induction s.
inversion H.
inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
intros.
destruct H.
apply (MUnionL s re1 re2 H).
apply (MUnionR re1 s re2 H).
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
intros.
induction ss.
simpl.
apply MStar0.
simpl.
apply MStarApp.
pose proof (H x) as H1.
apply H1.
unfold In.
left.
reflexivity.
apply IHss.
intros.
pose proof (H s) as H1.
apply H1.
simpl.
right.
apply H0.
Qed.

Lemma test_regexp : forall (T : Type) (s : list T) x,
  s =~ Char x -> s = [x].
Proof.
intros.
inversion H.
reflexivity.
Qed.

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.

intros.
split.

intros.
generalize dependent s1.
induction s2.
intros.
inversion H.
reflexivity.
intros.
simpl reg_exp_of_list in H.
inversion H.
inversion H3.
simpl.
pose proof (IHs2 s3) as H8.
pose proof (H8 H4) as H9.
rewrite H9.
reflexivity.

intros.
generalize dependent s1.
induction s2.
intros.
rewrite H.
simpl reg_exp_of_list.
apply MEmpty.
intros.
rewrite H.
simpl reg_exp_of_list.
apply (MApp [x]).
apply MChar.
pose proof (IHs2 s2).
apply H0.
reflexivity.
Qed.

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Lemma in_re_match_helper1 : forall (T : Type) (x : T) (s1 s2 : list T),
  In x (s1 ++ s2) -> In x s1 \/ In x s2.
Proof.
intros.
generalize dependent s1.
induction s1.
intros.
simpl in H.
right.
apply H.
intros.
assert (H1: (x0 :: s1) ++ s2 = x0 :: (s1 ++ s2)). { reflexivity. }
rewrite H1 in H.
simpl In in H.
destruct H.
left.
rewrite H.
simpl.
left.
reflexivity.
pose proof (IHs1 H) as H2.
destruct H2.
left.
simpl.
right.
apply H0.
right.
apply H0.
Qed.

Lemma in_re_match_helper2 : forall (T : Type) (x : T) (s1 s2 : list T),
  In x s1 \/ In x s2 -> In x (s1 ++ s2).
Proof.
intros.
induction s1.
simpl.
destruct H.
exfalso.
simpl In in H.
apply H.
apply H.
assert (H1: (x0 :: s1) ++ s2 = x0 :: (s1 ++ s2)). { reflexivity. }
rewrite H1.
clear H1.
simpl.
destruct H.
simpl In in H.
destruct H.
left.
apply H.
right.
apply IHs1.
left.
apply H.
right.
apply IHs1.
right.
apply H.
Qed.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
intros.
induction H.
exfalso.
simpl in H0.
apply H0.
simpl.
simpl in H0.
apply H0.
simpl.
pose proof (in_re_match_helper1 T x s1 s2) as H2.
pose proof (H2 H0) as H3.
destruct H3.
pose proof (in_re_match_helper2 T x (re_chars re1) (re_chars re2)) as H4.
apply H4.
left.
apply IHexp_match1.
apply H3.
pose proof (in_re_match_helper2 T x (re_chars re1) (re_chars re2)) as H4.
apply H4.
right.
apply IHexp_match2.
apply H3.
simpl.
pose proof (in_re_match_helper2 T x (re_chars re1) (re_chars re2)) as H4.
apply H4.
left.
apply IHexp_match.
apply H0.
simpl.
pose proof (in_re_match_helper2 T x (re_chars re1) (re_chars re2)) as H4.
apply H4.
right.
apply IHexp_match.
apply H0.
exfalso.
simpl in H0.
apply H0.
simpl.
pose proof (in_re_match_helper1 T x s1 s2) as H2.
pose proof (H2 H0) as H3.
destruct H3.
apply (IHexp_match1 H3).
pose proof (IHexp_match2 H3) as H4.
simpl re_chars in H4.
apply H4.
Qed.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
  | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
  | Star re => true (* since Star re alwys mathes the empty string *)
  end.

Lemma bool_helper1 : forall (a : bool), a || true = true.
Proof.
destruct a.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Lemma bool_helper2 : forall (b1 b2 : bool), b1 && b2 = true -> b1 = true /\ b2 = true.
Proof.
intros.
split.
destruct b1.
reflexivity.
discriminate.
destruct b2.
reflexivity.
destruct b1.
discriminate.
discriminate.
Qed.

Lemma bool_helper3 : forall b1 b2, b1 || b2 = true -> b1 = true \/ b2 = true.
Proof.
intros.
destruct b1.
left.
reflexivity.
destruct b2.
right.
reflexivity.
discriminate H.
Qed.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
intros.
split.

intros.
destruct H.
induction H.
reflexivity.
reflexivity.
simpl.
rewrite IHexp_match1.
rewrite IHexp_match2.
simpl.
reflexivity.
simpl.
rewrite IHexp_match.
simpl.
reflexivity.
simpl.
rewrite IHexp_match.
apply (bool_helper1 (re_not_empty re1)).
simpl.
reflexivity.
simpl.
reflexivity.

intros.
induction re.
exists [].
discriminate.
exists [].
apply MEmpty.
exists [t].
apply MChar.
simpl in H.
pose proof (bool_helper2 (re_not_empty re1) (re_not_empty re2)) as H1.
pose proof (H1 H) as H2.
destruct H2.
pose proof (IHre1 H0) as H3.
pose proof (IHre2 H2) as H4.
destruct H3.
destruct H4.
exists (x ++ x0).
apply (MApp x re1 x0 re2).
apply H3.
apply H4.
simpl in H.
pose proof (bool_helper3 (re_not_empty re1) (re_not_empty re2)) as H1.
pose proof (H1 H) as H2.
destruct H2.
pose proof (IHre1 H0) as H2.
destruct H2.
exists x.
apply MUnionL.
apply H2.
pose proof (IHre2 H0) as H2.
destruct H2.
exists x.
apply MUnionR.
apply H2.
exists [].
apply MStar0.
Qed.

Lemma re_impl_star : forall T (s : list T) (re : reg_exp T),
  s =~ re -> s =~ Star re.
intros.
assert (H1: [ ] =~ Star re). { apply MStar0. }
pose proof (MStarApp s [] re H H1) as H2.
rewrite append_nil_r in H2.
apply H2.
Qed.

Lemma app_assoc : forall T (s1 s2 s3 : list T),
  (s1 ++ s2) ++ s3 = s1 ++ (s2 ++ s3).
Proof.
intros.
induction s1.
simpl.
reflexivity.
simpl.
rewrite IHs1.
reflexivity.
Qed.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
intros.
remember (Star re) in H.
induction H.
simpl.
apply H0.
discriminate.
apply MStarApp.
inversion Heqr.
apply H0.
apply MStarApp.
inversion Heqr.
apply H0.
inversion Heqr.
simpl.
apply H0.
inversion Heqr.
pose proof (IHexp_match2 Heqr) as H2.
rewrite H3 in H.
assert (H4: (s1 ++ s0) ++ s2 = s1 ++ (s0 ++ s2)). { apply app_assoc. }
rewrite H4. clear H4.
apply MStarApp.
apply H.
apply H2.
Qed.

From LF Require Export Poly.

(* book version *)
Lemma star_app1: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
intros T s1 s2 re H1.
remember (Star re) as re'.
generalize dependent s2.
induction H1
 as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
     |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
     |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
injection Heqre' as Heqre''. intros s H. apply H.
injection Heqre' as Heqre''.
intros s2 H1. rewrite <- app_assoc.
apply MStarApp.
+ apply Hmatch1.
+ apply IH2.
  * rewrite Heqre''. reflexivity.
  * apply H1.
Qed.

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
intros.
remember (Star re) in H. 
induction H.
- exists []. simpl. split. 
  * reflexivity. 
  * intros. discriminate.
- exists [[x]]. simpl. split. 
  * reflexivity. 
  * intros. discriminate.
- exists [s1;s2]. simpl. rewrite append_nil_r. split. 
  * reflexivity. 
  * intros. discriminate.
- exists [s1]. simpl. rewrite append_nil_r. split. 
  * reflexivity. 
  * intros. discriminate.
- exists [s2]. simpl. rewrite append_nil_r. split.
  * reflexivity.
  * intros. discriminate.
- exists []. simpl. split.
  * reflexivity.
  * intros. exfalso. apply H.
- pose proof (IHexp_match2 Heqr) as H1.
  destruct H1.
  destruct H1.
  exists (s1 :: x).
  split.
  + simpl. rewrite <- H1. reflexivity.
  + intros.
    simpl in H3.
    destruct H3.
    ++ inversion Heqr. rewrite <- H3. rewrite <- H5. apply H.
    ++ apply ((H2 s') H3).
Qed.

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    pumping_constant re >= 1.
Proof.
intros.
induction re.
+ simpl. lia.
+ simpl. lia.
+ simpl. lia.
+ simpl. lia.
+ simpl. lia.
+ simpl. apply IHre.
Qed. 

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
intros.
pose proof (pumping_constant_ge_1 T re) as H1.
rewrite H in H1.
inversion H1.
Qed.

(* more complicated proof *)
Lemma pumping_constant_0_false1 :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
intros.
induction re.
+ simpl in H. discriminate H.
+ simpl in H. discriminate H.
+ simpl in H. discriminate H.
+ simpl in H.
  apply IHre1.
  assert (H1: pumping_constant re1 + pumping_constant re2 = 0 -> pumping_constant re1 = 0). {
    lia.
  }
  apply (H1 H).
+ simpl in H.
  apply IHre1.
  assert (H1: pumping_constant re1 + pumping_constant re2 = 0 -> pumping_constant re1 = 0). {
    lia.
  }
  apply (H1 H).
+ simpl in H. apply (IHre H).
Qed.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Compute (napp 10 [9]).

Lemma napp_comm : forall T (n : nat) (l : list T),
  l ++ (napp n l) = (napp n l) ++ l.
Proof.
intros.
induction n.
+ simpl. rewrite append_nil_r. reflexivity.
+ simpl. rewrite IHn at 1. apply app_assoc.
Qed. 

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
intros.
induction m.
+ simpl. rewrite append_nil_r. rewrite add_0_r. reflexivity.
+ simpl napp.
  assert (H: n + S m = S (n + m)). { lia. }
  rewrite H.
  simpl napp.
  rewrite IHm.
  rewrite app_assoc.
  rewrite app_assoc.
  assert (H1: l ++ napp n l = napp n l ++ l). { apply napp_comm. }
  rewrite H1.
  reflexivity.
Qed.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.  
Proof.
intros.
induction m.
+ simpl. apply H0.
+ simpl.
  rewrite <- app_assoc.
  apply MStarApp.
  ++ apply H.
  ++ apply IHm.
Qed.

Lemma pumping_constant_eq_1_implies : forall T (re : reg_exp T),
  pumping_constant re = 1 -> re = EmptyStr \/ 
                             re = EmptySet \/ 
                             (exists re1 : reg_exp T, re = Star re1 /\ 
                                           pumping_constant re1 = 1).
Proof.
intros.
induction re.
- right. left. reflexivity.
- left. reflexivity.
- exfalso. inversion H.
- exfalso. simpl in H.
  pose proof (pumping_constant_ge_1 T re1) as H1.
  pose proof (pumping_constant_ge_1 T re2) as H2.
  admit. (* easy to prove that H, H1, and H2 are mutually inconsistent *)
- simpl in H.
  pose proof (pumping_constant_ge_1 T re1) as H1.
  pose proof (pumping_constant_ge_1 T re2) as H2.
  admit. (* easy to prove that H, H1, and H2 are mutually inconsistent *)
- simpl in H.
  pose proof (IHre H) as H1.
  destruct H1.
  -- right. right.
     rewrite H0.
     exists EmptyStr.
     split.
     reflexivity.
     reflexivity.
  -- destruct H0.
     --- right. right.
         exists re.
         split.
         reflexivity.
         apply H.
     --- right. right.
         exists re.
         split.
         reflexivity.
         apply H.
Admitted.

Lemma le_helper1 : forall a b c d,
  a + b <= c + d ->
  a <= c \/ b <= d.
intros.
lia.
Qed.

Lemma length_helper1 : forall T (s1 s2 : list T),
  length (s1 ++ s2) = length s1 + length s2.
intros.
induction s1.
- simpl. reflexivity.
- assert (H1: (x :: s1) ++ s2 = x :: (s1 ++ s2)). { reflexivity. }
  rewrite H1. clear H1.
  simpl length.
  rewrite IHs1.
  lia.
Qed.

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
intros T re s Hmatch.
induction Hmatch
as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
     | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
     | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
- (* MEmpty *)
  simpl. intros contra. inversion contra.
- intros. simpl in H. inversion H. inversion H1.
- intros.
  simpl in H.
  assert (H0: length (s1 ++ s2) = length s1 + length s2).
  { apply length_helper1. }
  rewrite H0 in H. clear H0.
  pose proof (le_helper1 (pumping_constant re1)
                         (pumping_constant re2)
                         (length s1)
                         (length s2)) as H00.
  pose proof (H00 H) as H01. clear H00.
  destruct H01.
  ++  pose proof (IH1 H0) as H2. clear H0.
      destruct H2. destruct H0. destruct H0. destruct H0. destruct H1.
      exists x, x0, (x1 ++ s2). split.
      -- rewrite H0. repeat (rewrite app_assoc). reflexivity.
      -- split.
         --- apply H1.
         --- intros.
             pose proof (H2 m) as H3.
             pose proof (MApp (x ++ napp m x0 ++ x1) re1 s2 re2 H3 Hmatch2) as H4.
             assert (H5: (x ++ napp m x0 ++ x1) ++ s2 = 
                         x ++ napp m x0 ++ x1 ++ s2). 
             { repeat (rewrite app_assoc). reflexivity. }
             rewrite <- H5.
             apply H4.
  ++ pose proof (IH2 H0) as H2. clear H0.
     destruct H2. destruct H0. destruct H0. destruct H0. destruct H1.
     exists (s1++x), x0, x1. split.
     -- rewrite H0. repeat (rewrite app_assoc). reflexivity.
     -- split.
        --- apply H1.
        --- intros.
            pose proof (H2 m) as H3.
            pose proof (MApp s1 re1 (x ++ napp m x0 ++ x1) re2 Hmatch1 H3) as H4.
            assert (H5: s1 ++ x ++ napp m x0 ++ x1 = 
                        (s1 ++ x) ++ napp m x0 ++ x1).
            { repeat (rewrite app_assoc). reflexivity. }
            rewrite <- H5.
            apply H4.
- simpl.
  intros.
  assert (H1: pumping_constant re1 + pumping_constant re2 <= length s1
              -> pumping_constant re1 <= length s1). { lia. }
  pose proof (IH (H1 H)) as H2.
  destruct H2. destruct H0. destruct H0. destruct H0. destruct H2.
  exists x, x0, x1.
  split.
  -- apply H0.
  --  split.
      --- apply H2.
      --- intros.
          pose proof (H3 m) as H4.
          pose proof (MUnionL (x ++ napp m x0 ++ x1) re1 re2 H4) as H5.
          apply H5.
- simpl.
  intros.
  assert (H1: pumping_constant re1 + pumping_constant re2 <= length s2
              -> pumping_constant re2 <= length s2). { lia. }
  pose proof (IH (H1 H)) as H2.
  destruct H2. destruct H0. destruct H0. destruct H0. destruct H2.
  exists x, x0, x1.
  split.
  -- apply H0.
  --  split.
      --- apply H2.
      --- intros.
          pose proof (H3 m) as H4.
          pose proof (MUnionR re1 (x ++ napp m x0 ++ x1) re2 H4) as H5.
          apply H5.
- intros.
  simpl in H.
  inversion H.
  pose proof (pumping_constant_0_false T re) as H2.
  exfalso.
  apply (H2 H1).
- intros.
  destruct s1.
  -- simpl in H.
     pose proof (IH2 H) as H1.
     destruct H1. destruct H0. destruct H0.  destruct H0. destruct H1.
     exists x, x0, x1. split.
     --- simpl. apply H0.
     --- split.
         + apply H1.
         + intros. apply (H2 m).
  -- exists [], (x::s1), s2. split.
     --- simpl. reflexivity.
     --- split.
       + unfold not. intros. inversion H0.
       + intros.
         simpl.
         apply (napp_star T m (x::s1) s2 re).
         apply Hmatch1. apply Hmatch2.
Qed.

Lemma le_helper2 : forall a b c d,
  a + b <= c + d ->
  (a <= c /\ b > d) \/ (a <= c /\ b <= d) \/ (a > c /\ b <= d).
Proof.
intros.
lia.
Qed.  

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
intros T re s Hmatch.
induction Hmatch
  as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
     | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
     | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
- (* MEmpty *)
  simpl. intros contra. inversion contra.
- simpl. intros. inversion H. inversion H1.
- intros.
  simpl in H.
  rewrite length_helper1 in H.
  pose proof (le_helper2 (pumping_constant re1)
                         (pumping_constant re2)
                         (length s1)
                         (length s2)) as H00.
  pose proof (H00 H) as H01. clear H00.
  destruct H01.
  destruct H0.
  ++ pose proof (IH1 H0) as H2.
     destruct H2. destruct H2. destruct H2. destruct H2.
     destruct H3. destruct H4.
     exists x, x0, (x1++s2). split.
     -- rewrite H2. repeat (rewrite app_assoc). reflexivity.
     -- split.
        + apply H3.
        + split.
          --- simpl. 
              assert (H6: pumping_constant re1 <= 
                          pumping_constant re1 + pumping_constant re2).
              { lia.  }
              apply (le_trans (length x + length x0)
                              (pumping_constant re1)
                              (pumping_constant re1 + pumping_constant re2)).
              apply H4. apply H6.
          --- intros.
              pose proof (H5 m) as H6.
              pose proof (MApp (x ++ napp m x0 ++ x1) re1 s2 re2 H6 Hmatch2) as H7.
              assert (H8: (x ++ napp m x0 ++ x1) ++ s2 = 
                          x ++ napp m x0 ++ x1 ++ s2). 
              { repeat (rewrite app_assoc). reflexivity. }
                rewrite <- H8.
                apply H7.
  ++ destruct H0.
     destruct H0.
     pose proof (IH1 H0) as H2.
     destruct H2. destruct H2. destruct H2. destruct H2.
     destruct H3. destruct H4.
     exists x, x0, (x1++s2). split.
     -- rewrite H2. repeat (rewrite app_assoc). reflexivity.
     -- split.
        + apply H3.
        + split.
          --- simpl. 
              assert (H6: pumping_constant re1 <= 
                          pumping_constant re1 + pumping_constant re2).
              { lia.  }
              apply (le_trans (length x + length x0)
                              (pumping_constant re1)
                              (pumping_constant re1 + pumping_constant re2)).
              apply H4. apply H6.
          --- intros.
              pose proof (H5 m) as H6.
              pose proof (MApp (x ++ napp m x0 ++ x1) re1 s2 re2 H6 Hmatch2) as H7.
              assert (H8: (x ++ napp m x0 ++ x1) ++ s2 = 
                          x ++ napp m x0 ++ x1 ++ s2). 
              { repeat (rewrite app_assoc). reflexivity. }
                rewrite <- H8.
                apply H7.
     -- destruct H0. 
        pose proof (IH2 H1) as H2.
        destruct H2. destruct H2. destruct H2. destruct H2. 
        destruct H3. destruct H4.
        exists (s1++x), x0, x1. split.
        --- rewrite H2. repeat (rewrite app_assoc). reflexivity.
        --- split.
           + apply H3.
           + split.
             +++ simpl.
                 rewrite (length_helper1 T s1 x).
                 assert (H6: pumping_constant re1 > length s1
                          -> length s1 <= pumping_constant re1).
                 { lia. }
                 pose proof (H6 H0) as H7.
                 assert (H8: length s1 <= pumping_constant re1 /\
                             length x + length x0 <= pumping_constant re2 ->
                             length s1 + length x + length x0 <=
                             pumping_constant re1 + pumping_constant re2).
                 { lia. }
                 apply H8.
                 split.
                 apply H7.
                 apply H4.
             +++ intros.
                 pose proof (H5 m) as H6.
                 pose proof (MApp s1 re1 (x ++ napp m x0 ++ x1) re2 Hmatch1 H6) as H7.
                 assert (H8: s1 ++ x ++ napp m x0 ++ x1 = 
                             (s1 ++ x) ++ napp m x0 ++ x1).
                 { repeat (rewrite app_assoc). reflexivity. }
                 rewrite <- H8.
                 apply H7.
- simpl.
  intros.
  assert (H1: pumping_constant re1 + pumping_constant re2 <= length s1
              -> pumping_constant re1 <= length s1). { lia. }
  pose proof (IH (H1 H)) as H2.
  destruct H2. destruct H0. destruct H0. destruct H0. destruct H2.
  destruct H3.
  exists x, x0, x1.
  split.
  -- apply H0.
  -- split.
      --- apply H2.
      --- split. 
          +++ assert (H5: length x + length x0 <= pumping_constant re1 ->
                          length x + length x0 <= pumping_constant re1 + pumping_constant re2).
              { lia. }
              apply (H5 H3).
          +++ intros.
              pose proof (H4 m) as H5.
              pose proof (MUnionL (x ++ napp m x0 ++ x1) re1 re2 H5) as H6.
              apply H6.
- simpl.
  intros.
  assert (H1: pumping_constant re1 + pumping_constant re2 <= length s2
              -> pumping_constant re2 <= length s2). { lia. }
  pose proof (IH (H1 H)) as H2.
  destruct H2. destruct H0. destruct H0. destruct H0. destruct H2.
  destruct H3.
  exists x, x0, x1.
  split.
  -- apply H0.
  -- split.
      --- apply H2.
      --- split. 
          +++ assert (H5: length x + length x0 <= pumping_constant re2 ->
                          length x + length x0 <= pumping_constant re1 + pumping_constant re2).
              { lia. }
              apply (H5 H3).
          +++ intros.
              pose proof (H4 m) as H5.
              pose proof (MUnionR re1 (x ++ napp m x0 ++ x1) re2 H5) as H6.
              apply H6.
- intros.
  simpl in H.
  inversion H.
  pose proof (pumping_constant_0_false T re) as H2.
  exfalso.
  apply (H2 H1).
- intros.
  destruct s1.
  -- replace ([] ++ s2) with s2 in *. apply (IH2 H). simpl. reflexivity.
  -- pose proof (lt_ge_cases (length (x::s1)) (pumping_constant re)) as [Hs1lt | Hs1ge].
     --- exists [], (x::s1), s2. split.
         ---- simpl. reflexivity.
         ---- split.
              ++ unfold not. intros. inversion H0.
              ++ split.
                 +++ simpl. simpl in Hs1lt.
                     assert (H1: S (length s1) < pumping_constant re ->
                                 S (length s1) <= pumping_constant re). { lia. }
                     apply (H1 Hs1lt).
                 +++ intros. simpl.
                     apply (napp_star T m (x::s1) s2 re).
                     assumption. assumption.
      --- unfold ge in Hs1ge.
          pose proof (IH1 Hs1ge) as H2. 
          destruct H2. destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
          exists x0, x1, (x2++s2). split.
          ---- rewrite H0. repeat (rewrite app_assoc). reflexivity.
          ---- split.
               ++ assumption.
               ++ split.
                  +++ simpl. assumption.
                  +++ intros.
                      pose proof (H3 m) as H4.
                      pose proof (MStarApp (x0 ++ napp m x1 ++ x2) s2 re H4 Hmatch2) as H5.
                      assert (H6: (x0 ++ napp m x1 ++ x2) ++ s2 = x0 ++ napp m x1 ++ x2 ++ s2).
                      { repeat (rewrite app_assoc). reflexivity. } 
                      rewrite <- H6. assumption.
Qed.

(* End of regular expressions *)
  
Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
intros.
induction l. 
- exfalso.
  unfold not in H.
  apply H.
  reflexivity.
- simpl.
  simpl in H.
  destruct (n =? x) eqn: Heq.
  -- left.
     rewrite Logic.eqb_eq in Heq.
     symmetry.
     assumption.
  -- right.
     apply IHl.
     assumption.
Qed.

(* book version *)
Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite Logic.eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

 Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H : P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.
  

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
intros.
destruct H.
destruct b.
- assert (H1: P). { apply H0. reflexivity. }
  apply (ReflectT P).
  assumption.
- assert (H1: ~ P). { unfold not. intros. pose proof (H H1) as H2. inversion H2. }
  apply (ReflectF).
  assumption.
Qed.

(* book version *)
Theorem iff_reflect' : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
intros.
split.
intros.
destruct b eqn: Eb.
- reflexivity.
- inversion H.
  exfalso.
  unfold not in H1. apply (H1 H0).
- intros.
  inversion H.
  -- assumption.
  -- exfalso.
     symmetry in H2.
     destruct b eqn: Hb.
     --- inversion H2.
     --- inversion H0.
Qed.

Theorem reflect_iff_neg : forall P b, reflect P b -> (~P <-> b = false).
intros.
split.
- intros. unfold not in H0.
  apply reflect_iff in H.
  destruct H.
  destruct b eqn: Heq.
  -- exfalso. apply H0. apply H1. reflexivity.
  -- reflexivity.
- intros. unfold not. intros.
  apply reflect_iff in H.
  destruct H.
  destruct b eqn: Heq.
  -- discriminate H0.
  -- discriminate (H H1).
Qed.  

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
intros.
apply iff_reflect.
split.
- intros. rewrite H. apply Logic.eqb_eq. reflexivity.
- intros. apply Logic.eqb_eq. assumption.
Qed.

(* book version *)
Lemma eqbP' : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite Logic.eqb_eq. reflexivity.
Qed.

Theorem filter_not_empty_In_alt : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
intros.
induction l.
- simpl. unfold not in H. simpl in H. apply H. reflexivity.
- simpl.
  destruct (n =? x) eqn: Heq.
  -- left.
     pose proof (reflect_iff (n = x) (n =? x)) as H1.
     pose proof (H1 (eqbP n x)) as H2.
     symmetry.
     rewrite H2. assumption.
  -- right.
     apply IHl.
     simpl in H.
     rewrite Heq in H.
     assumption.
Qed.

(* book version *)
Theorem filter_not_empty_alt' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.
  
Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
intros.
unfold not.
intros.
induction l.
- inversion H0.
- simpl in H.
  destruct (eqbP n x) as [H1 | H1].
  -- discriminate H.
  -- simpl in H.
     pose proof (IHl H) as H2.
     apply H2.
     simpl in H0.
     destruct H0.
     --- exfalso.
         symmetry in H0.
         unfold not in H1. apply (H1 H0).
     --- exfalso. apply (H2 H0).
Qed.

Inductive nostutter {X:Type} : list X -> Prop :=
 | EmptyNoStutter : nostutter []
 | CharNoStutter (x : X) : nostutter [x]
 | ListNoStutter (x1 x2 : X) 
                 (l : list X) 
                 (H1 : x1 <> x2) 
                 (H2: nostutter (x2 :: l)) : nostutter (x1::x2::l).
 
Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. 
repeat constructor.
- unfold not. intros. inversion H.
- unfold not. intros. inversion H.
- unfold not. intros. inversion H.
- unfold not. intros. inversion H.
- unfold not. intros. inversion H.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof. apply EmptyNoStutter.
Qed.

Example test_nostutter_3: nostutter [5].
Proof. apply CharNoStutter. Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto. 
Qed.

Inductive is_merge {X:Type} : list X -> list X -> list X -> Prop :=
  | EmptyMergeL (l : list X) : is_merge l [] l
  | EmptyMergeR (l : list X) : is_merge l l []
  | RegularMergeL (x : X) (l l1 l2 : list X) (H: is_merge l l1 l2) 
                  : is_merge (x::l) (x::l1) l2
  | RegularMergeR (x : X) (l l1 l2 : list X) (H: is_merge l l1 l2) 
                  : is_merge (x::l) l1 (x::l2).

Example merge_1: is_merge [1;4;6;2;3] [1;6;2] [4;3].
Proof.
apply RegularMergeL.
apply RegularMergeR.
apply RegularMergeL.
apply RegularMergeL.
apply EmptyMergeL.
Qed.

Fixpoint filter {X:Type} (test: X->bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Lemma tail_eq : forall {X:Type} (l1 l2 : list X),
  l1 = l2 -> tail l1 = tail l2.
intros.
rewrite H. reflexivity.
Qed.

Lemma prefix_eq : forall {X:Type} (x : X) (l1 l2 : list X),
  l1 = l2 -> x::l1 = x::l2.
intros.
rewrite H. reflexivity.
Qed.

Lemma filter_len : forall {X:Type} (test0:X->bool) (l1 : list X),
  length (filter test0 l1) <= length l1. 
Proof.
intros.
induction l1.
- simpl. reflexivity.
- simpl. destruct (test0 x).
  -- simpl. lia.
  -- lia.
Qed.
 
Theorem filter_challenge1 : forall {X:Type} (test:X->bool) (l l1 l2 : list X),
  is_merge l l1 l2 ->
  filter test l1 = l1 ->
  filter test l2 = [] ->
  filter test l = l1.
Proof.
intros.
induction H.
- assumption.
- assumption.
- simpl.
  destruct (test0 x) eqn: Heq.
  -- simpl in H0.
     rewrite Heq in H0.
     pose proof (tail_eq (x :: filter test0 l1) (x::l1)) as H2.
     pose proof (H2 H0) as H3.
     simpl in H3.
     pose proof ((IHis_merge H3) H1) as H4.
     apply (prefix_eq x (filter test0 l) l1).
     assumption.
  -- simpl in H0.
     rewrite Heq in H0.
     pose proof (filter_len test0 l1) as H2.
     rewrite H0 in H2.
     simpl in H2.
     exfalso.
     lia.
- simpl.
  destruct (test0 x) eqn: Heq.
  -- pose proof (IHis_merge H0) as H2.
     simpl in H1.
     rewrite Heq in H1.
     exfalso.
     inversion H1.
  -- pose proof (IHis_merge H0) as H2.
     simpl in H1.
     rewrite Heq in H1.
     apply (H2 H1).
Qed.


Lemma filter_subseq : forall (test0 : nat->bool) (l1 l2 : list nat),
  subseq l1 l2 -> subseq (filter test0 l1) (filter test0 l2).
Proof.
intros.
induction H.
- simpl. apply subseq1.
- destruct (test0 h) eqn: Heq.
  -- simpl. rewrite Heq.
     apply subseq2.
     assumption.
  -- simpl. rewrite Heq.
     assumption.
- destruct (test0 h) eqn: Heq.
  -- simpl. rewrite Heq.
     apply subseq3.
     assumption.
  -- simpl. rewrite Heq.
     assumption.
Qed. 

Lemma subseq_x1_x2 : forall (x1 x2 : nat) (l1 l2 : list nat),
  x1 <> x2 ->
  subseq (x1::l1) (x2::l2) ->
  subseq (x1::l1) l2.
Proof.
intros.
apply subseq_inversion in H0.
destruct H0.
- exfalso. inversion H0.
- destruct H0.
  -- simpl in H0. assumption.
  -- destruct H0.
     simpl in H0.
     inversion H0.
     unfold not in H.
     exfalso.
     apply (H H3).
Qed.

Lemma subseq_le : forall (l1 l2 : list nat),
  subseq l1 l2 -> length l1 <= length l2.
Proof.
intros.
generalize dependent l1.
induction l2.
- intros. inversion H. reflexivity.
- intros.
  destruct l1.
  -- simpl. lia.
  -- destruct (x0 =? x) eqn: Heq.
     --- simpl.
         pose proof (eqbP x0 x) as H1.
         apply reflect_iff in H1.
         rewrite <- H1 in Heq.
         rewrite Heq in H.
         apply subseq_h_h_implies in H.
         pose proof (((IHl2 l1) H)) as H2.
         lia.
     --- simpl.
         pose proof (eqbP x0 x) as H1.
         pose proof (reflect_iff_neg (x0 = x) (x0 =? x)) as H2.
         pose proof (H2 H1) as H3.
         rewrite <- H3 in Heq.
         apply subseq_x1_x2 in H.
         ---- apply subseq_impl_tail in H. simpl in H.
              pose proof ((IHl2 l1) H) as H4.
              lia.
         ---- assumption.
Qed.

(* The following two lemmas are to show that (filter test0 l2) also belongs 
   to the set of subsequences of l2 for which test0 returns true for all their elements.
   
   Without these, we prove filter_challenge2, but wouldn't have shown 
   that the upper bound also belongs to the set of subsequences to 
   which l1 belongs. If required, we can add the necessary clauses 
   to the conclusion of filter_challenge2 and apply these two lemmas.
*)   
Lemma filter_all_true : forall (test0 : nat->bool) (l : list nat),
  forall x, In x (filter test0 l) -> test0 x = true.
intros.
induction l.
- exfalso. simpl in H. assumption.
- simpl In in H.
  destruct (test0 x0) eqn: Heq.
  simpl In in H.
  destruct H.
  -- rewrite H in Heq. assumption.
  -- apply (IHl H).
  -- apply (IHl H).
Qed.  

Lemma filter_is_subseq : forall (test0 : nat->bool) (l : list nat),
  subseq (filter test0 l) l.
Proof.
intros.
induction l.
- simpl. apply subseq1.
- destruct (test0 x) eqn: Heq.
  -- simpl. rewrite Heq.
     apply subseq2.
     assumption.
  -- simpl. rewrite Heq.
     apply subseq3.
     assumption.
Qed.     

Theorem filter_challenge2 : forall (test0 : nat->bool) (l1 l2 : list nat),
  subseq l1 l2 ->
  filter test0 l1 = l1 ->
  length l1 <= length (filter test0 l2).
Proof.
intros.
pose proof (filter_subseq test0 l1 l2) as H1.
pose proof (H1 H) as H2.
pose proof (subseq_le (filter test0 l1) (filter test0 l2)) as H3.
pose proof (H3 H2) as H4.
rewrite H0 in H4.
assumption.
Qed.

Inductive pal {X:Type} : list X -> Prop :=
  | EmptyPal  : pal []
  | CharPal (x : X) : pal [x]
  | EndsPal (x : X) (l : list X) (H : pal l) : pal ((x :: l) ++ [x]).
  
Theorem pal_app_rev : forall (X:Type) (l : list X), pal (l ++ rev l).
Proof.
intros.
induction l.
- simpl. apply EmptyPal.
- simpl rev.
  pose proof (EndsPal x (l ++ (rev l)) IHl) as H.
  assert (H1: (x :: l ++ rev l) ++ [x] = (x :: l) ++ rev l ++ [x]). 
  { assert (H2: (x :: l ++ rev l) = (x :: l) ++ rev l). { reflexivity. }
    rewrite H2. rewrite app_assoc. reflexivity. }
  rewrite <- H1.
  assumption.
Qed.

Compute rev (1::[2;3;4] ++ [5]).

Lemma rev_helper : forall (X:Type) (x:X) (l:list X),
  rev (l ++ [x]) = x :: (rev l).
Proof.
intros.
induction l.
- simpl. reflexivity.
- simpl.
  rewrite IHl.
  reflexivity.
Qed.

Theorem pal_rev : forall (X:Type) (l : list X), pal l -> l = rev l.
Proof.
intros.
induction H.
- reflexivity.
- reflexivity.
- simpl. rewrite rev_helper.
  rewrite <- IHpal.
  reflexivity.
Qed.

Definition but_last {X:Type} (l : list X) : (list X) :=
  rev (tail (rev l)).
  
Compute but_last [1;2].

Definition last {X:Type} (l : list X) : option X :=
  head (rev l).
  
Compute last [1;2;3].

Lemma but_last_append : forall {X:Type} (x:X) (l:list X),
  but_last (l ++ [x]) = l.
Admitted. (* can be proved *)

(*
Lemma pal_helper : forall {X:Type} (l:list X),
  l = rev l ->
  l <> [] ->
  exists x l', l = x :: l' ++ [x] /\ pal l'.
Admitted.
*)

Theorem palindrome_converse : forall (X:Type) (l : list X), l = rev l -> pal l.
Proof.
(* Moving on, will come back to this later if possible *)


