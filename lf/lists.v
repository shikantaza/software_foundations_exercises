From LF Require Export Induction.

Require Import Lia.

Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
intros.
destruct p.
simpl snd.
simpl fst.
reflexivity.
Qed.
  
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
intros.
destruct p.
simpl swap_pair.
simpl fst.
simpl snd.
reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Fixpoint nonzeros (l:natlist) : natlist :=
match l with
| nil => nil
| h :: t => match h with
            | O => nonzeros t
            | n => n :: (nonzeros t)
            end
end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof.
reflexivity.
Qed.

Fixpoint odd (n : nat) : bool :=
match n with
| O => false
| S n' => even n'
end
with even (n : nat) : bool :=
match n with
| O => true
| S n' => odd n'
end.

Compute odd 3.

Fixpoint oddmembers (l:natlist) : natlist :=
match l with
| nil => nil
| h :: t => match (odd h) with
            | true => h :: oddmembers t
            | false => oddmembers t
            end
end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof.
reflexivity.
Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
match l with
| nil => 0
| h :: t => match (odd h) with
            | true => S (countoddmembers t)
            | false => countoddmembers t
            end
end.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof.
reflexivity.
Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof.
reflexivity.
Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof.
reflexivity.
Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
match l1 with
| nil => l2
| h1 :: t1 => match l2 with
            | nil => h1 :: t1
            | h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
            end
end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof.
reflexivity.
Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof.
reflexivity.
Qed.

Compute alternate [1;2;3] [4].

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof.
reflexivity.
Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof.
reflexivity.
Qed.

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
match s with
| nil => 0
| h :: t => match (eqb h v) with
            | true => S (count v t)
            | false => count v t
            end
end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof.
reflexivity.
Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof.
reflexivity.
Qed.

Definition sum : bag -> bag -> bag := fun b1 b2 => b1 ++ b2.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof.
reflexivity.
Qed.

Definition add (v : nat) (s : bag) : bag := v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof.
reflexivity.
Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof.
reflexivity.
Qed.

Definition member (v : nat) (s : bag) : bool :=
match (count v s) with
| O => false
| _ => true
end.

Example test_member1: member 1 [1;4;1] = true.
Proof.
reflexivity.
Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof.
reflexivity.
Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
match s with
| nil => nil
| h :: t => match (eqb h v) with
            | true => t
            | false => h :: (remove_one v t)
            end
end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof.
reflexivity.
Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof.
reflexivity.
Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof.
reflexivity.
Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof.
reflexivity.
Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
match s with
| nil => nil
| h :: t => match (eqb h v) with
            | true => (remove_all v t)
            | false => h :: (remove_all v t)
            end
end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof.
reflexivity.
Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof.
reflexivity.
Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof.
reflexivity.
Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof.
reflexivity.
Qed.

Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
match s1, s2 with
| nil, _ => true
| _, nil => false
| h1 :: t1, h2 :: t2 => match (member h1 s2) with
                        | true => subset t1 (remove_one h1 s2)
                        | false => false
                        end
end.

Compute subset [1;2] [2;1;4;1].

Example test_subset1: subset [1;2] [2;1;4;1] = true.  
Proof.
reflexivity.
Qed.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof.
reflexivity.
Qed.

(* this is not what was asked to be proved *)
Example add_impl_incr_count': forall (s : bag) (v : nat), length (add v s) = (length s) + 1.
Proof.
intros.
induction s.
simpl.
reflexivity.
simpl.
lia.
Qed.

Lemma count_one: forall v, count v [v] = 1.
Proof.
intros.
induction v.
simpl.
reflexivity.
simpl count.
tauto.
Qed.

Lemma append_nil_r: forall s, s ++ [] = s.
intros.
induction s.
simpl.
reflexivity.
simpl.
rewrite IHs.
reflexivity.
Qed.

Lemma append_nil_l: forall s, [] ++ s = s.
intros.
induction s.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Lemma count_two_lists: forall (s1 s2 : bag) (v : nat), count v (s1 ++ s2) = count v s1 + count v s2.
Proof.
intros.
induction s1.
rewrite append_nil_l.
simpl.
reflexivity.
simpl.
destruct (n =? v).
assert (H: S (count v s1) + count v s2 = S (count v s1 + count v s2)). { lia. }
rewrite H. clear H.
rewrite IHs1.
reflexivity.
exact IHs1.
Qed.

Theorem add_impl_incr_count: forall (s : bag) (v : nat), count v (add v s) = (count v s) + 1.
Proof.
intros.
induction s.
assert (H: add v [] = [v]). { reflexivity. } rewrite H. clear H.
assert (H: count v [] = 0). { reflexivity. } rewrite H. clear H.
pose proof (count_one v) as H. rewrite H. clear H.
simpl. reflexivity.
assert (H: add v (n::s) = v::n::s). { reflexivity. }
rewrite H. clear H.
assert (H: v::n::s = [v ; n] ++ s). { reflexivity. }
rewrite H. clear H.
pose proof (count_two_lists [v ; n] s v) as H.
rewrite H. clear H.
assert (H: [v; n] = [v] ++ [n]). { reflexivity. }
rewrite H. clear H.
pose proof (count_two_lists [v] [n] v) as H.
rewrite H. clear H.
rewrite (count_one v).
pose proof (count_two_lists [n] s v) as H.
assert (H1: 1 + count v [n] + count v s = 1 + (count v [n] + count v s)). { reflexivity. }
rewrite H1. clear H1.
rewrite <- H. clear H.
assert (H: [n] ++ s = n :: s). { reflexivity. }
rewrite H. clear H.
rewrite add_comm.
reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
intros.
induction l1.
rewrite append_nil_l.
simpl rev.
rewrite append_nil_r.
reflexivity.
assert (H: rev (n :: l1) = rev l1 ++ [n]). { reflexivity. }
rewrite H. clear H.
rewrite <- app_assoc.
rewrite <- IHl1.
reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
intros.
induction l.
simpl.
reflexivity.
assert (H: rev (n :: l) = rev l ++ [n]). { reflexivity. }
rewrite H. clear H.
rewrite rev_app_distr.
rewrite IHl.
reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
intros.
repeat rewrite app_assoc.
reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
intros.
induction l1.
rewrite append_nil_l.
simpl.
reflexivity.
destruct n.
assert (H: nonzeros (0::l1) = nonzeros l1). { reflexivity. }
rewrite H. clear H.
rewrite <- IHl1.
reflexivity.
assert (H: nonzeros (S n :: l1) = S n :: (nonzeros l1)). { reflexivity. }
rewrite H. clear H.
assert (H: (S n :: nonzeros l1) ++ nonzeros l2 = [S n] ++ nonzeros l1 ++ nonzeros l2).
{ reflexivity. }
rewrite H. clear H.
rewrite <- IHl1.
reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
match l1, l2 with
| nil, nil       => true
| nil, _         => false
| _, nil         => false
| h1::t1, h2::t2 => match (eqb h1 h2) with
                    | true => eqblist t1 t2
                    | false => false
                    end
end.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. reflexivity. Qed.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Lemma eq_lemma : forall n, (eqb n n) = true.
intros.
induction n.
simpl.
reflexivity.
simpl.
assumption.
Qed.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite eq_lemma.
assumption.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
intros.
induction s.
simpl.
reflexivity.
assert (H: count 1 (1 :: n :: s) = 1 + count 1 (n :: s)). { reflexivity. }
rewrite H. clear H.
easy.
Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
intros.
induction s.
simpl.
reflexivity.
simpl count.
destruct n.
simpl.
apply leb_n_Sn.
simpl.
assumption.
Qed.

(* theorem involving bag, count, and sum already done (count_two_lists above) *)

Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
intros.
pose proof (rev_involutive l1) as H1.
pose proof (rev_involutive l2) as H2.
rewrite H in H1.
rewrite H1 in H2.
assumption.
Qed.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Definition hd_error (l : natlist) : natoption :=
match l with
| nil => None
| h :: t => Some h
end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

End NatList.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Module PartialMap.
Export NatList.

Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
intros.
destruct x.
simpl.
apply eq_lemma.
Qed.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
intros.
simpl.
rewrite eqb_id_refl.
reflexivity.
Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
intros.
simpl.
rewrite H.
reflexivity.
Qed.

Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).

(* the type baz has zero elements because we cannot create any value using
   the provided constructors - each constructor depends on an existing baz value *)