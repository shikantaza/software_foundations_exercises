Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Export Imp.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.
    
Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.
    
Theorem aequiv_example:
  aequiv
    <{ X - X }>
    <{ 0 }>.
Proof.
unfold aequiv.
intros.
simpl.
lia.
Qed.

Theorem bequiv_example:
  bequiv
    <{ X - X = 0 }>
    <{ true }>.
Proof.
unfold bequiv.
intros.
simpl.
assert (H: st X - st X = 0) by lia.
rewrite H. reflexivity.
Qed.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').
    
Definition refines (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') -> (st =[ c2 ]=> st').
    
Theorem skip_left : forall c,
  cequiv
    <{ skip; c }>
    c.    
Proof.    
intros.
unfold cequiv.
intros.
split.
- intros.
  inversion H.
  subst.
  inversion H2.
  assumption.
- intros.
  apply E_Seq with st.
  -- apply E_Skip.
  -- assumption.
Qed.

Theorem skip_right : forall c,
  cequiv
    <{ c ; skip }>
    c.
Proof.
intros.
unfold cequiv.
split.
- intros.
  inversion H. subst. inversion H5. subst. assumption.
- intros. apply E_Seq with st'.
  -- assumption.
  -- apply E_Skip.
Qed.

Theorem if_true_simple : forall c1 c2,
  cequiv
    <{ if true then c1 else c2 end }>
    c1.
intros.
unfold cequiv.
intros.
split.
- intros. inversion H. 
  -- subst. assumption.
  -- subst. discriminate.
- intros. apply E_IfTrue.
  -- reflexivity.
  -- assumption.
Qed.

Theorem if_true: forall b c1 c2,
  bequiv b <{true}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c1.
Proof.
intros.
unfold cequiv.
intros.
split.
- intros. inversion H0.
  -- subst. assumption.
  -- subst. unfold bequiv in H.
     pose proof (H st). simpl in H1. rewrite H6 in H1. discriminate.
- intros. unfold bequiv in H. pose proof (H st) as H1.
  simpl in H1. apply E_IfTrue.
  -- assumption.
  -- assumption.
Qed.


Theorem if_false :forall b c1 c2,
  bequiv b <{false}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c2.
Proof.
intros.
unfold cequiv.
intros.
split.
- intros. inversion H0.
  -- subst. unfold bequiv in H. pose proof (H st) as H1. simpl in H1.
     rewrite H6 in H1. discriminate.
  -- subst. assumption.
- intros.
  unfold bequiv in H. pose proof (H st) as H1. simpl in H1.
  apply E_IfFalse.
  -- assumption.
  -- assumption.
Qed.

Theorem swap_if_branches : forall b c1 c2,
  cequiv
    <{ if b then c1 else c2 end }>
    <{ if ~ b then c2 else c1 end }>.
Proof.
intros.
unfold cequiv.
intros.
split.
- intros. inversion H.
  -- subst. apply E_IfFalse.
     --- simpl. rewrite H5. reflexivity.
     --- assumption.
  -- subst. apply E_IfTrue.
     --- simpl. rewrite H5. reflexivity.
     --- assumption.
- intros. inversion H.
  -- subst. apply E_IfFalse.
     --- simpl in H5. destruct (beval st b) eqn: Heq.
         * discriminate H5.
         * reflexivity.
     --- assumption.
  -- subst. apply E_IfTrue.
     --- simpl in H5. destruct (beval st b) eqn: Heq.
         * reflexivity.
         * discriminate H5.
     --- assumption.
Qed.

Theorem while_false : forall b c,
  bequiv b <{false}> ->
  cequiv
    <{ while b do c end }>
    <{ skip }>.
Proof.
intros.
unfold cequiv.
intros.
split.
- intros. inversion H0.
  -- subst. apply E_Skip.
  -- subst. unfold bequiv in H.
     pose proof (H st) as H8. rewrite H3 in H8. discriminate H8.
- intros. inversion H0. apply E_WhileFalse.
  rewrite <- H3. unfold bequiv in H.
  pose proof (H st) as H4.
  rewrite H4. reflexivity.
Qed.

(* Informal proof of while_false *)
(*

(1) forward direction (->)

    st =[ while b do c end ]=> st' can hold under two conditions:

    a) (beval st b) is false - in which case st = st', which is what needs to
       proven
    b) (beval st b) is true - this contradicts the assumption that b is false 

2) reverse direction (<-)

   since st =[ skip ]=> st', st = st'
   
   we need to show that st =[ while b do c end ]=> st' holds, or, since b is 
   false, st = st', which is true.
*)

Lemma while_true_nonterm : forall b c st st',
  bequiv b <{true}> ->
  ~ (st =[ while b do c end ]=> st').
Proof.
intros.
unfold not.
intros. 
remember <{ while b do c end }> as cw eqn:Heqcw.
induction H0.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
- inversion Heqcw.
  rewrite <- H2 in H.
  rewrite H in H0.
  discriminate.
- apply (IHceval2 Heqcw).
Qed.

(* Explain what the lemma while_true_nonterm means in English. *)
(* A non-terminating program or command can never return a state
   from any initial state *)
   
Theorem while_true : forall b c,
  bequiv b <{true}> ->
  cequiv
    <{ while b do c end }>
    <{ while true do skip end }>.
Proof.   
intros.
unfold cequiv.
intros.
split.
- intros.
  exfalso.
  apply (while_true_nonterm b c st st' H). apply H0.
- intros.
  exfalso.
  assert (H1: bequiv BTrue <{true}>). { unfold bequiv. reflexivity. } 
  apply (while_true_nonterm <{true}> <{skip}> st st' H1).
  apply H0.
Qed.

Theorem loop_unrolling : forall b c,
  cequiv
    <{ while b do c end }>
    <{ if b then c ; while b do c end else skip end }>.
Proof.
intros.
unfold cequiv.
intros.
split.
- intros.
  inversion H.
  -- subst. apply E_IfFalse.
     * assumption.
     * apply E_Skip.
  -- subst. apply E_IfTrue.
     * assumption.
     * apply E_Seq with st'0.
       ** assumption.
       ** assumption.
- intros.
  inversion H.
  -- subst. inversion H6.
     subst. apply E_WhileTrue with st'0.
     * assumption.
     * assumption.
     * assumption.
  -- subst. inversion H6.
     subst. apply E_WhileFalse.
     assumption.
Qed.

Theorem seq_assoc : forall c1 c2 c3,
  cequiv <{(c1;c2);c3}> <{c1;(c2;c3)}>.
Proof.
intros.
unfold cequiv.
intros.
split.
- intros.
  inversion H. clear H. subst.
  inversion H2. clear H2. subst.
  pose proof (E_Seq c2 c3 st'1 st'0 st' H6 H5) as H7.
  pose proof (E_Seq c1 <{c2; c3}> st st'1 st' H1 H7) as H8.
  apply H8.
- intros.
  inversion H. clear H. subst.
  inversion H5. clear H5. subst.
  pose proof (E_Seq c1 c2 st st'0 st'1 H2 H1) as H7.
  pose proof (E_Seq <{c1;c2}> c3 st st'1 st' H7 H6) as H8.
  apply H8.
Qed.

Theorem identity_assignment : forall x,
  cequiv
    <{ x := x }>
    <{ skip }>.
Proof.
intros.
unfold cequiv.
intros.
split.
- intros.
  inversion H. clear H. subst.
  simpl.
  rewrite t_update_same.
  apply E_Skip.
- intros.
  inversion H. clear H. subst.
  assert (H1: st' =[ x := x]=> (x !-> st' x; st')). {
  apply E_Asgn. simpl. reflexivity. }
  rewrite t_update_same in H1.
  apply H1.
Qed.

Theorem assign_aequiv : forall (X : string) (a : aexp),
  aequiv <{ X }> a ->
  cequiv <{ skip }> <{ X := a }>.
Proof.  
intros.
unfold cequiv.
intros.
split.
- intros.
  inversion H0. clear H0. subst.
  unfold aequiv in H.
  pose proof (H st') as H1.
  assert (H2: st' =[ X := a ]=> (X !-> aeval st' a; st')). {
    apply E_Asgn. reflexivity.
  }
  rewrite <- H1 in H2.
  rewrite t_update_same in H2.
  apply H2.
- intros.
  inversion H0. clear H0. subst.
  unfold aequiv in H.
  pose proof (H st) as H1.
  rewrite <- H1.
  rewrite t_update_same.
  apply E_Skip.
Qed.
    
(* equiv_classes *)

Definition prog_a : com :=
  <{ while ~(X <= 0) do
       X := X + 1
     end }>.  
  
(* prog_a doesn't terminate if x > 0, terminates with x set to 1 if x = 0 *)  
  
Definition prog_b : com :=
  <{ if (X = 0) then
       X := X + 1;
       Y := 1
     else
       Y := 0
     end;
     X := X - Y;
     Y := 0 }>.  
  
(* prog_b sets y to 0 *)

Definition prog_c : com :=
  <{ skip }> .
  
(* prog_c does nothing, i.e., leaves the state unchanged *)

Definition prog_d : com :=
  <{ while X <> 0 do
       X := (X * Y) + 1
     end }>.
  
(* if x = 0, prog_d does nothing. if x <> 0, it doesn't terminate *)

Definition prog_e : com :=
  <{ Y := 0 }>.  
  
(* prog_e sets y to 0 *)

Definition prog_f : com :=
  <{ Y := X + 1;
     while X <> Y do
       Y := X + 1
     end }>.

(* prog_f doesn't terminate for any initial state *)

Definition prog_g : com :=
  <{ while true do
       skip
     end }>.

(* prog_g doesn't terminate for any initial state *)

Definition prog_h : com :=
  <{ while X <> X do
       X := X + 1
     end }>.

(* prog_h does nothing, i.e., leaves the state unchanged *)

Definition prog_i : com :=
  <{ while X <> Y do
       X := Y + 1
     end }>.

(* if x = y, prog_i does nothing. if x < y, sets x to y and terminates.
   if x > y, doesn't terminate *)

(* Equivalence classes: [ [prog_a]; [prog_b; prog_e]; [prog_c; prog_h];
                          [prog_d]; [prog_f; prog_g]; [prog_i] ] *)

Lemma refl_aequiv : forall (a : aexp),
  aequiv a a.
Proof.
intros. unfold aequiv. intros. reflexivity.
Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof. intros. unfold aequiv in H. unfold aequiv.
intros. pose proof (H st) as H1.
symmetry in H1. apply H1.
Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
intros. unfold aequiv.
intros. unfold aequiv in H0. unfold aequiv in H.
pose proof (H st) as H1. pose proof (H0 st) as H2.
rewrite <- H1 in H2. apply H2.
Qed.

Lemma refl_bequiv : forall (b : bexp),
  bequiv b b.
Proof. intros. unfold bequiv. intros. reflexivity. Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof. 
intros. unfold bequiv in H. unfold bequiv.
intros. pose proof (H st) as H1.
symmetry in H1. apply H1.
Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
intros. unfold bequiv in H. unfold bequiv in H0.
unfold bequiv. intros.
pose proof (H st) as H1. pose proof (H0 st) as H2.
rewrite <- H1 in H2. apply H2.
Qed.

Lemma refl_cequiv : forall (c : com),
  cequiv c c.
Proof. intros. unfold cequiv. intros. reflexivity. Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
intros. unfold cequiv in H. unfold cequiv.
intros. pose proof (H st st') as H1.
destruct H1.
split.
- apply H1.
- apply H0.
Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
intros.
unfold cequiv in H. unfold cequiv in H0. unfold cequiv.
intros. pose proof (H st st') as H1. pose (H0 st st') as H2.
destruct H1. destruct H2.
split.
- intros. apply H2. apply H1. apply H5.
- intros. apply H3. apply H4. apply H5.
Qed.

Theorem CAsgn_congruence : forall x a a',
  aequiv a a' ->
  cequiv <{x := a}> <{x := a'}>.
Proof.
intros.
unfold cequiv.
intros.
unfold aequiv in H.  
pose proof (H st) as H1.
split.
- intros.
  inversion H0. subst.
  rewrite H1.
  assert (H2: st =[ x := a' ]=> (x !-> aeval st a'; st)). {
    apply E_Asgn. reflexivity.
  }
  apply H2.
- intros.  
  inversion H0. subst.
  rewrite <- H1.
  assert (H2: st =[ x := a ]=> (x !-> aeval st a; st)). {
    apply E_Asgn. reflexivity.
  }
  apply H2.
Qed.

Theorem CWhile_congruence : forall b b' c c',
  bequiv b b' -> cequiv c c' ->
  cequiv <{ while b do c end }> <{ while b' do c' end }>.
Proof.

assert (A: forall b b' c c' st st', 
           bequiv b b' -> cequiv c c' ->
           st =[ while b do c end ]=> st' ->
           st =[ while b' do c' end ]=> st'). {

intros.
remember <{ while b do c end }> as cwhile
      eqn:Heqcwhile.
induction H1.
  -- discriminate.
  -- discriminate.
  -- discriminate.
  -- discriminate.
  -- discriminate.
  -- inversion Heqcwhile. subst.
     apply E_WhileFalse.
     unfold bequiv in H.
     pose proof (H st) as H2.
     rewrite H1 in H2. symmetry in H2. apply H2.
  -- inversion Heqcwhile. subst.
     apply E_WhileTrue with st'.
     * unfold bequiv in H.
       pose proof (H st) as H2.
       rewrite H1 in H2. symmetry in H2. apply H2.
     * unfold cequiv in H0.
       pose proof (H0 st st') as H2.
       destruct H2. apply (H2 H1_).
     * pose proof (IHceval2 Heqcwhile) as H2.
       apply H2.
}
intros.  
split.
- apply A.
  * assumption.
  * assumption.
- apply A.
  * apply sym_bequiv. assumption.
  * apply sym_cequiv. assumption.
Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof.

assert (A: forall c1 c1' c2 c2' st st',
           cequiv c1 c1' -> cequiv c2 c2' ->
           st =[ c1;c2 ]=> st' -> st =[ c1';c2' ]=> st'). {
  intros.
  remember <{ c1; c2 }> as cseq eqn: Heqseq.
  induction H1; inversion Heqseq; subst.
  apply E_Seq with st'.
  * unfold cequiv in H. apply (H st st'). assumption.
  * unfold cequiv in H0. apply (H0 st' st''). assumption.
}

intros.
unfold cequiv.
intros.
split.
- apply A.
  * assumption.
  * assumption.
- apply A. 
  * apply sym_cequiv. assumption.
  * apply sym_cequiv. assumption.
Qed.    

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ if b then c1 else c2 end }>
         <{ if b' then c1' else c2' end }>.
Proof.

assert (A: forall b b' c1 c1' c2 c2' st st',
           bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
           st =[ if b then c1 else c2 end ]=> st' ->
           st =[ if b' then c1' else c2' end ]=> st'). {
  intros.
  remember <{ if b then c1 else c2 end }> as cif eqn: Heqif.
  induction H2; inversion Heqif; subst.
  - apply E_IfTrue.
    * unfold bequiv in H. pose proof (H st) as H4.
      rewrite H2 in H4. symmetry in H4. apply H4.
    * unfold cequiv in H0. pose proof (H0 st st') as H4.
      destruct H4. apply (H4 H3).
  - apply E_IfFalse.
    * unfold bequiv in H. pose proof (H st) as H4.
      rewrite H2 in H4. symmetry in H4. apply H4.
    * unfold cequiv in H1. pose proof (H1 st st') as H4.
      destruct H4. apply (H4 H3).
}
intros.
unfold cequiv.
intros.
split.
- apply A; assumption.
- apply A; 
   try (apply sym_bequiv; assumption);
   try (apply sym_cequiv; assumption).
Qed.  
  
Example congruence_example:
  cequiv
    (* Program 1: *)
    <{ X := 0;
       if (X = 0) then Y := 0
       else Y := 42 end }>
    (* Program 2: *)
    <{ X := 0;
       if (X = 0) then Y := X - X (* <--- Changed here *)
       else Y := 42 end }>.
Proof.
apply CSeq_congruence.
- apply refl_cequiv.
- apply CIf_congruence.
  -- apply refl_bequiv.
  -- apply CAsgn_congruence.
     unfold aequiv. intros. simpl. lia.
  -- apply refl_cequiv.
Qed.

(*

We've shown that the cequiv relation is both an equivalence and a congruence 
on commands. Can you think of a relation on commands that is an equivalence 
but not a congruence? Write down the relation (formally), together with an 
informal sketch of a proof that it is an equivalence but not a congruence.

*)

(*

A relation that holds if both commands sets a variable, say X, to, say 3.

This relation is an equivalence.

If the commands are embedded in the else clause of an 'if..' program which 
never executes the else clause, the two versions of the 'if' program
will not be equivalent, as neither version sets X to 3.

*)

Definition equiv_non_congr (c1 c2 : com) : Prop :=
  forall (st st' : state),
    ((st =[ c1 ]=> st') -> (st' X = 3) /\
     (st =[ c2 ]=> st') -> (st' X = 3)).

Lemma refl_equiv_non_congr : forall c, equiv_non_congr c c.
Proof.
intros.
unfold equiv_non_congr.
intros.
destruct H0.
assumption.
Qed.

Lemma sym_equiv_non_congr : forall c1 c2,
  equiv_non_congr c1 c2 -> equiv_non_congr c2 c1.
Proof.
intros.
unfold equiv_non_congr.
unfold equiv_non_congr in H.
intros.
destruct H1.
assumption.
Qed.

Lemma trans_equiv_non_congr : forall c1 c2 c3,
  equiv_non_congr c1 c2 ->
  equiv_non_congr c2 c3 ->
  equiv_non_congr c1 c3.
Proof.
intros.
unfold equiv_non_congr.
unfold equiv_non_congr in H.
intros.
destruct H2.
assumption.
Qed.


Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).
    
Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).
    
Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | <{ a1 + a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => <{ a1' + a2' }>
    end
  | <{ a1 - a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => <{ a1' - a2' }>
    end
  | <{ a1 * a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => <{ a1' * a2' }>
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp <{ (1 + 2) * X }>
  = <{ 3 * X }>.
Proof.
unfold fold_constants_aexp. (* <-- not needed *)
reflexivity.
Qed.

Example fold_aexp_ex2 :
  fold_constants_aexp <{ X - ((0 * 6) + Y) }> = <{ X - (0 + Y) }>.
Proof. reflexivity. Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | <{true}> => <{true}>
  | <{false}> => <{false}>
  | <{ a1 = a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' = a2' }>
      end
  | <{ a1 <> a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if negb (n1 =? n2) then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <> a2' }>
      end
  | <{ a1 <= a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <= a2' }>
      end
  | <{ a1 > a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{false}> else <{true}>
      | (a1', a2') =>
          <{ a1' > a2' }>
      end
  | <{ ~ b1 }> =>
      match (fold_constants_bexp b1) with
      | <{true}> => <{false}>
      | <{false}> => <{true}>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }> =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (<{true}>, <{true}>) => <{true}>
      | (<{true}>, <{false}>) => <{false}>
      | (<{false}>, <{true}>) => <{false}>
      | (<{false}>, <{false}>) => <{false}>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.
 
Example fold_bexp_ex1 :
  fold_constants_bexp <{ true && ~(false && true) }>
  = <{ true }>.  
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp <{ (X = Y) && (0 = (2 - (1 + 1))) }>
  = <{ (X = Y) && true }>.
Proof. reflexivity. Qed.  
  
Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | <{ skip }> =>
      <{ skip }>
  | <{ x := a }> =>
      <{ x := (fold_constants_aexp a) }>
  | <{ c1 ; c2 }> =>
      <{ fold_constants_com c1 ; fold_constants_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match fold_constants_bexp b with
      | <{true}> => fold_constants_com c1
      | <{false}> => fold_constants_com c2
      | b' => <{ if b' then fold_constants_com c1
                       else fold_constants_com c2 end}>
      end
  | <{ while b do c1 end }> =>
      match fold_constants_bexp b with
      | <{true}> => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b' => <{ while b' do (fold_constants_com c1) end }>
      end
  end.
  
Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    <{ X := 4 + 5;
       Y := X - 3;
       if ((X - Y) = (2 + 4)) then skip
       else Y := 0 end;
       if (0 <= (4 - (2 + 1))) then Y := 0
       else skip end;
       while (Y = 0) do
         X := X + 1
       end }>
  = (* After constant folding: *)
    <{ X := 9;
       Y := X - 3;
       if ((X - Y) = 6) then skip
       else Y := 0 end;
       Y := 0;
       while (Y = 0) do
         X := X + 1
       end }>.    
Proof. reflexivity. Qed.

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
unfold atrans_sound.
intros.
induction a;
try (unfold fold_constants_aexp; apply refl_aequiv);
try (unfold aequiv in IHa1;
     unfold aequiv in IHa2;
     simpl fold_constants_aexp;
     destruct (fold_constants_aexp a1);
     try (destruct (fold_constants_aexp a2);
          try (unfold aequiv;
               intros;
               pose proof (IHa1 st) as H1;
               pose proof (IHa2 st) as H2;
               simpl aeval;
               rewrite H1; rewrite H2;
               reflexivity));
     try (unfold aequiv;
          intros;
          rewrite IHa1; rewrite IHa2;
(*           
          pose proof (IHa1 st) as H1;
          pose proof (IHa2 st) as H2;
          simpl aeval;
          rewrite H1; rewrite H2;
 *)       
          reflexivity)).
Qed.
  
Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
unfold btrans_sound.
intros.
unfold bequiv.
intros.
induction b;
  try reflexivity.
- simpl.
  remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
  remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
  assert (H1: aeval st a1 = aeval st a1'). {
    rewrite Heqa1'. apply fold_constants_aexp_sound.
  }
  assert (H2: aeval st a2 = aeval st a2'). {
    rewrite Heqa2'. apply fold_constants_aexp_sound.
  }
  rewrite H1. rewrite H2.
  destruct a1'; destruct a2'; try reflexivity.
  simpl. destruct (n =? n0); reflexivity.
- (* BNeq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
- simpl.
  remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
  remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
  assert (H1: aeval st a1 = aeval st a1'). {
    rewrite Heqa1'. apply fold_constants_aexp_sound.
  }
  assert (H2: aeval st a2 = aeval st a2'). {
    rewrite Heqa2'. apply fold_constants_aexp_sound.
  }
  rewrite H1. rewrite H2.
  destruct a1'; destruct a2'; try reflexivity.
  simpl. destruct (n <=? n0); reflexivity.
- simpl.
  remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
  remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
  assert (H1: aeval st a1 = aeval st a1'). {
    rewrite Heqa1'. apply fold_constants_aexp_sound.
  }
  assert (H2: aeval st a2 = aeval st a2'). {
    rewrite Heqa2'. apply fold_constants_aexp_sound.
  }
  rewrite H1. rewrite H2.
  destruct a1'; destruct a2'; try reflexivity.
  simpl. destruct (n <=? n0); reflexivity.
- (* BNot *)
  simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
  rewrite IHb.
  destruct b'; reflexivity.
- (* BAnd *)
  simpl.
  remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
  remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
  rewrite IHb1. rewrite IHb2.
  destruct b1'; destruct b2'; reflexivity.
Qed.

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* skip *) apply refl_cequiv.
  - (* := *) apply CAsgn_congruence.
              apply fold_constants_aexp_sound.
  - (* ; *) apply CSeq_congruence; assumption.
  - (* if *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          fold_constants_bexp_sound.) *)
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply if_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply if_false; assumption.
  - (* while *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn: Heqb.
    -- unfold cequiv.
       intros.
       split.
       --- apply while_true. assumption.
       --- apply while_true. assumption.
    -- unfold cequiv. intros.
       split.
       --- intros. 
           pose proof (while_false b c H) as H1.
           unfold cequiv in H1.
           destruct (H1 st st').
           apply (H2 H0).
       --- intros.
           pose proof (while_false b c H) as H1.
           unfold cequiv in H1.
           destruct (H1 st st').
           apply (H3 H0).
    -- unfold cequiv. intros. split.
       --- intros. apply CWhile_congruence with b c.
           * apply sym_bequiv in H. assumption.
           * apply sym_cequiv in IHc. assumption.
           * assumption.
       --- intros.
           apply sym_bequiv in H.
           apply sym_cequiv in IHc.
           pose proof (CWhile_congruence <{ a1 = a2 }> b (fold_constants_com c) c
                       H IHc) as H1.
           unfold cequiv in H1.
           pose proof (H1 st st') as H2.
           destruct H2.
           apply (H2 H0).
    -- unfold cequiv. intros. split.
       --- intros. apply CWhile_congruence with b c.
           * apply sym_bequiv in H. assumption.
           * apply sym_cequiv in IHc. assumption.
           * assumption.
       --- intros.
           apply sym_bequiv in H.
           apply sym_cequiv in IHc.
           pose proof (CWhile_congruence <{ a1 <> a2 }> b (fold_constants_com c) c
                       H IHc) as H1.
           unfold cequiv in H1.
           pose proof (H1 st st') as H2.
           destruct H2.
           apply (H2 H0).
    -- unfold cequiv. intros. split.
       --- intros. apply CWhile_congruence with b c.
           * apply sym_bequiv in H. assumption.
           * apply sym_cequiv in IHc. assumption.
           * assumption.
       --- intros.
           apply sym_bequiv in H.
           apply sym_cequiv in IHc.
           pose proof (CWhile_congruence <{ a1 <= a2 }> b (fold_constants_com c) c
                       H IHc) as H1.
           unfold cequiv in H1.
           pose proof (H1 st st') as H2.
           destruct H2.
           apply (H2 H0).
    -- unfold cequiv. intros. split.
       --- intros. apply CWhile_congruence with b c.
           * apply sym_bequiv in H. assumption.
           * apply sym_cequiv in IHc. assumption.
           * assumption.
       --- intros.
           apply sym_bequiv in H.
           apply sym_cequiv in IHc.
           pose proof (CWhile_congruence <{ a1 > a2 }> b (fold_constants_com c) c
                       H IHc) as H1.
           unfold cequiv in H1.
           pose proof (H1 st st') as H2.
           destruct H2.
           apply (H2 H0).
    -- unfold cequiv. intros. split.
       --- intros. apply CWhile_congruence with b c.
           * apply sym_bequiv in H. assumption.
           * apply sym_cequiv in IHc. assumption.
           * assumption.
       --- intros.
           apply sym_bequiv in H.
           apply sym_cequiv in IHc.
           pose proof (CWhile_congruence <{ ~ b0 }> b (fold_constants_com c) c
                       H IHc) as H1.
           unfold cequiv in H1.
           pose proof (H1 st st') as H2.
           destruct H2.
           apply (H2 H0).
    -- unfold cequiv. intros. split.
       --- intros. apply CWhile_congruence with b c.
           * apply sym_bequiv in H. assumption.
           * apply sym_cequiv in IHc. assumption.
           * assumption.
       --- intros.
           apply sym_bequiv in H.
           apply sym_cequiv in IHc.
           pose proof (CWhile_congruence <{ b0_1 && b0_2 }> b (fold_constants_com c) c
                       H IHc) as H1.
           unfold cequiv in H1.
           pose proof (H1 st st') as H2.
           destruct H2.
           apply (H2 H0).
Qed.

Fixpoint subst_aexp (x : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | AId x' =>
      if String.eqb x x' then u else AId x'
  | <{ a1 + a2 }> =>
      <{ (subst_aexp x u a1) + (subst_aexp x u a2) }>
  | <{ a1 - a2 }> =>
      <{ (subst_aexp x u a1) - (subst_aexp x u a2) }>
  | <{ a1 * a2 }> =>
      <{ (subst_aexp x u a1) * (subst_aexp x u a2) }>
  end.
  
Example subst_aexp_ex :
  subst_aexp X <{42 + 53}> <{Y + X}>
  = <{ Y + (42 + 53)}>.  
Proof. reflexivity. Qed.

Definition subst_equiv_property : Prop := forall x1 x2 a1 a2,
  cequiv <{ x1 := a1; x2 := a2 }>
         <{ x1 := a1; x2 := subst_aexp x1 a1 a2 }>.
         
Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
unfold not.
intros.
unfold subst_equiv_property in H.
pose proof (H X Y <{X + 1}> X) as H1. clear H.
simpl in H1.
unfold cequiv in H1.
pose proof (H1 empty_st (Y !-> 1; X !-> 1)) as H2.
destruct H2.
clear H0 H1.
assert (H1: empty_st =[ X := X + 1; Y := X ]=> (Y !-> 1; X !-> 1)).
{
  apply E_Seq with ( X !-> 1).
  - apply E_Asgn. simpl. reflexivity.
  - apply E_Asgn. simpl. reflexivity.
}
pose proof (H H1) as H2. clear H H1.
inversion H2. subst.
assert (H3: empty_st =[ X := X + 1 ]=> (X !-> 1)).
{ apply E_Asgn. simpl. reflexivity. }
pose proof (ceval_deterministic <{ X := X + 1 }> empty_st st' (X !-> 1) H1 H3) as H6.
rewrite H6 in H5.
inversion H5. subst.
simpl in H8.
assert (H9: (Y !-> 2; X !-> 1) Y = (Y !-> 1; X !-> 1) Y). { rewrite H8. reflexivity. }
discriminate.
Qed.

Inductive var_not_used_in_aexp (x : string) : aexp -> Prop :=
  | VNUNum : forall n, var_not_used_in_aexp x (ANum n)
  | VNUId : forall y, x <> y -> var_not_used_in_aexp x (AId y)
  | VNUPlus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 + a2 }>)
  | VNUMinus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 - a2 }>)
  | VNUMult : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 * a2 }>).
      
Lemma aeval_weakening : forall x st a ni,
  var_not_used_in_aexp x a ->
  aeval (x !-> ni ; st) a = aeval st a.
Proof.
intros.
induction H.
- simpl. reflexivity.
- simpl. apply t_update_neq. assumption.
- simpl. rewrite IHvar_not_used_in_aexp1. rewrite IHvar_not_used_in_aexp2. reflexivity.
- simpl. rewrite IHvar_not_used_in_aexp1. rewrite IHvar_not_used_in_aexp2. reflexivity.
- simpl. rewrite IHvar_not_used_in_aexp1. rewrite IHvar_not_used_in_aexp2. reflexivity.
Qed.

Lemma subst_equiv_helper :
  forall x1 x2 a1 a2 st st',
    st =[ x1 := a1; x2 := a2 ]=> st'
       -> st' = (x2 !-> aeval (x1 !-> aeval st a1; st) a2; x1 !-> aeval st a1; st).
Proof.
intros.
inversion H.
subst.
assert (H3: st =[ x1 := a1 ]=> (x1 !-> aeval st a1; st)). { apply E_Asgn. reflexivity. }
assert (H4: st'0 =[ x2 := a2 ]=> (x2 !-> aeval st'0 a2; st'0)).  { apply E_Asgn. reflexivity. }
pose proof (ceval_deterministic <{x1 := a1}> st st'0 (x1 !-> aeval st a1; st) H2 H3) as H6.
pose proof (ceval_deterministic <{x2 := a2}> st'0 st' (x2 !-> aeval st'0 a2; st'0) H5 H4) as H7.
rewrite H6 in H7.
assumption.
Qed.

(* this lemma is incorrect; a counterexample is
   a = 2, a1 = x1 + 2, a2 = 2 * x1 *)
Lemma cequiv_seq_impl' :
  forall x1 x2 a a1 a2,
    cequiv <{x1 := a; x2 := a1}> <{x1 := a; x2 := a2}> -> aequiv a1 a2.
Proof.
intros.
unfold cequiv in H.
unfold aequiv.
intros.

pose proof (H st (x2 !-> aeval (x1 !-> aeval st a; st) a1;
                  x1 !-> aeval st a; st)) as H1.
destruct H1.
assert (H2: st =[ x1 := a; x2 := a1]=> (x2 !-> aeval (x1 !-> aeval st a; st) a1;
                                        x1 !-> aeval st a; st)). {
  apply E_Seq with (x1 !-> aeval st a; st).
  -- apply E_Asgn. reflexivity.
  -- apply E_Asgn. reflexivity.
}
pose proof (H0 H2) as H3.
assert (H4: st =[ x1 := a; x2 := a2]=> (x2 !-> aeval (x1 !-> aeval st a; st) a2;
                                        x1 !-> aeval st a; st)). {
  apply E_Seq with (x1 !-> aeval st a; st).
  -- apply E_Asgn. reflexivity.
  -- apply E_Asgn. reflexivity.
}
pose proof (ceval_deterministic <{x1 := a; x2 := a2 }>
                                st
                                (x2 !-> aeval (x1 !-> aeval st a; st) a1;
                                 x1 !-> aeval st a; st)
                                (x2 !-> aeval (x1 !-> aeval st a; st) a2;
                                 x1 !-> aeval st a; st)
                                H3
                                H4) as H5.
assert (H6: (x2 !-> aeval (x1 !-> aeval st a; st) a1;
             x1 !-> aeval st a; st) x2 =
            (x2 !-> aeval (x1 !-> aeval st a; st) a2;
             x1 !-> aeval st a; st) x2).
{
  rewrite H5. reflexivity.
}
assert (H7: (x2 !-> aeval (x1 !-> aeval st a; st) a1;
             x1 !-> aeval st a; st) x2 = aeval (x1 !-> aeval st a; st) a1) by (apply t_update_eq).
assert (H8: (x2 !-> aeval (x1 !-> aeval st a; st) a2;
             x1 !-> aeval st a; st) x2 = aeval (x1 !-> aeval st a; st) a2) by (apply t_update_eq).
rewrite H7 in H6.
rewrite H8 in H6.
clear H H0 H1 H2 H3 H4 H5 H7 H8.
(* this lemma is incorrect; see counterexample above *)
Abort.

(* Not needed, there is an existing theorem for this
   (String.eqb_eq) *)
Lemma string_eqb_impl_eq :
  forall x1 x2, String.eqb x1 x2 = true -> x1 = x2.
Proof.
intros.
destruct (String.eqb_spec x1 x2).
- assumption.
- discriminate.
Qed.

Lemma tesst : forall x a1 a2, cequiv <{x := a1}> <{x := a2}> -> aequiv a1 a2.
Proof.
intros.
unfold cequiv in H.
unfold aequiv.
intros.
pose proof (H st (x !-> aeval st a1; st)) as H1.
destruct H1.
assert (H2: st =[ x := a1 ]=> (x !-> aeval st a1; st)). { apply E_Asgn. reflexivity. }
pose proof (H0 H2) as H3.
assert (H4: st =[ x := a2 ]=> (x !-> aeval st a2; st)). { apply E_Asgn. reflexivity. }
pose proof (ceval_deterministic <{x := a2}>
                                st
                                (x !-> aeval st a1; st)
                                (x !-> aeval st a2; st)
                                H3
                                H4) as H5.
assert (H6: (x !-> aeval st a1; st) x = (x !-> aeval st a2; st) x). { rewrite H5. reflexivity. }
repeat (rewrite t_update_eq in H6).
assumption.
Qed.

Lemma vnu_impl_vnu_subst : forall x a1 a2, 
  var_not_used_in_aexp x a1 -> 
  var_not_used_in_aexp x (subst_aexp x a1 a2).
Proof.
intros.
induction a2.
- simpl. apply VNUNum.
- simpl.
  destruct (String.eqb x x0) eqn: Heq.
  -- assumption.
  -- apply VNUId.
     apply String.eqb_neq. assumption.
- simpl. apply VNUPlus. assumption. assumption.
- simpl. apply VNUMinus. assumption. assumption.
- simpl. apply VNUMult. assumption. assumption.
Qed.

Lemma var_used_or_not_used : forall x a, var_not_used_in_aexp x a \/ ~ (var_not_used_in_aexp x a).
Proof.
intros.
induction a.
- left. apply VNUNum.
- destruct (String.eqb x x0) eqn: Heq.
  -- assert (H1: x = x0). { apply String.eqb_eq. assumption. }
     right. unfold not. intros. inversion H. rewrite H1 in H2. unfold not in H2.
     assert (H3: x0 = x0). { reflexivity. } apply (H2 H3).
  -- left. assert (H1: x <> x0). { apply String.eqb_neq. assumption. }
     apply VNUId. assumption.
- destruct IHa1.
  destruct IHa2.
  -- left.
     apply VNUPlus. assumption. assumption.
  -- right.
     unfold not.
     intros.
     inversion H1. subst. apply (H0 H5).
  -- destruct IHa2.
     --- right. unfold not.
         intros.
         inversion H1. apply (H H4).
     --- right. unfold not. intros.
         inversion H1. apply (H H4).
- destruct IHa1.
  destruct IHa2.
  -- left.
     apply VNUMinus. assumption. assumption.
  -- right.
     unfold not.
     intros.
     inversion H1. subst. apply (H0 H5).
  -- destruct IHa2.
     --- right. unfold not.
         intros.
         inversion H1. apply (H H4).
     --- right. unfold not. intros.
         inversion H1. apply (H H4).
- destruct IHa1.
  destruct IHa2.
  -- left.
     apply VNUMult. assumption. assumption.
  -- right.
     unfold not.
     intros.
     inversion H1. subst. apply (H0 H5).
  -- destruct IHa2.
     --- right. unfold not.
         intros.
         inversion H1. apply (H H4).
     --- right. unfold not. intros.
         inversion H1. apply (H H4).
Qed.

Theorem subst_equiv : 
  forall x1 x2 a1 a2, 
    var_not_used_in_aexp x1 a1 -> 
    cequiv <{ x1 := a1; x2 := a2 }>
           <{ x1 := a1; x2 := subst_aexp x1 a1 a2 }>.
Proof.
intros.
induction a2.
- simpl. apply refl_cequiv.
- simpl. destruct (String.eqb x1 x) eqn: Heq.
  -- unfold cequiv. intros. split.
     --- intros.
         assert (H1: x1 = x). { apply String.eqb_eq. assumption. }
         rewrite H1 in H0.
         pose proof (subst_equiv_helper x x2 a1 x st st' H0) as H2.
         rewrite H2.
         apply E_Seq with (x1 !-> aeval st a1; st).
         ---- apply E_Asgn. reflexivity.
         ---- rewrite <- H1. apply E_Asgn.
              pose proof (aeval_weakening x1 st a1 (aeval st a1)) as H3.
              pose proof (H3 H) as H4.
              rewrite H4.
              simpl aeval.
              rewrite t_update_eq.
              reflexivity.
     --- intros.
         assert (H1: x1 = x). { apply String.eqb_eq. assumption. }
         rewrite H1 in H0.
         pose proof (subst_equiv_helper x x2 a1 a1 st st' H0) as H2.
         rewrite H2.
         apply E_Seq with (x1 !-> aeval st a1; st).
         ---- apply E_Asgn. reflexivity.
         ---- rewrite <- H1.
              apply E_Asgn.
              simpl.
              rewrite t_update_eq.
              symmetry.
              pose proof (aeval_weakening x1 st a1 (aeval st a1)) as H3.
              apply (H3 H).
  -- apply refl_cequiv.
- simpl.
  apply CSeq_congruence.
  -- apply refl_cequiv.
  -- apply CAsgn_congruence.
     unfold aequiv. intros. simpl.
     
     assert (H1: aequiv a2_1 (subst_aexp x1 a1 a2_1)). { admit. }
     assert (H2: aequiv a2_2 (subst_aexp x1 a1 a2_2)). { admit. }
     simpl.
     unfold aequiv in H1.
     unfold aequiv in H2.
     pose proof (H1 st) as H3.
     pose proof (H2 st) as H4.
     rewrite H3. rewrite H4.
     reflexivity.
- simpl.
  apply CSeq_congruence.
  -- apply refl_cequiv.
  -- apply CAsgn_congruence.
     unfold aequiv. intros.
     assert (H1: aequiv a2_1 (subst_aexp x1 a1 a2_1)). { admit. }
     assert (H2: aequiv a2_2 (subst_aexp x1 a1 a2_2)). { admit. }
     simpl.
     unfold aequiv in H1.
     unfold aequiv in H2.
     pose proof (H1 st) as H3.
     pose proof (H2 st) as H4.
     rewrite H3. rewrite H4.
     reflexivity.
- simpl.
  apply CSeq_congruence.
  -- apply refl_cequiv.
  -- apply CAsgn_congruence.
     unfold aequiv. intros.
     assert (H1: aequiv a2_1 (subst_aexp x1 a1 a2_1)). { admit. }
     assert (H2: aequiv a2_2 (subst_aexp x1 a1 a2_2)). { admit. }
     simpl.
     unfold aequiv in H1.
     unfold aequiv in H2.
     pose proof (H1 st) as H3.
     pose proof (H2 st) as H4.
     rewrite H3. rewrite H4.
     reflexivity.
Admitted. (* come back to this later *)

Theorem inequiv_exercise:
  ~ cequiv <{ while true do skip end }> <{ skip }>.
Proof.
unfold not.
intros.
unfold cequiv in H.
pose proof (H empty_st empty_st) as H1. clear H.
destruct H1.
assert (H1: empty_st =[ skip ]=> empty_st). { apply E_Skip. }
pose proof (H0 H1) as H2. clear H H0 H1.
inversion H2.
- subst. inversion H3.
- subst.
  pose proof (while_true_nonterm BTrue <{skip}> st' empty_st) as H7.
  assert (H8: bequiv <{ true }> <{ true }>). { apply refl_bequiv. }
  apply ((H7 H8) H6).
Qed. 
