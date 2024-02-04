Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LF Require Import Maps.

Module AExp.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
  
Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).
  
Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof.
unfold aeval.
reflexivity.
Qed.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.
  
Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.
  
Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
intros.
induction a.
- simpl. reflexivity.
- simpl optimize_0plus. 
  assert (H1: aeval (APlus a1 a2) = aeval a1 + aeval a2). { reflexivity. }
  rewrite H1.
  rewrite <- IHa1. rewrite <- IHa2.
  destruct a1.
  -- simpl. induction n. simpl. reflexivity. simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
- simpl optimize_0plus.
  assert (H1: aeval (AMinus a1 a2) = aeval a1 - aeval a2). { reflexivity. }
  rewrite H1.
  rewrite <- IHa1. rewrite <- IHa2.
  simpl.
  reflexivity.
- simpl optimize_0plus.
  assert (H1: aeval (AMult a1 a2) = aeval a1 * aeval a2). { reflexivity. }
  rewrite H1.
  rewrite <- IHa1. rewrite <- IHa2.
  simpl.
  reflexivity.
Qed.

(* book version *)
Theorem optimize_0plus_sound_book: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *) simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity. Qed.

Fixpoint optimize_0plus_b (b : bexp) : bexp := 
match b with
  | BTrue => b
  | BFalse => b
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot (optimize_0plus_b b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.
  
Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
intros.
induction b;
(*
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. repeat (rewrite optimize_0plus_sound). reflexivity.
- simpl. repeat (rewrite optimize_0plus_sound). reflexivity.
- simpl. rewrite IHb. reflexivity.
- simpl. rewrite IHb1. rewrite IHb2. reflexivity.
*)
simpl;
try reflexivity;
try repeat (rewrite optimize_0plus_sound);
try rewrite IHb;
try (rewrite IHb1; rewrite IHb2);
reflexivity.
Qed.

(* additional optimizations:
   1) add zero to right
   2) subtract 0 (from 0, 0 from)
   3) multiply by 0 (right and left)
   4) multiply by 1 (right and left)
   5) or with true (right and left) <- or is not part of the language, actually
   6) and with false (right and left)
*)

Fixpoint optimize_fully_loaded (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_fully_loaded e2
  | APlus e1 (ANum 0) => optimize_fully_loaded e1

  | APlus e1 e2 => APlus (optimize_fully_loaded e1) (optimize_fully_loaded e2)
  | AMinus (ANum 0) e2 => ANum 0
  | AMinus e1 (ANum 0) => optimize_fully_loaded e1
  | AMinus e1 e2 => AMinus (optimize_fully_loaded e1) (optimize_fully_loaded e2)
  | AMult (ANum 0) e2 => ANum 0
  | AMult e1 (ANum 0) => ANum 0
  | AMult e1 e2 => AMult (optimize_fully_loaded e1) (optimize_fully_loaded e2)
  end.
  
Fixpoint optimize_fully_loaded_b (b : bexp) : bexp := 
match b with
  | BTrue => b
  | BFalse => b
  | BEq a1 a2 => BEq (optimize_fully_loaded a1) (optimize_fully_loaded a2)
  | BLe a1 a2 => BLe (optimize_fully_loaded a1) (optimize_fully_loaded a2)
  | BNot b1 => BNot (optimize_fully_loaded_b b1)
  | BAnd BFalse _ => BFalse
  | BAnd _ BFalse => BFalse  
  | BAnd b1 b2 => BAnd (optimize_fully_loaded_b b1) (optimize_fully_loaded_b b2)
  end.

Theorem optimize_fully_loaded_sound_naive: forall a,
  aeval (optimize_fully_loaded a) = aeval a.
Proof.
intros.
induction a.
- reflexivity.
- destruct a1.
  -- destruct n.
     * simpl. rewrite IHa2. reflexivity.
     * destruct a2.
       ** simpl. destruct n0.
          *** simpl. rewrite add_0_r. reflexivity.
          *** simpl. reflexivity.
       ** simpl. simpl in IHa1. simpl in IHa2.
          rewrite IHa2. reflexivity.
       ** simpl. simpl in IHa1. simpl in IHa2.
          rewrite IHa2. reflexivity.
       ** simpl. simpl in IHa1. simpl in IHa2.
          rewrite IHa2. reflexivity.
  -- destruct a2.
     * destruct n.
       ** simpl. simpl in IHa1.
          rewrite IHa1. rewrite add_0_r. reflexivity.
       ** simpl. simpl in IHa1. simpl in IHa2.
          rewrite IHa1. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity. 
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
  -- destruct a2.
     * destruct n.
       ** simpl. rewrite add_0_r.
          simpl in IHa1. apply IHa1.
       ** simpl. simpl in IHa1. rewrite IHa1. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
  -- destruct a2.
     * destruct n.
       ** simpl. simpl in IHa1.
          rewrite IHa1. rewrite add_0_r. reflexivity.
       ** simpl. simpl in IHa1. rewrite IHa1. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.

- destruct a1.
  -- destruct n.
     * simpl. reflexivity.
     * destruct a2.
       ** simpl. destruct n0.
          *** simpl. reflexivity.
          *** simpl. reflexivity.
       ** simpl. simpl in IHa1. simpl in IHa2.
          rewrite IHa2. reflexivity.
       ** simpl. simpl in IHa1. simpl in IHa2.
          rewrite IHa2. reflexivity.
       ** simpl. simpl in IHa1. simpl in IHa2.
          rewrite IHa2. reflexivity.
  -- destruct a2.
     * destruct n.
       ** simpl. simpl in IHa1.
          rewrite IHa1. lia.
       ** simpl. simpl in IHa1. simpl in IHa2.
          rewrite IHa1. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity. 
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
  -- destruct a2.
     * destruct n.
       ** simpl. 
          simpl in IHa1. rewrite IHa1. lia.
       ** simpl. simpl in IHa1. rewrite IHa1. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
  -- destruct a2.
     * destruct n.
       ** simpl. simpl in IHa1.
          rewrite IHa1. lia.
       ** simpl. simpl in IHa1. rewrite IHa1. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity. 

- destruct a1.
  -- destruct n.
     * simpl. reflexivity.
     * destruct a2.
       ** simpl. destruct n0.
          *** simpl. lia.
          *** simpl. reflexivity.
       ** simpl. simpl in IHa1. simpl in IHa2.
          rewrite IHa2. reflexivity.
       ** simpl. simpl in IHa1. simpl in IHa2.
          rewrite IHa2. reflexivity.
       ** simpl. simpl in IHa1. simpl in IHa2.
          rewrite IHa2. reflexivity.
  -- destruct a2.
     * destruct n.
       ** simpl. lia.
       ** simpl. simpl in IHa1. simpl in IHa2.
          rewrite IHa1. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity. 
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
  -- destruct a2.
     * destruct n.
       ** simpl. 
          simpl in IHa1. lia.
       ** simpl. simpl in IHa1. rewrite IHa1. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
  -- destruct a2.
     * destruct n.
       ** simpl. lia.
       ** simpl. simpl in IHa1. rewrite IHa1. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity.
     * simpl. simpl in IHa1. simpl in IHa2.
       rewrite IHa1. rewrite IHa2. reflexivity. 
Qed.

Theorem optimize_fully_loaded_sound: forall a,
  aeval (optimize_fully_loaded a) = aeval a.
Proof.
intros.
induction a;
  try reflexivity;
  try (destruct a1;
         try (destruct n;
                try (simpl; rewrite IHa2; reflexivity);
                try (destruct a2;
                       try (simpl; destruct n0;
                                     try (simpl; rewrite add_0_r; reflexivity);
                                     try (simpl; reflexivity));
                       try (simpl; simpl in IHa1; simpl in IHa2;
                            rewrite IHa2; reflexivity)));
         try (destruct a2;
                try (destruct n;
                       try (simpl; simpl in IHa1;
                            rewrite IHa1; lia; rewrite add_0_r; reflexivity);
                       try (simpl; simpl in IHa1; simpl in IHa2;
                            rewrite IHa1; reflexivity));
                try (simpl; simpl in IHa1; simpl in IHa2;
                     rewrite IHa1; rewrite IHa2; reflexivity));
         try (simpl; lia)).
Qed.

Lemma and_false: forall b, andb b false = false.
Proof.
intros.
destruct b.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

Theorem optimize_fully_loaded_b_sound_naive : forall b,
  beval (optimize_fully_loaded_b b) = beval b.
Proof.
intros.
induction b.
- reflexivity.
- reflexivity.
- simpl optimize_fully_loaded_b.
  unfold beval.
  repeat (rewrite optimize_fully_loaded_sound).
  reflexivity.
- simpl optimize_fully_loaded_b.
  unfold beval.
  repeat (rewrite optimize_fully_loaded_sound).
  reflexivity.
- simpl. rewrite IHb. reflexivity.
- destruct b1.
  -- destruct b2.
     --- reflexivity.
     --- reflexivity.
     --- simpl. repeat (rewrite optimize_fully_loaded_sound). reflexivity.
     --- simpl. repeat (rewrite optimize_fully_loaded_sound). reflexivity.
     --- simpl. repeat (rewrite optimize_fully_loaded_sound).
         simpl in IHb2. assumption.
     --- simpl in IHb2. simpl. assumption.
  -- reflexivity.
  -- destruct b2.
     --- simpl. simpl in IHb1. rewrite IHb1. reflexivity.
     --- simpl. lia.
     --- simpl in IHb1. simpl in IHb2. simpl.
         rewrite IHb1. rewrite IHb2. reflexivity.
     --- simpl in IHb1. simpl in IHb2. simpl.
         rewrite IHb1. rewrite IHb2. reflexivity.
     --- simpl in IHb1. simpl in IHb2. simpl.
         rewrite IHb1. rewrite IHb2. reflexivity.
     --- simpl in IHb1. simpl in IHb2. simpl.
         rewrite IHb1. rewrite IHb2. reflexivity.
  -- destruct b2.
     --- simpl. simpl in IHb1. rewrite IHb1. reflexivity.
     --- simpl. lia.
     --- simpl in IHb1. simpl in IHb2. simpl.
         rewrite IHb1. rewrite IHb2. reflexivity.
     --- simpl in IHb1. simpl in IHb2. simpl.
         rewrite IHb1. rewrite IHb2. reflexivity.
     --- simpl in IHb1. simpl in IHb2. simpl.
         rewrite IHb1. rewrite IHb2. reflexivity.
     --- simpl in IHb1. simpl in IHb2. simpl.
         rewrite IHb1. rewrite IHb2. reflexivity.
  -- destruct b2.
     --- simpl. simpl in IHb1. rewrite IHb1. reflexivity.
     --- simpl. lia.
     --- simpl in IHb1. simpl in IHb2. simpl.
         rewrite IHb1. rewrite IHb2. reflexivity.
     --- simpl in IHb1. simpl in IHb2. simpl.
         rewrite IHb1. rewrite IHb2. reflexivity.
     --- simpl in IHb1. simpl in IHb2. simpl.
         rewrite IHb1. rewrite IHb2. reflexivity.
     --- simpl in IHb1. simpl in IHb2. simpl.
         rewrite IHb1. rewrite IHb2. reflexivity.
  -- destruct b2.
     --- simpl. simpl in IHb1. rewrite IHb1. reflexivity.
     --- simpl. lia.
     --- simpl in IHb1. simpl in IHb2. simpl.
         rewrite IHb1. rewrite IHb2. reflexivity.
     --- simpl in IHb1. simpl in IHb2. simpl.
         rewrite IHb1. rewrite IHb2. reflexivity.
     --- simpl in IHb1. simpl in IHb2. simpl.
         rewrite IHb1. rewrite IHb2. reflexivity.
     --- simpl in IHb1. simpl in IHb2. simpl.
         rewrite IHb1. rewrite IHb2. reflexivity.
Qed.

Theorem optimize_fully_loaded_b_sound : forall b,
  beval (optimize_fully_loaded_b b) = beval b.
Proof.
intros.
induction b;
try reflexivity;
try (simpl optimize_fully_loaded_b;
     unfold beval;
     repeat (rewrite optimize_fully_loaded_sound);
     reflexivity);
try (simpl; rewrite IHb; reflexivity);
destruct b1;
  try (destruct b2;
         try reflexivity;
         try (simpl; repeat (rewrite optimize_fully_loaded_sound); reflexivity);
         try (simpl; repeat (rewrite optimize_fully_loaded_sound);
              simpl in IHb2; apply IHb2);
         try (simpl in IHb2; simpl; apply IHb2);
         try (simpl; simpl in IHb1; rewrite IHb1; reflexivity);
         try (simpl; lia);
         try (simpl in IHb1; simpl in IHb2; simpl;
              rewrite IHb1; rewrite IHb2; reflexivity));
         try reflexivity.
Qed.

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).
      
Module HypothesisNames.

End HypothesisNames.

Notation "e '==>' n"
         := (aevalR e n)
            (at level 90, left associativity)
         : type_scope.
         
End aevalR_first_try.

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMult e1 e2) ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.

(*
  Fixpoint beval (e : bexp) : bool :=
    match e with
    | BTrue       ⇒ true
    | BFalse      ⇒ false
    | BEq a1 a2   ⇒ (aeval a1) =? (aeval a2)
    | BLe a1 a2   ⇒ (aeval a1) <=? (aeval a2)
    | BNot b      ⇒ negb (beval b)
    | BAnd b1 b2  ⇒ andb (beval b1) (beval b2)
    end.
Write out a corresponding definition of boolean evaluation as a relation (in inference rule notation).

-------------- (E_BTrue)
BTrue ==> true

---------------- (E_BFalse)
BFalse ==> false

       a1 ==> n1
       a2 ==> n2
---------------------- (E_BEq)
Beq a1 a2 ==> n1 =? n2

       a1 ==> n1
       a2 ==> n2
----------------------- (E_BLe)
BLe a1 a2 ==> n1 <=? n2

     b ==> bool1
--------------------- (E_BNot)
BNot b ==> negb bool1

         b1 ==> boo11
         b2 ==> bool2
------------------------------- (E_BAnd)
BAnd b1 b2 ==> andb bool1 bool2

*)

Theorem aeval_iff_aevalR : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
 split.
 - (* -> *)
   intros H.
   induction H; simpl.
   + (* E_ANum *)
     reflexivity.
   + (* E_APlus *)
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
   + (* E_AMinus *)
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
   + (* E_AMult *)
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
 - (* <- *)
   generalize dependent n.
   induction a;
      simpl; intros; subst.
   + (* ANum *)
     apply E_ANum.
   + (* APlus *)
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMinus *)
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMult *)
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

Reserved Notation "e '==>b' b" (at level 90, left associativity).

Inductive bevalR: bexp -> bool -> Prop :=
 | E_BTrue : BTrue ==>b true
 | E_BFalse : BFalse ==>b false
 | E_BEq (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (BEq e1 e2) ==>b (n1 =? n2)
 | E_BLe (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (BLe e1 e2) ==>b (n1 <=? n2)
 | E_BNot (b1 : bexp) (bool1 : bool) :
     (b1 ==>b bool1) -> (BNot b1) ==>b negb bool1
 | E_BAnd (b1 b2 : bexp) (bool1 bool2 : bool) :
     (b1 ==>b bool1) -> (b2 ==>b bool2) -> (BAnd b1 b2) ==>b andb bool1 bool2

where "e '==>b' b" := (bevalR e b) : type_scope.

Lemma beval_iff_bevalR : forall b bv,
  b ==>b bv <-> beval b = bv.
Proof.
intros.
split.
- intros.
  induction H.
  -- reflexivity.
  -- reflexivity.
  -- simpl. rewrite aeval_iff_aevalR in H. rewrite aeval_iff_aevalR in H0.
     rewrite H. rewrite H0. reflexivity.
  -- simpl. rewrite aeval_iff_aevalR in H. rewrite aeval_iff_aevalR in H0.
     rewrite H. rewrite H0. reflexivity.
  -- simpl. rewrite IHbevalR. reflexivity.
  -- simpl. rewrite IHbevalR1. rewrite IHbevalR2. reflexivity.
- intros.
  generalize dependent bv.
  induction b.
  -- intros. subst. simpl. apply E_BTrue.
  -- intros. subst. simpl. apply E_BFalse. 
  -- intros. subst. simpl. apply E_BEq.
     * rewrite aeval_iff_aevalR. reflexivity.
     * rewrite aeval_iff_aevalR. reflexivity.
  -- intros. subst. simpl. apply E_BLe.
     * rewrite aeval_iff_aevalR. reflexivity.
     * rewrite aeval_iff_aevalR. reflexivity.
  -- intros. subst. simpl. apply E_BNot.
     pose proof (IHb (beval b)) as H1.
     apply H1. reflexivity.
  -- intros. subst. simpl. apply E_BAnd.
     * pose proof (IHb1 (beval b1)) as H1.
       apply H1. reflexivity.
     * pose proof (IHb2 (beval b2)) as H1.
       apply H1. reflexivity.
Qed.

End AExp.

Module aevalR_division.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp). (* <--- NEW *)  
  
Reserved Notation "e '==>' n"
                  (at level 90, left associativity).  
                  
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) : (* <----- NEW *)
      (a1 ==> n1) -> (a2 ==> n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) ==> n3                  

where "a '==>' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.

Reserved Notation "e '==>' n" (at level 90, left associativity).
Inductive aexp : Type :=
  | AAny (* <--- NEW *)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
  
Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any (n : nat) :
      AAny ==> n (* <--- NEW *)
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)

where "a '==>' n" := (aevalR a n) : type_scope.

End aevalR_extended.

Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string) (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
  
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.

Print example_bexp.
(* Set Printing Coercions. *) (* - this needs to be done using the IDE menu option *)
Print example_bexp.
(* Unset Printing Coercions *) (* - this needs to be done using the IDE menu option *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x (* <--- NEW *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.
  
Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  end.
  
Definition empty_st := (_ !-> 0).

Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

Example aexp1 :
    aeval (X !-> 5) <{ 3 + (X * 2) }>
  = 13.
Proof. reflexivity. Qed.  

Example aexp2 :
    aeval (X !-> 5 ; Y !-> 4) <{ Z + (X * Y) }>
  = 20.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) <{ true && ~(X <= 4) }>
  = true.
Proof. reflexivity. Qed.

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).
  
Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while ~(Z = 0) do
       Y := Y * Z;
       Z := Z - 1
     end }>.
     
Print fact_in_coq.            

Unset Printing Notations.

Print fact_in_coq.

Set Printing Coercions.

Print fact_in_coq.

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).
          
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').
  
Example ceval_example1:
  empty_st =[
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
apply (E_Seq <{ X := 2 }> 
             <{ if (X <= 1) then Y := 3 else Z := 4 end }> 
             empty_st
             ( X !-> 2)
             (Z !-> 4; X !-> 2)).
- apply E_Asgn. reflexivity.
- apply E_IfFalse.
  -- simpl. reflexivity.
  -- apply E_Asgn.
     simpl. reflexivity.
Qed.

Example ceval_example2:
  empty_st =[
    X := 0;
    Y := 1;
    Z := 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
apply E_Seq with (X !-> 0).
- apply E_Asgn. simpl. reflexivity. 
- apply E_Seq with (Y !-> 1; X !-> 0).
  -- apply E_Asgn. simpl. reflexivity.
  -- apply E_Asgn. simpl. reflexivity.
Qed.

Definition pup_to_n : com := 
  <{ Y := 0;
     while (1 <= X ) do
       Y := Y + X;
       X := X - 1
     end
  }>.

Compute (X !-> 2) =[ pup_to_n ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
unfold pup_to_n.
apply E_Seq with (Y !-> 0 ; X !-> 2).
- apply E_Asgn. simpl. reflexivity.
- apply E_WhileTrue with (X !-> 1; Y !-> 2 ; Y !-> 0; X !-> 2).
  -- simpl. reflexivity.
  -- apply E_Seq with (Y !-> 2 ; Y !-> 0 ; X !-> 2).
     * apply E_Asgn. simpl. reflexivity.
     * apply E_Asgn. simpl. reflexivity.
  -- apply E_WhileTrue with (X !-> 0; Y !-> 3 ; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
     * simpl. reflexivity.
     * apply E_Seq with (Y !-> 3 ; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
       ** apply E_Asgn. simpl. reflexivity.
       ** apply E_Asgn. simpl. reflexivity.
     * apply E_WhileFalse. simpl. reflexivity.
Qed.

(* from book *)
Theorem ceval_deterministic_book: forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Asgn *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption. Qed.
    
Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
intros.
generalize dependent st2.
induction H.
- intros. inversion H0. reflexivity.
- intros. inversion H0. subst. reflexivity.
- intros. inversion H1. subst.
  pose proof (IHceval1 st'0) as H8.
  pose proof (H8 H4) as H9.
  rewrite H9 in IHceval2.
  apply ((IHceval2 st2) H7).
- intros. inversion H1. subst.
  -- apply ((IHceval st2) H8).
  -- rewrite H in H7. inversion H7.
- intros. inversion H1. subst.
  -- rewrite H in H7. inversion H7.
  -- subst. apply ((IHceval st2) H8).
- intros. inversion H0.
  -- reflexivity.
  -- subst. inversion H0.
     * reflexivity.
     * subst. rewrite H in H3. inversion H3.
- intros. inversion H2. subst.
  -- rewrite H in H7. inversion H7.
  -- subst. pose proof ((IHceval1 st'0) H6) as H10.
     rewrite H10 in IHceval2.
     apply ((IHceval2 st2) H9).
Qed.

Definition plus2 : com :=
  <{ X := X + 2 }>.
  
Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
intros.
unfold plus2 in H0.
inversion H0.
cbn.
rewrite <- H5.
simpl. rewrite H. reflexivity.
Qed.  
  
Theorem plus2_spec_book_version : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.  
  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq. Qed.
  

Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.

Theorem xtimesyinz_spec : forall st x y st',
  st X = x ->
  st Y = y ->
  st =[ XtimesYinZ ]=> st' ->
  st' Z = x * y.
Proof.
intros.
unfold XtimesYinZ in H1.
inversion H1.
subst. clear H1.
apply t_update_eq. 
Qed.

Definition loop : com :=
  <{ while true do
       skip
     end }>.
  
Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember <{ while true do skip end }> as loopdef
           eqn:Heqloopdef.  
  induction contra.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - inversion Heqloopdef.
    rewrite H1 in H.
    simpl in H.
    discriminate.
  - apply (IHcontra2 Heqloopdef).
Qed.

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | <{ skip }> =>
      true
  | <{ _ := _ }> =>
      true
  | <{ c1 ; c2 }> =>
      andb (no_whiles c1) (no_whiles c2)
  | <{ if _ then ct else cf end }> =>
      andb (no_whiles ct) (no_whiles cf)
  | <{ while _ do _ end }> =>
      false
  end.
  
Inductive no_whilesR: com -> Prop :=
  | W_Skip : no_whilesR <{ skip }>
  | W_Asgn : forall x a, no_whilesR <{ x := a }>
  | W_Seq : forall (c1 c2 : com), no_whilesR c1 -> no_whilesR c2 -> no_whilesR <{ c1; c2 }>
  | W_If : forall (b : bexp) (c1 c2 : com), 
           no_whilesR c1 -> no_whilesR c2 -> no_whilesR <{ if b then c1 else c2 end }>
.  
  
Search andb.  
  
Theorem no_whiles_eqv:
  forall c, no_whiles c = true <-> no_whilesR c.
Proof.
intros.
split.
- intros.
  induction c.
  -- apply W_Skip.
  -- apply W_Asgn.
  -- simpl in H.
     apply W_Seq.
     --- apply andb_prop in H.
         destruct H. apply (IHc1 H).
     --- apply andb_prop in H.
         destruct H. apply (IHc2 H0).
  -- simpl in H.
     apply W_If.
     --- apply andb_prop in H.
         destruct H. apply (IHc1 H).
     --- apply andb_prop in H.
         destruct H. apply (IHc2 H0).
  -- simpl in H. discriminate.
- intros.
  induction H.
  -- reflexivity.
  -- reflexivity.
  -- simpl. rewrite IHno_whilesR1. rewrite IHno_whilesR2. reflexivity.
  -- simpl. rewrite IHno_whilesR1. rewrite IHno_whilesR2. reflexivity.
Qed.

Theorem no_whiles_terminating :
  forall c, no_whiles c = true -> forall st, exists st', st =[ c ]=> st'.
Proof.
intros c H.
induction c.
- intros. exists st. apply E_Skip.
- intros. exists ( x !-> aeval st a; st). apply E_Asgn. reflexivity.
- intros. simpl in H.
  apply andb_prop in H.
  destruct H.
  pose proof (IHc1 H) as H1.
  pose proof (IHc2 H0) as H2.
  pose proof (H1 st) as H3.
  destruct H3.
  pose proof (H2 x) as H4.
  destruct H4.
  exists x0.
  apply E_Seq with x. apply H3. apply H4.
- intros. simpl in H.
  apply andb_prop in H.
  destruct H.
  pose proof (IHc1 H) as H1.
  pose proof (IHc2 H0) as H2.
  pose proof (H1 st) as H3.
  destruct H3.
  pose proof (H2 x) as H4.
  destruct H4.
  destruct (beval st b) eqn: Heq.
  -- exists x. apply E_IfTrue. apply Heq. apply H3.
  -- pose proof (H2 st) as H5. destruct H5.
     exists x1. apply E_IfFalse. apply Heq. apply H5.
- intros. simpl in H. discriminate.
Qed.

  
  
  
  
  
  
  
  
  
  
  