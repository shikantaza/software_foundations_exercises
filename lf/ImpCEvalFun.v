From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
Import Nat.
From Coq Require Import Arith.EqNat.
From LF Require Import Imp Maps.

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).
   
Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.   

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.

Definition pup_to_n : com := 
  <{ Y := 0;
     while (1 <= X ) do
       Y := Y + X;
       X := X - 1
     end
  }>.
  
Example pup_to_n_1 :
  test_ceval (X !-> 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.

Definition peven : com :=
  <{ Y := X; while (2 <= Y) do Y := Y - 2; Z := Y end }>.

Example peven_test :
  test_ceval (X !-> 4) peven = Some (4, 0, 0).
Proof. reflexivity. Qed.

(* implemented book version with simplified style *)
Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      st =[ c ]=> st'.
Proof.
intros.
inversion H.
clear H.
generalize dependent st'.
generalize dependent st.
generalize dependent c.
induction x.
- intros. simpl in H0. discriminate.
- intros. destruct c.
  -- simpl in H0. inversion H0. apply E_Skip.
  -- simpl in H0. inversion H0. apply E_Asgn. reflexivity.
  -- simpl in H0.  
     destruct (ceval_step st c1 x) eqn: Heq.
     --- apply E_Seq with s.
         * apply (IHx c1 st s). apply Heq.
         * apply (IHx c2 s st'). apply H0.
     --- discriminate.
  -- simpl in H0.
     destruct (beval st b) eqn: Heq.
     --- apply E_IfTrue.
         * apply Heq.
         * apply (IHx c1 st st'). apply H0.
     --- apply E_IfFalse.
         * apply Heq.
         * apply (IHx c2 st st'). apply H0.
  -- simpl in H0.
     destruct (beval st b) eqn: Heq.
     --- destruct (ceval_step st c x) eqn: Heq1.
         * apply E_WhileTrue with s.
           ** apply Heq.
           ** apply (IHx c st s). apply Heq1.
           ** apply (IHx <{ while b do c end }> s st'). apply H0.
         * discriminate.
     --- inversion H0. subst. apply E_WhileFalse. apply Heq.
Qed.

(* informal proof of ceval_step__ceval *)
(*
TPT: forall c, st, st' : if ceval_step returns st' by applying c to st in i steps,
     c, st, and st' also obey the relation ceval.
     
Proof by induction on i.
1) i = 0: ceval_step cannot return st' in zero steps (returne None by deinition for i=0), 
   hence the premise is a contradiction.

2) Assume the proposition is true for x, TPT the proposition is true for (S x).
   i.e., forall c, st, st' : ceval_step st c x = Some st' -> ceval c st st') ->
         forall c, st, st' : ceval_step st c (S x) = Some st' -> ceval c st st') ->

   We destruct on c:
   1) c = skip - ceval_step returns st, i.e., st = st'. TPT ceval <{skip}> st st, 
      which is true by definition (E_Skip).
      
   2) c = x0 := a - ceval_step returns (x !-> aeval st a; st)
      TPT ceval <{ x0 := a >} st (x !-> aeval st a; st), 
      which can be shown to be true by definition (E_Asgn).
    
   3) c = c1 ; c2
   
      induction hypothesis: forall c st st', ceval_step st c x = Some st' -> ceval c st st'  

      ceval_step simpilifies to
      
          match ceval_step st c1 x with
            | Some st' => ceval_step st' c2 x
            | None     => Nome
            
      We destruct on ceval_step st c1 x.
      1) Some s (i.e., ceval_step st c1 x = Some s):
         TPT ceval <{c1; c2}> st st' is true
         For this to be true, (ceval c1 st s) and (ceval c2 s st') should be true for some s
         (application E_Seq inductive rule)
         Both these follow from suitable instantiations of the induction hypothesis.
      2) None: This means that ceval_step returns None, whoch contradicts the premise
      
   4) c = if b then c1 else s2 end  (with induction hypothesis similar to (3)
      
      We destruct on (beval st b)
      1) True: TPT ceval c1 st st'. This follows from a suitable instantiation of the 
         induction hypothesis.
      2) False: TPT ceval c2 st st'. This follows from a suitable instantiation of the 
         induction hypothesis.
   
   5) c = while b do c end
   
      ceval_step st c x simplifies to
      
        if beval st b
        then match (ceval_step st c x) with
               | Some st' => ceval_step st' <{while b do c end}> x
               | Nome     => None
        else Some st)
        
      We destruct on (beval st b)
      1) True:
         ceval_step st c x simplifies to
           match (ceval_step st c x) with
               | Some st' => ceval_step st' <{while b do c end}> x
               | Nome     => None
               
         We destruct on (ceval_step st c x)
         1) Some st': TPT ceval <{while b do c end}> st st' is true
            Since beval st b is true, we need to show that 
              a) ceval st s 
              b) ceval <{while b do c end}> s st      
            for some s.
            Both can be proved by suitable instantiations of the induction hypothesis.
         2) None: ceval_step returns None, which contradicts the premise
         
      2) False:
         ceval_step returns Some st, i.e., st = st'
         TPT ceval <{while b do c end}> st st'
         which is true because (beval st b) is false and st = st'.
         
QED.               
*)

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - (* i1 = 0 *)
    simpl in Hceval. discriminate Hceval.
  - (* i1 = S i1' *)
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by lia.
    destruct c.
    + (* skip *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* := *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ; *)
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* st1'o = None *)
        discriminate Hceval.
    + (* if *)
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval;
        assumption.
    + (* while *)
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* i1'o = None *)
        simpl in Hceval. discriminate Hceval. Qed.

Theorem ceval__ceval_step: forall c st st',
      st =[ c ]=> st' ->
      exists i, ceval_step st c i = Some st'.
Proof.
intros c st st' Hce.
induction Hce.
- exists 1. reflexivity.
- exists 1. simpl. rewrite H. reflexivity.
- destruct IHHce1. destruct IHHce2.
  exists (S (x + x0)).
  simpl.
  destruct (ceval_step st c1 (x + x0)) eqn: Heq.
  -- assert (H1: x <= x + x0) by lia.
     pose proof (ceval_step_more x (x + x0) st st' c1 H1 H) as H2.
     rewrite H2 in Heq.
     inversion Heq.
     rewrite <- H4.
     assert (H5: x0 <= x + x0) by lia.
     apply (ceval_step_more x0 (x + x0) st' st'' c2 H5 H0).
  -- assert (H1: x <= x + x0) by lia.
     pose proof (ceval_step_more x (x + x0) st st' c1 H1 H) as H2.
     rewrite H2 in Heq. discriminate.
- destruct IHHce.
  exists (S x).
  simpl.
  rewrite H.
  apply H0.
- destruct IHHce.
  exists (S x).
  simpl.
  rewrite H.
  apply H0.
- destruct c.
  -- exists 1. simpl. rewrite H. reflexivity.
  -- exists 1. simpl. rewrite H. reflexivity.
  -- exists 1. simpl. rewrite H. reflexivity.
  -- exists 1. simpl. rewrite H. reflexivity.
  -- exists 1. simpl. rewrite H. reflexivity.
- destruct IHHce1. destruct IHHce2.
  exists (S (x + x0)).
  simpl.
  rewrite H.
  destruct (ceval_step st c (x + x0)) eqn: Heq.
  -- assert (H2: x <= x + x0) by lia.
     pose proof (ceval_step_more x (x + x0) st st' c H2 H0) as H3.
     rewrite Heq in H3.
     inversion H3.
     assert (H6: x0 <= x + x0) by lia.
     apply (ceval_step_more x0 (x + x0) st' st'' <{ while b do c end }> H6 H1).
  -- assert (H2: x <= (x + x0)) by lia.
     pose proof (ceval_step_more x (x + x0) st st' c H2 H0) as H3.
     rewrite H3 in Heq.
     discriminate.
Qed.

Theorem ceval_and_ceval_step_coincide: forall c st st',
      st =[ c ]=> st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.
  
Theorem ceval_deterministic' : forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
intros.
apply ceval__ceval_step in H.
apply ceval__ceval_step in H0.
destruct H.
destruct H0.
assert (H1: x <= x + x0) by lia.
pose proof (ceval_step_more x (x + x0) st st1 c H1 H) as H2.
assert (H3: x0 <= x + x0) by lia.
pose proof (ceval_step_more x0 (x + x0) st st2 c H3 H0) as H4.
rewrite H2 in H4.
inversion H4.
reflexivity.
Qed.







