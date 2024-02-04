Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From PLF Require Import Hoare.

Definition FILL_IN_HERE := <{True}>.

(*
  {{ True }}
    if X <= Y then
              {{ True /\ X <= Y }} ->>
              {{ Y = X + Y - X }}
      Z := Y - X
              {{ Y = X + Z }}
    else
              {{ True /\ ~ (X <= Y) }} ->>
              {{ X + Z = X + Z }}
      Y := X + Z
              {{ Y = X + Z }}
    end
  {{ Y = X + Z }}
  
  Both implications are trivial / reflexive  
  
*)

Definition reduce_to_zero' : com :=
  <{ while X <> 0 do
       X := X - 1
     end }>.
     
Theorem reduce_to_zero_correct' :
  {{True}}
    reduce_to_zero'
  {{X = 0}}.
Proof.
unfold reduce_to_zero'.
eapply hoare_consequence_post.                       
- apply hoare_while. 
  eapply hoare_consequence_pre.
  -- apply hoare_asgn.
  -- unfold assn_sub, "->>".
     intros. simpl. exact I.
- unfold "->>".
  intros st [Inv GuardFalse].
  unfold bassn in GuardFalse.
  simpl in GuardFalse.
  rewrite not_true_iff_false in GuardFalse.
  rewrite negb_false_iff in GuardFalse.
  apply eqb_eq in GuardFalse.
  simpl.
  apply GuardFalse. 
Qed.

Ltac verify_assn :=
  repeat split;
  simpl;
  unfold assert_implies;
  unfold ap in *; unfold ap2 in *;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq;
          [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] =>
                         destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] =>
            rewrite -> H in *; clear H
        | [H : _ = st _ |- _] =>
            rewrite <- H in *; clear H
        end
    end;
  try eauto;
  try lia.
  
Theorem reduce_to_zero_correct''' :
  {{True}}
    reduce_to_zero'
  {{X = 0}}.
Proof.
unfold reduce_to_zero'.
eapply hoare_consequence_post.
- apply hoare_while.
  eapply hoare_consequence_pre.
  -- apply hoare_asgn.
  -- verify_assn.
- verify_assn.
Qed.

(* definition of a decorated command *)
Inductive dcom : Type :=
| DCSkip (Q : Assertion)
  (* skip {{ Q }} *)
| DCSeq (d1 d2 : dcom)
  (* d1 ; d2 *)
| DCAsgn (X : string) (a : aexp) (Q : Assertion)
  (* X := a {{ Q }} *)
| DCIf (b : bexp) (P1 : Assertion) (d1 : dcom)
       (P2 : Assertion) (d2 : dcom) (Q : Assertion)
  (* if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }} *)
| DCWhile (b : bexp) (P : Assertion) (d : dcom)
          (Q : Assertion)
  (* while b do {{ P }} d end {{ Q }} *)
| DCPre (P : Assertion) (d : dcom)
  (* ->> {{ P }} d *)
| DCPost (d : dcom) (Q : Assertion)
  (* d ->> {{ Q }} *).

(* dcom - decorated command;
   decorated - decorated program *)

(* to provide the initial precondition that goes
   at the beginning of the program *)
Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.
  
Declare Scope dcom_scope.
Notation "'skip' {{ P }}"
      := (DCSkip P)
      (in custom com at level 0, P constr) : dcom_scope.
Notation "l ':=' a {{ P }}"
      := (DCAsgn l a P)
      (in custom com at level 0, l constr at level 0,
          a custom com at level 85, P constr, no associativity) : dcom_scope.
Notation "'while' b 'do' {{ Pbody }} d 'end' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
           (in custom com at level 89, b custom com at level 99,
           Pbody constr, Ppost constr) : dcom_scope.
Notation "'if' b 'then' {{ P }} d 'else' {{ P' }} d' 'end' {{ Q }}"
      := (DCIf b P d P' d' Q)
           (in custom com at level 89, b custom com at level 99,
               P constr, P' constr, Q constr) : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
      (in custom com at level 12, right associativity, P constr) : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
      (in custom com at level 10, right associativity, P constr) : dcom_scope.
Notation " d ; d' "
      := (DCSeq d d')
      (in custom com at level 90, right associativity) : dcom_scope.
Notation "{{ P }} d"
      := (Decorated P d)
      (in custom com at level 91, P constr) : dcom_scope.
Local Open Scope dcom_scope.

Example dec0 :=
  <{ skip {{ True }} }>.

Example dec1 :=
  <{ while true do {{ True }} skip {{ True }} end
  {{ True }} }>.
  
Set Printing All.
Print dec1.
Unset Printing All.

Example dec_while : decorated :=
  <{
  {{ True }}
    while X <> 0
    do
                 {{ True /\ (X <> 0) }}
      X := X - 1
                 {{ True }}
    end
  {{ True /\ X = 0}} ->>
  {{ X = 0 }} }>.

(* strips decorations from a decorated command *)  
Fixpoint extract (d : dcom) : com :=
  match d with
  | DCSkip _ => CSkip
  | DCSeq d1 d2 => CSeq (extract d1) (extract d2)
  | DCAsgn X a _ => CAsgn X a
  | DCIf b _ d1 _ d2 _ => CIf b (extract d1) (extract d2)
  | DCWhile b _ d _ => CWhile b (extract d)
  | DCPre _ d => extract d
  | DCPost d _ => extract d
  end.

(* strips the initial precondition from a program *)  
Definition extract_dec (dec : decorated) : com :=
  match dec with
  | Decorated P d => extract d
  end.
  
Example extract_while_ex :
    extract_dec dec_while
  = <{while X <> 0 do X := X - 1 end}>.
Proof.
  unfold dec_while.
  simpl.
  reflexivity.
Qed.

(* returns the precondition of a decorated program *)
Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.

(* returns the postcondition of a decorated command *)  
Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P => P
  | DCSeq _ d2 => post d2
  | DCAsgn _ _ Q => Q
  | DCIf _ _ _ _ _ Q => Q
  | DCWhile _ _ _ Q => Q
  | DCPre _ d => post d
  | DCPost _ Q => Q
  end.

(* returns the postcondition of a decorated program *)  
Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.
  
Example pre_dec_while : pre_dec dec_while = True.
Proof. simpl. reflexivity. Qed.

Example post_dec_while : post_dec dec_while = (X = 0)%assertion.
Proof. simpl. reflexivity. Qed.

Definition outer_triple_valid (dec : decorated) :=
  {{pre_dec dec}} extract_dec dec {{post_dec dec}}.
  
Example dec_while_triple_correct :
     outer_triple_valid dec_while
   =
     {{ True }}
       while X <> 0 do X := X - 1 end
     {{ X = 0 }}.
unfold outer_triple_valid.
unfold dec_while.
simpl.
reflexivity.
Qed.

(* returns the proposition that must be satisfied for an
   assertion to be compatible with (imply) a decorated command *) 
Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
      (P ->> Q)
  | DCSeq d1 d2 =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
      (P ->> Q [X |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((P /\ b) ->> P1)%assertion
      /\ ((P /\ ~ b) ->> P2)%assertion
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost =>
      (* post d is the loop invariant and the initial
         precondition *)
      (P ->> post d)
      /\ ((post d /\ b) ->> Pbody)%assertion
      /\ ((post d /\ ~ b) ->> Ppost)%assertion
      /\ verification_conditions Pbody d
  | DCPre P' d =>
      (P ->> P')
      /\ verification_conditions P' d
  | DCPost d Q =>
      verification_conditions P d
      /\ (post d ->> Q)
  end.
  
Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} extract d {{post d}}.
Proof.
intros d.
induction d.
- intros. simpl.
  simpl in H.
  apply hoare_consequence_pre with (P' := Q).
  -- apply hoare_skip.
  -- assumption.
- intros.
  simpl in H.
  simpl.
  destruct H.
  apply hoare_seq with (Q := post d1).
  -- apply (IHd2 (post d1)). assumption.
  -- apply (IHd1 P). assumption.
- intros. simpl. simpl in H.
  eapply hoare_consequence_pre.
  -- apply hoare_asgn.
  -- assumption.
- intros. simpl. simpl in H.
  destruct H.
  destruct H0.
  destruct H1.
  destruct H2.
  destruct H3.
  eapply hoare_if.
  -- apply hoare_consequence_pre with (P' := P1).
     --- pose proof ((IHd1 P1) H3) as H5.
         apply hoare_consequence_post with (Q' := post d1).
         + assumption.
         + assumption.
     --- assumption.
  -- apply hoare_consequence_pre with (P' := P2).
     --- pose proof ((IHd2 P2) H4) as H5.
         apply hoare_consequence_post with (Q' := post d2).
         + assumption.
         + assumption.
     --- assumption.
- intros. simpl. simpl in H.
  destruct H.
  destruct H0.
  destruct H1.
  apply hoare_consequence_pre with (P' := post d).
  -- eapply hoare_consequence_post.
     + eapply hoare_while.
       eapply hoare_consequence_pre.
       --- eauto.
       --- eauto.
     + eauto.
  -- eauto.
- intros. simpl. simpl in H.
  destruct H.
  eapply hoare_consequence_pre.
  -- apply ((IHd P) H0).
  -- eauto.
- intros. simpl. simpl in H.
  destruct H.
  apply hoare_consequence_post with (Q' := post d).
  -- eauto.
  -- eauto.
Qed.

Definition verification_conditions_dec
              (dec : decorated) : Prop :=
  match dec with
  | Decorated P d => verification_conditions P d
  end.
  
Corollary verification_correct_dec : forall dec,
  verification_conditions_dec dec ->
  outer_triple_valid dec.
Proof.
intros.
unfold outer_triple_valid.
destruct dec.
simpl.
simpl in H.
apply verification_correct.
assumption.
Qed.

Example vc_dec_while : verification_conditions_dec dec_while.
Proof. verify_assn. Qed.

Ltac verify :=
  intros;
  apply verification_correct;
  verify_assn.
  
Theorem dec_while_correct :
  outer_triple_valid dec_while.
Proof. verify. Qed.

Definition swap_dec (m n:nat) : decorated :=
  <{
    {{ X = m /\ Y = n}} ->>
         {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}
    X := X + Y
         {{ X - (X - Y) = n /\ X - Y = m }};
    Y := X - Y
         {{ X - Y = n /\ Y = m }};
    X := X - Y
    {{ X = n /\ Y = m}}
  }>.
  
Theorem swap_correct : forall m n,
  outer_triple_valid (swap_dec m n).
Proof. verify. Qed.  

Definition positive_difference_dec :=
  <{
    {{True}}
    if X <= Y then
          {{True /\ X <= Y}} ->>
          {{(Y - X) + X = Y
                   \/ (Y - X) + Y = X}}
      Z := Y - X
          {{Z + X = Y \/ Z + Y = X}}
    else
          {{True /\ ~(X <= Y)}} ->>
          {{(X - Y) + X = Y
                   \/ (X - Y) + Y = X}}
      Z := X - Y
          {{Z + X = Y \/ Z + Y = X}}
    end
    {{Z + X = Y \/ Z + Y = X}}
  }>.
  
Theorem positive_difference_correct :
  outer_triple_valid positive_difference_dec.
Proof. verify. Qed.

Compute (extract_dec positive_difference_dec).

Definition if_minus_plus_dec :=
  <{
  {{True}}
  if (X <= Y) then
              {{ True /\ X <= Y }} ->>
              {{ Y = X + (Y - X) }}
    Z := Y - X
              {{ Y = X + Z }}
  else
              {{ True /\ ~ (X <= Y) }} ->>
              {{ X + Z = X + Z }}
    Y := X + Z
              {{ Y = X + Z }}
  end
  {{ Y = X + Z}} }>.
  
Theorem if_minus_plus_correct :
  outer_triple_valid if_minus_plus_dec.
Proof. verify. Qed.

Definition div_mod_dec (a b : nat) : decorated :=
  <{
  {{ True }} ->>
  {{ b * 0 + a = a }}
    X := a
             {{ b * 0 + X = a }};
    Y := 0
             {{ b * Y + X = a }};
    while b <= X do
             {{ b * Y + X = a /\ b <= X }} ->>
             {{ b * (Y + 1) + (X - b) = a }}
      X := X - b
             {{ b * (Y + 1) + X = a }};
      Y := Y + 1
             {{ b * Y + X = a }}
    end
  {{ b * Y + X = a /\ ~(b <= X) }} ->>
  {{ b * Y + X = a /\ X < b }} }>.
  
Theorem div_mod_outer_triple_valid : forall a b,
  outer_triple_valid (div_mod_dec a b).
Proof. verify. Qed.

Example subtract_slowly_dec (m : nat) (p : nat) : decorated :=
  <{
  {{ X = m /\ Z = p }} ->>
  {{ Z - X = p - m }}
    while X <> 0 do
                  {{ Z - X = p - m /\ X <> 0 }} ->>
                  {{ (Z - 1) - (X - 1) = p - m }}
       Z := Z - 1
                  {{ Z - (X - 1) = p - m }} ;
       X := X - 1
                  {{ Z - X = p - m }}
    end
  {{ Z - X = p - m /\ X = 0 }} ->>
  {{ Z = p - m }} }>.
  
Theorem subtract_slowly_outer_triple_valid : forall m p,
  outer_triple_valid (subtract_slowly_dec m p).
Proof. verify. Qed.

Example slow_assignment_dec (m : nat) : decorated :=
  <{
    {{ X = m }}
      Y := 0
                    {{ X = m /\ Y = 0 }} ->>
                    {{ X + Y = m }} ;
      while X <> 0 do
                    {{ (X + Y = m) /\ X <> 0 }} ->>
                    {{ (X + Y = m)  [Y |-> Y + 1] [X |-> X - 1]}}
         X := X - 1
                    {{ (X + Y = m) [Y |-> Y + 1] }} ;
         Y := Y + 1
                    {{ X + Y = m }}
      end
    {{ X + Y = m /\ X = 0 }} ->>
    {{ Y = m }}
  }>.

Theorem slow_assignment : forall m,
  outer_triple_valid (slow_assignment_dec m).
Proof. verify. Qed.

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

Definition parity_equals (X : string) (m : nat) : Assertion :=
  fun st : state => parity (st X) = parity m.

Definition parity_minus_2_equals (X : string) (m : nat) : Assertion :=
  fun st : state => parity ((st X) - 2) = parity m.
  
Example parity_dec (m : nat) : decorated :=
<{
  {{ X = m }} ->>
  {{ parity_equals X m }}
    while 2 <= X do
                {{ (parity_equals X m) /\ 2 <= X }} ->>
                {{ parity_minus_2_equals X m }}
      X := X - 2
                {{ parity_equals X m }}
    end
  {{ (parity_equals X m) /\ ~(2 <= X) }} ->>
  {{ X = parity m }}
}>.

Theorem parity_proof : forall m,
  outer_triple_valid (parity_dec m).
Proof. 
verify.
- unfold parity_equals. reflexivity.
- destruct (st X).
  -- inversion H0.
  -- destruct n.
     --- inversion H0.
     --- lia.
- unfold not.
  intros.
  destruct (st X).
  -- inversion H1.
  -- destruct n.
     --- inversion H1.
         inversion H3.
     --- inversion H0.
- unfold parity_minus_2_equals.
  unfold parity_equals in H.
  rewrite <- H.
  destruct (st X).
  -- simpl. reflexivity.
  -- simpl. destruct n.
     --- simpl. inversion H0. inversion H2.
     --- inversion H0.
         + simpl. reflexivity.
         + simpl. assert (H3: n - 0 = n) by lia. rewrite H3. reflexivity.
- unfold parity_equals in H.
  unfold not in H0.
  rewrite <- H.
  destruct (st X).
  -- simpl. reflexivity.
  -- unfold parity.
     destruct n.
     --- reflexivity.
     --- exfalso.
         apply H0.
         lia.
Qed. 
      
Definition sqrt_dec (m:nat) : decorated :=
  <{
    {{ X = m }} ->>
    {{ X = m /\ 0 * 0 <= m }}
      Z := 0
                   {{ X = m /\ Z * Z <= m }};
      while ((Z+1)*(Z+1) <= X) do
                   {{ X = m /\ Z * Z <= m /\ (Z+1)*(Z+1)<=X }} ->>
                   {{ X = m /\ (Z+1)*(Z+1) <= m }}
        Z := Z + 1
                   {{ X = m /\ Z * Z <= m }}
      end
    {{ X = m /\ Z * Z <= m /\ ~((Z+1)*(Z+1) <= X) }} ->>
    {{ Z * Z <= m /\ m < (Z+1)*(Z+1) }}
  }>.
  
Theorem sqrt_correct : forall m,
  outer_triple_valid (sqrt_dec m).
Proof. verify. Qed.

Fixpoint fact (n : nat) : nat :=
      match n with
      | O => 1
      | S n' => n * (fact n')
      end.

Definition equals_fact (X Y : string) :=
  fun st : state => st X = fact (st Y).

Definition equals_fact' (X Y : string) :=
  fun st : state => (st X) * ((st Y) + 1) = fact (st Y + 1).

Definition equals_fact'' (X Y : string) :=
  fun st : state => (st X) * (st Y) = fact (st Y).

Definition factorial_dec (m : nat) : decorated :=
<{
   {{ X = m }}
   Y := 1
   {{ X = m /\ Y = 1 }};
   Z := 0
   {{ X = m /\ (equals_fact Y Z) }};
   while Z <> m do
            {{ X = m /\ (equals_fact Y Z) /\ Z <> m }} ->>
            {{ X = m /\ (equals_fact' Y Z) }}
     Z := Z + 1
            {{ X = m /\ (equals_fact'' Y Z) }};
     Y := Y * Z
            {{ X = m /\ (equals_fact Y Z) }}
   end
   {{ X = m /\ equals_fact Y Z /\ ~(Z <> m) }} ->>
   {{ equals_fact Y X }}
}>.

Theorem factorial_correct : forall m,
  outer_triple_valid (factorial_dec m).
Proof. 
verify. 
- unfold equals_fact'.
  unfold equals_fact in H0.
  rewrite H0.
  destruct (st Z).
  -- simpl. reflexivity.
  -- simpl. assert (H2: S (n + 1) = n + 1 + 1) by lia.
     rewrite H2. 
     assert (H3: fact (n + 1) = (n + 1) * fact n).
     {
       clear H0 H1 H2.
       induction n.
       - simpl. reflexivity.
       - simpl. rewrite IHn. lia.
     }
     rewrite H3. lia.
- unfold equals_fact in *.
  assert (H2: st Z = st X) by lia.
  rewrite <- H2. assumption.
Qed.

Definition minimum_dec (a b : nat) : decorated :=
  <{
    {{ True }} ->>
    {{ a + 0 = a /\ b + 0 = b }}
      X := a
             {{ X + 0 = a /\ b + 0 = b }};
      Y := b
             {{ X + 0 = a /\ Y + 0 = b }};
      Z := 0
             {{ X + Z = a /\ Y + Z = b }};
      while X <> 0 && Y <> 0 do
             {{ X + Z = a /\ Y + Z = b /\ X <> 0 /\ Y <> 0 }} ->>
             {{ (X - 1) + (Z + 1) = a /\ (Y - 1) + (Z + 1) = b }}
        X := X - 1
             {{ X + (Z + 1) = a /\ (Y - 1) + (Z + 1) = b }};
        Y := Y - 1
             {{ X + (Z + 1) = a /\ Y + (Z + 1) = b }};
        Z := Z + 1
             {{ X + Z = a /\ Y + Z = b }}
      end
    {{ X + Z = a /\ Y + Z = b /\ ~( X <> 0 /\ Y <> 0) }} ->>
    {{ Z = min a b }}
  }>.
  
Theorem minimum_correct : forall a b,
  outer_triple_valid (minimum_dec a b).
Proof. 
verify.
- rewrite andb_true_iff in H0.
  destruct H0.
  rewrite negb_true_iff in H.
  rewrite eqb_neq in H.
  assumption.
- rewrite andb_true_iff in H0.
  destruct H0.
  rewrite negb_true_iff in H0.
  rewrite eqb_neq in H0.
  assumption.
- rewrite andb_false_iff in H0.
  destruct H0.
  -- unfold not.
     intros.
     destruct H0.
     apply H0.
     rewrite negb_false_iff in H.
     rewrite eqb_eq in H.
     assumption.
  -- unfold not.
     intros.
     destruct H0.
     apply H1.
     rewrite negb_false_iff in H.
     rewrite eqb_eq in H.
     assumption.
Qed.

(* to check the last assertion in minimum_dec *)
Lemma test_min : forall x y z a b,
  x + z = a /\ y + z = b /\ ~( x <> 0 /\ y <> 0)
    -> z = min a b.
Proof.
lia.  
Qed.
     
Definition two_loops_dec (a b c : nat) : decorated :=
  <{
    {{ True }} ->>
    {{ c = 0 + c }}
      X := 0
                   {{ c = X + c }};
      Y := 0
                   {{ c = X + c /\ Y = 0}};
      Z := c
                   {{ Z = X + c /\ Y = 0}};
      while X <> a do
                   {{ Z = X + c /\ Y = 0 /\ (X <> a)}} ->>
                   {{ Z + 1 = X + 1 + c /\ Y = 0}}
        X := X + 1
                   {{ Z + 1 = X + c /\ Y = 0}};
        Z := Z + 1
                   {{ Z = X + c /\ Y = 0}}
      end
                   {{ Z = X + c /\ Y = 0 /\ ~ (X <> a) }} ->>
                   {{ Z = Y + a + c }};
      while Y <> b do
                   {{ Z = Y + a + c /\ (Y <> b) }} ->>
                   {{ Z + 1 = Y + 1 + a + c }}
        Y := Y + 1
                   {{ Z + 1 = Y + a + c }};
        Z := Z + 1
                   {{ Z = Y + a + c }}
      end
    {{ Z = Y + a + c /\ ~( Y <> b) }} ->>
    {{ Z = a + b + c }}
  }>.     

Theorem two_loops : forall a b c,
  outer_triple_valid (two_loops_dec a b c).
Proof.
verify.
Qed.

Fixpoint pow2 n :=
  match n with
  | 0 => 1
  | S n' => 2 * (pow2 n')
  end.     

Definition dpow2_dec (n : nat) :=     
<{
    {{ True }} ->>
    {{ 1 = 2 * 1 - 1 /\ 1 = ap pow2 0 }}
      X := 0
               {{ 1 = 2 * 1 - 1 /\ 1 = ap pow2 X }};
      Y := 1
               {{ Y = 2 * 1 - 1 /\ 1 = ap pow2 X }};
      Z := 1
               {{ Y = 2 * Z - 1 /\ Z = ap pow2 X }};
      while X <> n do
               {{ Y = 2 * Z - 1 /\ Z = ap pow2 X /\ X <> n }} ->>
               {{ Y + (2 * Z) = 2 * (2 * Z) - 1 /\ (2 * Z) = ap pow2 (X + 1) }}
        Z := 2 * Z
               {{ Y + Z = 2 * Z - 1 /\ Z = ap pow2 (X + 1) }};
        Y := Y + Z
               {{ Y = 2 * Z - 1 /\ Z = ap pow2 (X + 1)}};
        X := X + 1
               {{ Y = 2 * Z - 1 /\ Z = ap pow2 X }}
      end
    {{ Y = 2 * Z - 1 /\ Z = ap pow2 X /\ ~ (X <> n) }} ->>
    {{ Y = pow2 (n+1) - 1 }}
  }>.
     
Lemma pow2_plus_1 : forall n,
  pow2 (n+1) = pow2 n + pow2 n.
Proof. induction n; simpl. reflexivity. lia. Qed.

Lemma pow2_le_1 : forall n, pow2 n >= 1.
Proof. induction n. simpl. constructor. simpl. lia. Qed.

Theorem dpow2_down_correct : forall n,
  outer_triple_valid (dpow2_dec n).
Proof.
verify.
- rewrite add_0_r.
  destruct (st X).
  -- simpl. reflexivity.
  -- simpl. rewrite add_0_r. rewrite add_0_r.
     rewrite pow2_plus_1. reflexivity.
- rewrite add_0_r.
  rewrite pow2_plus_1.
  assert (H2: st X = n) by lia.
  rewrite H2. reflexivity.
Qed.


     
     
     
     
     
     
     
     