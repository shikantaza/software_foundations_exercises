Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.

From Coq Require Import Logic.FunctionalExtensionality.

Definition Assertion := state -> Prop.

Module ExAssertions.

Definition assn1 : Assertion := fun st => st X <= st Y.

Definition assn2 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.

Definition assn3 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).

Definition assn4 : Assertion :=
  fun st => st Z = max (st X) (st Y).

(* 
assn1: Holds for all states in which the value of X is less than 
       or equal to that of Y

assn2: Holds for all states in which the value of X is 3 or the
       value of X is less than or equal to that of Y

assn3: Holds for all states in which the square of the value of Z is
       less than or equal to that of X and the square of the value of 
       (Z+1) is greater than that of X

assn4: Holds for all states in which the value of Z is the greater
       of the values of X and Y 
*)
 
End ExAssertions.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope hoare_spec_scope.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.

Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.
  
Definition Aexp : Type := state -> nat.
Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.
Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.
Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

Declare Scope assertion_scope.

Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.

Delimit Scope assertion_scope with assertion.

Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).
Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st -> assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <-> assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.

Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st => f (x st).
  
Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) :=
  f (x st) (y st).
  
Module ExamplePrettyAssertions.

Definition ex1 : Assertion := X = 3.
Definition ex2 : Assertion := True.
Definition ex3 : Assertion := False.
Definition assn1 : Assertion := X <= Y.
Definition assn2 : Assertion := X = 3 \/ X <= Y.
Definition assn3 : Assertion := Z = ap2 max X Y.
Definition assn4 : Assertion := Z * Z <= X
                            /\ ~ (((ap S Z) * (ap S Z)) <= X).

End ExamplePrettyAssertions.

(*
Paraphrase the following in English. 
     1) {{True}} c {{X = 5}}
        The command c transforms any state into one in which X = 5

     2) forall m, {{X = m}} c {{X = m + 5)}}
        The command c transforms all states into one in which X is incremented by 5
      

     3) {{X ≤ Y}} c {{Y ≤ X}}
        The command c transforms a state in which X <= Y into one in which Y <= X

     4) {{True}} c {{False}}
        The command c does not terminate given any initial state

     5) forall m,
          {{X = m}}
          c
          {{Y = real_fact m}}
        The command c transforms all states into one in which Y = real_fact X

     6) forall m,
          {{X = m}}
          c
          {{(Z × Z) ≤ m ∧ ¬(((S Z) × (S Z)) ≤ m)}}
        The command c transforms all states into one in which Z^2 is <= X and (Z+1)^2 is <= X
*)

(*
Which of the following Hoare triples are valid -- i.e., the claimed relation between P, c, and Q is true? 

   1) {{True}} X := 5 {{X = 5}} - VALID

   2) {{X = 2}} X := X + 1 {{X = 3}} - VALID

   3) {{True}} X := 5; Y := 0 {{X = 5}} - VALID

   4) {{X = 2 ∧ X = 3}} X := 5 {{X = 0}} - INVALID

   5) {{True}} skip {{False}} - INVALID

   6) {{False}} skip {{True}} - INVALID

   7) {{True}} while true do skip end {{False}} - VALID

   8) {{X = 0}}
        while X = 0 do X := X + 1 end
      {{X = 1}} - VALID

   9) {{X = 1}}
        while X ≠ 0 do X := X + 1 end
      {{X = 100}} - INVALID
*)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st ->
     Q st'.
     
Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.
  
Check ({{True}} X := 0 {{True}}).

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
intros.
unfold hoare_triple.
intros.
apply (H st').
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
intros.
unfold hoare_triple.
intros.
pose proof (H st) as H2.
exfalso.
apply (H2 H1).
Qed.

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
intros.
unfold hoare_triple.
intros.
inversion H.
rewrite <- H3. assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof.
intros.
unfold hoare_triple.
intros.
unfold hoare_triple in H0.
unfold hoare_triple in H.
inversion H1.
subst.
pose proof (H0 st st'0) as H9.
pose proof (H st'0 st') as H10.
pose proof (H9 H5) as H11.
pose proof (H10 H8) as H12.
apply (H12 (H11 H2)).
Qed.

Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).
    
Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level, a custom com).
  
Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
intros.
unfold hoare_triple.
intros.
unfold assn_sub in H0.
inversion H.
subst.
assumption.
Qed.

Example assn_sub_example :
  {{(X < 5) [X |-> X + 1]}}
    X := X + 1
  {{X < 5}}.
Proof.  apply hoare_asgn. Qed.

Example hoare_asgn_examples1 :
  exists P,
    {{ P }}
      X := 2 * X
    {{ X <= 10 }}.
Proof.
exists (fun st => (st X) = 4).
simpl.
unfold hoare_triple.
intros.
inversion H.
subst.
simpl.
rewrite t_update_eq.
rewrite H0.
lia.
Qed.

Example hoare_asgn_examples2 :
  exists P,
    {{ P }}
      X := 3
    {{ 0 <= X /\ X <= 5 }}.
Proof.
exists (fun st => (0 <= 3 /\ 3 <= 5)).
simpl.
unfold hoare_triple.
intros.
inversion H.
subst.
rewrite t_update_eq.
simpl.
assumption.
Qed.

(* counterexample for wrong forward assignment rule: X := X + 1 *)

Theorem hoare_asgn_fwd :
  forall m a P,
  {{fun st => P st /\ st X = m}}
    X := a
  {{fun st => P (X !-> m ; st)
           /\ st X = aeval (X !-> m ; st) a }}.
Proof.
intros.
unfold hoare_triple.
intros.
destruct H0.
split.
- inversion H. subst.
  rewrite t_update_shadow.
  rewrite t_update_same.
  assumption.
- inversion H. subst.
  rewrite t_update_eq.
  rewrite t_update_shadow.
  rewrite t_update_same.
  reflexivity.
Qed.

Theorem hoare_asgn_fwd_exists :
  forall a P,
  {{fun st => P st}}
    X := a
  {{fun st => exists m, P (X !-> m ; st) /\
                st X = aeval (X !-> m ; st) a }}.
Proof.
intros.
unfold hoare_triple.
intros.
inversion H.
subst.
rewrite t_update_eq.
exists (st X).
split.
- rewrite t_update_shadow.
  rewrite t_update_same.
  assumption.
- rewrite t_update_shadow.
  rewrite t_update_same.
  reflexivity.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
intros.
unfold hoare_triple.
intros.
unfold hoare_triple in H.
unfold assert_implies in H0.
apply (((H st st') H1) ((H0 st) H2)).
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
intros.
unfold hoare_triple.
unfold hoare_triple in H.
unfold assert_implies in H0.
intros.
apply ((H0 st') (((H st st') H1) H2)).
Qed.

Example hoare_asgn_example1 :
  {{True}} X := 1 {{X = 1}}.
Proof.
assert (H1:  {{(X = 1) [X |-> 1]}} X := 1 {{X = 1}}) by (apply hoare_asgn).
assert (H2: True ->> (X = 1) [X |-> 1]). 
{ simpl. unfold assert_implies.
  reflexivity.
}
apply (hoare_consequence_pre True ((X=1)[X |->1]) (X=1) <{X := 1}> H1 H2).
Qed.

Example assn_sub_example2 :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
(* technique used in the book *) 
(*
apply hoare_consequence_pre with (P' := (X < 5) [X |-> X + 1]).
- apply hoare_asgn.
- unfold assert_implies.
  intros.
  simpl.
  unfold assn_sub.
  rewrite t_update_eq.
  simpl.
  simpl in H.
  lia.
Qed.
*)

assert (H1: {{ (X < 5)[X |-> X + 1] }} X := X + 1 {{ X < 5 }}) by (apply hoare_asgn).
assert (H2: (fun st => st X < 4) ->> (X < 5)[X |-> X + 1]). { 
unfold assert_implies. intros. simpl. unfold assn_sub. rewrite t_update_eq. simpl. lia. }
apply (hoare_consequence_pre (X < 4) ((X < 5)[X |-> X + 1]) (X < 5) <{X := X + 1 }> H1 H2).
Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
(* technique used in the book *)
(*
intros.
apply hoare_consequence_pre with (P' := P').
- apply hoare_consequence_post with (Q' := Q').
  -- assumption.
  -- assumption.
- assumption.
Qed.
*)
intros.
unfold hoare_triple.
intros.
unfold hoare_triple in H.
unfold assert_implies in H0.
unfold assert_implies in H1.
eauto.
Qed.

Hint Unfold assert_implies hoare_triple assn_sub t_update : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.


Theorem hoare_consequence_pre' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

Theorem hoare_consequence_pre''' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  eapply Hhoare.
  - eassumption.
  - apply Himp. assumption.
Qed.

Example assn_sub_ex1' :
  {{ X <= 5 }}
    X := 2 * X
  {{ X <= 10 }}.
Proof.
  unfold hoare_triple, "->>".
  intros.
  simpl.
  simpl in H0.
  inversion H.
  subst.
  rewrite t_update_eq.
  simpl.
  lia.
Qed.
 
Example assn_sub_ex2' :
  {{ 0 <= 3 /\ 3 <= 5 }}
    X := 3
  {{ 0 <= X /\ X <= 5 }}.
Proof.
(*
unfold hoare_triple, "->>".
intros.
simpl.
simpl in H0.
inversion H.
subst.
rewrite t_update_eq.
simpl.
assumption.
*)
eapply hoare_consequence_pre.
- apply hoare_asgn.
- unfold "->>".
  intros.
  eauto.
Qed.

Ltac assn_auto :=
  try auto; (* as in example 1, above *)
  try (unfold "->>", assn_sub, t_update;
       intros; simpl in *; lia).

Example hoare_asgn_example3 : forall (a:aexp) (n:nat),
  {{a = n}}
    X := a;
    skip
  {{X = n}}.
Proof.
(*
intros.
unfold hoare_triple.
intros.
simpl.
simpl in H0.
inversion H. subst.
inversion H6. subst.
inversion H3. subst.
rewrite t_update_eq.
reflexivity.
*)
(* book version *)
intros a n. eapply hoare_seq.
  - (* right part of seq *)
    apply hoare_skip.
  - (* left part of seq *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto.
Qed.

Example hoare_asgn_example4 :
  {{ True }}
    X := 1;
    Y := 2
  {{ X = 1 /\ Y = 2 }}.
Proof.
  apply hoare_seq with (Q := (X = 1)%assertion).
  - eapply hoare_consequence_pre.
    -- apply hoare_asgn.
    -- eauto.
  - eapply hoare_consequence_pre.
    -- apply hoare_asgn.
    -- eauto.
Qed.

Definition swap_program : com := <{ Z := X; X := Y; Y := Z }>.

Theorem swap_exercise :
  {{X <= Y}}
    swap_program
  {{Y <= X}}.
Proof.
unfold swap_program.
eapply hoare_seq.
- eapply hoare_seq.
  -- apply hoare_asgn.
  -- apply hoare_asgn.
- eapply hoare_consequence_pre.
  -- apply hoare_asgn.
  -- assn_auto.
Qed.

Theorem invalid_triple : ~ forall (a : aexp) (n : nat),
    {{ a = n }}
      X := 3; Y := a
    {{ Y = n }}.
Proof.
  unfold hoare_triple.
  intros H.
  simpl in H.
  specialize H with (a := X) (n := 2).
  pose proof (H (X !-> 2) (Y !-> 3; X !-> 3; X !-> 2)) as H1.
  assert (H2: (X !-> 2) =[ X := 3; Y := X ]=> (Y !-> 3; X !-> 3; X !-> 2)).
  {
    apply E_Seq with (X !-> 3; X !-> 2). 
    - apply E_Asgn. simpl. reflexivity.
    - apply E_Asgn. simpl. rewrite t_update_eq. reflexivity. 
  }
  pose proof (H1 H2) as H3.
  rewrite t_update_eq in H3.
  simpl in H3.
  rewrite t_update_eq in H3.
  lia.
Qed.  

Definition bassn b : Assertion :=
  fun st => (beval st b = true).
  
Coercion bassn : bexp >-> Assertion.

Arguments bassn /.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
(*
intros.
unfold not.
intros.
simpl in H0.
rewrite H in H0.
discriminate.
*)
(* book proof *)
congruence.
Qed.

Hint Resolve bexp_eval_false : core.

Theorem hoare_if : forall P Q b c1 c2,
        {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
        {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
        {{P}} if b then c1 else c2 end {{Q}}.
Proof.
intros.
unfold hoare_triple.
intros.
unfold hoare_triple in H, H0.
pose proof (H st st') as H3.
pose proof (H0 st st') as H4.
inversion H1.
- subst.
  pose proof (H3 H11) as H12.
  apply H12.
  split.
  -- assumption.
  -- simpl. assumption.
- subst.
  pose proof (H4 H11) as H12.
  apply H12.
  split.
  -- assumption.
  -- simpl. rewrite H10. lia.
Qed.

Example if_example :
  {{True}}
    if (X = 0)
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
apply hoare_if.
- unfold hoare_triple.
  intros.
  simpl.
  inversion H.
  subst.
  simpl.
  rewrite t_update_eq.
  destruct H0.
  simpl in H1.
  rewrite eqb_eq in H1.
  destruct (String.eqb X Y) eqn: Heq.
  -- rewrite String.eqb_eq in Heq.
     rewrite Heq.
     rewrite t_update_eq. lia.
  -- rewrite String.eqb_neq in Heq.
     rewrite t_update_neq.
     --- rewrite H1. lia.
     --- auto.
- unfold hoare_triple.
  intros.
  simpl.
  inversion H.
  subst.
  simpl.
  rewrite t_update_eq.
  destruct (String.eqb X Y) eqn: Heq.
  -- rewrite String.eqb_eq in Heq.
     rewrite Heq.
     rewrite t_update_eq. lia.
  -- rewrite String.eqb_neq in Heq.
     rewrite t_update_neq.
     --- lia.
     --- auto.
Qed.

(* book version *)
Example if_example' :
  {{True}}
    if (X = 0)
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
apply hoare_if.
  - (* Then *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto. (* no progress *)
      unfold "->>", assn_sub, t_update, bassn.
      simpl. intros st [_ H]. apply eqb_eq in H.
      rewrite H. lia.
  - (* Else *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto.
Qed.  

Ltac assn_auto' :=
  unfold "->>", assn_sub, t_update, bassn;
  intros; simpl in *;
  try rewrite -> eqb_eq in *; (* for equalities *)
  auto; try lia.
  
Ltac assn_auto'' :=
  unfold "->>", assn_sub, t_update, bassn;
  intros; simpl in *;
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *; (* for inequalities *)
  auto; try lia.
  
Theorem if_minus_plus :
  {{True}}
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  {{Y = X + Z}}.
Proof.
apply hoare_if.
- eapply hoare_consequence_pre.
  -- apply hoare_asgn.
  -- assn_auto''.
- eapply hoare_consequence_pre.
  -- apply hoare_asgn.
  -- assn_auto''.
Qed.


Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'if1' x 'then' y 'end'" :=
         (CIf1 x y)
             (in custom com at level 0, x custom com at level 99).
Notation "'skip'" :=
         CSkip (in custom com at level 0).
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

Reserved Notation "st '=[' c ']=>'' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).
          
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''
  | E_If1True : forall st st' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st =[ if1 b then c end ]=> st'
  | E_If1False : forall b st c,
      beval st b = false ->
      st =[ if1 b then c end ]=> st 

where "st '=[' c ']=>' st'" := (ceval c st st').

Hint Constructors ceval : core.

Example if1true_test :
  empty_st =[ if1 X = 0 then X := 1 end ]=> (X !-> 1).
Proof.
(* apply E_If1True.
- simpl. reflexivity.
- apply E_Asgn. simpl. reflexivity. *)
eauto.
Qed.

Example if1false_test :
  (X !-> 2) =[ if1 X = 0 then X := 1 end ]=> (X !-> 2).
Proof.
eauto.
Qed.

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
       st =[ c ]=> st' ->
       P st ->
       Q st'.
       
Hint Unfold hoare_triple : core.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c custom com at level 99)
                                  : hoare_spec_scope.

Theorem hoare_if1 : forall P Q b c,
        {{fun st => P st /\ bassn b st}} c {{Q}} ->
        {{fun st => P st /\ ~(bassn b st)}} c {{P}} ->
        {{P}} if1 b then c end {{P \/ Q}}.
Proof.
intros.
unfold hoare_triple.
unfold hoare_triple in H, H0.
intros.
inversion H1.
- subst.
  right.
  apply ((H st st') H8).
  split.
  -- assumption.
  -- simpl. assumption.
- subst.
  left.
  assumption.
Qed.

Theorem hoare_if1_good :
  {{ X + Y = Z }}
    if1 Y <> 0 then
      X := X + Y
    end
  {{ X = Z }}.
Proof.
unfold hoare_triple.
intros.
simpl in H0.
inversion H.
- subst.
  simpl.
  inversion H6.
  subst.
  simpl.
  rewrite t_update_eq.
  destruct (String.eqb X Z) eqn: Heq.
  -- assert (H7: X = Z). { apply String.eqb_eq. assumption. }
     rewrite <- H7. rewrite t_update_eq. reflexivity.
  -- assert (H7: X <> Z). { apply String.eqb_neq. assumption. }
     rewrite t_update_neq.
     --- assumption.
     --- assumption.
- subst.
  simpl.
  simpl in H5.
  rewrite negb_false_iff in H5.
  rewrite eqb_eq in H5.
  rewrite H5 in H0.
  rewrite <- H0.
  lia.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
unfold hoare_triple.
intros.
apply H with (st := st) (st' := st').
- assumption.
- unfold "->>" in H0.
  apply (H0 st). assumption.        
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
intros.
unfold hoare_triple.
unfold hoare_triple in H.
unfold assert_implies in H0.
intros.
apply ((H0 st') (((H st st') H1) H2)).
Qed.

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X := a) {{Q}}.
Proof.
intros.
unfold hoare_triple.
intros.
inversion H.
subst.
unfold assn_sub in H0.
assumption.
Qed.

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
intros.
unfold hoare_triple.
intros.
remember <{while b do c end }> as cw eqn: Heqcw.
induction H0.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
- inversion Heqcw. clear Heqcw.
  unfold hoare_triple in H.
  split.
  -- assumption.
  -- simpl.
     rewrite H3 in H0.
     unfold not.
     intros.
     rewrite H0 in H2.
     discriminate.
- inversion Heqcw. clear Heqcw.
  unfold hoare_triple in H.
  split.
  -- subst.
     pose proof ((H st st') H0_) as H2.
     simpl in H2.
     assert (H3: P st') by auto.
     assert (H4: <{ while b do c end }> = <{ while b do c end }>) by reflexivity.
     pose proof ((IHceval2 H4) H3) as H5.
     destruct H5.
     assumption.
  -- subst.
     pose proof ((H st st') H0_) as H2.
     simpl in H2.
     assert (H3: P st') by auto.
     assert (H4: <{ while b do c end }> = <{ while b do c end }>) by reflexivity.
     pose proof ((IHceval2 H4) H3) as H5.
     destruct H5.
     assumption.
- discriminate.
- discriminate.
Qed.

Lemma while_example_helper : forall (n m  : nat), (n <=? m) <> true -> n > m.
Proof.
intros.
unfold not in H.
unfold gt.
apply lt_nge.
unfold not.
intros.
apply leb_correct in H0.
apply (H H0).
Qed.

Example while_example :
  {{X <= 3}}
    while (X <= 2) do
      X := X + 1
    end
  {{X = 3}}. 
Proof.
simpl.
assert (H: {{fun st : state => st X <= 3}} 
           while X <= 2 do X := X + 1 end
           {{fun st : state => st X <= 3 /\ (st X <=? 2) <> true}}).
{ apply hoare_while.
  unfold hoare_triple.
  intros.
  inversion H.
  subst.
  simpl.
  rewrite t_update_eq.
  destruct H0.
  simpl in H1.
  apply leb_complete in H1.
  lia.
}  
(* pose proof (hoare_while (X <= 3)%assertion <{X <= 2}> <{X := X + 1 }>) as H. *)
(* simpl in H. *)
assert (H1: (fun st : state => st X <= 3 /\ (st X <=? 2) <> true) 
            ->>  (fun st : state => st X = 3)).
{
  unfold "->>".
  intros.
  destruct H0.
  apply while_example_helper in H1.
  lia.
}
pose proof (hoare_consequence_post (fun st : state => st X <= 3)
                                   (fun st : state => st X = 3)
                                   (fun st : state => st X <= 3 /\ (st X <=? 2) <> true)
                                   <{ while X <= 2 do X := X + 1 end }>
                                   H
                                   H1) as H2.
assumption.
Qed.

(* book version *)
Example while_example' :
  {{X <= 3}}
    while (X <= 2) do
      X := X + 1
    end
  {{X = 3}}. 
Proof.
 eapply hoare_consequence_post.
  - apply hoare_while.
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto''.
  - assn_auto''.
Qed.

Theorem loop_never_stops : forall st st',
  ~(st =[ while true do skip end ]=> st').
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
  - discriminate.
  - discriminate.
Qed.

Theorem always_loop_hoare : forall Q,
  {{True}} while true do skip end {{Q}}.
Proof.
intros.
unfold hoare_triple.
intros.
exfalso.
pose proof (loop_never_stops st st') as H1.
apply (H1 H).
Qed.

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
intros.
unfold hoare_triple.
intros.
apply (H st').
Qed.

(* book version *)
Theorem always_loop_hoare' : forall Q,
  {{True}} while true do skip end {{Q}}.
Proof.
  intros Q.
  eapply hoare_consequence_post.
  - apply hoare_while. apply hoare_post_true. auto.
  - simpl. intros st [Hinv Hguard]. congruence.
Qed.

End If1.

Module RepeatExercise.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.
  
Notation "'repeat' e1 'until' b2 'end'" :=
          (CRepeat e1 b2)
              (in custom com at level 0,
               e1 custom com at level 99, b2 custom com at level 99).
Notation "'skip'" :=
         CSkip (in custom com at level 0).
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).
            
Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''
  | E_RepeatEnd : forall st st' b c,
      st =[ c ]=> st' ->
      beval st' b = true ->
      st =[ repeat c until b end ]=> st'
  | E_RepeatLoop : forall st st' st'' b c,
      st =[ c ]=> st' ->
      beval st' b = false ->
      st' =[ repeat c until b end ]=> st'' ->
      st =[ repeat c until b end ]=> st''
where "st '=[' c ']=>' st'" := (ceval st c st').

Hint Constructors ceval : core.

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion)
                        : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Hint Unfold hoare_triple : core.
  
Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99).

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
intros.
unfold hoare_triple.
unfold hoare_triple in H.
unfold assert_implies in H0.
intros.
apply ((H0 st') (((H st st') H1) H2)).
Qed.

Definition ex1_repeat :=
  <{ repeat
       X := 1;
       Y := Y + 1
     until (X = 1) end }>.

Theorem ex1_repeat_works :
  empty_st =[ ex1_repeat ]=> (Y !-> 1 ; X !-> 1).
Proof.
unfold ex1_repeat.
apply E_RepeatEnd.
- apply E_Seq with (X !-> 1).
  -- apply E_Asgn. simpl. reflexivity.
  -- apply E_Asgn. simpl. reflexivity.
- simpl. reflexivity.
Qed.

Theorem hoare_repeat : forall P Q (b:bexp) c,
  {{P}} c {{Q}} ->
  (Q /\ ~ b)%assertion ->> P ->
  {{P}} repeat c until b end {{Q /\ b}}.
Proof.
intros.
unfold hoare_triple.
intros.
remember <{repeat c until b end }> as cr.
induction H1.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
- inversion Heqcr. subst.
  split.
  -- apply H with (st := st).
     --- apply H1.
     --- apply H2.
  -- simpl. apply H3.
- inversion Heqcr. subst. apply IHceval2.
  -- reflexivity.
  -- apply H0.
     split.
     --- apply H with (st := st).
         + apply H1_.
         + apply H2.
     --- simpl.
         unfold not.
         intros.
         rewrite H3 in H1.
         inversion H1.
Qed. 

Lemma hoare_repeat_correct_helper1 :
  {{X > 0}} 
    Y := X; X := X - 1 
  {{Y > 0}}.
Proof.
simpl.
unfold hoare_triple.
intros.
assert (H1: st' = (X !-> aeval (Y !-> aeval st X; st) <{X - 1}>;
                   Y !-> aeval st X; st)). { 
  inversion H. subst.
  inversion H4. subst.
  inversion H6. subst.
  reflexivity.
}
rewrite H1.
simpl.
rewrite t_update_permute.
- rewrite t_update_eq. assumption.
- unfold not. intros.
  discriminate.
Qed.

Lemma hoare_repeat_correct_helper2 :
  (Y > 0 /\ ~ <{X = 0}> )%assertion ->> (X > 0)%assertion.
Proof.
simpl.
unfold "->>".
intros.
destruct H.
apply eq_true_not_negb in H0.
apply negb_true_iff in H0.
apply beq_nat_false in H0.
lia.
Qed.

Lemma hoare_repeat_correct_helper3 :
  (fun st : state => st Y > 0 /\ (st X =? 0) = true)
          ->> (fun st : state => st Y > 0 /\ st X = 0).
Proof.
unfold "->>".
intros.
destruct H.
split.
- assumption.
- apply beq_nat_true in H0.
  assumption.
Qed.

Lemma hoare_repeat_correct_helper4 :
  (fun st : state => st Y > 0 /\ st X = 0)
         ->> (fun st : state => st X = 0 /\ st Y > 0).
Proof.
unfold "->>".
intros.
destruct H.
split.
- assumption.
- assumption.
Qed.

Example hoare_repeat_is_correct :
  {{ X > 0 }}
    repeat
      Y := X;
      X := X - 1
    until X = 0 end
  {{ X = 0 /\ Y > 0 }}.
Proof.
simpl.
assert (H1: {{X > 0}} Y := X; X := X - 1 {{Y > 0}}).
{ apply hoare_repeat_correct_helper1. }
assert (H2: (Y > 0 /\ ~ <{X = 0}> )%assertion ->> (X > 0)%assertion).
{ apply hoare_repeat_correct_helper2. }
pose proof (hoare_repeat (X > 0)%assertion
                         (Y > 0)%assertion
                         <{X = 0}>
                         <{ Y := X; X := X - 1}>
                         H1
                         H2) as H3.
simpl in H3.
assert (H4: (fun st : state => st Y > 0 /\ (st X =? 0) = true)
          ->> (fun st : state => st Y > 0 /\ st X = 0)).
{ apply hoare_repeat_correct_helper3. }
pose proof (hoare_consequence_post (X > 0)%assertion
                                   (Y > 0 /\ X = 0)%assertion
                                   (Y > 0 /\ <{X = 0}>)%assertion
                                   <{ repeat Y := X; X := X - 1 until X = 0 end }>
                                   H3
                                   H4) as H5.
simpl in H5.
assert (H6: (fun st : state => st Y > 0 /\ st X = 0)
         ->> (fun st : state => st X = 0 /\ st Y > 0)).
{ apply hoare_repeat_correct_helper4. }
pose proof (hoare_consequence_post (X > 0)%assertion
                                   (X = 0 /\ Y > 0)%assertion
                                   (Y > 0 /\ X = 0)%assertion
                                   <{ repeat Y := X; X := X - 1 until X = 0 end }>
                                   H5
                                   H6) as H7.
assumption.
Qed.





