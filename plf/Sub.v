Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.

(*

Definition f (s : Student) : Nat := s.gpa

Definition g (f' : Person -> Nat) : Nat :=
  let p in Person 10 "xyz"
   in f' p

These will pass type-checking if subtyping is incorrectly
defined as covariant on both the right and the left of the
arrow types, but 'g f; will get stuck because p
would not have a member 'gpa'.

*)

(*

Given: S <: T and U <: V

1. T->S <: T->S   - TRUE (reflexivity)
2. Top->U <: S->Top - FALSE (Top cannot be a subtype of any type)
3. (C->C) -> (A×B)  <:  (C->C) -> (Top×B) - TRUE
4. T->T->U <: S->S->V - TRUE (contravariance)
5. (T->T)->U <: (S->S)->V - FALSE (per contravariance, (T->S)->U <: (S->T)->V )
6. ((T->S)->T)->U <: ((S->T)->S)->V - TRUE (contravariance)
7. S×V <: T×U - FALSE (V is not a subtype of U, it's the other way round)

*)

(*

(Top -> Student) <: (Person -> Student) <: (Student -> Person) <: (Student -> Top) <: Top

(Individually, Student <: Person <: Top)

Top                     :>    Top -> (Top -> Top)
Top -> Student           Not comparable to Top -> (Top -> Top)
Student -> Person        ditto
Student -> Top           ditto
Person -> Student        ditto

*)

(*

forall S T,
          S <: T  ->
          S->S   <:  T->T    FALSE
          
forall S,
         S <: A->A ->
         ∃ T,
           S = T->T  ∧  T <: A     FALSE

∃ S,
           S <: S->S    FALSE (assuming non-inductive types)

∃ S,
           S->S <: S    FALSE (same as above)

forall S T1 T2,
           S <: T1×T2 ->
           ∃ S1 S2,
              S = S1×S2  ∧  S1 <: T1  ∧  S2 <: T2   TRUE
*)

(*

There exists a type that is a supertype of every other type.
TRUE (Top)

There exists a type that is a subtype of every other type.
FALSE.

There exists a pair type that is a supertype of every other pair type.
TRUE (Top * Top) 

There exists a pair type that is a subtype of every other pair type.
FALSE.

There exists an arrow type that is a supertype of every other arrow type.
FALSE (contravariance fails for the type to the left of the arrow)

There exists an arrow type that is a subtype of every other arrow type.
FALSE (covariance fails for the type to the right of the arrow)

There is an infinite descending chain of distinct types in the subtype 
relation---that is, an infinite sequence of types  S0, S1, etc., such that 
all the Si's are different and each S(i+1) is a subtype of Si.
TRUE (Top, Top->Top, Top->(Top->Top), ...)

There is an infinite ascending chain of distinct types in the subtype 
relation---that is, an infinite sequence of types  S0, S1, etc., such that 
all the Si's are different and each S(i+1) is a supertype of Si.
FALSE, because there is no Bottom type.

*)

(*

forall T,
         ~(T = Bool ∨ ∃ n, T = Base n) ->
         ∃ S,
            S <: T  ∧  S ≠ T
FALSE. This holds good only for if T involves only Top (e.g., Top itself, 
Top->Top, Top*Top, etc.)

*)

(*

What is the smallest type T ("smallest" in the subtype relation) that makes the 
following assertion true? (Assume we have Unit among the base types and unit 
as a constant of this type.)
 
       empty |- (\p:T×Top. p.fst) ((\z:A.z), unit) \in A->A

A->A

What is the largest type T that makes the same assertion true?

A->Top

*)

(*

What is the smallest type T that makes the following assertion true? 
       empty |- (\p:(A->A × B->B). p) ((\z:A.z), (\z:B.z)) \in T
       
(A->A * B->B)       
       
      
What is the largest type T that makes the same assertion true?

(A->Top * B-> Top)

*)

(*

What is the smallest type T that makes the following assertion true? 
       a:A |- (\p:(A×T). (p.snd) (p.fst)) (a, \z:A.z) \in A
       
A->A       

What is the largest type T that makes the same assertion true?

A->Top

*)

(*

What is the smallest type T (if one exists) that makes the following assertion true? 
      ∃ S t,
        empty |- (\x:T. x x) t \in S
        
No such T exists

*)

(*

What is the smallest type T that makes the following assertion true? 
      empty |- (\x:Top. x) ((\z:A.z) , (\z:B.z)) \in T
      
(A->A * B->B)

*)

(*

How many supertypes does the record type {x:A, y:C->C} have? That is, how many 
different types T are there such that {x:A, y:C->C} <:  T? (We consider two types 
to be different if they are written differently, even if each is a subtype of 
the other. For example,  {x:A,y:B} and {y:B,x:A} are different.)

{x:A}
{x:Top}
{y:C->C}
{y:C->Top}
{y:C->C, x:A}
{x:Top,y:C->C} and its permutation
{x:Top,y:C->Top) and its permutation

*)

(*

Is extending the permutation rule to the subtyping rules for products (pairs). 
Is this a good idea?

This is not a good idea. If we do so, then by the definition of subtyping, wherever a value 
of type (T1 * T2) is expected, we can provide a value of type (T2 * T1).

This will lead to stuck computations. 

Example: (Bool * Nat) being substituted for (Nat * Bool)
A context in which we expect a Nat as v.fst would receive a Bool 
because of the substitution, which will lead to failure.

*)

Module STLCSub.

Inductive ty : Type :=
  | Ty_Top : ty
  | Ty_Bool : ty
  | Ty_Base : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Unit : ty
  | Ty_Prod : ty -> ty -> ty
.

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | tm_unit : tm
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := tm_true (in custom stlc at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := tm_false (in custom stlc at level 0).

Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).

Notation "'Base' x" := (Ty_Base x) (in custom stlc at level 0).

Notation "'Top'" := (Ty_Top) (in custom stlc at level 0).

Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc at level 2, X custom stlc, Y custom stlc at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 0).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 0).

Notation "{ x }" := x (in custom stlc at level 1, x constr).

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  | <{unit}> =>
      <{unit}>
  | <{ (t1, t2) }> =>
      <{( [x:=s] t1, [x:=s] t2 )}>
  | <{t0.fst}> =>
      <{ ([x:=s] t0).fst}>
  | <{t0.snd}> =>
      <{ ([x:=s] t0).snd}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  | v_unit :
      value <{unit}>
  | v_prod : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{ (v1, v2) }>
.

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1 t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
  | ST_Pair1 : forall t1 t1' t2,
      t1 --> t1' ->
      <{ (t1, t2) }> --> <{ (t1', t2) }>
  | ST_Pair2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      <{ (v1, t2) }> --> <{ (v1, t2') }>
  | ST_Fst1 : forall t1 t1',
      t1 --> t1' ->
      <{ t1.fst }> --> <{ t1'.fst }>
  | ST_FstPair : forall v1 v2,
      value v1 ->
      value v2 ->
      <{ (v1, v2).fst }> --> <{ v1 }>
  | ST_Snd1 : forall t1 t1',
      t1 --> t1' ->
      <{ t1.snd }> --> <{ t1'.snd }>
  | ST_SndPair : forall v1 v2,
      value v1 ->
      value v2 ->
      <{ (v1, v2).snd }> --> <{ v2 }>
      
      
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      S <: <{Top}>
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      <{S1->S2}> <: <{T1->T2}>
  | S_Prod : forall S1 S2 T1 T2,
      S1 <: T1 ->
      S2 <: T2 ->
      <{ S1 * S2 }>  <: <{ T1 * T2 }>
      
where "T '<:' U" := (subtype T U).

Hint Constructors subtype : core.

Module Examples.

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation z := "z".

Notation A := <{Base "A"}>.
Notation B := <{Base "B"}>.
Notation C := <{Base "C"}>.

Notation String := <{Base "String"}>.
Notation Float := <{Base "Float"}>.
Notation Integer := <{Base "Integer"}>.

Example subtyping_example_0 :
  <{C->Bool}> <: <{C->Top}>.
Proof.
apply S_Arrow.
- apply S_Refl.
- apply S_Top.
Qed.

Definition Person : ty
 := <{String * (Top * Top)}>.
 
Definition Student : ty
 := <{ String * (Float * Top) }>.
 
Definition Employee : ty
 := <{ String * (Integer * Top) }>.

Example sub_student_person :
  Student <: Person.
Proof.
unfold Student.
unfold Person.
apply S_Prod.
- apply S_Refl.
- apply S_Prod. apply S_Top. apply S_Refl.  
Qed.

Example sub_employee_person :
  Employee <: Person.
Proof.
unfold Employee.
unfold Person.
apply S_Prod.
- apply S_Refl.
- apply S_Prod. apply S_Top. apply S_Refl.  
Qed.

Example subtyping_example_1 :
  <{Top->Student}> <: <{(C->C)->Person}>.
Proof with eauto.
apply S_Arrow.
- apply S_Top.
- apply sub_student_person.
Qed.

Example subtyping_example_2 :
  <{Top->Person}> <: <{Person->Top}>.
Proof with eauto.
(* eauto. *)
apply S_Arrow.
- apply S_Top.
- apply S_Top.
Qed.

End Examples.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc at level 0).
                                          
Inductive has_type : context -> tm -> ty -> Prop :=
  (* Same as before: *)
  (* pure STLC *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      (x |-> T2 ; Gamma) |- t1 \in T1 ->
      Gamma |- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (T2 -> T1) ->
      Gamma |- t2 \in T2 ->
      Gamma |- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |- true \in Bool
  | T_False : forall Gamma,
       Gamma |- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T1 ->
       Gamma |- t3 \in T1 ->
       Gamma |- if t1 then t2 else t3 \in T1
  | T_Unit : forall Gamma,
      Gamma |- unit \in Unit
  (* New rule of subsumption: *)
  | T_Sub : forall Gamma t1 T1 T2,
      Gamma |- t1 \in T1 ->
      T1 <: T2 ->
      Gamma |- t1 \in T2
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in T2 ->
      Gamma |- <{ (t1, t2) }> \in <{ T1 * T2 }>
  | T_Fst : forall Gamma t0 T1 T2,
      Gamma |- t0 \in <{ T1 * T2 }> ->
      Gamma |- <{ t0.fst }> \in T1
  | T_Snd : forall Gamma t0 T1 T2,
      Gamma |- t0 \in <{ T1 * T2 }> ->
      Gamma |- <{ t0.snd }> \in T2

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Module Examples2.
Import Examples.

Example typing_example_0 :
  empty |- ((\z:A,z), (\z:B,z)) \in ((A->A) * (B->B)).
Proof.
apply T_Pair.
- apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
- apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
Qed.

Example typing_example_1 :
  empty |- (\x:(Top * (B->B)), x.snd) ((\z:A,z), (\z:B,z))
         \in <{B->B}>.
Proof.
eapply T_App.
- apply T_Abs.
  eapply T_Snd.
  apply T_Var.
  rewrite update_eq.
  reflexivity.
- eapply T_Pair.
  -- eapply T_Sub.
     --- apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
     --- apply S_Top.
  -- apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.  
Qed.

Example typing_example_2 :
  empty |- (\z:(C->C)->(Top * (B->B)), (z (\x:C,x)).snd)
              (\z:C->C, ((\z:A,z), (\z:B,z)))
         \in <{B->B}>.
Proof.
eapply T_App.
- eapply T_Abs.
  eapply T_Snd.
  eapply T_App.
  -- apply T_Var. rewrite update_eq. reflexivity.
  -- apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
- apply T_Abs.
  apply T_Pair.
  -- eapply T_Sub.
     --- apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
     --- apply S_Top.
  -- apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
Qed.
         
End Examples2.

Lemma sub_inversion_Bool : forall U,
     U <: <{Bool}> ->
     U = <{Bool}>.   
Proof with auto.
intros U Hs.
remember <{Bool}> as V.
induction Hs.
- reflexivity.
- pose proof (IHHs2 HeqV) as H1. rewrite HeqV in H1. pose proof (IHHs1 H1) as H2.
  rewrite <- HeqV in H1. rewrite <- H2 in H1. assumption.
- inversion HeqV.
- inversion HeqV.
- inversion HeqV.
Qed.

Lemma sub_inversion_arrow : forall U V1 V2,
     U <: <{V1->V2}> ->
     exists U1 U2,
     U = <{U1->U2}> /\ V1 <: U1 /\ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember <{V1->V2}> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs.
  - intros. exists V1, V2.
    split. assumption. split. apply S_Refl. apply S_Refl.
  - intros. pose proof (IHHs2 V1 V2 HeqV) as H1.
    destruct H1. destruct H. destruct H. destruct H0.
    pose proof (IHHs1 x x0 H) as H2.
    destruct H2. destruct H2. destruct H2. destruct H3.
    exists x1, x2.
    split. assumption. split.
    apply (S_Trans V1 x x1 H0 H3).
    apply (S_Trans x2 x0 V2 H4 H1).
  - intros. inversion HeqV.
  - intros. inversion HeqV.     
    exists S1, S2.
    split. reflexivity.
    split. rewrite <- H0. assumption. rewrite <- H1. assumption.
  - intros. inversion HeqV.  
Qed.    
    
Lemma sub_inversion_Unit : forall U,
     U <: <{Unit}> ->
     U = <{Unit}>.
Proof with auto.
  intros U Hs.
  remember <{Unit}> as V.
  induction Hs.
  - reflexivity.
  - pose proof (IHHs2 HeqV) as H1. rewrite HeqV in H1. pose proof (IHHs1 H1) as H2.
    rewrite <- HeqV in H1. rewrite <- H2 in H1. assumption.
  - inversion HeqV.
  - inversion HeqV.
  - inversion HeqV.
Qed.

Lemma sub_inversion_Base : forall U s,
     U <: <{Base s}> ->
     U = <{Base s}>.
Proof with auto.
  intros U s Hs.
  remember <{Base s}> as V.
  induction Hs.
  - reflexivity.
  - pose proof (IHHs2 HeqV) as H1. rewrite HeqV in H1. pose proof (IHHs1 H1) as H2.
    rewrite <- HeqV in H1. rewrite <- H2 in H1. assumption.
  - inversion HeqV.
  - inversion HeqV.
  - inversion HeqV.
Qed.

Lemma sub_inversion_Top : forall U,
     <{ Top }> <: U ->
     U = <{ Top }>.
Proof with auto.
  intros U Hs.
  remember <{Top}> as V.
  induction Hs.
  - reflexivity.
  - pose proof (IHHs1 HeqV) as H1. rewrite HeqV in H1. pose proof (IHHs2 H1) as H2.
    rewrite <- HeqV in H1. rewrite <- H2 in H1. assumption.
  - inversion HeqV. reflexivity.
  - inversion HeqV.
  - inversion HeqV.
Qed.

Lemma sub_inversion_pair' : forall U V1 V2,
  U <: <{V1 * V2}> ->
  exists U1 U2, U = <{U1 * U2}> /\ U1 <: V1 /\ U2 <: V2.
Proof.
  intros U V1 V2 Hs.
  remember <{V1 * V2}> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs.
  - intros. exists V1, V2. split. assumption. split. apply S_Refl. apply S_Refl.
  - intros. pose proof (IHHs2 V1 V2 HeqV) as H1.
    destruct H1. destruct H. destruct H. destruct H0.
    pose proof (IHHs1 x x0 H) as H2.
    destruct H2. destruct H2. destruct H2. destruct H3.
    exists x1, x2.
    split. 
    -- assumption. 
    -- split. 
       --- eapply S_Trans. apply H3. assumption.
       --- eapply S_Trans. apply H4. assumption.
  - intros. inversion HeqV.
  - intros. inversion HeqV.
  - intros. exists S1, S2.
    split.
    -- reflexivity.
    -- inversion HeqV. subst. split. assumption. assumption.
Qed.       

Lemma sub_inversion_pair : forall U1 U2 V,
  <{U1 * U2}> <: V ->
  (exists V1 V2, V = <{V1 * V2}>) \/ V = <{Top}>.
Proof.
  intros U1 U2 V Hs.
  remember <{U1 * U2}> as U.
  generalize dependent U2. generalize dependent U1.
  induction Hs.
  - intros. left. exists U1, U2. assumption.
  - intros.
    pose proof (IHHs1 U1 U2 HeqU) as H1.
    destruct H1.
    -- destruct H. destruct H.
       pose proof (IHHs2 x x0 H) as H1. assumption.
    -- rewrite H in Hs2. apply sub_inversion_Top in Hs2. right. assumption.
  - intros. right. reflexivity.
  - intros. inversion HeqU.
  - intros. left. exists T1, T2. reflexivity.
Qed.

Lemma Bool_super_isTop : forall U,
     <{Bool}> <: U ->
     U = <{Bool}> \/ U = <{Top}>.   
Proof with auto.
intros U Hs.
remember <{Bool}> as V.
induction Hs.
- left. reflexivity.
- pose proof (IHHs1 HeqV) as H1.
  destruct H1.
  -- subst. apply IHHs2. reflexivity.
  -- subst. apply sub_inversion_Top in Hs2. right. assumption.
- right. reflexivity.
- inversion HeqV.
- inversion HeqV.
Qed.

Lemma TyBase_super_isTop : forall s U,
     (Ty_Base s) <: U ->
     U = (Ty_Base s) \/ U = <{Top}>.   
Proof with auto.
intros s U Hs.
remember (Ty_Base s) as V.
induction Hs.
- left. reflexivity.
- pose proof (IHHs1 HeqV) as H1.
  destruct H1.
  -- subst. apply IHHs2. reflexivity.
  -- subst. apply sub_inversion_Top in Hs2. right. assumption.
- right. reflexivity.
- inversion HeqV.
- inversion HeqV.
Qed.

Lemma Unit_super_isTop : forall U,
     <{Unit}> <: U ->
     U = <{Unit}> \/ U = <{Top}>.   
Proof with auto.
intros U Hs.
remember <{Unit}> as V.
induction Hs.
- left. reflexivity.
- pose proof (IHHs1 HeqV) as H1.
  destruct H1.
  -- subst. apply IHHs2. reflexivity.
  -- subst. apply sub_inversion_Top in Hs2. right. assumption.
- right. reflexivity.
- inversion HeqV.
- inversion HeqV.
Qed.

Lemma true_super_is_bool_or_top : forall Gamma U,
  Gamma |- true \in U ->
  U = <{Bool}> \/ U = <{Top}>.
Proof.
intros.
remember <{true}> as t1.
induction H.
- inversion Heqt1.
- inversion Heqt1.
- inversion Heqt1.
- left. reflexivity.
- left. reflexivity.
- inversion Heqt1.
- inversion Heqt1.
- pose proof (IHhas_type Heqt1) as H1.
  destruct H1.
  -- rewrite H1 in H0.
     apply Bool_super_isTop in H0. assumption.
  -- rewrite H1 in H0. apply sub_inversion_Top in H0.
     right. assumption.
- inversion Heqt1.
- inversion Heqt1.
- inversion Heqt1.
Qed.  

Lemma false_super_is_bool_or_top : forall Gamma U,
  Gamma |- false \in U ->
  U = <{Bool}> \/ U = <{Top}>.
Proof.
intros.
remember <{false}> as t1.
induction H.
- inversion Heqt1.
- inversion Heqt1.
- inversion Heqt1.
- left. reflexivity.
- left. reflexivity.
- inversion Heqt1.
- inversion Heqt1.
- pose proof (IHhas_type Heqt1) as H1.
  destruct H1.
  -- rewrite H1 in H0.
     apply Bool_super_isTop in H0. assumption.
  -- rewrite H1 in H0. apply sub_inversion_Top in H0.
     right. assumption.
- inversion Heqt1.
- inversion Heqt1.
- inversion Heqt1.
Qed.  

Lemma unit_super_is_unit_or_top : forall Gamma U,
  Gamma |- unit \in U ->
  U = <{Unit}> \/ U = <{Top}>.
Proof.
intros.
remember <{unit}> as t1.
induction H.
- inversion Heqt1.
- inversion Heqt1.
- inversion Heqt1.
- inversion Heqt1.
- inversion Heqt1.
- inversion Heqt1.
- left. reflexivity.
- pose proof (IHhas_type Heqt1) as H1.
  destruct H1.
  -- rewrite H1 in H0.
     apply Unit_super_isTop in H0. assumption.
  -- rewrite H1 in H0. apply sub_inversion_Top in H0.
     right. assumption.
- inversion Heqt1.
- inversion Heqt1.
- inversion Heqt1.
Qed.  

Lemma pair_super_is_prod_or_top : forall Gamma t1 t2 U,
  Gamma |- <{ (t1, t2) }> \in U ->
  (exists T1 T2, U = <{ T1 * T2 }>) \/ U = <{Top}>.
Proof with eauto.
intros.
remember <{ (t1, t2) }> as tpair.
induction H.
- inversion Heqtpair.
- inversion Heqtpair.
- inversion Heqtpair.
- inversion Heqtpair.
- inversion Heqtpair.
- inversion Heqtpair.
- inversion Heqtpair.
- pose proof (IHhas_type Heqtpair) as H1.
  destruct H1. 
  -- destruct H1. destruct H1.
     rewrite H1 in H0.
     apply sub_inversion_pair in H0.
     assumption.
  -- rewrite H1 in H0. apply sub_inversion_Top in H0.
     right. assumption.
- left. exists T1, T2. reflexivity.
- inversion Heqtpair.
- inversion Heqtpair.
Qed.

(*
Lemma canonical_forms_of_pairs_pre : forall Gamma s T1 T2,
  Gamma |- s \in <{ T1 * T2 }> ->
  exists t1 t2, s = <{ (t1, t2) }>.
Proof with eauto.
*)

(* copy of typing_inversion_abs from below *)
Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |- \x:S1,t2 \in T ->
     exists S2,
       <{S1->S2}> <: T
       /\ (x |-> S1 ; Gamma) |- t2 \in S2.
Proof.
intros.
remember <{\x:S1,t2}> as tabs.
induction H.
- inversion Heqtabs.
- inversion Heqtabs. subst.
  exists T1. split. apply S_Refl. assumption.
- inversion Heqtabs.
- inversion Heqtabs.
- inversion Heqtabs.
- inversion Heqtabs.
- inversion Heqtabs.
- pose proof (IHhas_type Heqtabs) as H1.
  destruct H1.
  destruct H1.
  exists x0.
  split.
  -- eapply S_Trans. apply H1. assumption.
  -- assumption.
- inversion Heqtabs.
- inversion Heqtabs.
- inversion Heqtabs.
Qed.

    
Lemma canonical_forms_of_pair_types : forall Gamma s T1 T2,
  Gamma |- s \in <{T1 * T2}> ->
  value s ->
  exists t1 t2, s = <{(t1, t2)}> /\ value t1 /\ value t2.
Proof.
intros.
inversion H0; subst.
- remember <{T1 * T2}> as T.
  apply typing_inversion_abs in H.
  destruct H. destruct H.
  rewrite HeqT in H.
  apply sub_inversion_pair' in H.
  destruct H. destruct H. destruct H. inversion H.
- apply true_super_is_bool_or_top in H.
  destruct H. inversion H. inversion H.
- apply false_super_is_bool_or_top in H.
  destruct H. inversion H. inversion H.
- apply unit_super_is_unit_or_top in H.
  destruct H. inversion H. inversion H.
- exists v1, v2. split. reflexivity. split. assumption. assumption.
Qed.

Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |- s \in (T1->T2) ->
  value s ->
  exists x S1 s2,
     s = <{\x:S1,s2}>.
Proof with eauto.
intros.
inversion H0; clear H0; subst.
- exists x, T0, t1. reflexivity.
- apply true_super_is_bool_or_top in H.
  destruct H. inversion H. inversion H.
- apply false_super_is_bool_or_top in H.
  destruct H. inversion H. inversion H.
- apply unit_super_is_unit_or_top in H.
  destruct H. inversion H. inversion H.
- apply pair_super_is_prod_or_top in H.
  destruct H. destruct H. destruct H. inversion H. inversion H.
Qed.
     
Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |- s \in Bool ->
  value s ->
  s = tm_true \/ s = tm_false.
Proof with eauto.
  intros Gamma s Hty Hv.
  remember <{Bool}> as T.
  induction Hty; try solve_by_invert...
  - (* T_Sub *)
    subst. apply sub_inversion_Bool in H. subst...
Qed.

(* my version *)
Lemma canonical_forms_of_Bool' : forall Gamma s,
  Gamma |- s \in Bool ->
  value s ->
  s = tm_true \/ s = tm_false.
Proof.
intros.
remember <{Bool}> as T.
induction H; subst.
- inversion H0.
- inversion HeqT.
- inversion H0.
- eauto.
- eauto.
- inversion H0.
- inversion HeqT.
- apply sub_inversion_Bool in H1. apply IHhas_type. assumption. assumption.
- inversion HeqT.
- inversion H0.
- inversion H0.
Qed.

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof.
intros.
remember empty as Gamma.
induction H.
- rewrite HeqGamma in H. inversion H.
- left. apply v_abs.
- pose proof (IHhas_type1 HeqGamma) as H1.
  pose proof (IHhas_type2 HeqGamma) as H2.
  destruct H1.
  -- destruct H2.
     --- pose proof (canonical_forms_of_arrow_types Gamma t1 T2 T1 H H1) as H3.
         destruct H3. destruct H3. destruct H3.
         right. exists <{[x:=t2]x1}>. rewrite H3. apply ST_AppAbs. assumption.
     --- right. destruct H2. exists <{t1 x}>. apply ST_App2. assumption. assumption.
  -- destruct H2.
     --- right. destruct H1. exists <{x t2}>. apply ST_App1. assumption.
     --- right. destruct H1. exists <{x t2}>. apply ST_App1. assumption. 
- left. apply v_true.
- left. apply v_false.
- right. pose proof (IHhas_type1 HeqGamma) as H2.
  destruct H2.
  -- pose proof (canonical_forms_of_Bool Gamma t1 H H2) as H3.
     destruct H3.
     --- rewrite H3. exists t2. apply ST_IfTrue.
     --- rewrite H3. exists t3. apply ST_IfFalse.
  -- destruct H2. exists <{if x then t2 else t3 }>. apply ST_If. assumption.
- left. apply v_unit.
- pose proof (IHhas_type HeqGamma) as H1. assumption.
- pose proof (IHhas_type1 HeqGamma) as H1.
  destruct H1.
  -- pose proof (IHhas_type2 HeqGamma) as H2.
     destruct H2.
     --- left. apply v_prod. assumption. assumption.
     --- right. destruct H2. exists <{ (t1, x) }>. apply ST_Pair2.
         assumption. assumption.
  -- right. destruct H1. exists <{ (x, t2) }>. apply ST_Pair1. assumption.
- pose proof (IHhas_type HeqGamma) as H1.
  destruct H1.
  -- right.
     pose proof (canonical_forms_of_pair_types Gamma t0 T1 T2 H H0) as H1.
     destruct H1. destruct H1. destruct H1. destruct H2.
     exists x. rewrite H1. apply ST_FstPair. assumption. assumption. 
  -- destruct H0.    
     right. exists (tm_fst x). apply ST_Fst1. assumption.
- pose proof (IHhas_type HeqGamma) as H1.
  destruct H1.
  -- right.
     pose proof (canonical_forms_of_pair_types Gamma t0 T1 T2 H H0) as H1.
     destruct H1. destruct H1. destruct H1. destruct H2.
     exists x0. rewrite H1. apply ST_SndPair. assumption. assumption. 
  -- destruct H0.    
     right. exists (tm_snd x). apply ST_Snd1. assumption.
Qed.

Lemma typing_inversion_var : forall Gamma (x:string) T,
  Gamma |- x \in T ->
  exists S,
    Gamma x = Some S /\ S <: T.
Proof.
intros.
remember (tm_var x) as tx.
induction H.
- inversion Heqtx.
  rewrite <- H1.
  exists T1. split.
  -- assumption.
  --  apply S_Refl.
- inversion Heqtx.
- inversion Heqtx.
- inversion Heqtx.
- inversion Heqtx.
- inversion Heqtx.
- inversion Heqtx.
- inversion Heqtx.
  destruct (IHhas_type H1).
  destruct H2.
  exists x0.
  split.
  -- assumption.
  -- eapply S_Trans.
     --- apply H3.
     --- assumption.
- inversion Heqtx.
- inversion Heqtx.
- inversion Heqtx.
Qed.

Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  Gamma |- t1 t2 \in T2 ->
  exists T1,
    Gamma |- t1 \in (T1->T2) /\
    Gamma |- t2 \in T1.
Proof with eauto.
intros.
remember<{ t1 t2 }> as tapp.
induction H; inversion Heqtapp; try solve_by_invert...
- subst. exists T2. split. assumption. assumption.
- destruct (IHhas_type Heqtapp).
  destruct H2. exists x. split.
  -- assert (H4: (Ty_Arrow x T1) <: (Ty_Arrow x T2)).
     apply S_Arrow.
     --- apply S_Refl.
     --- assumption.
     --- eapply T_Sub.
         ---- apply H2.
         ---- assumption.
  -- assumption.
Qed.

Lemma typing_inversion_unit : forall Gamma T,
  Gamma |- unit \in T ->
    <{Unit}> <: T.
Proof.
intros.
remember <{unit}> as tunit.
induction H; inversion Heqtunit; try solve_by_invert...
- apply S_Refl.
- pose proof (IHhas_type H1) as H2.
  eapply S_Trans.
  -- apply H2.
  -- assumption.
Qed.

Lemma typing_inversion_pair' : forall Gamma t1 t2 T,
  Gamma |- <{(t1, t2)}> \in T ->
  exists T1 T2, 
    Gamma |- t1 \in T1 /\
    Gamma |- t2 \in T2 /\
    <{T1 * T2 }> <: T.
Proof with eauto.
intros.
remember <{(t1, t2)}> as tpair.
induction H; inversion Heqtpair; try solve_by_invert...
- pose proof (IHhas_type Heqtpair) as H2.
  destruct H2. destruct H2. destruct H2. destruct H3.
  exists x, x0. split. assumption. split. assumption.
  eapply S_Trans.  apply H4. assumption.
- exists T1, T2. split.
  -- rewrite H2 in H. assumption.
  -- split.
     --- rewrite H3 in H0. assumption.
     --- apply S_Refl.
Qed.

Lemma pair_subtype : forall S1 S2 T1 T2,
  <{S1 * S2}> <: <{T1 * T2}> ->
  S1 <: T1 /\ S2 <: T2.
Proof.
intros.
remember <{S1 * S2}> as U.
apply sub_inversion_pair' in H.
destruct H. destruct H. destruct H. destruct H0.
rewrite HeqU in H.
inversion H. subst.
split. assumption. assumption.
Qed.    
    
Lemma typing_inversion_pair : forall Gamma t1 t2 T1 T2,
  Gamma |- <{(t1, t2)}> \in <{T1 * T2}> ->
  Gamma |- t1 \in T1 /\ Gamma |- t2 \in T2.
Proof with eauto.
intros. 
remember <{T1 * T2 }> as T.
apply typing_inversion_pair' in H.
destruct H. destruct H. destruct H. destruct H0.
rewrite HeqT in H1.
apply pair_subtype in H1. destruct H1.
split.
- eapply T_Sub. apply H. assumption.
- eapply T_Sub. apply H0. assumption.
Qed.
     
Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |- \x:S1,s2 \in (T1->T2) ->
     T1 <: S1
  /\ (x |-> S1 ; empty) |- s2 \in T2.
Proof with eauto.
intros.
apply typing_inversion_abs in H.
destruct H. destruct H.  
apply sub_inversion_arrow in H.
destruct H. destruct H. destruct H. destruct H1.
inversion H. subst.
split.
- assumption.
- eapply T_Sub.
  -- apply H0.
  -- assumption.
Qed.

(* same as in StlcProp *)
Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma |- t \in T ->
     Gamma' |- t \in T.
Proof.  
intros.
generalize dependent Gamma'.
induction H0; eauto. (* can also simply do eauto using includedin_update *)
intros.
apply T_Abs.
pose proof (IHhas_type (x |-> T2; Gamma')) as H1.
apply H1.
apply includedin_update.
assumption.
Qed.  

(* same as in StlcProp *)  
Lemma weakening_empty : forall Gamma t T,
     empty |- t \in T ->
     Gamma |- t \in T.
Proof.  
intros.
assert (H1: includedin empty Gamma).
{ 
  unfold includedin.
  intros.
  exfalso. inversion H0.
}
eapply weakening.
- apply H1.
- assumption.
Qed.  

Lemma substitution_preserves_typing : forall Gamma x U t v T,
   (x |-> U ; Gamma) |- t \in T ->
   empty |- v \in U ->
   Gamma |- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
  - destruct (eqb x x0) eqn: Heq.
    -- rewrite eqb_eq in Heq.
       rewrite <- Heq in H.
       rewrite G in H.
       rewrite update_eq in H.
       inversion H.
       rewrite <- H1.
       apply weakening_empty. assumption.
    -- rewrite eqb_neq in Heq.
       rewrite G in H.
       rewrite update_neq in H.
       --- apply T_Var. assumption.
       --- assumption.
  - destruct (eqb x x0) eqn: Heq.
    -- rewrite eqb_eq in Heq.
       apply T_Abs.
       rewrite G in Ht.
       rewrite Heq in Ht.
       rewrite update_shadow in Ht.
       assumption.
    -- rewrite eqb_neq in Heq.
       apply T_Abs.
       pose proof (IHHt (x0 |-> T2; Gamma')) as H1.
       apply H1.
       rewrite G.
       apply update_permute.
       assumption.
Qed.

Theorem preservation : forall t t' T,
     empty |- t \in T ->
     t --> t' ->
     empty |- t' \in T.
Proof.
intros.
remember empty as Gamma.
generalize dependent t'.
induction H.
- intros. inversion H0.
- intros. inversion H0.
- intros.
  inversion H1; subst.
  -- apply abs_arrow in H.
     destruct H.
     apply substitution_preserves_typing with (U := T0).
     --- assumption.
     --- eapply T_Sub. apply H0. assumption.
  -- eapply T_App.
     --- apply IHhas_type1. reflexivity. assumption.
     --- assumption.
  -- assert (H7: empty |- t2' \in T2).
     {
       apply IHhas_type2. reflexivity. assumption.
     }
     eapply T_App.
     --- apply H.
     --- assumption.
- intros. inversion H0.
- intros. inversion H0.
- intros. inversion H2; subst.
  -- assumption.
  -- assumption.
  -- apply T_If.
     --- apply IHhas_type1. reflexivity. assumption.
     --- assumption.
     --- assumption.
- intros. inversion H0.
- intros.
  pose proof ((IHhas_type HeqGamma t') H1) as H2.
  eapply T_Sub. apply H2. assumption.
- intros. inversion H1; subst.
  -- eauto.
  -- eauto.
- intros. inversion H0; subst.
  -- eauto.
  -- apply typing_inversion_pair in H. destruct H. assumption.
- intros. inversion H0; subst.
  -- eauto.
  -- apply typing_inversion_pair in H. destruct H. assumption.
Qed.

(*

1)

        Gamma ⊢ t ∈ S1->S2	
S1 <: T1     T1 <: S1      S2 <: T2	(T_Funny1)  
-----------------------------------
        Gamma ⊢ t ∈ T1->T2	

Both progress and preservation stay true, as S1 <: T1 and T1 <: S1
mean that S1 = T1, in which case S1->S2 <: T1->T2, and the subsumption
rule holds

2)

--------------------  	(ST_Funny21)  
unit --> (\x:Top. x)	

Both progress and preservation become false:
1. progress - unit being a value, should not step, but 
   would do so under this rule
2. preservation: unit's type is Unit, while the type of (\x:Top. x) 
   is Top->Top, so preservation fails
   
   
3)

----------------  	(S_Funny3)  
Unit <: Top->Top	
   
Since Unit <: Top->Top, Gamma |- unit \in Top->Top (by subsumption rule).
This means that <{unit true }> is well-typed (since true <: Top) and not a
value, and should progress, but can't. Thus, progress fails.

For preservation to be evaluated, the expression must progress (to see whether
the type is preserved by the step). Since progress fails here, not sure
whether we consider preservation too to fail.

4)

----------------  	(S_Funny4)  
Top->Top <: Unit	

No impact on progress or preservation. If Top->Top <: Unit, a term of 
type Top->Top can be substituted for unit. This does not matter because unit
is a value, as is a term of type Top->Top (i.e., it's an abstraction), 
and nothing can be done with unit.

5)

---------------------  	(ST_Funny5)  
(unit t) --> (t unit)	

Progress would fail, for example, for t = true (<{true unit}> is not a 
value and cannot step). Preservation too would fail, for example for 
t = <{\x:Top,Top}> - the type changes from 'undefined' to Top as we step
using this rule.

6)

---------------------  	(ST_Funny5)  
(unit t) --> (t unit)
	
-----------------------  	(T_Funny6)  
empty ⊢ unit ∈ Top->Top	

Both progress and preservation fail, for example for t = true.
Progress: we get stuck at <{true unit}>, which is not a value.
Preservation: the type changes from Top to 'undefined' as we step 
using this rule.

7)

S1 <: T1     S2 <: T2	  
---------------------   (S_Arrow')
   S1->S2 <: T1->T2	

Counterexample:

(S1 = Bool) <: (T1 = Top)
(S2 = Unit) <: (T2 = Unit)

Therefore by the new rule, Bool->Unit <: Top->Unit 

So we can pass a term of type Bool->Unit
where a term of type Top->Unit is expected.
 
Consider the term <{ (\f:Top->Unit, f unit) (\x:Top, unit) }>

The argument's type is Top->Unit

Consider the term <{ \x:Bool, if x then unit else unit end }>

The type of this term is Bool->Unit

Thus, this term can replace the argument. The original term then becomes

<{ (\f:Top->Unit, f unit) (\x:Bool, if x then unit else unit end) }>

which is well-typed and not a value, but cannot step. Thus, progress fails.

For preservation to be evaluated, the expression must progress (to see whether
the type is preserved by the step). Since progress fails here, not sure
whether we consider preservation too to fail.

*)

Module FormalThoughtExercises.
Import Examples.
Notation p := "p".
Notation a := "a".

Definition TF P := P \/ ~P.

Theorem formal_subtype_instances_tf_1a:
  TF (forall S T U V, S <: T -> U <: V ->
         <{T->S}> <: <{T->S}>).
Proof.
unfold TF.
left.
intros.
apply S_Refl.
Qed.

Theorem formal_subtype_instances_tf_1b:
  TF (forall S T U V, S <: T -> U <: V ->
         <{Top->U}> <: <{S->Top}>).
Proof.
unfold TF.
left.
intros.
apply S_Arrow. apply S_Top. apply S_Top.
Qed.

Theorem formal_subtype_instances_tf_1c:
  TF (forall S T U V, S <: T -> U <: V ->
         <{(C->C)->(A*B)}> <: <{(C->C)->(Top*B)}>).
Proof.
unfold TF.
left.
intros.
apply S_Arrow.
- apply S_Refl.
- apply S_Prod.
  -- apply S_Top.
  -- apply S_Refl.
Qed.

Theorem formal_subtype_instances_tf_1d:
  TF (forall S T U V, S <: T -> U <: V ->
         <{T->(T->U)}> <: <{S->(S->V)}>).
Proof.
unfold TF.
left.
intros.
apply S_Arrow.
- assumption.
- apply S_Arrow.
  -- assumption.
  -- assumption.
Qed.

Theorem formal_subtype_instances_tf_1e:
  TF (forall S T U V, S <: T -> U <: V ->
         <{(T->T)->U}> <: <{(S->S)->V}>).
Proof with eauto.
unfold TF.
right.
unfold not.
intros.
pose proof (H Ty_Bool Ty_Top Ty_Bool Ty_Top) as H1.
assert (H2: Ty_Bool <: Ty_Top) by (apply S_Top).
pose proof (H1 H2 H2) as H4.
apply sub_inversion_arrow with (U := <{ (Top -> Top) -> Bool }>) in H4.
destruct H4. destruct H0. destruct H0. destruct H3.
inversion H0.
rewrite <- H6 in H3.
apply sub_inversion_arrow with (U := <{ Bool -> Bool }>) in H3.
destruct H3. destruct H3. destruct H3. destruct H5.
inversion H3.
rewrite <- H10 in H5.
apply sub_inversion_Top with (U := <{Bool}>) in H5.
inversion H5.
Qed.

Theorem formal_subtype_instances_tf_1f:
  TF (forall S T U V, S <: T -> U <: V ->
         <{((T->S)->T)->U}> <: <{((S->T)->S)->V}>).
Proof.
unfold TF.
left.
intros.
apply S_Arrow.
- apply S_Arrow.
  -- apply S_Arrow. assumption. assumption.
  -- assumption.
- assumption.
Qed.

Theorem formal_subtype_instances_tf_1g:
  TF (forall S T U V, S <: T -> U <: V ->
         <{S*V}> <: <{T*U}>).
Proof.
unfold TF.
right.
unfold not.
intros.
pose proof (H Ty_Bool Ty_Top Ty_Bool Ty_Top) as H1.
assert (H2: Ty_Bool <: Ty_Top) by (apply S_Top).
pose proof (H1 H2 H2) as H4.
apply sub_inversion_pair' with (U := <{ Bool * Top }>) in H4.
destruct H4. destruct H0. destruct H0. destruct H3.
inversion H0.
apply sub_inversion_Bool in H4.
rewrite H4 in H7.
inversion H7.
Qed.

Theorem formal_subtype_instances_tf_2a:
  TF (forall S T,
         S <: T ->
         <{S->S}> <: <{T->T}>).
Proof.
unfold TF.
right.
unfold not.
intros.
pose proof (H Ty_Bool Ty_Top) as H1.
assert (H2: Ty_Bool <: Ty_Top) by (apply S_Top).
pose proof (H1 H2) as H3.
apply sub_inversion_arrow with (U := <{ Bool -> Bool }>) in H3.
destruct H3. destruct H0. destruct H0. destruct H3.
inversion H0.
rewrite <- H6 in H3.
apply sub_inversion_Top in H3. inversion H3.
Qed.

Theorem formal_subtype_instances_tf_2b:
  TF (forall S A,
         S <: <{A->A}> ->
         exists T,
           S = <{T->T}> /\ T <: A).
Proof.
unfold TF.
right.
unfold not.
intros.
pose proof (H (Ty_Arrow Ty_Top Ty_Bool) Ty_Top) as H1.
assert (H2: <{ Top -> Bool }> <: <{ Top -> Top }>).
{
  apply S_Arrow. apply S_Refl. apply S_Top.
}
pose proof (H1 H2) as H3.
destruct H3.
destruct H0.
inversion H0.
inversion H6.
Qed.

Theorem formal_subtype_instances_tf_2d:
  TF (exists S,
         S <: <{S->S}>).
Proof.
unfold TF.
right.
unfold not.
intros.
destruct H.
induction x.
- apply sub_inversion_Top in H. inversion H.
- apply Bool_super_isTop in H. destruct H. inversion H. inversion H.
- apply sub_inversion_arrow with (U := Ty_Base s) in H.
  destruct H. destruct H. destruct H. destruct H0.
  inversion H.
- admit.
- apply Unit_super_isTop in H. destruct H. inversion H. inversion H.
- apply sub_inversion_arrow with (U := <{ x1 * x2 }>) in H.
  destruct H. destruct H. destruct H. inversion H.
Admitted.

Theorem formal_subtype_instances_tf_2e:
  TF (exists S,
         <{S->S}> <: S).
Proof.
unfold TF.
left.
exists <{Top}>.
apply S_Top.
Qed.

Theorem formal_subtype_concepts_tfa:
  TF (exists T, forall S, S <: T).
Proof.
unfold TF. left. exists <{Top}>.
apply S_Top.
Qed.

Theorem formal_subtype_concepts_tfb:
  TF (exists T, forall S, T <: S).
Proof.
unfold TF.
right.
unfold not.
intros.
destruct H.
induction x.
- pose proof (H <{Bool}>). apply sub_inversion_Top in H0. inversion H0.
- pose proof (H <{Unit}>). apply sub_inversion_Unit in H0. inversion H0.
- pose proof (H <{Unit}>). apply sub_inversion_Unit in H0. inversion H0.
- pose proof (H <{Unit}>). apply sub_inversion_Unit in H0. inversion H0.
- pose proof (H <{Bool}>). apply sub_inversion_Bool in H0. inversion H0.
- pose proof (H <{Unit}>). apply sub_inversion_Unit in H0. inversion H0.
Qed.

Theorem formal_subtype_concepts_tfc:
  TF (exists T1 T2, forall S1 S2, <{S1*S2}> <: <{T1*T2}>).
Proof.
unfold TF.
left.
exists <{Top}>, <{Top}>.
intros.
apply S_Prod. apply S_Top. apply S_Top.
Qed.

Theorem formal_subtype_concepts_tfd:
  TF (exists T1 T2, forall S1 S2, <{T1*T2}> <: <{S1*S2}>).
Proof.
unfold TF.
right.
unfold not.
intros.
destruct H. destruct H.
pose proof (H <{Unit}> <{Unit}>) as H1.
apply sub_inversion_pair' with (U := <{ x * x0 }>) in H1.
destruct H1. destruct H0. destruct H0. destruct H1.
apply sub_inversion_Unit in H1.
apply sub_inversion_Unit in H2.
rewrite H1 in H0. rewrite H2 in H0.
rewrite H0 in H.
pose proof (H <{Bool}> <{Bool}>) as H3.
apply sub_inversion_pair' with (U := <{Unit * Unit}>) in H3.
destruct H3. destruct H3. destruct H3. destruct H4.
inversion H3. rewrite <- H7 in H4.
apply sub_inversion_Bool in H4. inversion H4.
Qed.

Theorem formal_subtype_concepts_tfe:
  TF (exists T1 T2, forall S1 S2, <{S1->S2}> <: <{T1->T2}>).
Proof.
unfold TF.
right.
unfold not.
intros.
destruct H. destruct H.
destruct x. destruct x0.
- pose proof (H <{Bool}> <{Bool}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  apply sub_inversion_Top in H1. inversion H0. rewrite H1 in H4. inversion H4.
- pose proof (H <{Bool}> <{Bool}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  apply sub_inversion_Top in H1. inversion H0. rewrite H1 in H4. inversion H4.
- pose proof (H (Ty_Base s) (Ty_Base s)) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  apply sub_inversion_Top in H1. inversion H0. rewrite H1 in H4. inversion H4.
- pose proof (H (Ty_Arrow x0_1 x0_2) (Ty_Arrow x0_1 x0_2)) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  apply sub_inversion_Top in H1. inversion H0. rewrite H1 in H4. inversion H4.
- pose proof (H Ty_Unit Ty_Unit) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  apply sub_inversion_Top in H1. inversion H0. rewrite H1 in H4. inversion H4.
- pose proof (H (Ty_Prod x0_1 x0_2) (Ty_Prod x0_1 x0_2)) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  apply sub_inversion_Top in H1. inversion H0. rewrite H1 in H4. inversion H4.
- pose proof (H <{Unit}> <{Top}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  inversion H0. rewrite <- H4 in H1. apply sub_inversion_Unit in H1. inversion H1.
- pose proof (H <{Unit}> <{Top}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  inversion H0. rewrite <- H4 in H1. apply sub_inversion_Unit in H1. inversion H1.
- pose proof (H <{Unit}> <{Top}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  inversion H0. rewrite <- H4 in H1. apply sub_inversion_Unit in H1. inversion H1.
- pose proof (H <{Bool}> <{Top}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  inversion H0. rewrite <- H4 in H1. apply sub_inversion_Bool in H1. inversion H1.
- pose proof (H <{Bool}> <{Top}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  inversion H0. rewrite <- H4 in H1. apply sub_inversion_Bool in H1. inversion H1.
Qed. 

Theorem formal_subtype_concepts_tff:
  TF (exists T1 T2, forall S1 S2, <{T1->T2}> <: <{S1->S2}>).
Proof.
unfold TF.
right.
unfold not.
intros.
destruct H. destruct H.
destruct x. destruct x0.
- pose proof (H <{Bool}> <{Bool}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  apply sub_inversion_Bool in H2. inversion H0. rewrite <- H5 in H2. inversion H2.
- pose proof (H <{Bool}> <{Unit}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  apply sub_inversion_Unit in H2. inversion H0. rewrite <- H5 in H2. inversion H2.
- pose proof (H <{Bool}> <{Unit}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  apply sub_inversion_Unit in H2. inversion H0. rewrite <- H5 in H2. inversion H2.
- pose proof (H <{Bool}> <{Unit}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  apply sub_inversion_Unit in H2. inversion H0. rewrite <- H5 in H2. inversion H2.
- pose proof (H <{Bool}> <{Bool}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  apply sub_inversion_Bool in H2. inversion H0. rewrite <- H5 in H2. inversion H2.
- pose proof (H <{Bool}> <{Bool}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  apply sub_inversion_Bool in H2. inversion H0. rewrite <- H5 in H2. inversion H2.
- pose proof (H <{Unit}> <{Top}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  inversion H0. rewrite <- H4 in H1. apply sub_inversion_Bool in H1. inversion H1.
- pose proof (H <{Unit}> <{Top}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  inversion H0. rewrite <- H4 in H1. apply sub_inversion_Base in H1. inversion H1.
- pose proof (H <{Unit}> <{Top}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.  
  inversion H0. subst. apply sub_inversion_arrow with (U := <{Unit}>) in H1.
  destruct H1. destruct H1. destruct H1. inversion H1.
- pose proof (H <{Bool}> <{Bool}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  inversion H0. rewrite <- H4 in H1. apply sub_inversion_Unit in H1. inversion H1.
- pose proof (H <{Bool}> <{Bool}>) as H1.
  apply sub_inversion_arrow in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  inversion H0. apply sub_inversion_Bool in H2. rewrite <- H4 in H1.
  apply sub_inversion_pair' in H1. destruct H1. destruct H1. destruct H1. inversion H1.
Qed.

Fixpoint top_fn i : ty :=
  match i with 
    | 0 => Ty_Top
    | S n => Ty_Arrow Ty_Top (top_fn n)
  end.

Compute (top_fn 2).

(*
There is an infinite descending chain of distinct types in the subtype 
relation---that is, an infinite sequence of types  S0, S1, etc., such that 
all the Si's are different and each S(i+1) is a subtype of Si.
*)

Theorem formal_subtype_concepts_tfg:
  TF (exists f : nat -> ty,
         (forall i j, i <> j -> f i <> f j) /\
         (forall i, f (S i) <: f i)).
Proof.
unfold TF.
left.
exists top_fn.
split.
- intros. unfold not in *. intros. apply H. clear H.
  generalize dependent j.
  induction i.
  -- intros. destruct j. reflexivity. simpl in H0. inversion H0.
  -- intros. destruct j. simpl in H0. inversion H0.
     apply eq_S. apply IHi.
     simpl in H0. inversion H0. reflexivity. 
- intros.
  simpl.
  induction i.
  -- simpl. apply S_Top.
  -- simpl. apply S_Arrow. apply S_Refl. assumption.
Qed.

(*
There is an infinite ascending chain of distinct types in the subtype 
relation---that is, an infinite sequence of types  S0, S1, etc., such that 
all the Si's are different and each S(i+1) is a supertype of Si.
*)
Theorem formal_subtype_concepts_tfh:
  TF (exists f : nat -> ty,
         (forall i j, i <> j -> f i <> f j) /\
         (forall i, f i <: f (S i))).
Proof.
unfold TF.
right.
unfold not.
intros.
destruct H.
destruct H.
pose proof (H0 0 ) as H1.
destruct (x 0).
- apply sub_inversion_Top in H1.
  pose proof (H0 1) as H2.
  rewrite H1 in H2.
  apply sub_inversion_Top in H2.
  rewrite <- H2 in H1.
  assert (H3: 1 = 2 -> False). { intros. inversion H3. }
  apply (H 1 2 H3 H1).
- apply Bool_super_isTop in H1.
  destruct H1.
  -- pose proof (H0 0) as H2.
     rewrite H1 in H2.
     apply sub_inversion_Bool in H2.
     rewrite <- H1 in H2. 
     assert (H3: 0 = 1 -> False). { intros. inversion H3. }
     apply (H 0 1 H3 H2).
  -- pose proof (H0 1) as H2.
     rewrite H1 in H2.
     apply sub_inversion_Top in H2.
     rewrite <- H2 in H1.
     assert (H3: 1 = 2 -> False). { intros. inversion H3. }
     apply (H 1 2 H3 H1).
- apply TyBase_super_isTop in H1.
  destruct H1.
  -- pose proof (H0 0) as H2.
     rewrite H1 in H2.
     apply sub_inversion_Base in H2.
     rewrite <- H1 in H2. 
     assert (H3: 0 = 1 -> False). { intros. inversion H3. }
     apply (H 0 1 H3 H2).
  -- pose proof (H0 1) as H2.
     rewrite H1 in H2.
     apply sub_inversion_Top in H2.
     rewrite <- H2 in H1.
     assert (H3: 1 = 2 -> False). { intros. inversion H3. }
     apply (H 1 2 H3 H1).
- admit.
- apply Unit_super_isTop in H1.
  destruct H1.
  -- pose proof (H0 0) as H2.
     rewrite H1 in H2.
     apply sub_inversion_Unit in H2.
     rewrite <- H1 in H2. 
     assert (H3: 0 = 1 -> False). { intros. inversion H3. }
     apply (H 0 1 H3 H2).
  -- pose proof (H0 1) as H2.
     rewrite H1 in H2.
     apply sub_inversion_Top in H2.
     rewrite <- H2 in H1.
     assert (H3: 1 = 2 -> False). { intros. inversion H3. }
     apply (H 1 2 H3 H1).
- admit.
Admitted.

Theorem formal_proper_subtypes:
  TF (forall T,
         ~(T = <{Bool}> \/ (exists n, T = <{Base n}>) \/ T = <{Unit}>) ->
         exists S,
           S <: T /\ S <> T).
Proof.
unfold TF.
right.
unfold not.
intros.
pose proof (H (Ty_Prod  Ty_Bool Ty_Unit)) as H1.
assert (<{ Bool * Unit }> = <{ Bool }> \/
      (exists n : string, <{ Bool * Unit }> = Ty_Base n) \/
      <{ Bool * Unit }> = <{ Unit }> -> False).
{
  intros.
  destruct H0.
  - inversion H0.
  - destruct H0.
    -- destruct H0. inversion H0.
    -- inversion H0.
}
pose proof (H1 H0) as H2. clear H H1 H0.
destruct H2.
destruct H.
apply sub_inversion_pair' in H.
destruct H. destruct H. destruct H. destruct H1.
apply sub_inversion_Bool in H1.
apply sub_inversion_Unit in H2.
rewrite H1 in H. rewrite H2 in H.
apply (H0 H).
Qed.

Definition smallest_largest HT :=
  (* There exists a smallest and a largest. *)
  (exists TS TL, forall T, TS <: T /\ T <: TL <-> HT T)
  \/
  (* There exists a smallest, but no largest. *)
  ((exists TS, forall T, TS <: T <-> HT T) /\
   ~(exists TL, forall T, T <: TL <-> HT T))
  \/
  (* There exists a largest, but not smallest. *)
  (~(exists TS, forall T, TS <: T <-> HT T) /\
   (exists TL, forall T, T <: TL <-> HT T))
  \/
  (* There exists neither a smallest nor a largest. *)
  (~(exists TS, forall T, TS <: T <-> HT T) /\
   ~(exists TL, forall T, T <: TL <-> HT T)).

Lemma ttt : forall T, T = <{A->A}> \/ T = <{Top->A}> -> T <: <{A->A}>.
intros.
destruct H.
- rewrite H. apply S_Refl.
- rewrite H. apply S_Arrow. apply S_Top. apply S_Refl. 
Qed.

(* to confirm that the condition we are looking for is  T : A -> A *)
(*
Lemma test123 : forall T,
  T = <{A->A}> \/ T = <{Top->A}> ->
  empty |- <{(\p:T*Top, p.fst) ((\z:A, z), unit)}> \in <{A->A}>.
intros.
apply ttt in H.
(* destruct H. *)
- apply T_App with (T2 := <{T * Top}>).
  -- apply T_Abs.
     apply T_Fst with (T2 := Ty_Top).
     eapply T_Sub.
     + apply T_Var. rewrite update_eq. reflexivity.
     + apply S_Prod.
       ++ assumption.
       ++ apply S_Refl.
  -- apply T_Pair.
     + eapply T_Sub.
       ++ apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
       ++ rewrite H. apply S_Refl.
     + eapply T_Sub.
       ++ apply T_Unit.
       ++ apply S_Top.
- apply T_App with (T2 := <{T * Top}>).
  -- apply T_Abs.
     apply T_Fst with (T2 := Ty_Top).
     eapply T_Sub.
     + apply T_Var. rewrite update_eq. reflexivity.
     + apply S_Prod.
       ++ rewrite H. apply S_Arrow. apply S_Top. apply S_Refl.
       ++ apply S_Refl.
  -- apply T_Pair.
     + eapply T_Sub.
       ++ apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
       ++ rewrite H. apply S_Arrow.
     + eapply T_Sub.
       ++ apply T_Unit.
       ++ apply S_Top.       
*)

Lemma afafa : ("p" |-> <{Bool * Unit}>) |- <{p.fst}> \in <{Bool}>.
Proof.
apply T_Fst with (T2 := <{Unit}>).
apply T_Var.
rewrite update_eq.
reflexivity.
Qed.

Lemma context_type_impl_sub_type :
  forall Gamma x T1 T2, (x |-> T1; Gamma) |- x \in T2 -> T1 <: T2.
Proof.
intros.
apply typing_inversion_var in H.
destruct H.
destruct H.
rewrite update_eq in H.
inversion H.
assumption.
Qed.

Lemma fst_impl_pair : forall Gamma p T,
  Gamma |- <{p.fst}> \in T ->
  exists T', Gamma |- <{p}> \in <{T * T'}>.
Proof.
intros.
exists <{Top}>.
remember <{p.fst}> as t.
induction H; inversion Heqt.
- eauto.
- subst.
  assert (H1: <{T1 * T2}> <: <{T1 * Top}>). { apply S_Prod. apply S_Refl. apply S_Top. }
  eapply T_Sub. apply H. apply H1.
Qed.

Lemma snd_impl_pair : forall Gamma p T,
  Gamma |- <{p.snd}> \in T ->
  exists T', Gamma |- <{p}> \in <{T' * T}>.
Proof.
intros.
exists <{Top}>.
remember <{p.snd}> as t.
induction H; inversion Heqt.
- eauto.
- subst.
  assert (H1: <{T1 * T2}> <: <{Top * T2}>). { apply S_Prod. apply S_Top. apply S_Refl. }
  eapply T_Sub. apply H. apply H1.
Qed.

Theorem formal_small_large_1:
  smallest_largest
  (fun T =>
   empty |- <{(\p:T*Top, p.fst) ((\z:A, z), unit)}> \in <{A->A}>).
Proof.
unfold smallest_largest.
left.
exists (Ty_Arrow A A), (Ty_Arrow A A).
intros.
split.
- intros.
  destruct H.
  apply T_App with (T2 := <{T * Top}>).
  -- apply T_Abs.
     apply T_Fst with (T2 := Ty_Top).
     eapply T_Sub.
     + apply T_Var. rewrite update_eq. reflexivity.
     + apply S_Prod.
       ++ assumption.
       ++ apply S_Refl.
  -- apply T_Pair.
     + eapply T_Sub.
       ++ apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
       ++ assumption.
     + eapply T_Sub.
       ++ apply T_Unit.
       ++ apply S_Top. 
- intros.
  split.
  -- apply typing_inversion_app in H. destruct H. destruct H.
     apply typing_inversion_abs in H. destruct H. destruct H.
     apply sub_inversion_arrow in H. destruct H. destruct H.
     destruct H. destruct H2.
     inversion H. clear H. subst.
     apply sub_inversion_pair' in H2. destruct H2. destruct H.
     destruct H. destruct H2.
     rewrite H in H0. clear H.
     apply typing_inversion_pair' in H0.
     destruct H0. destruct H. destruct H.
     destruct H0.
     apply typing_inversion_abs in H.
     destruct H. destruct H. apply typing_inversion_var in H6.
     destruct H6. destruct H6. rewrite update_eq in H6. inversion H6.
     clear H6. subst.
     apply TyBase_super_isTop in H7.
     destruct H7.
     --- apply sub_inversion_pair' in H5.
         destruct H5. destruct H5. destruct H5. destruct H6. destruct H7.
         inversion H5. subst.
         eapply S_Trans.
         apply H.
         eapply S_Trans. apply H6. assumption.
     --- apply sub_inversion_pair' in H5.
         destruct H5. destruct H5. destruct H5. destruct H7.
         inversion H5. clear H5. subst.
         assert (H9: <{A -> A}> <: <{A -> Top}>).
         {  apply S_Arrow. apply S_Refl. apply S_Top. }
         eapply S_Trans. apply H9.
         eapply S_Trans. apply H.
         eapply S_Trans. apply H7. assumption.
  -- apply typing_inversion_app in H. destruct H. destruct H.
     apply typing_inversion_abs in H. destruct H. destruct H.
     
     apply sub_inversion_arrow in H.
     destruct H. destruct H. destruct H. destruct H2.
     inversion H. clear H.
     subst.
     apply sub_inversion_pair' in H2.
     destruct H2. destruct H. destruct H. destruct H2. subst.
     apply typing_inversion_pair in H0. destruct H0.
     apply typing_inversion_abs in H. destruct H. destruct H.
     apply context_type_impl_sub_type in H5.
     apply TyBase_super_isTop in H5.
     destruct H5.
     --- subst.
         apply fst_impl_pair in H1.
         destruct H1.
         apply context_type_impl_sub_type in H1.
         apply sub_inversion_pair' in H1.
         destruct H1. destruct H1. destruct H1. destruct H5. inversion H1.
         eauto. 
     --- subst.
         apply fst_impl_pair in H1.
         destruct H1.
         apply context_type_impl_sub_type in H1.
         apply sub_inversion_pair' in H1.
         destruct H1. destruct H1. destruct H1. destruct H5. inversion H1.
         eauto. 
Qed.

Theorem sub_typing_is_antisymmetric : forall T1 T2,
  T1 <: T2 /\ T2 <: T1 <-> T1 = T2.
Proof.
intros.
split.
- intros.
  destruct H.
  induction H.
  -- reflexivity.
  -- assert (H2: T <: U). { eapply S_Trans. apply H0. assumption. }
     pose proof (IHsubtype2 H2) as H3.
     rewrite <- H3 in H0.
     pose proof (IHsubtype1 H0) as H4. rewrite H3 in H4. assumption.
  -- apply sub_inversion_Top. assumption.
  -- apply sub_inversion_arrow in H0.
     destruct H0. destruct H0. destruct H0. destruct H2.
     inversion H0. subst.
     pose proof (IHsubtype1 H2) as H4.
     pose proof (IHsubtype2 H3) as H5.
     rewrite H4. rewrite H5. reflexivity.
  -- apply sub_inversion_pair' in H0.
     destruct H0.
     destruct H0. destruct H0. inversion H0. subst. clear H0.
     destruct H2.
     pose proof (IHsubtype1 H0) as H3.
     pose proof (IHsubtype2 H2) as H4.
     rewrite H3. rewrite H4. reflexivity.
- intros.
  split. rewrite H. apply S_Refl. rewrite H. apply S_Refl.     
Qed.  
  
Theorem formal_small_large_2:
  smallest_largest
  (fun T =>
   empty |- <{(\p:(A->A)*(B->B), p) ((\z:A, z), (\z:B, z))}> \in T).
Proof.
unfold smallest_largest.
left.
exists <{(A->A)*(B->B)}>, <{Top}>.
intros.
split.
- intros.
  eapply T_Sub.
  -- eapply T_App.
     --- apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
     --- apply T_Pair.
         + apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
         + apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
  -- destruct H. assumption.
- intros.
  split.
  -- apply typing_inversion_app in H.
     destruct H. destruct H.
     apply typing_inversion_abs in H.
     destruct H. destruct H.
     apply context_type_impl_sub_type in H1.
     apply sub_inversion_arrow in H.
     destruct H. destruct H. destruct H. destruct H2.
     inversion H.
     subst.
     eapply S_Trans.
     --- apply H1.
     --- assumption.
  -- apply S_Top.
Qed.

Lemma test:
  (a |-> A) |- <{(\p:A*(A->A), (p.snd) (p.fst)) (a, \z:A, z)}> \in A.
Proof.
eapply T_App.
- eapply T_Abs.
  eapply T_App.
  -- eapply T_Snd.
     apply T_Var.
     rewrite update_eq.
     reflexivity.
  -- eapply T_Fst.
     apply T_Var.
     rewrite update_eq.
     reflexivity.
- apply T_Pair.
  -- apply T_Var. rewrite update_eq. reflexivity.
  -- apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
Qed.

Theorem formal_small_large_3:
  smallest_largest
  (fun T =>
   (a |-> A) |- <{(\p:A*T, (p.snd) (p.fst)) (a, \z:A, z)}> \in A).
Proof.
unfold smallest_largest.
left.
exists <{A->A}>, <{A->A}>.
intros.
split.
- intros.
  destruct H.
  apply T_App with (T2 := <{A * T}>).
  -- apply T_Abs.
     apply T_App with (T2 := A).
     + apply T_Snd with (T1 := A).
       apply T_Var.
       rewrite update_eq.
       assert (H1: <{ A -> A }> = T).
       { apply sub_typing_is_antisymmetric. split. assumption. assumption. }
       rewrite H1. reflexivity.
     + apply T_Fst with (T2 := T).
       apply T_Var. rewrite update_eq. reflexivity.
  -- apply T_Pair.
     + apply T_Var. rewrite update_eq. reflexivity.
     + assert (H1: <{ A -> A }> = T).
       { apply sub_typing_is_antisymmetric. split. assumption. assumption. }
       rewrite <- H1. apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
- intros.
  apply sub_typing_is_antisymmetric.
  apply typing_inversion_app in H. destruct H. destruct H.
  apply typing_inversion_abs in H. destruct H. destruct H.
  apply typing_inversion_app in H1. destruct H1. destruct H1.
  apply typing_inversion_pair' in H0. destruct H0. destruct H0. destruct H0. destruct H3.

  apply typing_inversion_abs in H3. destruct H3. destruct H3.
  apply context_type_impl_sub_type in H5.
  subst.
  apply sub_inversion_arrow in H. destruct H. destruct H. destruct H. destruct H6.
  apply sub_inversion_Base in H7. subst.
  inversion H. clear H.
  subst.
  apply context_type_impl_sub_type in H0.

  apply fst_impl_pair in H2. destruct H2.
  apply context_type_impl_sub_type in H.
  apply snd_impl_pair in H1. destruct H1.
  apply context_type_impl_sub_type in H1.
  subst.
  
  apply sub_inversion_pair' in H1.
  destruct H1. destruct H1. destruct H1. destruct H2.
  inversion H1. clear H1.
  
  apply sub_inversion_pair' in H.
  destruct H. destruct H. destruct H. destruct H1.
  inversion H. clear H.
  
  subst.
  
  clear x0 H8.
  clear x5 H2.
  assert (H8: <{ x2 * x3 }> <: <{ A * x9 }>). { eapply S_Trans. apply H4. assumption. }
  clear H4 H6.
  
  apply sub_inversion_pair' in H8. destruct H8. destruct H. destruct H. destruct H2.
  inversion H. subst. clear H.
  apply sub_inversion_Base in H2. subst. clear H0.
  
  assert (H8: <{ A -> x4 }> <: x9). { eapply S_Trans. apply H3. assumption. }
  clear H3 H4 x5.
  
  assert (H9: <{ A -> x4 }> <: <{ x1 -> A }>). { eapply S_Trans. apply H8. assumption. }
  
  apply sub_inversion_arrow in H9. destruct H9. destruct H. destruct H. destruct H0.
  inversion H. clear H. subst.
  
  apply sub_inversion_Base in H0.
  apply sub_inversion_Base in H2.
  subst.
  clear H1 H5.
  apply sub_typing_is_antisymmetric.
  split.
  assumption.
  assumption.
Qed.

Lemma test1 : forall T,
  T = <{A->A}> -> 
  exists S,
     empty |- <{\p:A*T, (p.snd) (p.fst)}> \in S.
Proof.
intros.
exists <{(A * T) -> A}>.
apply T_Abs.
apply T_App with (T2 := A).
- eapply T_Snd. apply T_Var. rewrite update_eq. rewrite <- H. reflexivity.
- apply T_Fst with (T2 := T). apply T_Var. rewrite update_eq. reflexivity.
Qed.  

Lemma test2 : forall T,
  T = <{A->Top}> -> 
  exists S,
     empty |- <{\p:A*T, (p.snd) (p.fst)}> \in S.
Proof.
intros.
exists <{(A * T) -> Top}>.
apply T_Abs.
apply T_App with (T2 := A).
- eapply T_Snd. apply T_Var. rewrite update_eq. rewrite <- H. reflexivity.
- apply T_Fst with (T2 := T). apply T_Var. rewrite update_eq. reflexivity.
Qed.  

Lemma test3 : forall T,
  T = <{A->(Top->Top)}> -> 
  exists S,
     empty |- <{\p:A*T, (p.snd) (p.fst)}> \in S.
Proof.
intros.
exists <{(A * T) -> (Top->Top)}>.
apply T_Abs.
apply T_App with (T2 := A).
- eapply T_Snd. apply T_Var. rewrite update_eq. rewrite <- H. reflexivity.
- apply T_Fst with (T2 := T). apply T_Var. rewrite update_eq. reflexivity.
Qed.  

Lemma formal_small_large_4_helper: forall T,
  <{ A -> A }> <: T ->
  T <: <{ A -> Top }> ->
  T = <{ A -> A }> \/ T = <{ A -> Top }>.
Proof.
intros.
apply sub_inversion_arrow in H0. destruct H0. destruct H0. destruct H0. destruct H1.
subst.
apply sub_inversion_arrow in H. destruct H. destruct H. destruct H. destruct H0.
inversion H. clear H. subst.
assert (H4: A = x). { apply sub_typing_is_antisymmetric. split. assumption. assumption. }
apply TyBase_super_isTop in H3.
destruct H3.
- left. rewrite H. rewrite <- H4. reflexivity.
- right. rewrite H. rewrite <- H4. reflexivity.
Qed.

Lemma tessss: forall S,
   <{A->S}> <: <{A->Top}>.
Proof.
intros.
apply S_Arrow.
- apply S_Refl.
- apply S_Top.
Qed. 

Lemma testssss : forall T,
  (exists T1, T = <{A -> T1}>) <->
    exists S,
     empty |- <{\p:A*T, (p.snd) (p.fst)}> \in S.
Proof.
intros.
split.
- intros.
  destruct H.
  exists <{(A * T) -> x}>.
  apply T_Abs.
  apply T_App with (T2 := A).
  -- eapply T_Snd. apply T_Var. rewrite update_eq. rewrite H. reflexivity.
  -- apply T_Fst with (T2 := T). apply T_Var. rewrite update_eq. reflexivity.
- admit.
Admitted.  

Theorem formal_small_large_4:
  smallest_largest
  (fun T =>
   exists S,
     empty |- <{\p:A*T, (p.snd) (p.fst)}> \in S).
Proof.
Admitted.
(*
unfold smallest_largest.

right.
right.
right.
split.
- unfold not.
  intros.
  destruct H.
  pose proof (H <{Top}>) as H1. clear H.
  destruct H1.
  assert (H2: x <: <{Top}>) by (apply S_Top).
  pose proof (H H2) as H3.
  
  clear H H0 H2.
  
  destruct H3.
  apply typing_inversion_abs in H. destruct H. destruct H.
  apply typing_inversion_app in H0. destruct H0. destruct H0.

  apply snd_impl_pair in H0. destruct H0.
  apply context_type_impl_sub_type in H0.
  
  apply fst_impl_pair in H1. destruct H1.
  apply context_type_impl_sub_type in H1.
  
  apply sub_inversion_pair' in H0. destruct H0. destruct H0. destruct H0.
  inversion H0.
  destruct H2. rewrite <- H5 in H3.
  apply sub_inversion_arrow in H3.
  destruct H3. destruct H3. destruct H3. inversion H3.
- unfold not.
  intros.
  destruct H.
  pose proof (H <{A -> Top}>) as H1.
  destruct H1.
  
  assert (H2: (exists S : ty,
        empty
        |- \ "p" : A * (A -> Top),
           <{p.snd}> <{p.fst}> \in S)).
  {
    admit. (* can be proved *)
  }
  pose proof (H1 H2) as H3.
  assert (H4: x = <{A -> Top}> \/ x = <{Top}>). { admit. } (* can be proved *)
  
  destruct H4.
  -- rewrite H4 in H.
  
     pose proof (H <{Top -> Top}>) as H5.
  
     assert (H6: <{ Top -> Top }> <: <{ A -> Top }>).
     {
       apply S_Arrow. apply S_Top. apply S_Top.
     }
  
     destruct H5.
  
     pose proof (H5 H6) as H8.
  
     clear x H H0 H1 H2 H3 H4 H5 H6 H7.
  
     destruct H8.
     
     apply typing_inversion_abs in H. destruct H. destruct H.
     apply typing_inversion_app in H0. destruct H0. destruct H0.
     apply snd_impl_pair in H0. destruct H0.
     apply context_type_impl_sub_type in H0.
     apply fst_impl_pair in H1. destruct H1.
     apply context_type_impl_sub_type in H1.
     
     apply sub_inversion_pair' in H1. destruct H1. destruct H1. destruct H1. destruct H2.
     inversion H1. clear H1.
     
     apply sub_inversion_pair' in H0. destruct H0. destruct H0. destruct H0. destruct H1.
     inversion H0. clear H0.
     subst.
     
     apply sub_inversion_arrow in H4. destruct H4. destruct H0. destruct H0. destruct H4.
     inversion H0. clear H0.
     subst.
     
     apply sub_inversion_Top in H5.
     subst.
  
     admit.
     
     
  

left.
exists <{A->Unit}>, <{A->Top}>.
intros.
split.
- intros.
  destruct H.
  assert (H1: T = <{A->Unit}> \/ T = <{A->Top}>). { 
    (* apply formal_small_large_4_helper.
    assumption.
    assumption. *)
    admit. 
  }
  destruct H1.
  -- exists <{(A * T) -> Unit}>.
     eapply T_Sub.
     + apply T_Abs.
       apply T_App with (T2 := A).
       ++ eapply T_Snd. apply T_Var. rewrite update_eq. rewrite H1. reflexivity.
       ++ apply T_Fst with (T2 := T). apply T_Var. rewrite update_eq. reflexivity.
     + apply S_Refl.
  -- exists <{(A * T) -> Top}>.
     eapply T_Sub.
     + apply T_Abs.
       apply T_App with (T2 := A).
       ++ eapply T_Snd. apply T_Var. rewrite update_eq. rewrite H1. reflexivity.
       ++ apply T_Fst with (T2 := T). apply T_Var. rewrite update_eq. reflexivity.
     + apply S_Refl.
- intros.
  destruct H.
  
  (* assert (H1: T = <{A->A}> \/ T = <{A->Top}> -> <{ A -> A }> <: T /\ T <: <{ A -> Top }>).
  { 
    intros. destruct H0.
    - rewrite H0. split. apply S_Refl. apply S_Arrow. apply S_Refl. apply S_Top.
    - rewrite H0. split. apply S_Arrow. apply S_Refl. apply S_Top. apply S_Refl.
  }
  apply H1.
  clear H1. *)
    
  apply typing_inversion_abs in H. destruct H. destruct H.
  apply typing_inversion_app in H0. destruct H0. destruct H0.
  apply snd_impl_pair in H0. destruct H0.
  apply context_type_impl_sub_type in H0.
  apply fst_impl_pair in H1. destruct H1.
  apply context_type_impl_sub_type in H1.
  
  apply sub_inversion_pair' in H0. destruct H0. destruct H0. destruct H0. destruct H2.
  inversion H0. clear H0. subst.
  
  apply sub_inversion_pair' in H1. destruct H1. destruct H0. destruct H0. destruct H1.
  inversion H0. clear H0. subst.
  
  apply sub_inversion_arrow in H3.
  destruct H3. destruct H0. destruct H0. destruct H3. subst.
  
  clear H2 x2. 
  
  assert (H6: A <: x4). { eapply S_Trans. apply H1. assumption. }
  clear H1 H3 x1.
  
  clear H4. clear x3.
  
  assert (H7: exists U1 U2, x = <{U1 -> U2}> /\ x0 <: U2 /\ U1 <: <{ A * (x4 -> x5) }>).
  { admit. }
  destruct H7. destruct H0. destruct H0. destruct H1.
  clear H. subst.
  
  apply sub_inversion_pair' in H2. destruct H2. destruct H. destruct H. destruct H0.
  apply sub_inversion_Base in H0.
  subst.
  
  apply sub_inversion_arrow in H2. destruct H2. destruct H. destruct H. destruct H0.
  subst.
  
 
  
  left.
*)

Definition smallest P :=
  TF (exists TS, forall T, TS <: T <-> P T).  
  

(* Revisit these exercises later *)    
