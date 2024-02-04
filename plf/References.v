Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From Coq Require Import Lists.List.
Import Nat.

Module STLCRef.

Inductive ty : Type :=
  | Ty_Nat : ty
  | Ty_Unit : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Ref : ty -> ty.
  
Inductive tm : Type :=
  (* STLC with numbers: *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_const : nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0 : tm -> tm -> tm -> tm
  (* New terms: *)
  | tm_unit : tm
  | tm_ref : tm -> tm
  | tm_deref : tm -> tm
  | tm_assign : tm -> tm -> tm
  | tm_loc : nat -> tm.
  
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

Notation "{ x }" := x (in custom stlc at level 0, x constr).

Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).

Notation "'Nat'" := Ty_Nat (in custom stlc at level 0).
Notation "'succ' x" := (tm_succ x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "'pred' x" := (tm_pred x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "x * y" := (tm_mult x y) (in custom stlc at level 1,
                                      left associativity).
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Coercion tm_const : nat >-> tm.

Notation "'Ref' t" :=
  (Ty_Ref t) (in custom stlc at level 4).
Notation "'loc' x" := (tm_loc x) (in custom stlc at level 2).
Notation "'ref' x" := (tm_ref x) (in custom stlc at level 2).
Notation "'!' x " := (tm_deref x) (in custom stlc at level 2).
Notation " e1 ':=' e2 " := (tm_assign e1 e2) (in custom stlc at level 21).

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_nat : forall n : nat ,
      value <{ n }>
  | v_unit :
      value <{ unit }>
  | v_loc : forall l,
      value <{ loc l }>.
      
Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  (* numbers *)
  | tm_const _ =>
      t
  | <{succ t1}> =>
      <{succ [x := s] t1}>
  | <{pred t1}> =>
      <{pred [x := s] t1}>
  | <{t1 * t2}> =>
      <{ ([x := s] t1) * ([x := s] t2)}>
  | <{if0 t1 then t2 else t3}> =>
      <{if0 [x := s] t1 then [x := s] t2 else [x := s] t3}>
  (* unit *)
  | <{ unit }> =>
    <{ unit }>
  (* references *)
  | <{ ref t1 }> =>
      <{ ref ([x:=s] t1) }>
  | <{ !t1 }> =>
      <{ !([x:=s] t1) }>
  | <{ t1 := t2 }> =>
    <{ ([x:=s] t1) := ([x:=s] t2) }>
  | <{ loc _ }> =>
      t
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Definition tseq t1 t2 :=
  <{ (\ x : Unit, t2) t1 }>.
  
Notation "t1 ; t2" := (tseq t1 t2) (in custom stlc at level 3).

(*
let c1 = newcounter unit in
let c2 = newcounter unit in
// Note that we've allocated two separate storage cells now!
let r1 = c1.i unit in
let r2 = c2.i unit in
r2  // yields 1, not 2! 

Draw (on paper) the contents of the store at the point in execution where the 
first two lets have finished and the third one is about to begin.

|-----|   |-----|
|  0  |   |  0  |
|-----|   |-----|

*) 


(*

update = \a:NatArray. \m:Nat. \v:Nat.
             let oldf = !a in
             a := (\n:Nat. if equal m n then v else oldf n);

If we defined update more compactly like this

      update = \a:NatArray. \m:Nat. \v:Nat.
                  a := (\n:Nat. if equal m n then v else (!a) n)

would it behave the same?


ANS: No, it would not behave the same, as the application of the function stored in the cell 'a' (
else portion) will use the current value of the function stored in 'a' instead of the 
intended (previous) function.

*)

(*

Show how explicit deallocation of references lead to a violation of type safety.

a := ref 10

b := a           (b \in ref Nat)

free a

a := ref <some function Nat -> Nat >

(pred !b) -> this attempts to do pred on a Nat->Nat object and hence a typing error

*)

Definition store := list tm.

Definition store_lookup (n:nat) (st:store) :=
  nth n st <{ unit }>.
  
Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil => nil
  | h :: t =>
    match n with
    | O => x :: t
    | S n' => h :: replace n' x t
    end
  end.  

Lemma replace_nil : forall A n (x:A),
  replace n x nil = nil.
Proof.
intros.
destruct n.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

Lemma length_replace : forall A n x (l:list A),
  length (replace n x l) = length l.
Proof.
intros.
generalize dependent l.
induction n.
- intros. destruct l.
  -- rewrite replace_nil. reflexivity.
  -- simpl. reflexivity.
- intros. destruct l.
  -- rewrite replace_nil. reflexivity.
  -- simpl.
     pose proof (IHn l) as H.
     rewrite H. reflexivity.
Qed.

Lemma lookup_replace_eq : forall l t st,
  l < length st ->
  store_lookup l (replace l t st) = t.
Proof.
intros.
generalize dependent st.
induction l.
- intros. destruct st.
  -- inversion H.
  -- simpl. reflexivity.
- intros. destruct st.
  -- inversion H.
  -- simpl. simpl in H.
     assert (H1: l < length st).
     {
       inversion H.
       + lia.
       + lia.
     }
     apply IHl. assumption.
Qed.

Lemma lookup_replace_neq : forall l1 l2 t st,
  l1 <> l2 ->
  store_lookup l1 (replace l2 t st) = store_lookup l1 st.
Proof.
intros.
generalize dependent l2.
generalize dependent l1.
induction st.
- intros. rewrite replace_nil. reflexivity.
- intros.
  destruct l1.
  -- destruct l2.
     + unfold not in H. exfalso. apply H. reflexivity.
     + unfold store_lookup. simpl. reflexivity.
  -- destruct l2.
     + unfold store_lookup. simpl. reflexivity.
     + unfold store_lookup. simpl. eauto.
Qed.

Reserved Notation "t '/' st '-->' t' '/' st'"
  (at level 40, st at level 39, t' at level 39).
  
Inductive step : tm * store -> tm * store -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2 st,
         value v2 ->
         <{ (\x : T2, t1) v2 }> / st --> <{ [x := v2] t1 }> / st
  | ST_App1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         <{ t1 t2 }> / st --> <{ t1' t2 }> / st'
  | ST_App2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 t2 }> / st --> <{ v1 t2' }> / st'
  (* numbers *)
  | ST_SuccNat : forall (n : nat) st,
         <{ succ n }> / st --> tm_const (S n) / st
  | ST_Succ : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ succ t1 }> / st --> <{ succ t1' }> / st'
  | ST_PredNat : forall (n : nat) st,
         <{ pred n }> / st --> tm_const (n - 1) / st
  | ST_Pred : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ pred t1 }> / st --> <{ pred t1' }> / st'
  | ST_MultNats : forall (n1 n2 : nat) st,
      <{ n1 * n2 }> / st --> tm_const (n1 * n2) / st
  | ST_Mult1 : forall t1 t2 t1' st st',
         t1 / st --> t1' / st' ->
         <{ t1 * t2 }> / st --> <{ t1' * t2 }> / st'
  | ST_Mult2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 * t2 }> / st --> <{ v1 * t2' }> / st'
  | ST_If0 : forall t1 t1' t2 t3 st st',
         t1 / st --> t1' / st' ->
         <{ if0 t1 then t2 else t3 }> / st --> <{ if0 t1' then t2 else t3 }> / st'
  | ST_If0_Zero : forall t2 t3 st,
         <{ if0 0 then t2 else t3 }> / st --> t2 / st
  | ST_If0_Nonzero : forall n t2 t3 st,
         <{ if0 {S n} then t2 else t3 }> / st --> t3 / st
  (* references *)
  | ST_RefValue : forall v st,
         value v ->
         <{ ref v }> / st --> <{ loc { length st } }> / (st ++ v::nil)
  | ST_Ref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ ref t1 }> / st --> <{ ref t1' }> / st'
  | ST_DerefLoc : forall st l,
         l < length st ->
         <{ !(loc l) }> / st --> <{ { store_lookup l st } }> / st
  | ST_Deref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ ! t1 }> / st --> <{ ! t1' }> / st'
  | ST_Assign : forall v l st,
         value v ->
         l < length st ->
         <{ (loc l) := v }> / st --> <{ unit }> / replace l v st
  | ST_Assign1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         <{ t1 := t2 }> / st --> <{ t1' := t2 }> / st'
  | ST_Assign2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 := t2 }> / st --> <{ v1 := t2' }> / st'

where "t '/' st '-->' t' '/' st'" := (step (t,st) (t',st')).

Hint Constructors step : core.

Definition multistep := (multi step).
Notation "t '/' st '-->*' t' '/' st'" :=
               (multistep (t,st) (t',st'))
               (at level 40, st at level 39, t' at level 39).

Definition context := partial_map ty.

Theorem cyclic_store:
  exists t,
    t / nil -->*
    <{ unit }> / (<{ \x:Nat, (!(loc 1)) x }> :: <{ \x:Nat, (!(loc 0)) x }> :: nil).
Proof.
exists <{ (ref (ref (\x:Nat, (!(loc 1)) x))) := (\x:Nat, (!(loc 0)) x) }>.     
eapply multi_step.
- apply ST_Assign1.
  apply ST_Ref.
  apply ST_RefValue.
  apply v_abs.
- eapply multi_step.
  -- apply ST_Assign1.
     simpl.
     apply ST_RefValue.
     apply v_loc.
  -- eapply multi_step.
     + simpl.
       apply ST_Assign.
       ++ apply v_abs.
       ++ simpl. lia.
     + simpl.
       apply multi_refl.
Qed.         

Definition store_ty := list ty.

Definition store_Tlookup (n:nat) (ST:store_ty) :=
  nth n ST <{ Unit }>.
  
Reserved Notation "Gamma ';' ST '|-' t '\in' T"
                  (at level 40, t custom stlc, T custom stlc at level 0).
                  
Inductive has_type (ST : store_ty) : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma ; ST |- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      update Gamma x T2 ; ST |- t1 \in T1 ->
      Gamma ; ST |- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma ; ST |- t1 \in (T2 -> T1) ->
      Gamma ; ST |- t2 \in T2 ->
      Gamma ; ST |- t1 t2 \in T1
  | T_Nat : forall Gamma (n : nat),
      Gamma ; ST |- n \in Nat
  | T_Succ : forall Gamma t1,
      Gamma ; ST |- t1 \in Nat ->
      Gamma ; ST |- succ t1 \in Nat
  | T_Pred : forall Gamma t1,
      Gamma ; ST |- t1 \in Nat ->
      Gamma ; ST |- pred t1 \in Nat
  | T_Mult : forall Gamma t1 t2,
      Gamma ; ST |- t1 \in Nat ->
      Gamma ; ST |- t2 \in Nat ->
      Gamma ; ST |- t1 * t2 \in Nat
  | T_If0 : forall Gamma t1 t2 t3 T0,
      Gamma ; ST |- t1 \in Nat ->
      Gamma ; ST |- t2 \in T0 ->
      Gamma ; ST |- t3 \in T0 ->
      Gamma ; ST |- if0 t1 then t2 else t3 \in T0
  | T_Unit : forall Gamma,
      Gamma ; ST |- unit \in Unit
  | T_Loc : forall Gamma l,
      l < length ST ->
      Gamma ; ST |- (loc l) \in (Ref {store_Tlookup l ST })
  | T_Ref : forall Gamma t1 T1,
      Gamma ; ST |- t1 \in T1 ->
      Gamma ; ST |- (ref t1) \in (Ref T1)
  | T_Deref : forall Gamma t1 T1,
      Gamma ; ST |- t1 \in (Ref T1) ->
      Gamma ; ST |- (! t1) \in T1
  | T_Assign : forall Gamma t1 t2 T2,
      Gamma ; ST |- t1 \in (Ref T2) ->
      Gamma ; ST |- t2 \in T2 ->
      Gamma ; ST |- (t1 := t2) \in Unit

where "Gamma ';' ST '|-' t '\in' T" := (has_type ST Gamma t T).

Hint Constructors has_type : core.

Definition store_well_typed (ST:store_ty) (st:store) :=
  length ST = length st /\
  (forall l, l < length st ->
     empty; ST |- { store_lookup l st } \in {store_Tlookup l ST }).
     
Theorem store_not_unique:
  exists st, exists ST1, exists ST2,
    store_well_typed ST1 st /\
    store_well_typed ST2 st /\
    ST1 <> ST2.
Proof.
exists (<{ \x:Nat, (!(loc 1)) x }> :: <{ \x:Nat, (!(loc 0)) x }> :: nil),
       ( <{Nat -> Nat}> ::  <{Nat -> Nat}> :: nil),
       ( <{Nat -> Unit}> ::  <{Nat -> Unit}> :: nil).
split.
- unfold store_well_typed.
  split.
  -- simpl. reflexivity.
  -- intros.
     simpl in H. 
     unfold store_lookup.
     unfold store_Tlookup.
     assert (H1: l = 0 \/ l = 1). { lia. }
     destruct H1.
     + rewrite H0.
       simpl.
       apply T_Abs.
       apply T_App with (T2 := <{Nat}>).
       ++ apply T_Deref.
          apply T_Loc.
          simpl. lia.
       ++ apply T_Var. rewrite update_eq. reflexivity.
     + rewrite H0.
       simpl.
       apply T_Abs.
       apply T_App with (T2 := <{Nat}>).
       ++ apply T_Deref.
          apply T_Loc.
          simpl. lia.
       ++ apply T_Var. rewrite update_eq. reflexivity.
- unfold store_well_typed.
  split.
  -- split.
     + simpl. reflexivity.
     + intros. 
       simpl in H.
       unfold store_lookup.
       unfold store_Tlookup.
       assert (H1: l = 0 \/ l = 1). { lia. }
       destruct H1.
       ++ rewrite H0.
          simpl.
          apply T_Abs.
          apply T_App with (T2 := <{Nat}>).
          +++ apply T_Deref.
              apply T_Loc.
              simpl. lia.
          +++ apply T_Var. rewrite update_eq. reflexivity.
       ++ rewrite H0.
          simpl.
          apply T_Abs.
          apply T_App with (T2 := <{Nat}>).
          +++ apply T_Deref.
              apply T_Loc.
              simpl. lia.
           +++ apply T_Var. rewrite update_eq. reflexivity.
  -- unfold not.
     intros.
     inversion H.
Qed.

Inductive extends : store_ty -> store_ty -> Prop :=
  | extends_nil : forall ST',
      extends ST' nil
  | extends_cons : forall x ST' ST,
      extends ST' ST ->
      extends (x::ST') (x::ST).
      
Hint Constructors extends : core.

Lemma extends_lookup : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  store_Tlookup l ST' = store_Tlookup l ST.
Proof.
intros l ST.
generalize dependent l.
induction ST.
- intros. inversion H.
- intros.
  destruct ST'.
  -- inversion H0.
  -- inversion H0; subst.
     destruct l.
     + unfold store_Tlookup. simpl. reflexivity.
     + unfold store_Tlookup. simpl.
       simpl in H.
       assert (H3: l < Datatypes.length ST). { lia. }
       eauto.
Qed.

Lemma length_extends : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  l < length ST'.       
Proof.
intros l ST.
generalize dependent l.
induction ST.
- intros. inversion H.
- intros. destruct ST'.
  -- inversion H0.
  -- inversion H0; subst.
     destruct l.
     + simpl. lia.
     + simpl.
       simpl in H.
       assert (H3: l < Datatypes.length ST). { lia. }
       pose proof (IHST l ST' H3 H2) as H4.
       lia.
Qed.

Lemma extends_app : forall ST T,
  extends (ST ++ T) ST.
Proof.
intros.
induction ST.
- simpl. apply extends_nil.
- simpl. apply extends_cons. assumption.
Qed.

Lemma extends_refl : forall ST,
  extends ST ST.
Proof.
intros.
induction ST.
- apply extends_nil.
- apply extends_cons. assumption.
Qed.

Lemma weakening : forall Gamma Gamma' ST t T,
     includedin Gamma Gamma' ->
     Gamma ; ST |- t \in T ->
     Gamma' ; ST |- t \in T.
Proof.
intros.
generalize dependent Gamma'.
induction H0; eauto. (* can also simply do eauto using includedin_update *)
intros.
apply T_Abs.
apply IHhas_type.
apply includedin_update.
assumption.
Qed.

Lemma weakening_empty : forall Gamma ST t T,
     empty ; ST |- t \in T ->
     Gamma ; ST |- t \in T.
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

Lemma substitution_preserves_typing : forall Gamma ST x U t v T,
  (update Gamma x U); ST |- t \in T ->
  empty ; ST |- v \in U ->
  Gamma ; ST |- [x:=v]t \in T.
Proof.
intros.
generalize dependent Gamma.
generalize dependent T.
induction t0.
- intros.
  destruct (String.eqb x0 s) eqn: Heq.
  -- rewrite String.eqb_eq in Heq.
     rewrite Heq in H.
     inversion H. subst.
     rewrite update_eq in H3. inversion H3.
     unfold subst. rewrite String.eqb_refl.
     apply weakening_empty. rewrite H2 in H0. assumption.
  -- rewrite String.eqb_neq in Heq.
     inversion H. subst.
     rewrite update_neq in H3.
     --- unfold subst.
         apply String.eqb_neq in Heq.
         rewrite Heq. apply T_Var. assumption.
     --- assumption.
- intros.
  simpl.
  inversion H. subst.
  pose proof (IHt0_1 (Ty_Arrow T2 T) Gamma) as H7.
  pose proof (H7 H4) as H8.
  pose proof (IHt0_2 T2 Gamma) as H9.
  pose proof (H9 H6) as H10.
  apply T_App with (T2 := T2).
  assumption. assumption.
- intros. inversion H. subst.
  destruct (String.eqb x0 s) eqn: Heq.
  -- rewrite String.eqb_eq in Heq.
     rewrite Heq. simpl.
     rewrite String.eqb_refl.
     apply T_Abs.
     pose proof (IHt0 T1 Gamma) as H7. subst.
     rewrite update_shadow in H6.
     assumption.
  -- rewrite String.eqb_neq in Heq.
     simpl.
     apply String.eqb_neq in Heq.
     rewrite Heq.
     apply T_Abs.
     apply IHt0.
     rewrite update_permute.
     + assumption.
     + apply String.eqb_neq in Heq. unfold not in Heq.
       unfold not. intros. symmetry in H1. apply (Heq H1).
- intros. simpl.
  inversion H. subst.
  assert (H1: (empty; ST |- {n} \in <{Nat}>)). { apply T_Nat. }
  eapply weakening in H1.
  -- apply H1.
  -- unfold includedin. intros.
     inversion H2.
- intros. simpl.
  inversion H. subst.
  pose proof (IHt0 <{Nat}> Gamma H3) as H4.
  apply T_Succ. assumption.
- intros. simpl.
  inversion H. subst.
  pose proof (IHt0 <{Nat}> Gamma H3) as H4.
  apply T_Pred. assumption.
- intros. simpl.
  inversion H. subst.
  pose proof (IHt0_1 <{Nat}> Gamma H4) as H7.
  pose proof (IHt0_2 <{Nat}> Gamma H6) as H8.
  apply T_Mult. assumption. assumption.
- intros.
  simpl.
  apply T_If0.
  inversion H.
  -- pose proof (IHt0_1 <{Nat}> Gamma) as Hthen. eauto.
  -- inversion H. eauto.
  -- inversion H. eauto.
- intros.
  inversion H. subst.
  assert (H1: (empty; ST |- <{unit}> \in <{Unit}>)). { apply T_Unit. }
  eapply weakening in H1.
  -- apply H1.
  -- unfold includedin. intros.
     inversion H2.
- intros. simpl.
  inversion H. subst.
  pose proof (IHt0 T1 Gamma H3) as H4.
  apply T_Ref. assumption.
- intros. simpl.
  apply T_Deref.
  inversion H. subst.
  pose proof (IHt0 <{Ref T}> Gamma H3) as H4.
  assumption.
- intros. simpl.
  inversion H. subst.
  pose proof (IHt0_1 <{Ref T2}> Gamma) as H7.
  pose proof (IHt0_2 T2 Gamma) as H8.
  pose proof (H7 H4) as H9.
  pose proof (H8 H6) as H10.
  eapply T_Assign.
  -- apply H9.
  -- apply H10.
- intros. simpl.
  inversion H. subst.
  apply T_Loc.
  assumption.
Qed.

Lemma assign_pres_store_typing : forall ST st l t,
  l < length st ->
  store_well_typed ST st ->
  empty ; ST |- t \in {store_Tlookup l ST} ->
  store_well_typed ST (replace l t st).
Proof.
intros.
unfold store_well_typed.
split.
- rewrite length_replace.
  inversion H0. assumption.
- intros.
  rewrite length_replace in H2.
  inversion H0.
  destruct (eqb l l0) eqn: Heq.
  -- rewrite eqb_eq in Heq.
     subst.
     rewrite lookup_replace_eq. assumption. assumption.
  -- rewrite lookup_replace_neq.
     + eauto.
     + rewrite eqb_neq in Heq. eauto.
Qed.

Lemma store_weakening : forall Gamma ST ST' t T,
  extends ST' ST ->
  Gamma ; ST |- t \in T ->
  Gamma ; ST' |- t \in T.
Proof.
intros.
generalize dependent ST'.
induction H0; eauto.
intros.
assert (H1: store_Tlookup l ST' = store_Tlookup l ST). 
{ 
  apply extends_lookup.
  assumption.
  assumption.
}
rewrite <- H1.
apply T_Loc.
eapply length_extends. apply H. apply H0.  
Qed.

(* extends equivalents for stores. needed for proving store_well_typed_app *)

Inductive extends_st : store -> store -> Prop :=
  | extends_st_nil : forall st',
      extends_st st' nil
  | extends_st_cons : forall x st' st,
      extends_st st' st ->
      extends_st (x::st') (x::st).
      
Hint Constructors extends_st : core.

Lemma extends_lookup_st : forall l st st',
  l < length st ->
  extends_st st' st ->
  store_lookup l st' = store_lookup l st.
Proof.
intros l st.
generalize dependent l.
induction st.
- intros. inversion H.
- intros.
  destruct st'.
  -- inversion H0.
  -- inversion H0; subst.
     destruct l.
     + unfold store_lookup. simpl. reflexivity.
     + unfold store_lookup. simpl.
       simpl in H.
       assert (H3: l < Datatypes.length st). { lia. }
       eauto.
Qed.

Lemma extends_st_app : forall st t,
  extends_st (st ++ t) st.
Proof.
intros.
induction st.
- simpl. apply extends_st_nil.
- simpl. apply extends_st_cons. assumption.
Qed.

(* end of extends equivalent lemmas for stores *)

Lemma length_st_helper : forall st t,
  nth (length st) (st ++ t :: nil) <{unit}> = t.
Proof.
intros.
induction st.
- simpl. reflexivity.
- simpl. assumption.
Qed.

Lemma length_ST_helper : forall ST T,
  nth (length ST) (ST ++ T :: nil) <{Unit}> = T.
Proof.
intros.
induction ST.
- simpl. reflexivity.
- simpl. assumption.
Qed.

Lemma store_well_typed_app : forall ST st t1 T1,
  store_well_typed ST st ->
  empty ; ST |- t1 \in T1 ->
  store_well_typed (ST ++ T1::nil) (st ++ t1::nil).
Proof.
intros.
unfold store_well_typed in *.
destruct H.
split.
- rewrite app_length. rewrite app_length. simpl.
  rewrite H. reflexivity.
- intros.
  apply store_weakening with (ST := ST) (ST' := ST ++ T1 :: nil).
  -- apply extends_app.
  -- rewrite app_length in H2. simpl in H2.
     inversion H2.
     + assert (H5: l = length st). { lia. }
       unfold store_lookup.
       unfold store_Tlookup.
       assert (H6: (nth (Datatypes.length st) (st ++ t1 :: nil) <{unit}>) = t1).
       {  apply length_st_helper. }
       assert (H7: (nth (Datatypes.length st) (ST ++ T1 :: nil) <{Unit}>) = T1).
       {  rewrite <- H. apply length_ST_helper. }
       rewrite H5.
       rewrite H6. rewrite H7.
       assumption.
     + assert (H5: l < length st). { lia. }
       assert (H6: store_Tlookup l (ST ++ T1 :: nil) = store_Tlookup l ST).
       {
         apply extends_lookup. rewrite <- H in H5. assumption. apply extends_app.
       }
       rewrite H6.
       assert (H7: store_lookup l (st ++ t1 :: nil) = store_lookup l st).
       {
         apply extends_lookup_st. assumption. apply extends_st_app.
       }
       rewrite H7.
       eauto.
Qed.          

(* this is what we proved specifically for st and ST above
   (the helper theorems)! *)        
Lemma nth_eq_last : forall A (l:list A) x d,
  nth (length l) (l ++ x::nil) d = x.
Proof.
intros.
induction l.
- simpl. reflexivity.
- simpl. assumption.
Qed.

Theorem preservation : forall ST t t' T st st',
  empty ; ST |- t \in T ->
  store_well_typed ST st ->
  t / st --> t' / st' ->
  exists ST',
     extends ST' ST /\
     empty ; ST' |- t' \in T /\
     store_well_typed ST' st'.
Proof.
intros.
remember empty as Gamma.
generalize dependent t'.
induction H.
- rewrite HeqGamma in H. inversion H.
- intros. inversion H1.
- intros. inversion H2; subst.
  -- exists ST. split.
     + apply extends_refl.
     + split.
       ++ apply substitution_preserves_typing with (U := T2).
          +++ inversion H. subst. assumption.
          +++ assumption.
       ++ assumption.
  -- apply IHhas_type1 in H4.
     + destruct H4. destruct H3. destruct H4.
       exists x0. split.
       ++ assumption.
       ++ split.
          +++ apply T_App with (T2 := T2). assumption. 
              apply store_weakening with (ST := ST). assumption. assumption.
          +++ assumption.
     + reflexivity.
  -- apply IHhas_type2 in H9.
     + destruct H9. destruct H3. destruct H4.
       exists x0. split.
       ++ assumption.
       ++ split.
          +++ apply T_App with (T2 := T2).
              apply store_weakening with (ST := ST). assumption. assumption. assumption.
          +++ assumption.
     + reflexivity.
- intros. inversion H1.
- intros. inversion H1; subst.
  -- exists ST. split.
     + apply extends_refl.
     + split.
       ++ apply T_Nat.
       ++ assumption.
  -- apply IHhas_type in H3.
     + destruct H3. destruct H2. destruct H3.
       exists x0. split.
       ++ assumption.
       ++ split.
          +++ apply T_Succ. assumption.
          +++ assumption.
     + reflexivity.
- intros. inversion H1; subst.
  -- exists ST. split.
     + apply extends_refl.
     + split.
       ++ apply T_Nat.
       ++ assumption.
  -- apply IHhas_type in H3.
     + destruct H3. destruct H2. destruct H3.
       exists x0. split.
       ++ assumption.
       ++ split.
          +++ apply T_Pred. assumption.
          +++ assumption.
     + reflexivity.
- intros. inversion H2; subst.
  -- exists ST.
     + split.
       ++ apply extends_refl.
       ++ split.
          +++ apply T_Nat.
          +++ assumption.
  -- apply IHhas_type1 in H4.
     + destruct H4. destruct H3. destruct H4.
       exists x0. split.
       ++ assumption.
       ++ split.
          +++ apply T_Mult. 
              ++++ assumption.
              ++++ apply store_weakening with (ST := ST). assumption. assumption.
          +++ assumption.
     + reflexivity.
  -- apply IHhas_type2 in H9.
     + destruct H9. destruct H3. destruct H4.
       exists x0. split.
       ++ assumption.
       ++ split.
          +++ apply T_Mult.
              ++++ apply store_weakening with (ST := ST). assumption. assumption.
              ++++ assumption.
          +++ assumption.
     + reflexivity.
- intros. inversion H3; subst.
  -- apply IHhas_type1 in H5.
     + destruct H5. destruct H4. destruct H5.
       exists x0. split.
       ++ assumption.
       ++ split.
          +++ apply T_If0.
              ++++ assumption.
              ++++ apply store_weakening with (ST := ST). assumption. assumption.
              ++++ apply store_weakening with (ST := ST). assumption. assumption. 
          +++ assumption.
     + reflexivity.
  -- exists ST. split.
     + apply extends_refl.
     + split. assumption. assumption.
  -- exists ST. split.
     + apply extends_refl.
     + split. assumption. assumption.
- intros. inversion H1.
- intros. inversion H1.
- intros. inversion H1; subst.
  -- exists (ST ++ T1 :: nil). split.
     + apply extends_app.
     + split.
       ++ assert (H4: store_Tlookup (length st) (ST ++ T1 :: nil) = <{T1}>). 
          { 
            inversion H0.
            rewrite <- H2.
            unfold store_Tlookup.
            apply nth_eq_last.
          }
          rewrite <- H4 at 2.
          apply T_Loc with (ST := (ST ++ T1 :: nil)).
          assert (H5: length st = length ST). { inversion H0. symmetry. assumption. }
          rewrite H5. rewrite app_length. simpl. lia.
       ++ apply store_well_typed_app. assumption. assumption.
  -- apply IHhas_type in H3.
     + destruct H3. destruct H2. destruct H3.
       exists x0. split.
       ++ assumption.
       ++ split.
          +++ apply T_Ref. assumption.
          +++ assumption.
     + reflexivity.
- intros. inversion H1; subst.
  -- exists ST. split.
     + apply extends_refl.
     + split.
       ++ inversion H; subst. inversion H0.
          apply H4. assumption.
       ++ assumption.
  -- apply IHhas_type in H3.
     + destruct H3. destruct H2. destruct H3.
       exists x0. split.
       ++ assumption.
       ++ split.
          +++ apply T_Deref. assumption.
          +++ assumption.
     + reflexivity.
- intros. inversion H2; subst.
  -- exists ST. split.
     + apply extends_refl.
     + split.
       ++ apply T_Unit.
       ++ apply assign_pres_store_typing.
          +++ assumption.
          +++ assumption.
          +++ inversion H. subst. assumption.
  -- apply IHhas_type1 in H4.
     destruct H4. destruct H3. destruct H4.
     exists x0. split.
     + assumption.
     + split.
       ++ apply T_Assign with (T2 := T2). 
          +++ assumption.
          +++ apply store_weakening with (ST := ST). assumption. assumption.
       ++ assumption.
     + reflexivity.
  -- apply IHhas_type2 in H9.
     destruct H9. destruct H3. destruct H4.
     exists x0. split.
     + assumption.
     + split.
       ++ apply T_Assign with (T2 := T2).
          +++ apply store_weakening with (ST := ST). assumption. assumption.
          +++ assumption.
       ++ assumption.
     + reflexivity.
Qed.   
   
(* Informal proof of the preservation theorem *)
(*

Proof by induction on t \in T after generalize dependent on t'.

T_Var, T_Abs, T_Unit, T_Nat, and T_Loc are straightforward (they cannot reduce)

T_App - three cases:
1. t1 is an abstraction, in which case both st and ST don't undergo
   any changes because of the reduction (the reduction is simply
   substitution of the abstraction binding variable in the abstraction
   body with the second term of the appication (operand).
   Application of the substitution_preserves_typing lemma, along with
   other trivial lemmas like extends_refl proves the goals
2. t1 reduces to  t1', in which case, a strightforward application of
   the induction hypothesis combined with the reduction rule t1 --> t1'
   and the store_weakening lemma prove the goal
3. t2 reduces to t2' - similar to #2 above

T_Succ - two cases:
1. t1 is succ n, in which case it reduces to (S n), and a straightforward application 
   of T_Nat proves the goal
2. t1 reduces to t1', in which case, a strightforward application of
   the induction hypothesis combined with the reduction rule t1 --> t1'
   prove the goal

T_Pred - similar to T_Succ

T_Mult - similar to T_App, but with the first case proved by a simple application
of T_Nat. The second and third case proved exactly along the same lines as those
for T_App

T_If0 - three cases:
1. t1 reduces to t1' - in which case, a strightforward application of
   the induction hypothesis combined with the reduction rule t1 --> t1'
   prove the goal
2. t1 is 0 - proved using existing assumptions and extends_refl
3. t1 is non-zero - same as above

T_Ref -
ref t1 / st --> t' / st' can arise because of two cases:
1. t1 is a value (rule T_RefValue):
   in which case, there exists ST' = ST ++ T1
   a) sub goal #1 is proved by extends_app (ST' obviously extends ST) 
   b) sub goal #2 is proved by substituting for Ref T1 with
      store_Tlookup (length ST') ST' and applying T_Loc
   c) sub goal #3 is proved by the lemma applying store_well_typed_app
2. t1 reduces to  t1' (and hence ref t1 reduces to ref t1'):
   in which case, a strightforward application of the induction hypothesis
   combined with the reduction rule t1 --> t1' proves the goal

T_Deref - two case:
1. reduction/dereferencing of a loc term - in which case both st and ST don't undergo
   any changes because of the reduction and a straightforward inversion of hypotheses
   proves the goal
2. reduction of a non-loc term - in which case, a strightforward application 
   of the induction hypothesis combined with the reduction rule t1 --> t1'
   and T_Deref proves the goal

T_Assign - three cases:
1. Assignment to a loc - in which case both st and ST don't undergo
   any changes because of the reduction.
   Application of the assign_pres_store_typing lemma, along with
   other trivial lemmas like extends_refl proves the goals
2. t1 reduces to  t1', in which case, a strightforward application of
   the induction hypothesis combined with the reduction rule t1 --> t1'
   and the store_weakening lemma prove the goal
3. t2 reduces to t2' - similar to #2 above

*)

(* End of informal proof of the preservation theorem *)
          
Theorem progress : forall ST t T st,
  empty ; ST |- t \in T ->
  store_well_typed ST st ->
  (value t \/ exists t' st', t / st --> t' / st').
remember empty as Gamma.

intros.
induction H.
- rewrite HeqGamma in H. inversion H.
- left. apply v_abs.
- right.
   pose proof (IHhas_type1 HeqGamma) as H2.
   pose proof (IHhas_type2 HeqGamma) as H3.
   destruct H2.
   destruct H3.
   + destruct H2.
     ++ exists <{[x0 := t2] t1}>, st. apply ST_AppAbs. assumption.
     ++ inversion H.
     ++ inversion H.
     ++ inversion H.
   + destruct H3. destruct H3.
     exists <{ t1 x0 }>, x1. apply ST_App2. assumption. assumption.
   + destruct H2. destruct H2.
     exists <{ x0 t2 }>, x1. apply ST_App1. assumption.
- left. apply v_nat.
- right. pose proof (IHhas_type HeqGamma) as H1.
  destruct H1.
  + inversion H1; subst.
    ++ inversion H.
    ++ exists <{ {S n} }>, st. apply ST_SuccNat.
    ++ inversion H.
    ++ inversion H.
  + destruct H1. destruct H1. exists <{ succ x0 }>, x1. apply ST_Succ. assumption.
- right. pose proof (IHhas_type HeqGamma) as H1.
  destruct H1.
  + inversion H1; subst.
    ++ inversion H.
    ++ exists <{ {tm_const (n-1)} }>, st. apply ST_PredNat.
    ++ inversion H.
    ++ inversion H.
  + destruct H1. destruct H1. exists <{ pred x0 }>, x1. apply ST_Pred. assumption.
- right. 
  pose proof (IHhas_type1 HeqGamma) as H2.
  pose proof (IHhas_type2 HeqGamma) as H3.
  destruct H2.
  + destruct H3.
    ++ inversion H2; subst.
       +++ inversion H.
       +++ destruct H3.
           ++++ inversion H1.
           ++++ exists <{ {tm_const (n * n0)} }>, st. apply ST_MultNats.
           ++++ inversion H1.
           ++++ inversion H1.
       +++ inversion H.
       +++ inversion H.
    ++ destruct H3. destruct H3. exists <{ t1 * x0 }>, x1.
       apply ST_Mult2. assumption. assumption.
  + destruct H3.
    ++ destruct H2. destruct H2. exists <{ x0 * t2 }>, x1. apply ST_Mult1. assumption.
    ++ destruct H2. destruct H2. exists <{ x0 * t2 }>, x1. apply ST_Mult1. assumption.  
- right.
  pose proof (IHhas_type1 HeqGamma) as H3.
  destruct H3.
  + destruct H3.
    ++ inversion H.
    ++ destruct n.
       +++ exists <{t2}>, st. apply ST_If0_Zero.
       +++ exists <{t3}>, st. apply ST_If0_Nonzero.
    ++ inversion H.
    ++ inversion H.
  + destruct H3. destruct H3.
    exists <{ if0 x0 then t2 else t3}>, x1. apply ST_If0. assumption.
- left. apply v_unit.
- left. apply v_loc.
- right.
  pose proof (IHhas_type HeqGamma) as H1.
  destruct H1.
  + destruct H1.
    ++ exists <{ loc { length st } }> , (st ++ <{ \ {x0} : {T2}, {t1} }>::nil).
       apply ST_RefValue. apply v_abs.
    ++ exists <{ loc { length st } }> , (st ++ <{ {tm_const n} }>::nil).
       apply ST_RefValue. apply v_nat.
    ++ exists <{ loc { length st } }> , (st ++ <{ unit }>::nil).
       apply ST_RefValue. apply v_unit.
    ++ exists <{ loc { length st } }> , (st ++ <{ (loc l) }>::nil).
       apply ST_RefValue. apply v_loc.
  + destruct H1. destruct H1.
    exists <{ ref x0 }>, x1. apply ST_Ref. assumption.
- right.
  pose proof (IHhas_type HeqGamma) as H1.
  destruct H1.
  + destruct H1.
    ++ inversion H.
    ++ inversion H.
    ++ inversion H.
    ++ exists <{ {store_lookup l st} }>, st. apply ST_DerefLoc.
       inversion H. inversion H0. rewrite H5 in H4. assumption.
  + destruct H1. destruct H1.
    exists <{ !x0 }>, x1. apply ST_Deref. assumption.
- right.
  pose proof (IHhas_type1 HeqGamma) as H2.
  pose proof (IHhas_type2 HeqGamma) as H3.
  destruct H2.
  + destruct H3.
    ++ destruct H2.
       +++ inversion H.
       +++ inversion H.
       +++ inversion H.
       +++ exists <{ unit }>, (replace l t2 st). apply ST_Assign. 
           assumption. inversion H. inversion H0.
           rewrite H7 in H6. assumption. 
    ++ destruct H3. destruct H3.
       exists <{ t1 := x0 }>, x1. apply ST_Assign2. assumption. assumption.
  + destruct H2. destruct H2. exists <{ x0 := t2 }>, x1.
    apply ST_Assign1. assumption.
Qed.

Module ExampleVariables.

Open Scope string_scope.

Definition x := "x".
Definition y := "y".
Definition r := "r".
Definition s := "s".

End ExampleVariables.

Module RefsAndNontermination.
Import ExampleVariables.

Definition loop_fun :=
  <{ \x : Unit, (!r) unit }>.
  
Definition loop :=
  <{ (\r : Ref (Unit -> Unit), (( r := loop_fun ); ( (! r) unit ) )) (ref (\x : Unit, unit)) }> .
  
Lemma loop_typeable : exists T, empty; nil |- loop \in T.
Proof.
unfold loop.
(* exists (Ty_Arrow (Ty_Ref (Ty_Arrow Ty_Unit Ty_Unit)) Ty_Unit). *)
exists Ty_Unit.
eapply T_App.
- apply T_Abs.
  unfold tseq.
  eapply T_App.
  -- apply T_Abs.
     eapply T_App.
     + apply T_Deref.
       apply T_Var. rewrite update_permute.
       ++ rewrite update_eq. reflexivity.
       ++ unfold not. intros. inversion H.
     + apply T_Unit.
  -- unfold loop_fun.
     eapply T_Assign.
     + apply T_Var. rewrite update_eq. reflexivity.
     + apply T_Abs.
       eapply T_App.
       ++ apply T_Deref.
          apply T_Var.
          rewrite update_permute.
          +++ rewrite update_eq. reflexivity.
          +++ unfold not. intros. inversion H.
       ++ apply T_Unit.
- apply T_Ref.
  apply T_Abs.
  apply T_Unit. 
Qed.

Inductive step_closure {X:Type} (R: relation X) : X -> X -> Prop :=
  | sc_one : forall (x y : X),
                R x y -> step_closure R x y
  | sc_step : forall (x y z : X),
                R x y ->
                step_closure R y z ->
                step_closure R x z.
                
Definition multistep1 := (step_closure step).
Notation "t1 '/' st '-->+' t2 '/' st'" :=
        (multistep1 (t1,st) (t2,st'))
        (at level 40, st at level 39, t2 at level 39).  
  
Ltac print_goal := match goal with |- ?x => idtac x end.
Ltac reduce :=
    repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; compute)];
            try solve [apply multi_refl]).
            
Lemma loop_steps_to_loop_fun :
  loop / nil -->*
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil.
Proof.
  unfold loop.
  reduce.
Qed.

Lemma loop_fun_step_self :
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil -->+
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil.
Proof.
eapply sc_step.
- apply ST_App1. apply ST_DerefLoc. simpl. lia.
- unfold store_lookup. simpl.
  apply sc_one.
  apply ST_AppAbs. apply v_unit.   
Qed.  

Definition fact_fun : tm :=
  <{ \x : Nat, (if0 x then 1 else (x * ((!r) (pred x)))) }>.

Definition factorial : tm :=
  <{ (\s: Nat, 
        ((\r : Ref (Nat -> Nat), (( r := fact_fun ); ( (! r) s ) )) (ref (\x : Nat, x)))) }> .

Lemma factorial_type : empty; nil |- factorial \in (Nat -> Nat).
Proof.
unfold factorial.
apply T_Abs.
eapply T_App.
- apply T_Abs.
  unfold fact_fun.
  eapply T_App.
  -- apply T_Abs.
     eapply T_App.
     + apply T_Deref.
       apply T_Var.
       rewrite update_permute.
       ++ rewrite update_eq. reflexivity.
       ++ unfold not. intros. inversion H.
     + apply T_Var.
       reflexivity.
  -- eapply T_Assign.
     + apply T_Var. reflexivity.
     + apply T_Abs.
       apply T_If0.
       ++ apply T_Var. reflexivity.
       ++ apply T_Nat.
       ++ apply T_Mult.
          +++ apply T_Var. reflexivity.
          +++ eapply T_App.
              ++++ apply T_Deref. apply T_Var. reflexivity.
              ++++ apply T_Pred. apply T_Var. reflexivity.
- apply T_Ref. apply T_Abs. apply T_Var. reflexivity. 
Qed.

Lemma factorial_4 : exists st,
  <{ factorial 4 }> / nil -->* tm_const 24 / st.
Proof.
  eexists. unfold factorial. reduce.
Qed.

                 