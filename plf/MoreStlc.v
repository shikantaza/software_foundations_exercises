Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.

(*
halve = fix
         (\f:Nat->Nat
            \x:Nat,
               if x=0 then 0
               else if (pred x)=0 then 0
               else 1 + (f (pred (pred x))))
*)

(*
(fact 1)
-> (fix (\f:Nat->Nat,\x:Nat, if x=0 then 1 else x * (f (pred x)))) 1
-> (\x:Nat, if x=0 then 1 else x * (fix f (pred x))) 1
-> if 1=0 then 1 else 1 * (fix f (pred 1))
-> 1 * (fix f (pred 1)
-> 1 * ((\x:Nat, if x=0 then 1 else x * (fix f (pred x)) 0)
-> 1 * if 0=0 then 1 else 0 * (fix f (pred 0))
-> 1 * 1
-> 1
*)

Module STLCExtended.

Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat : ty
  | Ty_Sum : ty -> ty -> ty
  | Ty_List : ty -> ty
  | Ty_Unit : ty
  | Ty_Prod : ty -> ty -> ty.
  
Inductive tm : Type :=
  (* pure STLC *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* numbers *)
  | tm_const: nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0 : tm -> tm -> tm -> tm
  (* sums *)
  | tm_inl : ty -> tm -> tm
  | tm_inr : ty -> tm -> tm
  | tm_case : tm -> string -> tm -> string -> tm -> tm
          (* i.e., case t0 of inl x1 => t1 | inr x2 => t2 *)
  (* lists *)
  | tm_nil : ty -> tm
  | tm_cons : tm -> tm -> tm
  | tm_lcase : tm -> tm -> string -> string -> tm -> tm
           (* i.e., case t1 of | nil => t2 | x::y => t3 *)
  (* unit *)
  | tm_unit : tm

  (* You are going to be working on the following extensions: *)

  (* pairs *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
  (* let *)
  | tm_let : string -> tm -> tm -> tm
         (* i.e., let x = t1 in t2 *)
  (* fix *)
  | tm_fix : tm -> tm.
  
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Declare Custom Entry stlc_ty.

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "( x )" := x (in custom stlc_ty, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc_ty at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "{ x }" := x (in custom stlc at level 1, x constr).

Notation "'Nat'" := Ty_Nat (in custom stlc_ty at level 0).
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

Notation "S + T" :=
  (Ty_Sum S T) (in custom stlc_ty at level 3, left associativity).
Notation "'inl' T t" := (tm_inl T t) (in custom stlc at level 0,
                                         T custom stlc_ty at level 0,
                                         t custom stlc at level 0).
Notation "'inr' T t" := (tm_inr T t) (in custom stlc at level 0,
                                         T custom stlc_ty at level 0,
                                         t custom stlc at level 0).
Notation "'case' t0 'of' '|' 'inl' x1 '=>' t1 '|' 'inr' x2 '=>' t2" :=
  (tm_case t0 x1 t1 x2 t2) (in custom stlc at level 89,
                               t0 custom stlc at level 99,
                               x1 custom stlc at level 99,
                               t1 custom stlc at level 99,
                               x2 custom stlc at level 99,
                               t2 custom stlc at level 99,
                               left associativity).
                               
Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc_ty at level 2, X custom stlc_ty, Y custom stlc_ty at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 0).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 0).
Notation "'List' T" :=
  (Ty_List T) (in custom stlc_ty at level 4).
Notation "'nil' T" := (tm_nil T) (in custom stlc at level 0, T custom stlc_ty at level 0).
Notation "h '::' t" := (tm_cons h t) (in custom stlc at level 2, right associativity).
Notation "'case' t1 'of' '|' 'nil' '=>' t2 '|' x '::' y '=>' t3" :=
  (tm_lcase t1 t2 x y t3) (in custom stlc at level 89,
                              t1 custom stlc at level 99,
                              t2 custom stlc at level 99,
                              x constr at level 1,
                              y constr at level 1,
                              t3 custom stlc at level 99,
                              left associativity).
                              
Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc_ty at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).

Notation "'let' x '=' t1 'in' t2" :=
  (tm_let x t1 t2) (in custom stlc at level 0).
  
Notation "'fix' t" := (tm_fix t) (in custom stlc at level 0).

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
  (* sums *)
  | <{inl T2 t1}> =>
      <{inl T2 ( [x:=s] t1) }>
  | <{inr T1 t2}> =>
      <{inr T1 ( [x:=s] t2) }>
  | <{case t0 of | inl y1 => t1 | inr y2 => t2}> =>
      <{case ([x:=s] t0) of
         | inl y1 => { if String.eqb x y1 then t1 else <{ [x:=s] t1 }> }
         | inr y2 => {if String.eqb x y2 then t2 else <{ [x:=s] t2 }> } }>
  (* lists *)
  | <{nil _}> =>
      t
  | <{t1 :: t2}> =>
      <{ ([x:=s] t1) :: [x:=s] t2 }>
  | <{case t1 of | nil => t2 | y1 :: y2 => t3}> =>
      <{case ( [x:=s] t1 ) of
        | nil => [x:=s] t2
        | y1 :: y2 =>
        {if String.eqb x y1 then
           t3
         else if String.eqb x y2 then t3
              else <{ [x:=s] t3 }> } }>
  (* unit *)
  | <{unit}> => <{unit}>

  (* Complete the following cases. *)

  (* pairs *)
  | <{ (t1, t2) }> => <{ ([x:=s] t1, [x:=s] t2) }>
  | tm_fst t1 => tm_fst <{ [x:=s] t1 }>
  | tm_snd t1 => tm_snd <{ [x:=s] t1 }>
  
  (* let *)
  | <{ let y = t1 in t2 }> =>
     if String.eqb x y then
        (* <{ let y = t1 in t2 }> *)
        <{ let y = [x:=s]t1 in t2 }>
      else
        <{ let y = [x:=s]t1 in [x:=s]t2 }>
        
  (* fix *)
  | <{ fix (\xf:T1, t1) }> =>
      if String.eqb x xf then
         t
      else
         <{ fix (\xf:T1, [x:=s]t1) }>
  | <{ fix t1 }> => <{ fix [x:=s]t1 }>
  (* | _ => t *) (* ... and delete this line when you finish the exercise *)
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Inductive value : tm -> Prop :=
  (* In pure STLC, function abstractions are values: *)
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  (* Numbers are values: *)
  | v_nat : forall n : nat,
      value <{n}>
  (* A tagged value is a value:  *)
  | v_inl : forall v T1,
      value v ->
      value <{inl T1 v}>
  | v_inr : forall v T1,
      value v ->
      value <{inr T1 v}>
  (* A list is a value iff its head and tail are values: *)
  | v_lnil : forall T1, value <{nil T1}>
  | v_lcons : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{v1 :: v2}>
  (* A unit is always a value *)
  | v_unit : value <{unit}>
  (* A pair is a value if both components are: *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{(v1, v2)}>.
      
Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  (* pure STLC *)
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
  (* numbers *)
  | ST_Succ : forall t1 t1',
         t1 --> t1' ->
         <{succ t1}> --> <{succ t1'}>
  | ST_SuccNat : forall n : nat,
         <{succ n}> --> <{ {S n} }>
  | ST_Pred : forall t1 t1',
         t1 --> t1' ->
         <{pred t1}> --> <{pred t1'}>
  | ST_PredNat : forall n:nat,
         <{pred n}> --> <{ {n - 1} }>
  | ST_Mulconsts : forall n1 n2 : nat,
         <{n1 * n2}> --> <{ {n1 * n2} }>
  | ST_Mult1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 * t2}> --> <{t1' * t2}>
  | ST_Mult2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 * t2}> --> <{v1 * t2'}>
  | ST_If0 : forall t1 t1' t2 t3,
         t1 --> t1' ->
         <{if0 t1 then t2 else t3}> --> <{if0 t1' then t2 else t3}>
  | ST_If0_Zero : forall t2 t3,
         <{if0 0 then t2 else t3}> --> t2
  | ST_If0_Nonzero : forall n t2 t3,
         <{if0 {S n} then t2 else t3}> --> t3
  (* sums *)
  | ST_Inl : forall t1 t1' T2,
        t1 --> t1' ->
        <{inl T2 t1}> --> <{inl T2 t1'}>
  | ST_Inr : forall t2 t2' T1,
        t2 --> t2' ->
        <{inr T1 t2}> --> <{inr T1 t2'}>
  | ST_Case : forall t0 t0' x1 t1 x2 t2,
        t0 --> t0' ->
        <{case t0 of | inl x1 => t1 | inr x2 => t2}> -->
        <{case t0' of | inl x1 => t1 | inr x2 => t2}>
  | ST_CaseInl : forall v0 x1 t1 x2 t2 T2,
        value v0 ->
        <{case inl T2 v0 of | inl x1 => t1 | inr x2 => t2}> --> <{ [x1:=v0]t1 }>
  | ST_CaseInr : forall v0 x1 t1 x2 t2 T1,
        value v0 ->
        <{case inr T1 v0 of | inl x1 => t1 | inr x2 => t2}> --> <{ [x2:=v0]t2 }>
  (* lists *)
  | ST_Cons1 : forall t1 t1' t2,
       t1 --> t1' ->
       <{t1 :: t2}> --> <{t1' :: t2}>
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       <{v1 :: t2}> --> <{v1 :: t2'}>
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
       t1 --> t1' ->
       <{case t1 of | nil => t2 | x1 :: x2 => t3}> -->
       <{case t1' of | nil => t2 | x1 :: x2 => t3}>
  | ST_LcaseNil : forall T1 t2 x1 x2 t3,
       <{case nil T1 of | nil => t2 | x1 :: x2 => t3}> --> t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
       value v1 ->
       value vl ->
       <{case v1 :: vl of | nil => t2 | x1 :: x2 => t3}>
         --> <{ [x2 := vl] ([x1 := v1] t3) }>

  (* Add rules for the following extensions. *)

  (* pairs *)
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
  | ST_FstPair: forall v1 v2,
       value v1 ->
       value v2 ->
       <{ (v1, v2).fst }> --> <{ v1 }>
  | ST_Snd1 : forall t1 t1',
       t1 --> t1' ->
       <{ t1.snd }> --> <{ t1'.snd }>
  | ST_SndPair: forall v1 v2,
       value v1 ->
       value v2 ->
       <{ (v1, v2).snd }> --> <{ v2 }>
       
  (* let *)
  | ST_Let1 : forall x t1 t1' t2,
       t1 --> t1' ->
       <{ let x = t1 in t2 }> --> <{ let x = t1' in t2 }>
  | ST_LetValue : forall x v1 t2,
       value v1 ->
       <{ let x= v1 in t2 }> --> <{ [x:=v1]t2 }>
       
  (* fix *)
  | ST_Fix1 : forall t1 t1',
       t1 --> t1' ->
       <{ fix t1 }> --> <{ fix t1' }>
  | ST_FixAbs : forall xf t1 T1,
       <{ fix (\xf:T1, t1) }> --> <{ [xf := fix (\xf:T1, t1)] t1 }>
   

  where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40, t custom stlc, T custom stlc_ty at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
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
  (* numbers *)
  | T_Nat : forall Gamma (n : nat),
      Gamma |- n \in Nat
  | T_Succ : forall Gamma t,
      Gamma |- t \in Nat ->
      Gamma |- succ t \in Nat
  | T_Pred : forall Gamma t,
      Gamma |- t \in Nat ->
      Gamma |- pred t \in Nat
  | T_Mult : forall Gamma t1 t2,
      Gamma |- t1 \in Nat ->
      Gamma |- t2 \in Nat ->
      Gamma |- t1 * t2 \in Nat
  | T_If0 : forall Gamma t1 t2 t3 T0,
      Gamma |- t1 \in Nat ->
      Gamma |- t2 \in T0 ->
      Gamma |- t3 \in T0 ->
      Gamma |- if0 t1 then t2 else t3 \in T0
  (* sums *)
  | T_Inl : forall Gamma t1 T1 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- (inl T2 t1) \in (T1 + T2)
  | T_Inr : forall Gamma t2 T1 T2,
      Gamma |- t2 \in T2 ->
      Gamma |- (inr T1 t2) \in (T1 + T2)
  | T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T3,
      Gamma |- t0 \in (T1 + T2) ->
      (x1 |-> T1 ; Gamma) |- t1 \in T3 ->
      (x2 |-> T2 ; Gamma) |- t2 \in T3 ->
      Gamma |- (case t0 of | inl x1 => t1 | inr x2 => t2) \in T3
  (* lists *)
  | T_Nil : forall Gamma T1,
      Gamma |- (nil T1) \in (List T1)
  | T_Cons : forall Gamma t1 t2 T1,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in (List T1) ->
      Gamma |- (t1 :: t2) \in (List T1)
  | T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
      Gamma |- t1 \in (List T1) ->
      Gamma |- t2 \in T2 ->
      (x1 |-> T1 ; x2 |-> <{{List T1}}> ; Gamma) |- t3 \in T2 ->
      Gamma |- (case t1 of | nil => t2 | x1 :: x2 => t3) \in T2
  (* unit *)
  | T_Unit : forall Gamma,
      Gamma |- unit \in Unit

  (* Add rules for the following extensions. *)

  (* pairs *)
  | T_Pair : forall Gamma t1 T1 t2 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in T2 ->
      Gamma |- (t1, t2) \in (T1 * T2)
  | T_Fst : forall Gamma t0 T1 T2,
      Gamma |- t0 \in (T1 * T2) ->
      Gamma |- t0.fst \in T1
  | T_Snd : forall Gamma t0 T1 T2,
      Gamma |- t0 \in (T1 * T2) ->
      Gamma |- t0.snd \in T2
      
  (* let *)
  | T_Let : forall Gamma x t1 T1 t2 T2,
      Gamma |- t1 \in T1 ->
      (x |-> T1; Gamma) |- t2 \in T2 ->
      Gamma |- let x = t1 in t2 \in T2
  
  (* fix *)
  | T_Fix : forall Gamma t1 T1,
      Gamma |- t1 \in (T1 -> T1) ->
      Gamma |- fix t1 \in T1

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Module Examples.

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".
Notation processSum := "processSum".
Notation n := "n".
Notation eq := "eq".
Notation m := "m".
Notation evenodd := "evenodd".
Notation even := "even".
Notation odd := "odd".
Notation eo := "eo".

Hint Extern 2 (has_type _ (tm_app _ _) _) =>
  eapply T_App; auto : core.
Hint Extern 2 (has_type _ (tm_lcase _ _ _ _ _) _) =>
  eapply T_Lcase; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.

Module Numtest.

(* tm_test0 (pred (succ (pred (2 * 0))) then 5 else 6 *)
Definition tm_test :=
  <{if0
    (pred
      (succ
        (pred
          (2 * 0))))
    then 5
    else 6}>.

Example typechecks :
  empty |- tm_test \in Nat.
Proof.
  unfold tm_test.
  (* This typing derivation is quite deep, so we need
     to increase the max search depth of auto from the
     default 5 to 10. *)
  auto 10.
Qed.

Example reduces :
  tm_test -->* 5.
Proof.
unfold tm_test.
(* alternately, just apply 'normalize' *)
apply multi_step with (y := <{ if0 pred succ pred 0 then 5 else 6 }>).
- apply ST_If0. apply ST_Pred. apply ST_Succ. apply ST_Pred. apply ST_Mulconsts.
- apply multi_step with (y := <{ if0 pred succ 0 then 5 else 6 }>).
  -- apply ST_If0. apply ST_Pred. apply ST_Succ. apply ST_PredNat.
  -- apply multi_step with (y := <{ if0 pred 1 then 5 else 6 }>).
     --- apply ST_If0. apply ST_Pred. apply ST_SuccNat.
     --- apply multi_step with (y := <{ if0 0 then 5 else 6 }>).
         ---- apply ST_If0. apply ST_PredNat.
         ---- eapply multi_step.
              + apply ST_If0_Zero.
              + apply multi_refl.
Qed.

End Numtest.

Module ProdTest.

Definition tm_test :=
  <{((5,6),7).fst.snd}>.
  
Example typechecks :
  empty |- tm_test \in Nat.
Proof.
unfold tm_test.
eapply T_Snd.
eapply T_Fst.
eapply T_Pair.
- eapply T_Pair.
  -- apply T_Nat.
  -- apply T_Nat.
- apply T_Nat.
Qed.

Example reduces :
  tm_test -->* 6.
Proof.
unfold tm_test.
- eapply multi_step.
  -- apply ST_Snd1.
     apply ST_FstPair.
     --- apply v_pair.
         ---- apply v_nat.
         ---- apply v_nat.
     --- apply v_nat.
  -- eapply multi_step.
     --- apply ST_SndPair.
         ---- apply v_nat.
         ---- apply v_nat.
     --- apply multi_refl.
Qed.

End ProdTest.

Module LetTest.

Definition tm_test :=
  <{let x = (pred 6) in
    (succ x)}>.

Example typechecks :
  empty |- tm_test \in Nat.
Proof.
unfold tm_test.
eapply T_Let.
- apply T_Pred.
  apply T_Nat.
- apply T_Succ.
  apply T_Var.
  rewrite update_eq.
  reflexivity.
Qed.

Example reduces :
  tm_test -->* 6.
Proof.
unfold tm_test.
eapply multi_step.
- apply ST_Let1.
  apply ST_PredNat.
- eapply multi_step.
  -- simpl. apply ST_LetValue. apply v_nat.
  -- eapply multi_step.
     --- simpl. apply ST_SuccNat.
     --- apply multi_refl.
Qed.

End LetTest.

Module Sumtest1.

Definition tm_test :=
  <{case (inl Nat 5) of
    | inl x => x
    | inr y => y}>.
    
Example typechecks :
  empty |- tm_test \in Nat.
Proof.
unfold tm_test.
eapply T_Case.
- apply T_Inl.
  apply T_Nat.
- apply T_Var.
  rewrite update_eq.
  reflexivity.
- apply T_Var.
  rewrite update_eq.
  reflexivity.
Qed.

Example reduces :
  tm_test -->* 5.
Proof.
unfold tm_test.
eapply multi_step.
- apply ST_CaseInl. apply v_nat.
- simpl. apply multi_refl.
Qed.

End Sumtest1.

Module Sumtest2.

Definition tm_test :=
  <{let processSum =
    (\x:Nat + Nat,
      case x of
       | inl n => n
       | inr n => (if0 n then 1 else 0)) in
    (processSum (inl Nat 5), processSum (inr Nat 5))}>.
    
Example typechecks :
  empty |- tm_test \in (Nat * Nat).
Proof.
unfold tm_test.
eapply T_Let.
- apply T_Abs.
  eapply T_Case.
  -- apply T_Var. rewrite update_eq. reflexivity.
  -- apply T_Var. rewrite update_eq. reflexivity.
  -- apply T_If0.
     --- apply T_Var. rewrite update_eq. reflexivity.
     --- apply T_Nat.
     --- apply T_Nat.
- apply T_Pair.
  -- eapply T_App.
     --- apply T_Var. rewrite update_eq. reflexivity.
     --- apply T_Inl. apply T_Nat.
  -- eapply T_App.
     --- apply T_Var. rewrite update_eq. reflexivity.
     --- apply T_Inr. apply T_Nat.
Qed.

Example reduces :
  tm_test -->* <{(5, 0)}>.
Proof.
unfold tm_test.
eapply multi_step.
- apply ST_LetValue.
  apply v_abs.
- eapply multi_step.
  -- simpl.
     apply ST_Pair1.
     apply ST_AppAbs.
     apply v_inl.
     apply v_nat.
  -- simpl.
     eapply multi_step.
     --- apply ST_Pair1.
         apply ST_CaseInl. apply v_nat.
     --- simpl. 
         eapply multi_step.
         ---- apply ST_Pair2.
              ----- apply v_nat.
              ----- apply ST_AppAbs. apply v_inr. apply v_nat.
         ---- eapply multi_step.
              ----- apply ST_Pair2.
                    + apply v_nat.
                    + simpl. apply ST_CaseInr. apply v_nat.
              ----- eapply multi_step.
                    + simpl. apply ST_Pair2. apply v_nat. apply ST_If0_Nonzero.
                    + apply multi_refl.
Qed.

End Sumtest2.

Module ListTest.

Definition tm_test :=
  <{let l = (5 :: 6 :: (nil Nat)) in
    case l of
    | nil => 0
    | x :: y => (x * x)}>.
    
Example typechecks :
  empty |- tm_test \in Nat.
Proof.
unfold tm_test.
eapply T_Let.
- apply T_Cons.
  -- apply T_Nat.
  -- apply T_Cons.
     --- apply T_Nat.
     --- apply T_Nil.
- eapply T_Lcase.
  -- apply T_Var. rewrite update_eq. reflexivity.
  -- apply T_Nat.
  -- apply T_Mult.
     --- apply T_Var. rewrite update_eq. reflexivity.
     --- apply T_Var. rewrite update_eq. reflexivity.
Qed.

Example reduces :
  tm_test -->* 25.
Proof.
unfold tm_test.
eapply multi_step.
- apply ST_LetValue.
  apply v_lcons.
  -- apply v_nat.
  -- apply v_lcons.
     --- apply v_nat.
     --- apply v_lnil.
- simpl. eapply multi_step.
  -- apply ST_LcaseCons.
     --- apply v_nat.
     --- apply v_lcons.
         ---- apply v_nat.
         ---- apply v_lnil.
  -- eapply multi_step.
     --- simpl. apply ST_Mulconsts.
     --- simpl. apply multi_refl.
Qed.

End ListTest.

Module FixTest1.

Definition fact :=
  <{fix
      (\f:Nat->Nat,
        \a:Nat,
         if0 a then 1 else (a * (f (pred a))))}>.
         
Example typechecks :
  empty |- fact \in (Nat -> Nat).
Proof.
unfold fact.
apply T_Fix.
apply T_Abs.
apply T_Abs.
apply T_If0.
- apply T_Var. rewrite update_eq. reflexivity.
- apply T_Nat.
- apply T_Mult.
  -- apply T_Var. rewrite update_eq. reflexivity.
  -- eapply T_App.
     --- apply T_Var. rewrite update_permute.
         ---- rewrite update_eq. reflexivity.
         ---- unfold not. intros. inversion H.
     --- apply T_Pred.
         apply T_Var. rewrite update_eq. reflexivity.
Qed.

Example reduces :
  <{fact 4}> -->* 24.
Proof.
unfold fact.
eapply multi_step.
- apply ST_App1.
  apply ST_FixAbs.
- simpl.
  eapply multi_step.
  -- apply ST_AppAbs.
     apply v_nat.
  -- simpl.
     eapply multi_step.
     --- apply ST_If0_Nonzero.
     --- eapply multi_step.
         ---- apply ST_Mult2.
              + apply v_nat.
              + apply ST_App1.
                ++ apply ST_FixAbs.
         ---- simpl. eapply multi_step.
              + apply ST_Mult2.
                ++ apply v_nat.
                ++ apply ST_App2.
                   +++ apply v_abs.
                   +++ apply ST_PredNat.
              + eapply multi_step.
                ++ simpl. apply ST_Mult2.
                   +++ apply v_nat.
                   +++ apply ST_AppAbs.
                       apply v_nat.
                ++ simpl. eapply multi_step. 
                   +++ apply ST_Mult2. 
                       ++++ apply v_nat. 
                       ++++ apply ST_If0_Nonzero. 
                   +++ eapply multi_step.
                       ++++ apply ST_Mult2.
                              apply v_nat.
                              apply ST_Mult2.
                                apply v_nat.
                                apply ST_App1.
                                apply ST_FixAbs.
                       ++++ eapply multi_step.
                              apply ST_Mult2.
                                apply v_nat.
                                apply ST_Mult2.
                                  apply v_nat. simpl.
                                  apply ST_App2.
                                    apply v_abs.
                                    apply ST_PredNat.
                                    eapply multi_step.
                                      apply ST_Mult2.
                                        apply v_nat.
                                        simpl.
                                        apply ST_Mult2.
                                          apply v_nat.
                                          apply ST_AppAbs.
                                            apply v_nat.
                                            eapply multi_step.
                                              apply ST_Mult2.
                                                apply v_nat.
                                                simpl. apply ST_Mult2.
                                                  apply v_nat.
                                                  apply ST_If0_Nonzero.
                                                  eapply multi_step.
                                                    apply ST_Mult2.
                                                      apply v_nat.
                                                      apply ST_Mult2.
                                                        apply v_nat.
                                                        apply ST_Mult2.
                                                          apply v_nat.
                                                          apply ST_App1.
                                                            apply ST_FixAbs.
                                                            eapply multi_step.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            simpl.
                                                            apply ST_App2.
                                                            apply v_abs.
                                                            apply ST_PredNat.
                                                            eapply multi_step.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            simpl.
                                                            apply ST_AppAbs.
                                                            apply v_nat.
                                                            simpl.
                                                            eapply multi_step.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_If0_Nonzero.
                                                            eapply multi_step.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_App1. (* *) 
                                                            apply ST_FixAbs.
                                                            simpl.
                                                            eapply multi_step.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_App2.
                                                            apply v_abs.
                                                            apply ST_PredNat.
                                                            simpl.
                                                            eapply multi_step.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_AppAbs.
                                                            apply v_nat.
                                                            eapply multi_step.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            simpl.
                                                            apply ST_If0_Zero.
                                                            eapply multi_step.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mulconsts.
                                                            simpl.
                                                            eapply multi_step.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mulconsts.
                                                            simpl.
                                                            eapply multi_step.
                                                            apply ST_Mult2.
                                                            apply v_nat.
                                                            apply ST_Mulconsts.
                                                            eapply multi_step.
                                                            apply ST_Mulconsts.
                                                            simpl.
                                                            apply multi_refl.
Qed.

End FixTest1.

Module FixTest2.

Definition map :=
  <{ \g:Nat->Nat,
       fix
         (\f:(List Nat)->(List Nat),
            \l:List Nat,
               case l of
               | nil => nil Nat
               | x::l => ((g x)::(f l)))}>.
               
Example typechecks :
  empty |- map \in
    ((Nat -> Nat) -> ((List Nat) -> (List Nat))).
Proof.
unfold map.
apply T_Abs.
apply T_Fix.
apply T_Abs.
apply T_Abs.
eapply T_Lcase.
- apply T_Var. rewrite update_eq. reflexivity.
- apply T_Nil.
- apply T_Cons.
  -- eapply T_App.
     --- apply T_Var. 
         rewrite update_neq.
         rewrite update_neq.
         rewrite update_neq.
         rewrite update_neq.
         rewrite update_eq. reflexivity.
         unfold not. intros. inversion H.
         unfold not. intros. inversion H.
         unfold not. intros. inversion H.
         unfold not. intros. inversion H.
     --- apply T_Var.
         rewrite update_eq.
         reflexivity.
  -- eapply T_App.
     --- apply T_Var. 
         rewrite update_neq.
         rewrite update_neq.
         rewrite update_neq.
         rewrite update_eq. reflexivity.
         unfold not. intros. inversion H.
         unfold not. intros. inversion H.
         unfold not. intros. inversion H.
     --- apply T_Var.
         rewrite update_neq.
         rewrite update_eq.
         reflexivity.
         unfold not. intros. inversion H.                
Qed.

Example reduces :
  <{map (\a:Nat, succ a) (1 :: 2 :: (nil Nat))}>
  -->* <{2 :: 3 :: (nil Nat)}>.
Proof.
unfold map.
normalize.
Qed.

End FixTest2.                                    

Module FixTest3.

Definition equal :=
  <{fix
        (\eq:Nat->Nat->Nat,
           \m:Nat, \n:Nat,
             if0 m then (if0 n then 1 else 0)
             else (if0 n
                   then 0
                   else (eq (pred m) (pred n))))}>.
                   
Example typechecks :
  empty |- equal \in (Nat -> Nat -> Nat).
Proof.
unfold equal.
apply T_Fix.
apply T_Abs.
apply T_Abs.
apply T_Abs.
apply T_If0.
- apply T_Var.
  rewrite update_neq. rewrite update_eq. reflexivity.
  unfold not. intros. inversion H.
- apply T_If0.
  -- apply T_Var. rewrite update_eq. reflexivity.
  -- apply T_Nat.
  -- apply T_Nat.
- apply T_If0.
  -- apply T_Var. rewrite update_eq. reflexivity.
  -- apply T_Nat.
  -- eapply T_App.
     --- eapply T_App.
         ---- apply T_Var.
              rewrite update_neq. rewrite update_permute.
              rewrite update_eq. reflexivity.
              unfold not. intros. inversion H.
              unfold not. intros. inversion H.
         ---- apply T_Pred.
              apply T_Var.
              rewrite update_neq. rewrite update_permute.
              rewrite update_neq.
              rewrite update_eq. reflexivity.
              unfold not. intros. inversion H.
              unfold not. intros. inversion H.
              unfold not. intros. inversion H.
     --- apply T_Pred.
         apply T_Var.
         rewrite update_eq. reflexivity.
Qed.

Example reduces :
  <{equal 4 4}> -->* 1.
Proof.
unfold equal.
normalize.
Qed.

Example reduces2 :
  <{equal 4 5}> -->* 0.
Proof.
unfold equal.
normalize.
Qed.

End FixTest3.

Module FixTest4.

Definition eotest :=
<{let evenodd =
         fix
           (\eo: ((Nat -> Nat) * (Nat -> Nat)),
              (\n:Nat, if0 n then 1 else (eo.snd (pred n)),
               \n:Nat, if0 n then 0 else (eo.fst (pred n)))) in
    let even = evenodd.fst in
    let odd = evenodd.snd in
    (even 3, even 4)}>.
    
Example typechecks :
  empty |- eotest \in (Nat * Nat).
Proof.
unfold eotest. eauto 30.
Qed.

Example reduces :
  eotest -->* <{(0, 1)}>.
Proof.
unfold eotest.
normalize.
Qed.

End FixTest4.

End Examples.

Lemma value_nat_lemma : forall t Gamma,
  Gamma |- t \in Nat ->
  value t ->
  exists n : nat, t = n.
Proof.
intros.
inversion H0. 
- rewrite <- H1 in H. inversion H.
- exists n. reflexivity.
- rewrite <- H2 in H. inversion H.
- rewrite <- H2 in H. inversion H.
- rewrite <- H1 in H. inversion H.
- rewrite <- H3 in H. inversion H.
- rewrite <- H1 in H. inversion H.
- rewrite <- H3 in H. inversion H.
Qed.

Lemma value_sum_lemma : forall t Gamma T1 T2,
  Gamma |- t \in (T1 + T2) ->
  value t ->
  exists t', value t' /\ (t = <{inl T2 t'}> \/ t = <{inr T1 t'}>).
Proof.
intros.
inversion H0.
- rewrite <- H1 in H. inversion H.
- rewrite <- H1 in H. inversion H.
- rewrite <- H2 in H. inversion H. subst. 
  exists v. split. assumption. left. reflexivity.
- rewrite <- H2 in H. inversion H. subst. 
  exists v. split. assumption. right. reflexivity.
- rewrite <- H1 in H. inversion H.
- rewrite <- H3 in H. inversion H.
- rewrite <- H1 in H. inversion H.
- rewrite <- H3 in H. inversion H.
Qed.

Lemma value_list_lemma : forall t T Gamma,
  Gamma |- t \in (List T) ->
  value t ->
  t = <{nil T}> \/ exists x1 x2, value x1 /\ value x2 /\ t = <{ x1 :: x2 }>.
Proof.
intros.
inversion H0.
- rewrite <- H1 in H. inversion H.
- rewrite <- H1 in H. inversion H.
- rewrite <- H2 in H. inversion H.
- rewrite <- H2 in H. inversion H.
- left. rewrite <- H1 in H. inversion H. subst. reflexivity.
- right. exists v1, v2. split. assumption. split. assumption. reflexivity.
- rewrite <- H1 in H. inversion H.
- rewrite <- H3 in H. inversion H.
Qed.

Lemma value_pair_lemma : forall t T1 T2 Gamma,
  Gamma |- t \in (T1 * T2) ->
  value t ->
  exists v1 v2, value v1 /\ value v2 /\ t = <{ (v1, v2) }>.
Proof.
intros.
inversion H0.
- rewrite <- H1 in H. inversion H.
- rewrite <- H1 in H. inversion H.
- rewrite <- H2 in H. inversion H.
- rewrite <- H2 in H. inversion H.
- rewrite <- H1 in H. inversion H.
- rewrite <- H3 in H. inversion H.
- rewrite <- H1 in H. inversion H.
- rewrite <- H3 in H. inversion H. subst.
  exists v1, v2. split. assumption. split. assumption. reflexivity.
Qed.

Lemma value_abs_lemma : forall t T1 T2 Gamma,
  Gamma |- t \in (T1 -> T2) ->
  value t ->
  exists x0 t1, t = <{\x0 : T1, t1 }>.
Proof.
intros.
inversion H0.
- rewrite <- H1 in H. inversion H. subst.
  exists x0, t1. reflexivity.
- rewrite <- H1 in H. inversion H.
- rewrite <- H2 in H. inversion H.
- rewrite <- H2 in H. inversion H.
- rewrite <- H1 in H. inversion H.
- rewrite <- H3 in H. inversion H.
- rewrite <- H1 in H. inversion H.
- rewrite <- H3 in H. inversion H.
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
- destruct IHhas_type1.
  -- apply HeqGamma.
  -- destruct IHhas_type2.
     --- apply HeqGamma.
     --- destruct H1.
         + right. exists <{ [x0:=t2]t1 }>.
           apply ST_AppAbs. assumption.
         + inversion H.
         + inversion H.
         + inversion H.
         + inversion H.
         + inversion H.
         + inversion H.
         + inversion H.
     --- destruct H2. 
         right. exists <{t1 x0 }>.
         apply ST_App2. assumption. assumption.
  -- destruct H1. right.
     exists <{x0 t2}>.
     apply ST_App1. assumption.
- left. apply v_nat.
- pose proof (IHhas_type HeqGamma) as H1.
  destruct H1.
  -- right.
     inversion H0.
     --- rewrite <- H1 in H. inversion H.
     --- exists <{ {S n} }>. apply ST_SuccNat.
     --- rewrite <- H2 in H. inversion H.
     --- rewrite <- H2 in H. inversion H.
     --- rewrite <- H1 in H. inversion H.
     --- rewrite <- H3 in H. inversion H.
     --- rewrite <- H1 in H. inversion H.
     --- rewrite <- H3 in H. inversion H.
  -- destruct H0.
     right. exists <{ succ x0 }>. apply ST_Succ. assumption.
- pose proof (IHhas_type HeqGamma) as H1.
  destruct H1.
  -- right.
     inversion H0.
     --- rewrite <- H1 in H. inversion H.
     --- exists <{ {n - 1} }>. apply ST_PredNat.
     --- rewrite <- H2 in H. inversion H.
     --- rewrite <- H2 in H. inversion H.
     --- rewrite <- H1 in H. inversion H.
     --- rewrite <- H3 in H. inversion H.
     --- rewrite <- H1 in H. inversion H.
     --- rewrite <- H3 in H. inversion H.
  -- destruct H0.
     right. exists <{ pred x0 }>. apply ST_Pred. assumption.
- right.
  pose proof (IHhas_type1 HeqGamma) as H1.
  pose proof (IHhas_type2 HeqGamma) as H2.
  destruct H1.
  inversion H1. 
  -- rewrite <- H3 in H; inversion H.
  -- destruct H2.
     --- inversion H2.
         ---- rewrite <- H4 in H0. inversion H0.
         ---- exists <{ {n * n0} }>. apply ST_Mulconsts.
         ---- rewrite <- H5 in H0. inversion H0.
         ---- rewrite <- H5 in H0. inversion H0.
         ---- rewrite <- H4 in H0. inversion H0.
         ---- rewrite <- H6 in H0. inversion H0.
         ---- rewrite <- H4 in H0. inversion H0.
         ---- rewrite <- H6 in H0. inversion H0.
     --- destruct H2.
         exists <{ n * x0 }>. apply ST_Mult2. apply v_nat. assumption.
  -- rewrite <- H4 in H. inversion H.
  -- rewrite <- H4 in H. inversion H.
  -- rewrite <- H3 in H. inversion H.
  -- rewrite <- H5 in H. inversion H.
  -- rewrite <- H3 in H. inversion H.
  -- rewrite <- H5 in H. inversion H.
  -- destruct H2.
     --- inversion H2.
         ---- rewrite <- H3 in H0. inversion H0.
         ---- destruct H1. exists <{ x0 * n }>. apply ST_Mult1. assumption.
         ---- rewrite <- H4 in H0. inversion H0.
         ---- rewrite <- H4 in H0. inversion H0.
         ---- rewrite <- H3 in H0. inversion H0.
         ---- rewrite <- H5 in H0. inversion H0.
         ---- rewrite <- H3 in H0. inversion H0.
         ---- rewrite <- H5 in H0. inversion H0.
     --- destruct H1. exists <{ x0 * t2 }>. apply ST_Mult1. assumption.
- right.
  pose proof (IHhas_type1 HeqGamma) as H2.
  destruct H2.
  -- pose proof (value_nat_lemma t1 Gamma H H2) as H3.
     destruct H3.
     rewrite H3.
     destruct x0.
     --- exists t2. apply ST_If0_Zero.
     --- exists t3. apply ST_If0_Nonzero.
  -- destruct H2.
     exists <{ if0 x0 then t2 else t3 }>. apply ST_If0. assumption.
- pose proof (IHhas_type HeqGamma) as H1.
  destruct H1.
  -- left. apply v_inl. assumption.
  -- destruct H0. right. exists <{ inl T2 x0 }>. apply ST_Inl. assumption.
- pose proof (IHhas_type HeqGamma) as H1.
  destruct H1.
  -- left. apply v_inr. assumption.
  -- destruct H0. right. exists <{ inr T1 x0 }>. apply ST_Inr. assumption.
- pose proof (IHhas_type1 HeqGamma) as H2.
  destruct H2.
  -- right.
     pose proof (value_sum_lemma t0 Gamma T1 T2 H H2) as H3.
     destruct H3.
     destruct H3.
     destruct H4.
     --- rewrite H4. exists <{ [x1 := x0] t1 }>. apply ST_CaseInl. assumption.
     --- rewrite H4. exists <{ [x2 := x0] t2 }>. apply ST_CaseInr. assumption.
  -- right.
     destruct H2.    
     exists <{ case x0 of | inl x1 => t1 | inr x2 => t2 }>.
     apply ST_Case. assumption.
- left. apply v_lnil.
- pose proof (IHhas_type1 HeqGamma) as H1.
  pose proof (IHhas_type2 HeqGamma) as H2.
  destruct H1.
  -- destruct H2.
     --- left. apply v_lcons. assumption. assumption.
     --- destruct H2. right. exists <{ t1 :: x0 }>. apply ST_Cons2. assumption. assumption.
  -- destruct H1.
     destruct H2.
     --- right. exists <{ x0 :: t2}>. apply ST_Cons1. assumption.
     --- right. exists <{ x0 :: t2}>. apply ST_Cons1. assumption.
- right.
  pose proof (IHhas_type1 HeqGamma) as H2.
  destruct H2.
  -- pose proof (value_list_lemma t1 T1 Gamma H H2) as H3.
     destruct H3.
     --- rewrite H3. exists t2. apply ST_LcaseNil.
     --- destruct H3. destruct H3. destruct H3. destruct H4.
         rewrite H5. exists <{ [x2 := x3] ([x1 := x0] t3) }>.
         apply ST_LcaseCons. assumption. assumption.
  -- destruct H2.
     exists <{ case x0 of | nil => t2 | x1 :: x2 => t3 }>. apply ST_Lcase1. assumption.
- left. apply v_unit.
- pose proof (IHhas_type1 HeqGamma) as H1.     
  pose proof (IHhas_type2 HeqGamma) as H2.
  destruct H1.
  -- destruct H2.
     --- left. apply v_pair. assumption. assumption.
     --- destruct H2. right. exists <{ (t1, x0) }>. apply ST_Pair2. assumption. assumption.
  -- destruct H2.
     --- right. destruct H1. exists <{ (x0, t2) }>. apply ST_Pair1. assumption.
     --- right. destruct H1. exists <{ (x0, t2) }>. apply ST_Pair1. assumption.
- right.
  pose proof (IHhas_type HeqGamma) as H1.
  destruct H1.
  -- pose proof (value_pair_lemma t0 T1 T2 Gamma H H0) as H1.
     destruct H1. destruct H1. destruct H1. destruct H2.
     exists x0. rewrite H3. apply ST_FstPair. assumption. assumption.
  -- destruct H0. exists (tm_fst x0). apply ST_Fst1. assumption.
- right.
  pose proof (IHhas_type HeqGamma) as H1.
  destruct H1.
  -- pose proof (value_pair_lemma t0 T1 T2 Gamma H H0) as H1.
     destruct H1. destruct H1. destruct H1. destruct H2.
     exists x1. rewrite H3. apply ST_SndPair. assumption. assumption.
  -- destruct H0. exists (tm_snd x0). apply ST_Snd1. assumption.
- right.
  pose proof (IHhas_type1 HeqGamma) as H1.  
  destruct H1.
  -- exists <{ [x0 := t1] t2 }>. apply ST_LetValue. assumption.
  -- destruct H1. exists <{ let x0 = x1 in t2 }>.  apply ST_Let1. assumption.
- right.
  pose proof (IHhas_type HeqGamma) as H1.
  destruct H1.
  -- pose proof (value_abs_lemma t1 T1 T1 Gamma H H0) as H1.
     destruct H1. destruct H1.
     rewrite H1.
     exists <{ [x0 := fix (\x0: T1, x1)] x1 }>. apply ST_FixAbs.
  -- destruct H0. exists (tm_fix x0). apply ST_Fix1. assumption.
Qed.  
  
Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma |- t \in T ->
     Gamma' |- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto 7 using includedin_update.
Qed.
Lemma weakening_empty : forall Gamma t T,
     empty |- t \in T ->
     Gamma |- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.  
  
Lemma substitution_preserves_typing : forall Gamma x U t v T,
  (x |-> U ; Gamma) |- t \in T ->
  empty |- v \in U ->
  Gamma |- [x:=v]t \in T.
Proof with eauto.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  (* Proof: By induction on the term t.  Most cases follow
     directly from the IH, with the exception of var
     and abs. These aren't automatic because we must
     reason about how the variables interact. The proofs
     of these cases are similar to the ones in STLC.
     We refer the reader to StlcProp.v for explanations. *)
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_spec x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_spec x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
  - (* tm_case *)
    rename s into x1, s0 into x2.
    eapply T_Case...
    + (* left arm *)
      destruct (eqb_spec x x1); subst.
      * (* x = x1 *)
        rewrite update_shadow in H8. assumption.
      * (* x <> x1 *)
        apply IHt2.
        rewrite update_permute; auto.
    + (* right arm *)
      destruct (eqb_spec x x2); subst.
      * (* x = x2 *)
        rewrite update_shadow in H9. assumption.
      * (* x <> x2 *)
        apply IHt3.
        rewrite update_permute; auto.
  - (* tm_lcase *)
    rename s into y1, s0 into y2.
    eapply T_Lcase...
    destruct (eqb_spec x y1); subst.
    + (* x=y1 *)
      destruct (eqb_spec y2 y1); subst.
      * (* y2=y1 *)
        repeat rewrite update_shadow in H9.
        rewrite update_shadow.
        assumption.
      * rewrite update_permute in H9; [|assumption].
        rewrite update_shadow in H9.
        rewrite update_permute; assumption.
    + (* x<>y1 *)
      destruct (eqb_spec x y2); subst.
      * (* x=y2 *)
        rewrite update_shadow in H9.
        assumption.
      * (* x<>y2 *)
        apply IHt3.
        rewrite (update_permute _ _ _ _ _ _ n0) in H9.
        rewrite (update_permute _ _ _ _ _ _ n) in H9.
        assumption.  
  - destruct (eqb_spec x s); subst.
    + eapply T_Let.
      * apply ((IHt1 T1 Gamma) H5).
      * rewrite update_shadow in H6. assumption.
    + eapply T_Let.
      * apply ((IHt1 T1 Gamma) H5).
      * apply (IHt2 T (s |-> T1; Gamma)).
        rewrite update_permute in H6. assumption. assumption.
  - destruct t.
    + apply T_Fix. simpl. destruct (eqb_spec x s).
      * pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. rewrite e in H3. simpl in H3.
        assert (H4: (eqb s s) = true). { apply eqb_refl. } rewrite H4 in H3. assumption.
      * inversion H2. subst. apply T_Var. rewrite <- H1. 
        rewrite update_neq. reflexivity. assumption.
    + apply T_Fix. simpl.
      pose proof (IHt (Ty_Arrow T T) Gamma H2) as H3. simpl in H3. assumption.
    + destruct (eqb_spec x s); subst.
      * apply T_Fix. inversion H2. subst.
        pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3.
        simpl in H3.
        assert (H4: (eqb s s) = true). { apply eqb_refl. } rewrite H4 in H3. assumption. 
      * apply T_Fix.
        pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3.
        rewrite <- String.eqb_neq in n. rewrite n in H3. assumption.
    + apply T_Fix. simpl. 
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
    + apply T_Fix. simpl.  
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
    + apply T_Fix. simpl.  
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
    + apply T_Fix. simpl.  
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
    + apply T_Fix. simpl.  
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
    + apply T_Fix. simpl.  
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
    + apply T_Fix. simpl.  
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
    + apply T_Fix. simpl.  
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
    + apply T_Fix. simpl.  
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
    + apply T_Fix. simpl.  
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
    + apply T_Fix. simpl.  
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
    + apply T_Fix. simpl.  
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
    + apply T_Fix. simpl.  
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
    + apply T_Fix. simpl.  
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
    + apply T_Fix. simpl.  
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
    + apply T_Fix. simpl.  
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
    + apply T_Fix. simpl.  
      pose proof ((IHt (Ty_Arrow T T) Gamma) H2) as H3. simpl in H3. assumption.
Qed.  

Theorem preservation : forall t t' T,
     empty |- t \in T ->
     t --> t' ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  (* Proof: By induction on the given typing derivation.  Many
     cases are contradictory (T_Var, T_Abs).  We show just
     the interesting ones. Again, we refer the reader to
     StlcProp.v for explanations. *)
  induction HT;
    intros t' HE; subst; inversion HE; subst...
  - (* T_App *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
  (* T_Case *)
  - (* ST_CaseInl *)
    inversion HT1; subst.
    eapply substitution_preserves_typing...
  - (* ST_CaseInr *)
    inversion HT1; subst.
    eapply substitution_preserves_typing...
  - (* T_Lcase *)
    + (* ST_LcaseCons *)
      inversion HT1; subst.
      apply substitution_preserves_typing with <{{List T1}}>...
      apply substitution_preserves_typing with T1...
  
  (* fst and snd *)
  - inversion HT; subst. assumption.
  - inversion HT; subst. assumption.
  
  (* let *)
  - apply substitution_preserves_typing with (U := T1). assumption. assumption.
  
  (* fix *)
  - inversion HT; subst. apply substitution_preserves_typing with (U := T1).
    + assumption.
    + apply T_Fix. assumption.
Qed.

End STLCExtended.

