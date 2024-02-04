Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.

Module STLCExtendedRecords.

Module FirstTry.

Definition alist (X : Type) := list (string * X).

Inductive ty : Type :=
  | Base : string -> ty
  | Arrow : ty -> ty -> ty
  | TRcd : (alist ty) -> ty.
  
Check ty_ind.

End FirstTry.

Inductive ty : Type :=
  | Ty_Base : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_RNil : ty
  | Ty_RCons : string -> ty -> ty -> ty.
  
Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* records *)
  | tm_rproj : tm -> string -> tm
  | tm_rnil : tm
  | tm_rcons : string -> tm -> tm -> tm.
  
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

Notation "'Base' x" := (Ty_Base x) (in custom stlc_ty at level 0).

Notation " l ':' t1 '::' t2" := (Ty_RCons l t1 t2) (in custom stlc_ty at level 3, right associativity).
Notation " l := e1 '::' e2" := (tm_rcons l e1 e2) (in custom stlc at level 3, right associativity).
Notation "'nil'" := (Ty_RNil) (in custom stlc_ty).
Notation "'nil'" := (tm_rnil) (in custom stlc).
Notation "o --> l" := (tm_rproj o l) (in custom stlc at level 0).

Open Scope string_scope.

Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation A := <{{ Base "A" }}>.
Notation B := <{{ Base "B" }}>.
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".

Check (Ty_RCons i1 A Ty_RNil).

Check (Ty_RCons i1 (Ty_Arrow A B) (Ty_RCons i2 A Ty_RNil)).

Inductive record_ty : ty -> Prop :=
  | RTnil :
        record_ty <{{ nil }}>
  | RTcons : forall i T1 T2,
        record_ty <{{ i : T1 :: T2 }}>.
        
Inductive well_formed_ty : ty -> Prop :=
  | wfBase : forall (i : string),
        well_formed_ty <{{ Base i }}>
  | wfArrow : forall T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        well_formed_ty <{{ T1 -> T2 }}>
  | wfRNil :
        well_formed_ty <{{ nil }}>
  | wfRCons : forall i T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        record_ty T2 ->
        well_formed_ty <{{ i : T1 :: T2 }}>.

Hint Constructors record_ty well_formed_ty : core.

Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm <{ nil }>
  | rtcons : forall i t1 t2,
        record_tm <{ i := t1 :: t2 }>.

Hint Constructors record_tm : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{ t1 --> i }> =>
      <{ ( [x := s] t1) --> i }>
  | <{ nil }> =>
      <{ nil }>
  | <{ i := t1 :: tr }> =>
     <{ i := [x := s] t1 :: ( [x := s] tr) }>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{ \ x : T2, t1 }>
  | v_rnil : value <{ nil }>
  | v_rcons : forall i v1 vr,
      value v1 ->
      value vr ->
      value <{ i := v1 :: vr }>.
      
Hint Constructors value : core.

Fixpoint tlookup (i:string) (tr:tm) : option tm :=
  match tr with
  | <{ i' := t :: tr'}> => if String.eqb i i' then Some t else tlookup i tr'
  | _ => None
  end.

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
  | ST_Proj1 : forall t1 t1' i,
        t1 --> t1' ->
        <{ t1 --> i }> --> <{ t1' --> i }>
  | ST_ProjRcd : forall tr i vi,
        value tr ->
        tlookup i tr = Some vi ->
        <{ tr --> i }> --> vi
  | ST_Rcd_Head : forall i t1 t1' tr2,
        t1 --> t1' ->
        <{ i := t1 :: tr2 }> --> <{ i := t1' :: tr2 }>
  | ST_Rcd_Tail : forall i v1 tr2 tr2',
        value v1 ->
        tr2 --> tr2' ->
        <{ i := v1 :: tr2 }> --> <{ i := v1 :: tr2' }>

where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

Fixpoint Tlookup (i:string) (Tr:ty) : option ty :=
  match Tr with
  | <{{ i' : T :: Tr' }}> =>
      if String.eqb i i' then Some T else Tlookup i Tr'
  | _ => None
  end.
  
Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc_ty at level 0).  

Inductive has_type (Gamma : context) :tm -> ty -> Prop :=
  | T_Var : forall x T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |- x \in T
  | T_Abs : forall x T11 T12 t12,
      well_formed_ty T11 ->
      (x |-> T11; Gamma) |- t12 \in T12 ->
      Gamma |- \x : T11, t12 \in (T11 -> T12)
  | T_App : forall T1 T2 t1 t2,
      Gamma |- t1 \in (T1 -> T2) ->
      Gamma |- t2 \in T1 ->
      Gamma |- ( t1 t2) \in T2
  (* records: *)
  | T_Proj : forall i t Ti Tr,
      Gamma |- t \in Tr ->
      Tlookup i Tr = Some Ti ->
      Gamma |- (t --> i) \in Ti
 | T_RNil :
      Gamma |- nil \in nil
  | T_RCons : forall i t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |- ( i := t :: tr) \in ( i : T :: Tr)

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Lemma typing_example_2 :
  empty |- (\a : ( i1 : (A -> A) :: i2 : (B -> B) :: nil), a --> i2)
            ( i1 := (\a : A, a) :: i2 := (\a : B,a ) :: nil ) \in (B -> B).
Proof.
eapply T_App.
- apply T_Abs.
  -- apply wfRCons.
     + apply wfArrow.
       ++ apply wfBase.
       ++ apply wfBase.
     + apply wfRCons.
       ++ apply wfArrow.
          +++ apply wfBase.
          +++ apply wfBase.
       ++ apply wfRNil.
       ++ apply RTnil.
     + apply RTcons.
  -- eapply T_Proj.
     + apply T_Var.
       ++ rewrite update_eq. reflexivity.
       ++ apply wfRCons.
          +++ apply wfArrow. apply wfBase. apply wfBase.
          +++ apply wfRCons. apply wfArrow. apply wfBase. apply wfBase. apply wfRNil. apply RTnil.
          +++ apply RTcons.
     + simpl. reflexivity.
- apply T_RCons.
  -- apply T_Abs. apply wfBase. apply T_Var. rewrite update_eq. reflexivity. apply wfBase.
  -- apply T_RCons. 
     + apply T_Abs. apply wfBase. apply T_Var. rewrite update_eq. reflexivity. apply wfBase.
     + apply T_RNil.
     + apply RTnil.
     + apply rtnil.
  -- apply RTcons.
  -- apply rtcons.
Qed.

Example typing_nonexample_2 : forall y,
  ~ exists T,
    (y |-> A) |-
     (\a : ( i1 : A :: nil ), a --> i1 )
      ( i1 := y :: i2 := y :: nil ) \in T.
Proof.
intros.
unfold not.
intros.
destruct H.
inversion H. clear H. subst.
inversion H2. clear H2. subst.
inversion H4.
inversion H8.
Qed.

Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
intros.
induction T.
- unfold Tlookup in H0. inversion H0.
- unfold Tlookup in H0. inversion H0.
- unfold Tlookup in H0. inversion H0.
- inversion H. subst.
  inversion H0. subst.
  destruct (i =? s) eqn: Heq.
  -- inversion H2. clear H2.
     rewrite H3 in H4. assumption.
  -- eauto.
Qed.  
  
Lemma step_preserves_record_tm : forall tr tr',
  record_tm tr ->
  tr --> tr' ->
  record_tm tr'.
Proof.
intros.
induction H.
- inversion H0.
- inversion H0; subst.
  -- apply rtcons.
  -- apply rtcons.  
Qed.  
  
Lemma has_type__wf : forall Gamma t T,
  Gamma |- t \in T -> well_formed_ty T.
Proof.
intros.
induction H.
- assumption.
- apply wfArrow.
  -- assumption.
  -- assumption.
- inversion IHhas_type1. subst. assumption.
- eapply wf_rcd_lookup.
  -- apply IHhas_type.
  -- apply H0.
- apply wfRNil.
- apply wfRCons.
  -- assumption.
  -- assumption.
  -- assumption.
Qed.

Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  empty |- v \in T ->
  Tlookup i T = Some Ti ->
  exists ti, tlookup i v = Some ti /\ empty |- ti \in Ti.
Proof.
intros.
induction H0; try solve_by_invert.
- inversion H. subst.
  destruct (i =? i0) eqn: Heq.
  -- unfold tlookup. rewrite Heq.   
     unfold Tlookup in H1. rewrite Heq in H1. inversion H1.
     rewrite H4 in H0_.
     exists t. split. reflexivity. assumption.
  -- assert (H8: Tlookup i <{{ i0 : T :: Tr }}> = Tlookup i Tr).
     {
       unfold Tlookup. rewrite Heq. reflexivity.
     }
     assert (H9: tlookup i <{ i0 := t :: tr }> = tlookup i tr).
     {
       unfold tlookup. rewrite Heq. reflexivity.
     }
     rewrite H8 in H1.
     rewrite H9.
     apply IHhas_type2. assumption. assumption.
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
         + right. exists <{ [x:=t2]t1 }>.
           apply ST_AppAbs. assumption.
         + inversion H.
         + inversion H.
     --- destruct H2. 
         right. exists <{t1 x}>.
         apply ST_App2. assumption. assumption.
  -- destruct H1. right.
     exists <{x t2}>.
     apply ST_App1. assumption.
- destruct IHhas_type.
  -- apply HeqGamma.    
  -- rewrite HeqGamma in H. 
     pose proof (lookup_field_in_value t Tr i Ti H1 H H0) as H2.
     destruct H2. destruct H2.
     right.  exists x.
     apply ST_ProjRcd. assumption. assumption.
  -- destruct H1. right.
     exists <{x --> i}>.
     apply ST_Proj1. assumption.
- left. apply v_rnil.
- destruct IHhas_type1.
  -- apply HeqGamma.
  -- destruct H3.
     + destruct IHhas_type2.
       ++ apply HeqGamma.
       ++ left. apply v_rcons. apply v_abs. assumption.
       ++ destruct H3.
          right.
          exists <{ i := \ x : T2, t1 :: x0 }>.
          apply ST_Rcd_Tail. apply v_abs. assumption.
     + destruct IHhas_type2.
       ++ apply HeqGamma.
       ++ left. apply v_rcons. apply v_rnil. assumption.
       ++ destruct H3.
          right.
          exists <{ i := nil :: x }>.
          apply ST_Rcd_Tail. apply v_rnil. assumption.
     + destruct IHhas_type2.
       ++ apply HeqGamma.
       ++ left. apply v_rcons. apply v_rcons. assumption. assumption. assumption.
       ++ destruct H3.
          right.
          exists <{ i := i0 := v1 :: vr :: x }>.
          apply ST_Rcd_Tail. apply v_rcons. assumption. assumption. assumption.
  -- destruct IHhas_type2.
     + apply HeqGamma.
     + destruct H3.
       right. exists <{ i := x :: tr }>. apply ST_Rcd_Head. assumption.
     + destruct H3. destruct H4.
       right. exists <{ i := x :: tr }>. apply ST_Rcd_Head. assumption.
Qed.  
  
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
- apply H.
- pose proof (IHhas_type (x |-> T11; Gamma')) as H2. 
  apply includedin_update with (x := x) (vx := T11) in H1.
  apply H2.
  assumption.
Qed.  
  
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
intros.
generalize dependent Gamma.
generalize dependent T.
induction t.
- intros.
  destruct (eqb x s) eqn: Heq.
  -- rewrite eqb_eq in Heq.
     rewrite Heq in H.
     inversion H. subst.
     rewrite update_eq in H2. inversion H2.
     unfold subst. rewrite eqb_refl.
     apply weakening_empty. rewrite H4 in H0. assumption.
  -- rewrite eqb_neq in Heq.
     inversion H. subst.
     rewrite update_neq in H2.
     --- unfold subst.
         apply String.eqb_neq in Heq.
         rewrite Heq. apply T_Var. assumption. assumption.
     --- assumption.
- intros.
  simpl.
  inversion H. subst.
  pose proof (IHt1 (Ty_Arrow T1 T) Gamma) as H7.
  pose proof (H7 H3) as H8.
  pose proof (IHt2 T1 Gamma) as H9.
  pose proof (H9 H5) as H10.
  apply T_App with (T1 := T1) (T2 := T).
  assumption. assumption.
- intros. inversion H. subst.
  destruct (eqb x s) eqn: Heq.
  -- rewrite eqb_eq in Heq.
     rewrite Heq. simpl.
     rewrite eqb_refl.
     apply T_Abs.
     + assumption.
     + pose proof (IHt U Gamma) as H7. subst.
       rewrite update_shadow in H6.
       assumption.
  -- rewrite eqb_neq in Heq.
     simpl.
     apply String.eqb_neq in Heq.
     rewrite Heq.
     apply T_Abs.
     + assumption.
     + pose proof (IHt T12 (s |->t; Gamma)) as H7.
       apply H7.
       assert (H8: (s |-> t; x |-> U; Gamma) = (x |-> U; s |-> t; Gamma)).
       {
         rewrite update_permute. reflexivity. apply eqb_neq. assumption.
       }
       rewrite <- H8. assumption.
- intros. inversion H. subst.
  pose proof (IHt Tr Gamma) as H6.
  pose proof (H6 H3) as H7.
  simpl.
  eapply T_Proj.
  -- apply H7.
  -- assumption.
- intros. inversion H. simpl. apply T_RNil.
- intros. inversion H. subst.
  pose proof (IHt1 T0 Gamma) as H9.
  pose proof (IHt2 Tr Gamma) as H10.
  pose proof (H9 H4) as H11.
  pose proof (H10 H5) as H12.
  assert (H13: <{[x := v] s := t1 :: t2}> = <{s := [x := v] t1 :: [x := v] t2}>).
  {
    simpl. reflexivity.
  }
  rewrite H13.
  apply T_RCons. 
  -- assumption. 
  -- assumption. 
  -- assumption.
  -- inversion H8.
     + apply rtnil.
     + apply rtcons.
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
- intros. rewrite HeqGamma in H. inversion H.
- intros. inversion H1.
- intros. 
  inversion H1; subst.
  -- apply substitution_preserves_typing with (U := T1).
     --- inversion H. assumption.
     --- assumption.
  -- apply T_App with (T1 := T1) (T2 := T2).
     + apply IHhas_type1.
       ++ reflexivity. 
       ++ assumption. 
     + assumption.
  -- apply T_App with (T1 := T1) (T2 := T2).
     + assumption.
     + apply IHhas_type2.
       ++ reflexivity.
       ++ assumption.
- intros. inversion H1; subst.
  -- eapply T_Proj.
     + apply IHhas_type. reflexivity. assumption.
     + assumption.
  -- pose proof (lookup_field_in_value t Tr i Ti H4 H H0) as H7.
     destruct H7. destruct H2.
     rewrite H6 in H2. inversion H2. assumption.
- intros. inversion H0.
- intros.
  pose proof (IHhas_type1 HeqGamma) as H4.
  pose proof (IHhas_type2 HeqGamma) as H5.
  inversion H3; subst.
  -- eapply T_RCons; eauto. 
  -- eapply T_RCons; eauto.
     + eapply step_preserves_record_tm.
       ++ apply H2.
       ++ assumption.
Qed.

End STLCExtendedRecords.  
  
  
  