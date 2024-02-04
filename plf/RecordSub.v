Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

Module RecordSub.

Inductive ty : Type :=
  (* proper types *)
  | Ty_Top : ty
  | Ty_Base : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  (* record types *)
  | Ty_RNil : ty
  | Ty_RCons : string -> ty -> ty -> ty.
  
Inductive tm : Type :=
  (* proper terms *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_rproj : tm -> string -> tm
  (* record terms *)
  | tm_rnil : tm
  | tm_rcons : string -> tm -> tm -> tm.
  
Declare Custom Entry stlc.
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
Notation "'Top'" := (Ty_Top) (in custom stlc_ty at level 0).

Inductive record_ty : ty -> Prop :=
  | RTnil :
        record_ty <{{ nil }}>
  | RTcons : forall i T1 T2,
        record_ty <{{ i : T1 :: T2 }}>.
        
Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm <{ nil }>
  | rtcons : forall i t1 t2,
        record_tm <{ i := t1 :: t2 }>.
        
Inductive well_formed_ty : ty -> Prop :=
  | wfTop :
        well_formed_ty <{{ Top }}>
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
        
Hint Constructors record_ty record_tm well_formed_ty : core.

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

Fixpoint Tlookup (i:string) (Tr:ty) : option ty :=
  match Tr with
  | <{{ i' : T :: Tr' }}> =>
      if String.eqb i i' then Some T else Tlookup i Tr'
  | _ => None
  end.
  
Fixpoint tlookup (i:string) (tr:tm) : option tm :=
  match tr with
  | <{ i' := t :: tr' }> =>
      if String.eqb i i' then Some t else tlookup i tr'
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

Hint Constructors step : core.

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  (* Subtyping between proper types *)
  | S_Refl : forall T,
    well_formed_ty T ->
    T <: T
  | S_Trans : forall S U T,
    S <: U ->
    U <: T ->
    S <: T
  | S_Top : forall S,
    well_formed_ty S ->
    S <: <{{ Top }}>
  | S_Arrow : forall S1 S2 T1 T2,
    T1 <: S1 ->
    S2 <: T2 ->
    <{{ S1 -> S2 }}> <: <{{ T1 -> T2 }}>
  (* Subtyping between record types *)
  | S_RcdWidth : forall i T1 T2,
    well_formed_ty <{{ i : T1 :: T2 }}> ->
    <{{ i : T1 :: T2 }}> <: <{{ nil }}>
  | S_RcdDepth : forall i S1 T1 Sr2 Tr2,
    S1 <: T1 ->
    Sr2 <: Tr2 ->
    record_ty Sr2 ->
    record_ty Tr2 ->
    <{{ i : S1 :: Sr2 }}> <: <{{ i : T1 :: Tr2 }}>
  | S_RcdPerm : forall i1 i2 T1 T2 Tr3,
    well_formed_ty <{{ i1 : T1 :: i2 : T2 :: Tr3 }}> ->
    i1 <> i2 ->
       <{{ i1 : T1 :: i2 : T2 :: Tr3 }}>
    <: <{{ i2 : T2 :: i1 : T1 :: Tr3 }}>

where "T '<:' U" := (subtype T U).

Hint Constructors subtype : core.

Module Examples.
Open Scope string_scope.

Notation x := "x".
Notation y := "y".
Notation z := "z".
Notation j := "j".
Notation k := "k".
Notation i := "i".
Notation A := <{{ Base "A" }}>.
Notation B := <{{ Base "B" }}>.
Notation C := <{{ Base "C" }}>.

Definition TRcd_j :=
  <{{ j : (B -> B) :: nil }}>. (* {j:B->B} *)
Definition TRcd_kj :=
  <{{ k : (A -> A) :: TRcd_j }}>. (* {k:C->C,j:B->B} *)
  
Example subtyping_example_0 :
  <{{ C -> TRcd_kj }}> <: <{{ C -> nil }}>.
Proof.
unfold TRcd_kj.
apply S_Arrow.
- apply S_Refl.
  apply wfBase.
- apply S_RcdWidth.
  apply wfRCons.
  -- apply wfArrow. apply wfBase. apply wfBase.
  -- unfold TRcd_j. apply wfRCons.
     + apply wfArrow. apply wfBase. apply wfBase.
     + apply wfRNil.
     + apply RTnil.
  -- unfold TRcd_j.
     apply RTcons.
Qed.

Example subtyping_example_1 :
  TRcd_kj <: TRcd_j.
(* {k:A->A,j:B->B} <: {j:B->B} *)
Proof with eauto.
unfold TRcd_kj, TRcd_j.
apply S_Trans with (U := <{{ "j" : B -> B :: "k" : A -> A :: nil }}>).
- apply S_RcdPerm.
  apply wfRCons.
  -- apply wfArrow. apply wfBase. apply wfBase.
  -- apply wfRCons. 
     + apply wfArrow. apply wfBase. apply wfBase.
     + apply wfRNil.
     + apply RTnil.
  -- apply RTcons.
  -- unfold not. intros. inversion H.
- apply S_RcdDepth.
  -- apply S_Refl. apply wfArrow. apply wfBase. apply wfBase.
  -- apply S_RcdWidth. 
     + apply wfRCons. 
       ++ apply wfArrow. apply wfBase. apply wfBase.
       ++ apply wfRNil.
       ++ apply RTnil.
  -- apply RTcons.
  -- apply RTnil.
Qed.

Example subtyping_example_2 :
  <{{ Top -> TRcd_kj }}> <:
          <{{ (C -> C) -> TRcd_j }}>.
Proof with eauto.
unfold TRcd_kj, TRcd_j.
apply S_Arrow; auto.
apply subtyping_example_1. 
Qed.

Example subtyping_example_3 :
  <{{ nil -> (j : A :: nil) }}> <:
          <{{ (k : B :: nil) -> nil }}>.
(* {}->{j:A} <: {k:B}->{} *)
Proof with eauto.
apply S_Arrow; auto.
Qed.

Example subtyping_example_4 :
  <{{ x : A :: y : B :: z : C :: nil }}> <:
  <{{ z : C :: y : B :: x : A :: nil }}>.
Proof with eauto.
apply S_Trans with (U := <{{ "y" : B :: "x" : A :: "z" : C :: nil }}>); auto.
- apply S_RcdPerm; auto.
  unfold not. intros. inversion H.
- apply S_Trans with (U := <{{ "y" : B :: "z" : C :: "x" : A :: nil }}>); auto.
  -- eapply S_RcdDepth; auto.
     apply S_RcdPerm; auto.
     unfold not. intros. inversion H.
  -- eapply S_RcdPerm; auto.
     unfold not. intros. inversion H.
Qed.

End Examples.

Lemma subtype__wf : forall S T,
  subtype S T ->
  well_formed_ty T /\ well_formed_ty S.
Proof.
intros.
induction H.
- split. assumption. assumption.
- split. inversion IHsubtype2. assumption. inversion IHsubtype1. assumption.
- split. apply wfTop. assumption.
- split.
    apply wfArrow. inversion IHsubtype1. assumption. inversion IHsubtype2. assumption.
    apply wfArrow. inversion IHsubtype1. assumption. inversion IHsubtype2. assumption.
- split. apply wfRNil. assumption.
- split. 
    apply wfRCons. inversion IHsubtype1. assumption. inversion IHsubtype2. assumption. assumption.
    apply wfRCons. inversion IHsubtype1. assumption. inversion IHsubtype2. assumption. assumption.
- split.
  -- apply wfRCons.
     + inversion H. inversion H5. assumption.
     + apply wfRCons. 
       ++ inversion H. assumption. 
       ++ inversion H. inversion H5. assumption.
       ++ inversion H. inversion H5. assumption.
     + inversion H. apply RTcons.
  -- assumption.
Qed.

Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
Proof.
intros.
induction H; inversion H0.
destruct (String.eqb i i0) eqn: Heq.
- inversion H4. rewrite H5 in H. assumption.
- auto.
Qed.  

Lemma lookup_implies : forall i T Ti,
  Tlookup i T = Some Ti ->
  (exists T2, T = <{{i : Ti :: T2}}>) \/
  (exists T1 T2 i0, (i <> i0) /\ T = <{{i0 : T1 :: T2}}> /\ Tlookup i T2 = Some Ti).
Proof.
intros.
induction T; try solve_by_invert.
destruct (String.eqb i s) eqn: Heq.
- simpl in H. rewrite Heq in H. inversion H.
  left. exists T2.
  rewrite eqb_eq in Heq. rewrite Heq. reflexivity.
- simpl in H. rewrite Heq in H.
  right. exists T1, T2, s. split.
  -- rewrite eqb_neq in Heq. assumption.
  -- split.
     + reflexivity.
     + pose proof (IHT2 H) as H1.
       destruct H1. 
       ++ destruct H0. rewrite H0. simpl.
          assert (H1: String.eqb i i = true) by (apply String.eqb_refl). rewrite H1. reflexivity.
       ++ assumption. 
Qed.

Lemma rcd_types_match : forall S T i Ti,
  subtype S T ->
  Tlookup i T = Some Ti ->
  exists Si, Tlookup i S = Some Si /\ subtype Si Ti.
Proof.
intros.
generalize dependent Ti.
induction H.
- intros. exists Ti. split.
  -- assumption.
  -- apply S_Refl. apply wf_rcd_lookup in H0. assumption. assumption.
- intros.
  pose proof (IHsubtype2 Ti) as H2.
  pose proof (H2 H1) as H3.
  destruct H3. destruct H3.
  pose proof (IHsubtype1 x) as H5.
  pose proof (H5 H3) as H6.
  destruct H6. destruct H6.
  exists x0. split.
  -- assumption.
  -- eapply S_Trans. apply H7. apply H4. 
- intros. inversion H0.
- intros. inversion H1.
- intros. inversion H0.
- intros.
  destruct (String.eqb i i0) eqn: Heq.
  -- simpl. rewrite Heq.
     simpl in H3. rewrite Heq in H3. inversion H3.
     exists S1. split. reflexivity. rewrite H5 in H. assumption.
  -- simpl. rewrite Heq.
     simpl in H3. rewrite Heq in H3.
     eauto.
- intros.
  destruct (String.eqb i i1) eqn: Heq1.
  -- simpl. rewrite Heq1.
     simpl in H1. rewrite Heq1 in H1.
     destruct (String.eqb i i2) eqn: Heq2.
     + rewrite eqb_eq in Heq1, Heq2. rewrite <- Heq1 in H0. rewrite <- Heq2 in H0.
       unfold not in H0. exfalso. apply H0. reflexivity.
     + exists T1. split. 
       ++ reflexivity.
       ++ inversion H1. apply S_Refl. inversion H. rewrite H3 in H6. assumption.
  -- simpl. rewrite Heq1.
     simpl in H1. rewrite Heq1 in H1.
     destruct (String.eqb i i2) eqn: Heq2.
     + inversion H1. exists T2. split.
       ++ rewrite H3. reflexivity.
       ++ rewrite H3. apply S_Refl.
          inversion H. inversion H7. rewrite <- H3. assumption.
     + exists Ti. split.
       ++ assumption.
       ++ apply S_Refl. eapply wf_rcd_lookup. inversion H. inversion H6.
          apply H12. apply H1.
Qed.

(*

Informal proof of rcd_types_match
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We generalize on Ti

Induction on S <: T

Tlookup i T = Some Ti implies that T is a record type, so the induction cases where T is an 
arrow type, Top, or Nil can be ruled out (Nil ruled out because Tlookup i T produces Some Ti, 
therefore T is not empty/Nil)

Case S_Refl:
Si = Ti satisfies the goal. The first subgoal satisfied by the assumption, the second subgoal satified
by S_Refl and wf_rcd_lookup lemma

Case S_Trans:
By suitable initialization of the induction hypotheses and S_Trans itself

Case S_Depth:
T = <{{ i:T1 :: Tr2 }}>, S = <{{ i:S1 :: Sr2 }}> with S1 <: T1 and Sr2 <: Tr2

We consider two cases:
Case 1: i = i0, in which case Ti = T1, and Si = S1 satisfies the goal, assisted by the assumptions.
Case 2: i <> i0 - application of the second induction hypotheses, assisted by the assumptions satisfies
        the goal.
        
Case S_Perm:
  T = i2:T2 :: i1:T1 :: Tr3
  S = i1:T1 :: i2:T2 :: Tr3
  
Case 1: i = i1
  Case 1: i = i2 -> contradicts assumption
  Case 2: i <> i2 -> Si = T1 satisfies the goal, assisted by the assumptions
  
Case 2:
  Case 1: i = i2 -> Si = T2 satisfies the goal, assisted by the assumptions, along with the application
          of S_Refl.
  Case 2: i <> i2 -> Si = Ti satifies the goal, assisted by the assumptions, along with the application
          of wf_rcd_lookup

*)

Lemma sub_inversion_arrow : forall U V1 V2,
     U <: <{{ V1 -> V2 }}> ->
     exists U1 U2,
       (U= <{{ U1 -> U2 }}> ) /\ (V1 <: U1) /\ (U2 <: V2).
Proof.
  intros U V1 V2 Hs.
  remember <{{V1->V2}}> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs.
  - intros. exists V1, V2.
    split. assumption. split. 
    -- apply S_Refl. rewrite HeqV in H. inversion H. assumption.
    -- apply S_Refl. rewrite HeqV in H. inversion H. assumption.
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
  - intros. inversion HeqV.
  - intros. inversion HeqV.
Qed.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40,
                                          t custom stlc at level 99, T custom stlc_ty at level 0).
                                          
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma (x : string) T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |- x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      well_formed_ty T11 ->
      (x |-> T11; Gamma) |- t12 \in T12 ->
      Gamma |- (\ x : T11, t12) \in (T11 -> T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (T1 -> T2) ->
      Gamma |- t2 \in T1 ->
      Gamma |- t1 t2 \in T2
  | T_Proj : forall Gamma i t T Ti,
      Gamma |- t \in T ->
      Tlookup i T = Some Ti ->
      Gamma |- t --> i \in Ti
  (* Subsumption *)
  | T_Sub : forall Gamma t S T,
      Gamma |- t \in S ->
      subtype S T ->
      Gamma |- t \in T
  (* Rules for record terms *)
  | T_RNil : forall Gamma,
      Gamma |- nil \in nil
  | T_RCons : forall Gamma i t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |- i := t :: tr \in (i : T :: Tr)

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.


Module Examples2.
Import Examples.

Definition trcd_kj :=
  <{ k := (\z : A, z) :: j := (\z : B, z) :: nil }>.
  
Example typing_example_0 :
  empty |- trcd_kj \in TRcd_kj.
Proof.
unfold trcd_kj, TRcd_kj.
eapply T_RCons.
- apply T_Abs. apply wfBase. apply T_Var. rewrite update_eq. reflexivity. apply wfBase.
- eapply T_RCons.
  -- apply T_Abs. apply wfBase. apply T_Var. rewrite update_eq. reflexivity. apply wfBase.
  -- apply T_RNil.
  -- apply RTnil.
  -- apply rtnil.
- unfold TRcd_j. apply RTcons.
- apply rtcons.
Qed.

Example typing_example_1 :
  empty |- (\x : TRcd_j, x --> j) trcd_kj \in (B -> B).
Proof.
unfold TRcd_j, trcd_kj.
eapply T_App.
- apply T_Abs.
  -- apply wfRCons.
     + apply wfArrow. apply wfBase. apply wfBase.
     + apply wfRNil.
     + apply RTnil.
  -- eapply T_Proj.
     + apply T_Var. 
       ++ rewrite update_eq. reflexivity.
       ++ apply wfRCons.
          +++ apply wfArrow. apply wfBase. apply wfBase.
          +++ apply wfRNil.
          +++ apply RTnil.
     + simpl. reflexivity.
- eapply T_Sub.
  -- apply T_RCons.
     + apply T_Abs. apply wfBase. apply T_Var. rewrite update_eq. reflexivity. apply wfBase.
     + apply T_RCons. apply T_Abs. apply wfBase. apply T_Var. rewrite update_eq. reflexivity. apply wfBase.
       apply T_RNil. apply RTnil. apply rtnil.
     + apply RTcons.
     + apply rtcons.
  -- eapply S_Trans.
     + apply S_RcdPerm.
       ++ apply wfRCons. 
          +++ apply wfArrow. apply wfBase. apply wfBase. 
          +++ apply wfRCons.
              ++++ apply wfArrow. apply wfBase. apply wfBase.
              ++++ apply wfRNil.
              ++++ apply RTnil.
          +++ apply RTcons.
       ++ unfold not. intros. inversion H.
     + eapply S_RcdDepth.
       ++ apply S_Refl. apply wfArrow. apply wfBase. apply wfBase.
       ++ apply S_RcdWidth. apply wfRCons.
          +++ apply wfArrow. apply wfBase. apply wfBase.
          +++ apply wfRNil.
          +++ apply RTnil.
       ++ apply RTcons.
       ++ apply RTnil.   
Qed.

Example typing_example_2 :
  empty |- (\ z : (C -> C) -> TRcd_j, (z (\ x : C, x) ) --> j )
            ( \z : (C -> C), trcd_kj ) \in (B -> B).
Proof.
unfold TRcd_j, trcd_kj.
eapply T_App.
- apply T_Abs.
  -- apply wfArrow. 
     + apply wfArrow. apply wfBase. apply wfBase.
     + apply wfRCons. apply wfArrow. apply wfBase. apply wfBase. apply wfRNil. apply RTnil.
  -- eapply T_Proj.
     + eapply T_App.
       ++ apply T_Var.
          +++ rewrite update_eq. reflexivity.
          +++ apply wfArrow.
              ++++ apply wfArrow. apply wfBase. apply wfBase.
              ++++ apply wfRCons. apply wfArrow. apply wfBase. apply wfBase. apply wfRNil. apply RTnil.
       ++ apply T_Abs.
          +++ apply wfBase.
          +++ apply T_Var. rewrite update_eq. reflexivity. apply wfBase.
     + simpl. reflexivity.
- apply T_Abs.
  -- apply wfArrow. apply wfBase. apply wfBase.
  -- eapply T_Sub.
     + apply T_RCons.
       ++ apply T_Abs.
          +++ apply wfBase.
          +++ apply T_Var.
              ++++ rewrite update_eq. reflexivity.
              ++++ apply wfBase.
       ++ apply T_RCons.
          +++ apply T_Abs.
              ++++ apply wfBase.
              ++++ apply T_Var.
                   +++++ rewrite update_eq. reflexivity.
                   +++++ apply wfBase.
          +++ apply T_RNil.
          +++ apply RTnil.
          +++ apply rtnil.
       ++ apply RTcons.
       ++ apply rtcons.
     + eapply S_Trans.
       ++ apply S_RcdPerm.
          +++ apply wfRCons. 
              ++++ apply wfArrow. apply wfBase. apply wfBase. 
              ++++ apply wfRCons.
                   +++++ apply wfArrow. apply wfBase. apply wfBase.
                   +++++ apply wfRNil.
                   +++++ apply RTnil.
              ++++ apply RTcons.
          +++ unfold not. intros. inversion H.
       ++ eapply S_RcdDepth.
          +++ apply S_Refl. apply wfArrow. apply wfBase. apply wfBase.
          +++ apply S_RcdWidth. apply wfRCons.
              ++++ apply wfArrow. apply wfBase. apply wfBase.
              ++++ apply wfRNil.
              ++++ apply RTnil.
          +++ apply RTcons.
          +++ apply RTnil.  
Qed.

End Examples2.
                      
Lemma has_type__wf : forall Gamma t T,
  has_type Gamma t T -> well_formed_ty T.
Proof.
intros.
induction H.
- assumption.
- apply wfArrow. assumption. assumption.
- inversion IHhas_type1. assumption.
- eapply wf_rcd_lookup. apply IHhas_type. apply H0.
- apply subtype__wf in H0. destruct H0. assumption.
- apply wfRNil.
- apply wfRCons. assumption. assumption. assumption.
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

Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  empty |- v \in T ->
  Tlookup i T = Some Ti ->
  exists vi, tlookup i v = Some vi /\ empty |- vi \in Ti.
Proof.
intros.
generalize dependent Ti.
induction H0; intros; try solve_by_invert.
- pose proof (rcd_types_match S T i Ti H1 H2) as H3.
  destruct H3. destruct H3.
  pose proof (((IHhas_type H) x) H3) as H5.
  destruct H5. destruct H5.
  exists x0. split.
  -- assumption.
  -- eapply T_Sub. apply H6. apply H4.
- destruct (String.eqb i i0) eqn: Heq.
  -- simpl. rewrite Heq.
     simpl in H2. rewrite Heq in H2. inversion H2.
     exists t. rewrite <- H4. split.
     + reflexivity.
     + assumption.
  -- simpl. rewrite Heq.
     simpl in H2. rewrite Heq in H2.
     apply IHhas_type2.
     + inversion H. assumption.
     + assumption.
Qed.     

Lemma rcd_super_is_rcd_or_top: forall T,
  record_ty T ->
  T = <{{nil}}> \/ exists i T1 T2, T = <{{i:T1 :: T2}}>.
Proof.
intros.
inversion H.
- left. reflexivity.
- right. exists i, T1, T2. reflexivity. 
Qed.

Lemma sub_inversion_Top : forall U,
     <{{ Top }}> <: U ->
     U = <{{ Top }}>.
Proof with auto.
  intros U Hs.
  remember <{{Top}}> as V.
  induction Hs.
  - reflexivity.
  - pose proof (IHHs1 HeqV) as H1. rewrite HeqV in H1. pose proof (IHHs2 H1) as H2.
    rewrite <- HeqV in H1. rewrite <- H2 in H1. assumption.
  - inversion HeqV. reflexivity.
  - inversion HeqV.
  - inversion HeqV.
  - inversion HeqV.
  - inversion HeqV.
Qed.


Lemma sub_inversion_nil : forall U,
     <{{ nil }}> <: U ->
     U = <{{ nil }}> \/ U = <{{ Top }}>.
Proof with auto.
  intros U Hs.
  remember <{{nil}}> as V.
  induction Hs.
  - left. reflexivity.
  - pose proof (IHHs1 HeqV) as H1. rewrite HeqV in H1. destruct H1.
    -- pose proof (IHHs2 H) as H2. destruct H2.
       + subst. left. reflexivity.
       + right. assumption.
    -- rewrite H in Hs2. right. apply sub_inversion_Top in Hs2. assumption.
  - right. reflexivity.
  - inversion HeqV.
  - inversion HeqV.
  - inversion HeqV.
  - inversion HeqV.  
Qed.

Lemma rec_type_super : forall S T,
  record_ty S ->
  S <: T ->
  record_ty T \/ T = <{{Top}}>.
Proof.
intros.
induction H0.
- left. assumption.
- destruct (IHsubtype1 H).
  -- eauto.
  -- rewrite H0 in H0_0.
     apply sub_inversion_Top in H0_0.
     right. assumption.
- right. reflexivity.
- inversion H.
- left. apply RTnil.
- left. apply RTcons.
- left. apply RTcons.
Qed.     

Lemma rec_implies: forall Gamma s T,
  record_tm s ->
  Gamma |- s \in T ->
  record_ty T \/ T = <{{Top}}>.
intros.
inversion H.
- subst. induction H0; try solve_by_invert.
  -- destruct (IHhas_type H).
     + apply (rec_type_super S T H2 H1).
     + rewrite H2 in H1. apply sub_inversion_Top in H1. right. assumption.
  -- left. apply RTnil.
  -- left. apply RTcons.
- subst. induction H0; try solve_by_invert.
  -- destruct (IHhas_type H).
     + apply (rec_type_super S T H2 H1).
     + rewrite H2 in H1. apply sub_inversion_Top in H1. right. assumption.
  -- left. apply RTnil.
  -- left. apply RTcons.  
Qed.

Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
     Gamma |- s \in (T1 -> T2) ->
     value s ->
     exists x S1 s2,
        s = <{ \ x : S1, s2 }>.
Proof with eauto.
intros.
inversion H0; clear H0.
- exists x, T0, t1. reflexivity.
- assert (H2: record_tm s). { rewrite <- H1. apply rtnil. }
  pose proof (rec_implies Gamma s <{{T1 -> T2}}> H2 H) as H3.
  pose proof (rcd_super_is_rcd_or_top <{{T1 -> T2}}>) as H4.
  destruct H4.
  -- destruct H3.
     + inversion H0.
     + inversion H0.
  -- inversion H0.
  -- destruct H0. destruct H0. destruct H0. inversion H0.
- assert (H4: record_tm s). { rewrite <- H3. apply rtcons. }
  pose proof (rec_implies Gamma s <{{T1 -> T2}}> H4 H) as H5.
  pose proof (rcd_super_is_rcd_or_top <{{T1 -> T2}}>) as H6.
  destruct H6.
  -- destruct H5. inversion H0. inversion H0.
  -- inversion H0.
  -- destruct H0. destruct H0. destruct H0. inversion H0.
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
     --- pose proof (canonical_forms_of_arrow_types Gamma t1 T1 T2 H H1) as H3.
         destruct H3. destruct H3. destruct H3.
         right. exists <{[x:=t2]x1}>. rewrite H3. apply ST_AppAbs. assumption.
     --- right. destruct H2. exists <{t1 x}>. apply ST_App2. assumption. assumption.
  -- destruct H2.
     --- right. destruct H1. exists <{x t2}>. apply ST_App1. assumption.
     --- right. destruct H1. exists <{x t2}>. apply ST_App1. assumption.
- destruct (IHhas_type HeqGamma).
  -- rewrite HeqGamma in H. 
     destruct (lookup_field_in_value t T i Ti H1 H H0). destruct H2.
     right. exists x. apply ST_ProjRcd. assumption. assumption.
  -- destruct H1. right. exists <{x --> i}>.
     apply ST_Proj1. assumption.
- apply (IHhas_type HeqGamma).
- left. apply v_rnil.
- destruct (IHhas_type1 HeqGamma).
  -- destruct (IHhas_type2).
     + assumption.
     + left. apply v_rcons. assumption. assumption.
     + destruct H4. right. exists <{i := t :: x}>. apply ST_Rcd_Tail. assumption. assumption.
  -- destruct H3. right. exists <{i := x :: tr}>. apply ST_Rcd_Head. assumption. 
Qed.

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |- \ x : S1, t2 \in T ->
     (exists S2, <{{ S1 -> S2 }}> <: T
              /\ (x |-> S1; Gamma) |- t2 \in S2).  
intros.
remember <{\x:S1,t2}> as tabs.
induction H.
- inversion Heqtabs.
- inversion Heqtabs. subst.
  exists T12. split. apply S_Refl.
  -- apply wfArrow.
     + assumption.
     + apply has_type__wf in H0. assumption.
  -- assumption.   
- inversion Heqtabs.
- inversion Heqtabs.
- destruct (IHhas_type Heqtabs).
  destruct H1. exists x0. split.
  -- eapply S_Trans. apply H1. assumption.
  -- assumption.
- inversion Heqtabs.
- inversion Heqtabs.
Qed.

Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |- \x : S1, s2 \in (T1 -> T2) ->
     T1 <: S1
  /\ (x |-> S1) |- s2 \in T2.
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

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma |- t \in T ->
     Gamma' |- t \in T.
intros.
generalize dependent Gamma'.
induction H0; eauto. (* can also simply do eauto using includedin_update *)
intros.
apply T_Abs.
- assumption.
- pose proof (IHhas_type (x |-> T11; Gamma')) as H2.
  apply H2.
  apply includedin_update.
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
       rewrite <- H2.
       apply weakening_empty. assumption.
    -- rewrite eqb_neq in Heq.
       rewrite G in H.
       rewrite update_neq in H.
       --- apply T_Var. assumption. assumption.
       --- assumption.
  - destruct (eqb x x0) eqn: Heq.
    -- rewrite eqb_eq in Heq.
       apply T_Abs.
       + assumption.
       + rewrite G in Ht.
         rewrite Heq in Ht.
         rewrite update_shadow in Ht.
         apply weakening with (Gamma := (x0 |-> T11; Gamma')).
         ++ unfold includedin. intros. assumption.
         ++ assumption.
    -- rewrite eqb_neq in Heq.
       apply T_Abs.
       + assumption.
       + pose proof (IHHt (x0 |-> T11; Gamma')) as H1.
         apply H1.
         rewrite G.
         apply update_permute.
         assumption.
  - apply T_RCons.
    -- eauto.
    -- eauto.
    -- assumption.
    -- inversion H0.
       + simpl. apply rtnil.
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
- rewrite HeqGamma in H. inversion H.
- intros. inversion H1.
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
  -- assert (H7: empty |- t2' \in T1).
     {
       apply IHhas_type2. reflexivity. assumption.
     }
     eapply T_App.
     --- apply H.
     --- assumption.
- intros.
  inversion H1; subst.
  -- apply IHhas_type in H5.
     + eapply T_Proj.
       ++ apply H5.
       ++ assumption.
     + reflexivity.
  -- pose proof (lookup_field_in_value t T i Ti H4 H H0) as H7.
     destruct H7. destruct H2. rewrite H6 in H2. inversion H2. assumption.
- intros. apply IHhas_type in H1.
  -- eapply T_Sub. apply H1. assumption.
  -- assumption.
- intros. inversion H0.
- intros. inversion H3; subst.
  -- apply T_RCons.
     + eauto.
     + eauto.
     + assumption.
     + assumption.
  -- apply T_RCons.
     + assumption.
     + eauto.
     + assumption.
     + eapply step_preserves_record_tm.
       ++ apply H2.
       ++ assumption.
Qed.

End RecordSub.