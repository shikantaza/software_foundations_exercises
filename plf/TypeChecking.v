Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.
From PLF Require MoreStlc.

Module STLCTypes.
Export STLC.

Locate "Bool".

Locate T_Pair.

Fixpoint eqb_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | <{ Bool }> , <{ Bool }> =>
      true
  | <{ T11->T12 }>, <{ T21->T22 }> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _,_ =>
      false
  end.
  
Lemma eqb_ty_refl : forall T,
  eqb_ty T T = true.
Proof.
intros.
induction T.
- simpl. reflexivity.
- simpl.
  rewrite IHT1. rewrite IHT2.
  simpl.
  reflexivity.
Qed.

Lemma bool_helper2 : forall b1 b2, b1 && b2 = true -> b1 = true /\ b2 = true.
Proof.
intros.
split.
destruct b1.
reflexivity.
discriminate.
destruct b2.
reflexivity.
destruct b1.
discriminate.
discriminate.
Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof.
intros.
generalize dependent T2.
induction T1.
- intros. destruct T2.
  -- reflexivity.
  -- inversion H.
- intros.
  destruct T2.
  -- inversion H.
  -- simpl in H.
     pose proof (IHT1_1 T2_1) as H1.
     pose proof (IHT1_2 T2_2) as H2.
     apply bool_helper2 in H.
     destruct H.
     rewrite (H1 H).
     rewrite (H2 H0).
     reflexivity.
Qed.

End STLCTypes.

Module FirstTry.
Import STLCTypes.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      Gamma x
  | <{\x:T2, t1}> =>
      match type_check (x |-> T2 ; Gamma) t1 with
      | Some T1 => Some <{T2->T1}>
      | _ => None
      end
  | <{t1 t2}> =>
      match type_check Gamma t1, type_check Gamma t2 with
      | Some <{T11->T12}>, Some T2 =>
          if eqb_ty T11 T2 then Some T12 else None
      | _,_ => None
      end
  | <{true}> =>
      Some <{Bool}>
  | <{false}> =>
      Some <{Bool}>
  | <{if guard then t else f}> =>
      match type_check Gamma guard with
      | Some <{Bool}> =>
          match type_check Gamma t, type_check Gamma f with
          | Some T1, Some T2 =>
              if eqb_ty T1 T2 then Some T1 else None
          | _,_ => None
          end
      | _ => None
      end
  end.
  
End FirstTry.

Notation " x <- e1 ;; e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end)
         (right associativity, at level 60).
         
Notation " 'return' e "
  := (Some e) (at level 60).
  
Notation " 'fail' "
  := None.
  
Module STLCChecker.
Import STLCTypes.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None => fail
      end
  | <{\x:T2, t1}> =>
      T1 <- type_check (x |-> T2 ; Gamma) t1 ;;
      return <{T2->T1}>
  | <{t1 t2}> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{T11->T12}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | <{true}> =>
      return <{ Bool }>
  | <{false}> =>
      return <{ Bool }>
  | <{if guard then t1 else t2}> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match Tguard with
      | <{ Bool }> =>
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.

Lemma eqb_ty_impl_eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof.
intros.
generalize dependent T2.
induction T1.
- intros. destruct T2.
  -- reflexivity.
  -- inversion H.
- intros. destruct T2.
  -- inversion H.
  -- inversion H. 
     apply bool_helper2 in H1.
     destruct H1.
     pose proof (IHT1_1 T2_1) as H2.
     pose proof (IHT1_2 T2_2) as H3.
     pose proof (H2 H0) as H4.
     pose proof (H3 H1) as H5.
     rewrite H4. rewrite H5.
     reflexivity.
Qed.

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof.
intros Gamma t.
generalize dependent Gamma.
induction t; intros Gamma T Htc; inversion Htc.
- apply T_Var. destruct (Gamma s).
  -- assumption.
  -- inversion H0.
- destruct (type_check Gamma t1) eqn: Heqt1.
  -- destruct (type_check Gamma t2) eqn: Heqt2.
     + destruct t eqn: Heqt.
       ++ inversion H0.
       ++ destruct (eqb_ty t3_1 t0) eqn: Heqb.
          +++ inversion H0. subst.  
              apply eqb_ty_impl_eq in Heqb.
              subst.
              pose proof (IHt1 Gamma <{t0->T}>) as H1.
              pose proof (IHt2 Gamma t0) as H2.
              pose proof (H1 Heqt1) as H3.
              pose proof (H2 Heqt2) as H4.
              eapply T_App. apply H3. assumption.
          +++ inversion H0.
     + inversion H0.
  -- inversion H0.
- destruct (type_check (s |-> t; Gamma) t0) eqn: Heqt0.
  -- inversion H0.
     pose proof (IHt (s |-> t; Gamma) t1) as H2.
     pose proof (H2 Heqt0) as H3.
     apply T_Abs. assumption.
  -- inversion H0.
- apply T_True.
- apply T_False.
- destruct (type_check Gamma t1) eqn: Heqt1.
  -- destruct (type_check Gamma t2) eqn: Heqt2.
     + destruct (type_check Gamma t3) eqn: Heqt3.
       ++ destruct t eqn: Heqt.
          +++ destruct (eqb_ty t0 t4) eqn: Heqb.
              ++++ inversion H0.
                   pose proof (IHt1 Gamma <{Bool}>) as H2.
                   pose proof (IHt2 Gamma t0) as H3.
                   pose proof (IHt3 Gamma t4) as H4.
                   pose proof (H2 Heqt1) as H5.
                   pose proof (H3 Heqt2) as H6.
                   pose proof (H4 Heqt3) as H7.
                   apply eqb_ty_impl_eq in Heqb. 
                   rewrite H1 in H6. rewrite <- Heqb in H7. rewrite H1 in H7.
                   apply T_If.
                   assumption. assumption. assumption.
              ++++ inversion H0.
          +++ inversion H0.
       ++ inversion H0.
     + inversion H0.
  -- inversion H0.
Qed.
        
Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof.
intros.
induction H.
- simpl.
  destruct (Gamma x0) eqn: Heqx0.
  -- assumption.
  -- inversion H.
- simpl.
  destruct (type_check (x0 |-> T2; Gamma) t1) eqn: Heqt1.
  -- inversion IHhas_type. reflexivity.
  -- inversion IHhas_type.
- simpl.
  destruct (type_check Gamma t1) eqn: Heqt1.
  -- destruct (type_check Gamma t2) eqn: Heqt2.
     + destruct t eqn: Heqt.
       ++ inversion IHhas_type1.
       ++ inversion IHhas_type1. inversion IHhas_type2. subst.
          assert (H1: eqb_ty T2 T2 = true) by (apply eqb_ty_refl).
          rewrite H1. reflexivity.
     + inversion IHhas_type2.
  -- inversion IHhas_type1.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl.
  destruct (type_check Gamma t1) eqn: Heqt1.
  -- destruct (type_check Gamma t2) eqn: Heqt2.
     + destruct (type_check Gamma t3) eqn: Heqt3.
       ++ destruct t eqn: Heqt.
          +++ inversion IHhas_type2. inversion IHhas_type3.
              assert (H5: eqb_ty T1 T1 = true) by (apply eqb_ty_refl).
              rewrite H5. reflexivity.
          +++ inversion IHhas_type1.
       ++ inversion IHhas_type3.
     + inversion IHhas_type2.
  -- inversion IHhas_type1.
Qed.

End STLCChecker.

Module TypecheckerExtensions.
Import MoreStlc.
Import STLCExtended.

Locate T_Fst.

Fixpoint eqb_ty (T1 T2 : ty) : bool :=
  match T1,T2 with
  | <{{Nat}}>, <{{Nat}}> =>
      true
  | <{{Unit}}>, <{{Unit}}> =>
      true
  | <{{T11 -> T12}}>, <{{T21 -> T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 * T12}}>, <{{T21 * T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 + T12}}>, <{{T21 + T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{List T11}}>, <{{List T21}}> =>
      eqb_ty T11 T21
  | _,_ =>
      false
  end.
  
Lemma eqb_ty_refl : forall T,
  eqb_ty T T = true.
Proof.
intros.
induction T.
- simpl. apply andb_true_iff. split. assumption. assumption.
- simpl. reflexivity.
- simpl. apply andb_true_iff. split. assumption. assumption.
- simpl. assumption.
- simpl. reflexivity.
- simpl. apply andb_true_iff. split. assumption. assumption.
Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof.
intros.
generalize dependent T2.
induction T1.
- intros. inversion H.
  destruct T2 eqn: HeqT2.
  -- apply andb_true_iff in H1. destruct H1.
     pose proof (IHT1_1 t1) as H2.
     pose proof (IHT1_2 t2) as H3.
     pose proof (H2 H0) as H4.
     pose proof (H3 H1) as H5.
     subst. reflexivity.
  -- inversion H1.
  -- inversion H1.
  -- inversion H1.
  -- inversion H1.
  -- inversion H1.
- intros. inversion H.
  destruct T2 eqn: HeqT2.
  -- inversion H1.
  -- reflexivity.
  -- inversion H1.
  -- inversion H1.
  -- inversion H1.
  -- inversion H1.
- intros. inversion H.
  destruct T2 eqn: HeqT2.
  -- inversion H1.
  -- inversion H1.
  -- apply andb_true_iff in H1. destruct H1.
     pose proof (IHT1_1 t1) as H2.
     pose proof (IHT1_2 t2) as H3.
     pose proof (H2 H0) as H4.
     pose proof (H3 H1) as H5.
     subst. reflexivity.
  -- inversion H1.
  -- inversion H1.
  -- inversion H1.
- intros. inversion H.
  destruct T2 eqn: HeqT2.
  -- inversion H1.
  -- inversion H1.
  -- inversion H1.
  -- pose proof (IHT1 t) as H2.
     pose proof (H2 H1) as H3. rewrite H3. reflexivity.
  -- inversion H1.
  -- inversion H1.
- intros. inversion H.
  destruct T2 eqn: HeqT2.
  -- inversion H1.
  -- inversion H1.
  -- inversion H1.
  -- inversion H1.
  -- reflexivity.
  -- inversion H1.
- intros.
  destruct T2 eqn: HeqT2.
  -- inversion H.
  -- inversion H.
  -- inversion H.
  -- inversion H.
  -- inversion H.
  -- inversion H.
     apply andb_true_iff in H1. destruct H1.
     pose proof (IHT1_1 t1) as H2.
     pose proof (IHT1_2 t2) as H3.
     pose proof (H2 H0) as H4.
     pose proof (H3 H1) as H5.
     subst. reflexivity.
Qed.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None => fail
      end
  | <{ \ x1 : T1, t2 }> =>
      T2 <- type_check (x1 |-> T1 ; Gamma) t2 ;;
      return <{{T1 -> T2}}>
  | <{ t1 t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{{T11 -> T12}}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | tm_const _ =>
      return <{{Nat}}>
  | <{ succ t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ pred t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ t1 * t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1, T2 with
      | <{{Nat}}>, <{{Nat}}> => return <{{Nat}}>
      | _,_ => fail
      end
  | <{ if0 guard then t else f }> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t ;;
      T2 <- type_check Gamma f ;;
      match Tguard with
      | <{{Nat}}> => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end

  (* Complete the following cases. *)
  
  (* sums *)
  | <{ inl T2 t }> =>
     T1 <- type_check Gamma t ;; return <{{ T1 + T2 }}>

  | <{ inr T1 t }> =>
     T2 <- type_check Gamma t ;; return <{{ T1 + T2 }}>

  | <{ case t of | inl x1 => t1 | inr x2 => t2 }> =>
      T <- type_check Gamma t ;;
      match T with
      | <{{ T1 + T2 }}> => 
          T1' <- type_check (x1 |-> T1; Gamma) t1 ;;
          T2' <- type_check (x2 |-> T2; Gamma) t2 ;;
          if eqb_ty T1' T2' then return T1' else fail
      | _ => fail
      end
      
  (* lists (the tm_lcase is given for free) *)
  | <{ nil T }> => return <{{ List T }}>
  
  | <{ t1 :: t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T2 with
      | <{{ List T }}> =>
          if eqb_ty T1 T then return <{{ List T }}> else fail
      | _ => fail
      end
  
  | <{ case t0 of | nil => t1 | x21 :: x22 => t2 }> =>
      T0 <- type_check Gamma t0 ;;
      match T0 with
      | <{{List T}}> =>
          T1 <- type_check Gamma t1 ;;
          T2 <- type_check (x21 |-> T ; x22 |-> <{{List T}}> ; Gamma) t2 ;;
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
      
  (* unit *)
  | <{ unit }> => return <{{ Unit }}>
  
  (* pairs *)
  | <{ (t1, t2) }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      return <{{ T1 * T2 }}>
      
  | <{ t.fst }> =>
      T <- type_check Gamma t ;;
      match T with
      | <{{ T1 * T2 }}> => return T1
      | _ => fail
      end
          
  | <{ t.snd }> =>
      T <- type_check Gamma t ;;
      match T with
      | <{{ T1 * T2 }}> => return T2
      | _ => fail
      end
  
  (* let *)
  | <{ let x=t1 in t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check (x |-> T1 ; Gamma) t2 ;;
      return T2
  
  (* fix *)
  | <{ fix t }> =>
      T <- type_check Gamma t ;;
      match T with
      | <{{ T1 -> T2 }}> => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
      
  end.
  
Ltac invert_typecheck Gamma t T :=
  remember (type_check Gamma t) as TO;
  destruct TO as [T|];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).
  
Ltac analyze T T1 T2 :=
  destruct T as [T1 T2| |T1 T2|T1| |T1 T2]; try solve_by_invert.
  
Ltac fully_invert_typecheck Gamma t T T1 T2 :=
  let TX := fresh T in
  remember (type_check Gamma t) as TO;
  destruct TO as [TX|]; try solve_by_invert;
  destruct TX as [T1 T2| |T1 T2|T1| |T1 T2];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).
  
Ltac case_equality S T :=
  destruct (eqb_ty S T) eqn: Heqb;
  inversion H0; apply eqb_ty__eq in Heqb; subst; subst; eauto.
  
Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T ->
  has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H.
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12.
    case_equality T11 T2.
  - (* abs *)
    rename s into x, t into T1.
    remember (x |-> T1 ; Gamma) as Gamma'.
    invert_typecheck Gamma' t0 T0.
  - (* const *) eauto.
  - (* scc *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* prd *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* mlt *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12; analyze T2 T21 T22.
    inversion H0. subst. eauto.
  - (* test0 *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    invert_typecheck Gamma t3 T3.
    destruct T1; try solve_by_invert.
    case_equality T2 T3.
  (* Complete the following cases. *)
  (* sums *)
  - invert_typecheck Gamma t0 T1.
  - invert_typecheck Gamma t0 T2.
  - invert_typecheck Gamma t1 T1.
    analyze T1 T11 T12.
    invert_typecheck (s |-> T11; Gamma) t2 T1.
    invert_typecheck (s0 |-> T12; Gamma) t3 T2.
    case_equality T1 T2.
  (* lists (the tm_lcase is given for free) *)
  - apply T_Nil.
  - invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T2 T11 T12.
    case_equality T1 T11.
  - (* tlcase *)
    rename s into x31, s0 into x32.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
    invert_typecheck Gamma t2 T2.
    remember (x31 |-> T11 ; x32 |-> <{{List T11}}> ; Gamma) as Gamma'2.
    invert_typecheck Gamma'2 t3 T3.
    case_equality T2 T3.
  (* unit *)
  - apply T_Unit.
  (* pairs *)
  - invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
  - invert_typecheck Gamma t T1.
    analyze T1 T11 T12.
    inversion H0. rewrite <- H2.
    eapply T_Fst. apply IHt.
    symmetry in HeqTO. apply HeqTO.
  - invert_typecheck Gamma t T2.
    analyze T2 T11 T12.
    inversion H0. rewrite <- H2.
    eapply T_Snd. apply IHt.
    symmetry in HeqTO. apply HeqTO.  
  (* let *)
  - invert_typecheck Gamma t1 T1.
    invert_typecheck (s |-> T1; Gamma) t2 T2.
  (* fix *)
  - invert_typecheck Gamma t T1.
    analyze T1 T11 T12.
    case_equality T11 T12.
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T ->
  type_check Gamma t = Some T.
Proof.
  intros Gamma t T Hty.
  induction Hty; simpl;
    try (rewrite IHHty);
    try (rewrite IHHty1);
    try (rewrite IHHty2);
    try (rewrite IHHty3);
    try (rewrite (eqb_ty_refl T0));
    try (rewrite (eqb_ty_refl T1));
    try (rewrite (eqb_ty_refl T2));
    try (rewrite (eqb_ty_refl T3));
    eauto.
    - destruct (Gamma _); [assumption| solve_by_invert].
Qed.

End TypecheckerExtensions.  