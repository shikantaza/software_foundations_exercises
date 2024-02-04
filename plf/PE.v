From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

From PLF Require Import Smallstep.
From PLF Require Import Imp.

Definition pe_state := list (string * nat).

Fixpoint pe_lookup (pe_st : pe_state) (V:string) : option nat :=
  match pe_st with
  | [] => None
  | (V',n')::pe_st => if String.eqb V V' then Some n'
                      else pe_lookup pe_st V
  end.
  
Definition empty_pe_state : pe_state := [].

Tactic Notation "compare" ident(i) ident(j) :=
  let H := fresh "Heq" i j in
  destruct (String.eqb_spec i j) as [H|H];
  [ subst j | ].
  
Theorem pe_domain: forall pe_st V n,
  pe_lookup pe_st V = Some n ->
  In V (map (@fst _ _) pe_st).
Proof.
intros.
induction pe_st.
- inversion H.
- simpl.
  destruct a.
  simpl in H.
  simpl.
  destruct (String.eqb V s) eqn: Heq.
  -- rewrite String.eqb_eq in Heq. rewrite Heq.
     left. reflexivity.
  -- right. apply IHpe_st. assumption.
Qed.

Fixpoint inb {A : Type} (eqb : A -> A -> bool) (a : A) (l : list A) :=
  match l with
  | [] => false
  | a'::l' => eqb a a' || inb eqb a l'
  end.
 
Lemma inbP : forall A : Type, forall eqb : A->A->bool,
  (forall a1 a2, reflect (a1 = a2) (eqb a1 a2)) ->
  forall a l, reflect (In a l) (inb eqb a l).
Proof.
intros.
induction l.
- simpl. apply ReflectF. unfold not. auto.
- simpl. pose proof (X a a0). inversion H. subst.
  -- simpl. apply ReflectT. left. auto.
  -- simpl. destruct IHl.
     + apply ReflectT. right. assumption.
     + apply ReflectF. unfold not. intros.
       destruct H2.
       ++ auto.
       ++ auto.
Qed.

(* book version *)
Lemma inbP' : forall A : Type, forall eqb : A->A->bool,
  (forall a1 a2, reflect (a1 = a2) (eqb a1 a2)) ->
  forall a l, reflect (In a l) (inb eqb a l).
Proof.
  intros A eqb beqP a l.
  induction l as [|a' l' IH].
  - constructor. intros [].
  - simpl. destruct (beqP a a').
    + subst. constructor. left. reflexivity.
    + simpl. destruct IH; constructor.
      * right. trivial.
      * intros [H1 | H2]; congruence.
Qed.

Fixpoint pe_aexp (pe_st : pe_state) (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i => match pe_lookup pe_st i with (* <----- NEW *)
             | Some n => ANum n
             | None => AId i
             end
  | <{ a1 + a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 + n2)
      | (a1', a2') => <{ a1' + a2' }>
      end
  | <{ a1 - a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 - n2)
      | (a1', a2') => <{ a1' - a2' }>
      end
  | <{ a1 * a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 * n2)
      | (a1', a2') => <{ a1' * a2' }>
      end
  end.

Example test_pe_aexp1:
  pe_aexp [(X,3)] <{X + 1 + Y}>
  = <{4 + Y}>.
Proof.
simpl. reflexivity.
Qed.

Example text_pe_aexp2:
  pe_aexp [(Y,3)] <{X + 1 + Y}>
  = <{X + 1 + 3}>.
Proof.
simpl. reflexivity.
Qed.

Definition pe_consistent (st:state) (pe_st:pe_state) :=
  forall V n, Some n = pe_lookup pe_st V -> st V = n.
  
Theorem pe_aexp_correct_weak: forall st pe_st, pe_consistent st pe_st ->
  forall a, aeval st a = aeval st (pe_aexp pe_st a).
Proof. 
unfold pe_consistent. intros st pe_st H a.
induction a.
- simpl. reflexivity.
- simpl. destruct (pe_lookup pe_st x) eqn: Heq.
  -- simpl. pose proof (H x n). apply H0. auto.
  -- simpl. reflexivity.
- unfold aeval. fold aeval.
  rewrite IHa1. rewrite IHa2.
  unfold pe_aexp. fold pe_aexp.
  destruct (pe_aexp pe_st a1).
  -- destruct (pe_aexp pe_st a2); simpl; reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
- unfold aeval. fold aeval.
  rewrite IHa1. rewrite IHa2.
  unfold pe_aexp. fold pe_aexp.
  destruct (pe_aexp pe_st a1).
  -- destruct (pe_aexp pe_st a2); simpl; reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
- unfold aeval. fold aeval.
  rewrite IHa1. rewrite IHa2.
  unfold pe_aexp. fold pe_aexp.
  destruct (pe_aexp pe_st a1).
  -- destruct (pe_aexp pe_st a2); simpl; reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.  
Qed.

Fixpoint pe_update (st:state) (pe_st:pe_state) : state :=
  match pe_st with
  | [] => st
  | (V,n)::pe_st => t_update (pe_update st pe_st) V n
  end.
  
Example test_pe_update:
  pe_update (Y !-> 1) [(X,3);(Z,2)]
  = (X !-> 3 ; Z !-> 2 ; Y !-> 1).
Proof. reflexivity. Qed.

Theorem false_eqb_string : forall x y : string,
   x <> y -> String.eqb x y = false.
Proof.
intros.
apply String.eqb_neq in H. assumption.
Qed.

Theorem pe_update_correct: forall st pe_st V0,
  pe_update st pe_st V0 =
  match pe_lookup pe_st V0 with
  | Some n => n
  | None => st V0
  end.
Proof.
intros.
induction pe_st.
- reflexivity.
- unfold pe_update. fold pe_update.
  destruct a. simpl.
  destruct (String.eqb V0 s) eqn: Heq.
  -- rewrite String.eqb_eq in Heq. rewrite Heq. rewrite t_update_eq. reflexivity.
  -- rewrite String.eqb_neq in Heq. rewrite t_update_neq.
     destruct (pe_lookup pe_st V0) eqn: Heq1; auto. unfold not in *.
     intros. apply Heq. auto.
Qed.

Theorem pe_update_consistent: forall st pe_st,
  pe_consistent (pe_update st pe_st) pe_st.
Proof.
intros.
unfold pe_consistent.
intros.
induction pe_st.
- simpl in H. inversion H.
- simpl. destruct a. simpl in H.
  destruct (String.eqb V s) eqn: Heq.
  -- rewrite String.eqb_eq in Heq. rewrite Heq. rewrite t_update_eq. inversion H. reflexivity.
  -- rewrite String.eqb_neq in Heq. rewrite t_update_neq.
     + eauto.
     + unfold not in *. intros. apply Heq. auto.
Qed.

Theorem pe_consistent_update: forall st pe_st,
  pe_consistent st pe_st -> forall V, st V = pe_update st pe_st V.
Proof.
intros.
rewrite pe_update_correct.
remember (pe_lookup pe_st V) as l.
destruct l.
  - unfold pe_consistent in H. apply (H V n Heql).
  - reflexivity. 
Qed.       

Print aeval.

Theorem pe_aexp_correct: forall (pe_st:pe_state) (a:aexp) (st:state),
  aeval (pe_update st pe_st) a = aeval st (pe_aexp pe_st a).     
Proof.
intros.
induction a.
- simpl. reflexivity.
- simpl. rewrite pe_update_correct.
  destruct (pe_lookup pe_st x) eqn: Heq.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
- unfold aeval. fold aeval.
  rewrite IHa1. rewrite IHa2.
  unfold pe_aexp. fold pe_aexp.
  destruct (pe_aexp pe_st a1).  
  -- destruct (pe_aexp pe_st a2); simpl; reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
- unfold aeval. fold aeval.
  rewrite IHa1. rewrite IHa2.
  unfold pe_aexp. fold pe_aexp.
  destruct (pe_aexp pe_st a1).  
  -- destruct (pe_aexp pe_st a2); simpl; reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
- unfold aeval. fold aeval.
  rewrite IHa1. rewrite IHa2.
  unfold pe_aexp. fold pe_aexp.
  destruct (pe_aexp pe_st a1).  
  -- destruct (pe_aexp pe_st a2); simpl; reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
Qed.

Fixpoint pe_bexp (pe_st : pe_state) (b : bexp) : bexp :=
  match b with
  | <{ true }> => <{ true }>
  | <{ false }> => <{ false }>
  | <{ a1 = a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if n1 =? n2 then <{ true }> else <{ false }>
      | (a1', a2') => <{ a1' = a2' }>
      end
  | <{ a1 <> a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if negb (n1 =? n2) then <{ true }> else <{ false }>
      | (a1', a2') => <{ a1' <> a2' }>
      end
  | <{ a1 <= a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if n1 <=? n2 then <{ true }> else <{ false }>
      | (a1', a2') => <{ a1' <= a2' }>
      end
  | <{ a1 > a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if n1 <=? n2 then <{ false }> else <{ true }>
      | (a1', a2') => <{ a1' > a2' }>
      end
  | <{ ~ b1 }> =>
      match (pe_bexp pe_st b1) with
      | <{ true }> => <{ false }>
      | <{ false }> => <{ true }>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }> =>
      match (pe_bexp pe_st b1, pe_bexp pe_st b2) with
      | (<{ true }>, <{ true }>) => <{ true }>
      | (<{ true }>, <{ false }>) => <{ false }>
      | (<{ false }>, <{ true }>) => <{ false }>
      | (<{ false }>, <{ false }>) => <{ false }>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.    
     
Example test_pe_bexp1:
  pe_bexp [(X,3)] <{~(X <= 3)}>
  = <{ false }>.   
Proof. simpl. reflexivity. Qed.

Example test_pe_bexp2: forall b:bexp,
  b = <{ ~(X <= (X + 1)) }> ->
  pe_bexp [] b = b.
Proof.
intros.
rewrite H.
simpl.
reflexivity.
Qed.

Theorem pe_bexp_correct: forall (pe_st:pe_state) (b:bexp) (st:state),
  beval (pe_update st pe_st) b = beval st (pe_bexp pe_st b).
Proof.
intros.
induction b.
- simpl. reflexivity.   
- simpl. reflexivity.
- unfold beval. fold beval.
  simpl pe_bexp.
  destruct (pe_aexp pe_st a1) eqn: Heqa1.
  -- destruct (pe_aexp pe_st a2) eqn: Heqa2.
     + destruct (eqb n n0) eqn: Heq.
       ++ simpl. rewrite pe_aexp_correct. rewrite pe_aexp_correct.
          rewrite Heqa1. rewrite Heqa2. simpl. assumption.
       ++ simpl. rewrite pe_aexp_correct. rewrite pe_aexp_correct.
          rewrite Heqa1. rewrite Heqa2. simpl. assumption.
     + rewrite pe_aexp_correct. rewrite pe_aexp_correct.
       rewrite Heqa1. rewrite Heqa2. simpl. reflexivity.
     + rewrite pe_aexp_correct. rewrite pe_aexp_correct.
       rewrite Heqa1. rewrite Heqa2. simpl. reflexivity.
     + rewrite pe_aexp_correct. rewrite pe_aexp_correct.
       rewrite Heqa1. rewrite Heqa2. simpl. reflexivity.
     + rewrite pe_aexp_correct. rewrite pe_aexp_correct.
       rewrite Heqa1. rewrite Heqa2. simpl. reflexivity.
  -- rewrite pe_aexp_correct. rewrite pe_aexp_correct.
     rewrite Heqa1. simpl. reflexivity.
  -- rewrite pe_aexp_correct. rewrite pe_aexp_correct.
     rewrite Heqa1. simpl. reflexivity.
  -- rewrite pe_aexp_correct. rewrite pe_aexp_correct.
     rewrite Heqa1. simpl. reflexivity.
  -- rewrite pe_aexp_correct. rewrite pe_aexp_correct.
     rewrite Heqa1. simpl. reflexivity.
- unfold beval. fold beval.
  simpl pe_bexp.
  destruct (pe_aexp pe_st a1) eqn: Heqa1.
  -- destruct (pe_aexp pe_st a2) eqn: Heqa2.
     + destruct (eqb n n0) eqn: Heq.
       ++ simpl. rewrite pe_aexp_correct. rewrite pe_aexp_correct.
          rewrite Heqa1. rewrite Heqa2. simpl. unfold negb. rewrite Heq. reflexivity.
       ++ simpl. rewrite pe_aexp_correct. rewrite pe_aexp_correct.
          rewrite Heqa1. rewrite Heqa2. simpl. unfold negb. rewrite Heq. reflexivity.
     + rewrite pe_aexp_correct. rewrite pe_aexp_correct.
       rewrite Heqa1. rewrite Heqa2. simpl. reflexivity.
     + rewrite pe_aexp_correct. rewrite pe_aexp_correct.
       rewrite Heqa1. rewrite Heqa2. simpl. reflexivity.
     + rewrite pe_aexp_correct. rewrite pe_aexp_correct.
       rewrite Heqa1. rewrite Heqa2. simpl. reflexivity.
     + rewrite pe_aexp_correct. rewrite pe_aexp_correct.
       rewrite Heqa1. rewrite Heqa2. simpl. reflexivity.
  -- rewrite pe_aexp_correct. rewrite pe_aexp_correct.
     rewrite Heqa1. simpl. reflexivity.
  -- rewrite pe_aexp_correct. rewrite pe_aexp_correct.
     rewrite Heqa1. simpl. reflexivity.
  -- rewrite pe_aexp_correct. rewrite pe_aexp_correct.
     rewrite Heqa1. simpl. reflexivity.
  -- rewrite pe_aexp_correct. rewrite pe_aexp_correct.
     rewrite Heqa1. simpl. reflexivity.
- unfold beval. fold beval.
  simpl pe_bexp.
  destruct (pe_aexp pe_st a1) eqn: Heqa1.
  -- destruct (pe_aexp pe_st a2) eqn: Heqa2.
     + destruct (eqb n n0) eqn: Heq.
       ++ simpl. rewrite pe_aexp_correct. rewrite pe_aexp_correct.
          rewrite Heqa1. rewrite Heqa2. simpl.
          rewrite eqb_eq in Heq. rewrite Heq.
          assert (n0 <=? n0 = true). { rewrite leb_iff. auto. }
          rewrite H. simpl. reflexivity.
       ++ simpl. rewrite pe_aexp_correct. rewrite pe_aexp_correct.
          rewrite Heqa1. rewrite Heqa2. simpl.
          destruct (n <=? n0). reflexivity. reflexivity.
     + rewrite pe_aexp_correct. rewrite pe_aexp_correct.
       rewrite Heqa1. rewrite Heqa2. simpl. reflexivity.
     + rewrite pe_aexp_correct. rewrite pe_aexp_correct.
       rewrite Heqa1. rewrite Heqa2. simpl. reflexivity.
     + rewrite pe_aexp_correct. rewrite pe_aexp_correct.
       rewrite Heqa1. rewrite Heqa2. simpl. reflexivity.
     + rewrite pe_aexp_correct. rewrite pe_aexp_correct.
       rewrite Heqa1. rewrite Heqa2. simpl. reflexivity.
  -- rewrite pe_aexp_correct. rewrite pe_aexp_correct.
     rewrite Heqa1. simpl. reflexivity.
  -- rewrite pe_aexp_correct. rewrite pe_aexp_correct.
     rewrite Heqa1. simpl. reflexivity.
  -- rewrite pe_aexp_correct. rewrite pe_aexp_correct.
     rewrite Heqa1. simpl. reflexivity.
  -- rewrite pe_aexp_correct. rewrite pe_aexp_correct.
     rewrite Heqa1. simpl. reflexivity.
- unfold beval. fold beval.
  simpl pe_bexp.
  destruct (pe_aexp pe_st a1) eqn: Heqa1.
  -- destruct (pe_aexp pe_st a2) eqn: Heqa2.
     + destruct (eqb n n0) eqn: Heq.
       ++ simpl. rewrite pe_aexp_correct. rewrite pe_aexp_correct.
          rewrite Heqa1. rewrite Heqa2. simpl. unfold negb.
          destruct (n <=? n0). reflexivity. reflexivity.
       ++ simpl. rewrite pe_aexp_correct. rewrite pe_aexp_correct.
          rewrite Heqa1. rewrite Heqa2. simpl. unfold negb.
          destruct (n <=? n0). reflexivity. reflexivity.          
     + rewrite pe_aexp_correct. rewrite pe_aexp_correct.
       rewrite Heqa1. rewrite Heqa2. simpl. reflexivity.
     + rewrite pe_aexp_correct. rewrite pe_aexp_correct.
       rewrite Heqa1. rewrite Heqa2. simpl. reflexivity.
     + rewrite pe_aexp_correct. rewrite pe_aexp_correct.
       rewrite Heqa1. rewrite Heqa2. simpl. reflexivity.
     + rewrite pe_aexp_correct. rewrite pe_aexp_correct.
       rewrite Heqa1. rewrite Heqa2. simpl. reflexivity.
  -- rewrite pe_aexp_correct. rewrite pe_aexp_correct.
     rewrite Heqa1. simpl. reflexivity.
  -- rewrite pe_aexp_correct. rewrite pe_aexp_correct.
     rewrite Heqa1. simpl. reflexivity.
  -- rewrite pe_aexp_correct. rewrite pe_aexp_correct.
     rewrite Heqa1. simpl. reflexivity.
  -- rewrite pe_aexp_correct. rewrite pe_aexp_correct.
     rewrite Heqa1. simpl. reflexivity.
- unfold beval. fold beval.
  simpl pe_bexp.
  destruct (pe_bexp pe_st b) eqn: Heqb.
  -- unfold negb. rewrite IHb. simpl. reflexivity.
  -- unfold negb. rewrite IHb. simpl. reflexivity.
  -- unfold negb. rewrite IHb. simpl. reflexivity.  
  -- unfold negb. rewrite IHb. simpl. reflexivity.  
  -- unfold negb. rewrite IHb. simpl. reflexivity.
  -- unfold negb. rewrite IHb. simpl. reflexivity.
  -- unfold negb. rewrite IHb. simpl. reflexivity.  
  -- unfold negb. rewrite IHb. simpl. reflexivity.  
- unfold beval. fold beval.
  simpl pe_bexp.
  rewrite IHb1. rewrite IHb2.
  destruct (pe_bexp pe_st b1) eqn: Heqb1.
  -- destruct (pe_bexp pe_st b2) eqn: Heqb2.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
  -- destruct (pe_bexp pe_st b2) eqn: Heqb2.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
  -- destruct (pe_bexp pe_st b2) eqn: Heqb2.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.          
  -- destruct (pe_bexp pe_st b2) eqn: Heqb2.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.          
  -- destruct (pe_bexp pe_st b2) eqn: Heqb2.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.          
  -- destruct (pe_bexp pe_st b2) eqn: Heqb2.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.          
  -- destruct (pe_bexp pe_st b2) eqn: Heqb2.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.          
  -- destruct (pe_bexp pe_st b2) eqn: Heqb2.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.
     + simpl. reflexivity.          
Qed.

Fixpoint pe_remove (pe_st:pe_state) (V:string) : pe_state :=
  match pe_st with
  | [] => []
  | (V',n')::pe_st => if String.eqb V V' then pe_remove pe_st V
                      else (V',n') :: pe_remove pe_st V
  end.

Theorem pe_remove_correct: forall pe_st V V0,
  pe_lookup (pe_remove pe_st V) V0
  = if String.eqb V V0 then None else pe_lookup pe_st V0.
Proof.
intros.
induction pe_st.
- simpl. compare V V0. reflexivity. reflexivity.
- destruct a. simpl. compare V s.
  -- compare V0 V. 
     + assert ((V0 =? V0)%string = true). 
         rewrite String.eqb_eq. reflexivity.
       rewrite H. rewrite H in IHpe_st. assumption.
     + assert (V <> V0).
         unfold not in *. intros. apply HeqV0V. auto. 
       rewrite <- String.eqb_neq in H. rewrite H in *. assumption. 
  -- compare V V0.
     + simpl. 
       rewrite <- String.eqb_neq in HeqVs. rewrite HeqVs. assumption.
     + simpl.
       destruct (String.eqb V0 s) eqn: HeqV0s.
       ++ reflexivity.
       ++ assumption.
Qed.

Definition pe_add (pe_st:pe_state) (V:string) (n:nat) : pe_state :=
  (V,n) :: pe_remove pe_st V.      

Theorem string_eqb_refl : forall s, (s =? s)%string = true.
Proof. intros. rewrite String.eqb_eq. reflexivity. Qed.

Theorem string_neq_comm : forall s1 s2 : string, s1 <> s2 -> s2 <> s1.
Proof. intros. unfold not in *. intros. apply H. auto. Qed.

Theorem string_eqb_comm : forall s1 s2, (s1 =? s2)%string = (s2 =? s1)%string.
Proof.
intros.
compare s1 s2.
- rewrite string_eqb_refl. reflexivity.
- symmetry. rewrite String.eqb_neq. unfold not in *. intros. apply Heqs1s2. auto.
Qed.
  
Theorem pe_add_correct: forall pe_st V n V0,
  pe_lookup (pe_add pe_st V n) V0
  = if String.eqb V V0 then Some n else pe_lookup pe_st V0.
Proof.
intros.
induction pe_st.
- simpl.
  assert ((V0 =? V)%string = (V =? V0)%string). 
    compare V V0.
      apply String.eqb_eq. reflexivity.
      apply String.eqb_neq. unfold not in *. intros. apply HeqVV0. auto.  
  rewrite H. reflexivity.
- simpl in *.
  compare V0 V.
  -- rewrite string_eqb_refl. reflexivity.
  -- destruct a. compare V s.
     + apply string_neq_comm in HeqV0V.
       rewrite <- String.eqb_neq in HeqV0V. rewrite HeqV0V in *.
       rewrite string_eqb_comm. rewrite HeqV0V. assumption.
     + rewrite string_eqb_comm. rewrite <- String.eqb_neq in HeqV0V.
       rewrite HeqV0V.
       simpl.
       compare V0 s. reflexivity.
       rewrite string_eqb_comm in IHpe_st.
       rewrite HeqV0V in IHpe_st. assumption.
Qed.

Theorem pe_update_update_remove: forall st pe_st V n,
  t_update (pe_update st pe_st) V n =
  pe_update (t_update st V n) (pe_remove pe_st V).
Proof.
intros.
apply functional_extensionality.
intros.
induction pe_st.
- simpl. reflexivity.
- destruct a. simpl.
  compare V s.
  -- rewrite t_update_shadow. assumption.
  -- simpl. compare V x.
     + rewrite t_update_eq.
       rewrite t_update_neq.
       ++ rewrite <- IHpe_st. rewrite t_update_eq. reflexivity.
       ++ unfold not in *. intros. apply HeqVs. auto.
     + rewrite t_update_neq.
       ++ compare s x.
          +++ rewrite t_update_eq. rewrite t_update_eq. reflexivity.
          +++ rewrite t_update_neq.
              ++++ rewrite t_update_neq. 
                     rewrite <- IHpe_st.
                     rewrite t_update_neq. reflexivity. assumption.
                   assumption.
              ++++ assumption.
       ++ assumption.
Qed.

Theorem pe_update_update_add: forall st pe_st V n,
  t_update (pe_update st pe_st) V n =
  pe_update st (pe_add pe_st V n).
Proof.
intros.
apply functional_extensionality.
intros.
compare V x.
- rewrite t_update_eq. simpl. 
  rewrite t_update_eq. reflexivity.
- rewrite t_update_neq.
  -- simpl. rewrite t_update_neq.
     induction pe_st.
     + simpl. reflexivity.
     + destruct a. simpl.
       compare V s.
       ++ rewrite t_update_neq. assumption. assumption.
       ++ simpl. compare s x.
          +++ rewrite !t_update_eq. reflexivity.
          +++ rewrite !t_update_neq. assumption. assumption. assumption.
     + assumption.
  -- assumption. 
Qed.

Definition pe_disagree_at (pe_st1 pe_st2 : pe_state) (V:string) : bool :=
  match pe_lookup pe_st1 V, pe_lookup pe_st2 V with
  | Some x, Some y => negb (x =? y)
  | None, None => false
  | _, _ => true
  end.                 

Lemma in_orl : forall V (st1 st2 : pe_state),
  In V (map (@fst _ _) st1) -> In V ((map (@fst _ _) st1) ++ (map (@fst _ _) st2)).
Proof.
intros.
remember (map fst st1) as l1. clear Heql1.
remember (map fst st2) as l2. clear Heql2.
induction l1.
- inversion H.
- induction l2. 
  -- simpl. inversion H.
     + left. assumption.
     + right. rewrite app_nil_r. assumption.
  -- simpl. inversion H.
     + left. assumption.
     + right. eauto. 
Qed.

Lemma in_orr : forall V (st1 st2 : pe_state),
  In V (map (@fst _ _) st2) -> In V ((map (@fst _ _) st1) ++ (map (@fst _ _) st2)).
intros.
remember (map fst st1) as l1. clear Heql1.
remember (map fst st2) as l2. clear Heql2.
induction l1.
- rewrite app_nil_l. assumption.
- induction l2. 
  -- simpl. inversion H.
  -- simpl. inversion H.
     + right. assumption.
     + right. assumption. 
Qed.

Theorem pe_disagree_domain: forall (pe_st1 pe_st2 : pe_state) (V:string),
  true = pe_disagree_at pe_st1 pe_st2 V ->
  In V (map (@fst _ _) pe_st1 ++ map (@fst _ _) pe_st2).
Proof.
intros.
unfold pe_disagree_at in H.
destruct (pe_lookup pe_st1 V) eqn: Heq1.
- apply pe_domain in Heq1. apply in_orl. assumption.
- destruct (pe_lookup pe_st2 V) eqn: Heq2.
  -- apply pe_domain in Heq2. apply in_orr.  assumption.
  -- inversion H.
Qed.

Fixpoint pe_unique (l : list string) : list string :=
  match l with
  | [] => []
  | x::l =>
      x :: filter (fun y => if String.eqb x y then false else true) (pe_unique l)
  end.

Print filter_In.

(* book version; couldn't prove it without knowing about filter_In *)
Theorem pe_unique_correct: forall l x,
  In x l <-> In x (pe_unique l).
Proof. intros l x. induction l as [| h t]. reflexivity.
  simpl in *. split.
  - (* -> *)
    intros. inversion H; clear H.
      left. assumption.
      destruct (String.eqb_spec h x).
         left. assumption.
         right. apply filter_In. split.
           apply IHt. assumption.
           rewrite false_eqb_string; auto.
  - (* <- *)
    intros. inversion H; clear H.
       left. assumption.
       apply filter_In in H0. inversion H0. right. apply IHt. assumption.
Qed.

Definition pe_compare (pe_st1 pe_st2 : pe_state) : list string :=
  pe_unique (filter (pe_disagree_at pe_st1 pe_st2)
    (map (@fst _ _) pe_st1 ++ map (@fst _ _) pe_st2)).

Theorem pe_compare_correct: forall pe_st1 pe_st2 V,
  pe_lookup pe_st1 V = pe_lookup pe_st2 V <->
  ~ In V (pe_compare pe_st1 pe_st2).
Proof.
intros.
split.
- intros. unfold not. intros.
  unfold pe_compare in H0.
  rewrite <- pe_unique_correct in H0.
  rewrite filter_In in H0.
  destruct H0.
  unfold pe_disagree_at in H1.
  destruct (pe_lookup pe_st1 V) eqn: Heq1.
  -- destruct (pe_lookup pe_st2 V) eqn: Heq2.
     + inversion H. rewrite H3 in H1. unfold negb in H1.
       rewrite eqb_refl in H1. inversion H1.
     + inversion H.
  -- destruct (pe_lookup pe_st2 V) eqn: Heq2.
     + inversion H.
     + inversion H1.
- intros. unfold not in H.
  unfold pe_compare in H.
  rewrite <- pe_unique_correct in H.
  rewrite filter_In in H.
  
  (* taken from book *)
  assert (Hagree: pe_disagree_at pe_st1 pe_st2 V = false).
    { (* Proof of assertion *)
      remember (pe_disagree_at pe_st1 pe_st2 V) as disagree.
      destruct disagree; [| reflexivity].
      apply pe_disagree_domain in Heqdisagree.
      exfalso. apply H. split. assumption. reflexivity. }
  unfold pe_disagree_at in Hagree.
  destruct (pe_lookup pe_st1 V) as [n1|];
  destruct (pe_lookup pe_st2 V) as [n2|];
      try reflexivity; try solve_by_invert.
    rewrite negb_false_iff in Hagree.
    apply eqb_eq in Hagree. subst. reflexivity.
Qed.

Fixpoint pe_removes (pe_st:pe_state) (ids : list string) : pe_state :=
  match ids with
  | [] => pe_st
  | V::ids => pe_remove (pe_removes pe_st ids) V
  end.

Theorem pe_removes_correct: forall pe_st ids V,
  pe_lookup (pe_removes pe_st ids) V =
  if inb String.eqb V ids then None else pe_lookup pe_st V.
Proof.
intros.
induction ids.
- simpl. reflexivity.
- simpl. compare V a.
  -- simpl. rewrite pe_remove_correct. rewrite string_eqb_refl. reflexivity.
  -- simpl. rewrite pe_remove_correct.
     rewrite string_eqb_comm.
     rewrite <- String.eqb_neq in HeqVa. rewrite HeqVa. assumption.
Qed.

Check String.eqb_spec.

Theorem pe_compare_removes: forall pe_st1 pe_st2 V,
  pe_lookup (pe_removes pe_st1 (pe_compare pe_st1 pe_st2)) V =
  pe_lookup (pe_removes pe_st2 (pe_compare pe_st1 pe_st2)) V.
Proof.
intros.
rewrite !pe_removes_correct.
destruct (inb String.eqb V (pe_compare pe_st1 pe_st2)) eqn: Heq.
- reflexivity.
- rewrite pe_compare_correct.
  intros. unfold not. intros.
  pose proof (inbP string String.eqb).
  assert (forall a1 a2 : string,
            reflect (a1 = a2) (a1 =? a2)%string).
  {
    intros. compare a1 a2.
    -- apply ReflectT. reflexivity.
    -- apply ReflectF. assumption.
  }
  pose proof (H0 H1).
  pose proof (H2 V (pe_compare pe_st1 pe_st2)).
  rewrite Heq in H3.
  inversion H3.
  apply (H4 H).
Qed.

Theorem pe_compare_update: forall pe_st1 pe_st2 st,
  pe_update st (pe_removes pe_st1 (pe_compare pe_st1 pe_st2)) =
  pe_update st (pe_removes pe_st2 (pe_compare pe_st1 pe_st2)).
Proof.
intros.
apply functional_extensionality.
intros.
rewrite !pe_update_correct.
rewrite pe_compare_removes.
reflexivity.
Qed.

Fixpoint assign (pe_st : pe_state) (ids : list string) : com :=
  match ids with
  | [] => <{ skip }>
  | V::ids => match pe_lookup pe_st V with
              | Some n => <{ assign pe_st ids; V := n }>
              | None => assign pe_st ids
              end
  end.
  
Definition assigned (pe_st:pe_state) (ids : list string) (st:state) : state :=
  fun V => if inb String.eqb V ids then
                match pe_lookup pe_st V with
                | Some n => n
                | None => st V
                end
           else st V.

Theorem assign_removes: forall pe_st ids st,
  pe_update st pe_st =
  pe_update (assigned pe_st ids st) (pe_removes pe_st ids).
Proof.
intros.
apply functional_extensionality.
intros.
rewrite !pe_update_correct.
unfold assigned.
rewrite pe_removes_correct.
destruct (pe_lookup pe_st x).
- destruct (inb String.eqb x ids). reflexivity. reflexivity.
- destruct (inb String.eqb x ids). reflexivity. reflexivity.
Qed.

Lemma ceval_extensionality: forall c st st1 st2,
  st =[ c ]=> st1 -> (forall V, st1 V = st2 V) -> st =[ c ]=> st2.
Proof.
intros.
apply functional_extensionality in H0.
rewrite H0 in H. assumption.
Qed.

Theorem eval_assign: forall pe_st ids st,
  st =[ assign pe_st ids ]=> assigned pe_st ids st.
Proof.
intros.
induction ids.
- simpl.
  apply E_Skip.
- simpl.
  destruct (pe_lookup pe_st a) eqn: Heq.
  -- eapply E_Seq.
     + apply IHids.
     + assert ((assigned pe_st (a :: ids) st) = (a !-> n ; (assigned pe_st ids st))).
       {
         apply functional_extensionality.
         intros.
         unfold assigned.
         compare x a.
         - simpl. rewrite string_eqb_refl. simpl.
           rewrite t_update_eq. rewrite Heq. reflexivity.
         - rewrite t_update_neq.
           -- simpl. rewrite <- String.eqb_neq in Heqxa. rewrite Heqxa. simpl. reflexivity. 
           -- unfold not. intros. apply Heqxa. auto.
       }
       rewrite H. apply E_Asgn. simpl. reflexivity.
  -- eapply ceval_extensionality.
     + apply IHids.
     + intros. unfold assigned.
       compare V a.
       ++ rewrite Heq. simpl.
          destruct (inb String.eqb V ids).
          +++ rewrite string_eqb_refl. simpl. reflexivity.
          +++ rewrite string_eqb_refl. simpl. reflexivity.
       ++ destruct (inb String.eqb V ids) eqn: HeqV.
          +++ simpl. rewrite <- String.eqb_neq in HeqVa. rewrite HeqVa. simpl.
              rewrite HeqV. reflexivity.
          +++ simpl. rewrite <- String.eqb_neq in HeqVa. rewrite HeqVa. simpl.
              rewrite HeqV. reflexivity.
Qed.

Reserved Notation "c1 '/' st '==>' c1' '/' st'"
  (at level 40, st at level 39, c1' at level 39).
  
Inductive pe_com : com -> pe_state -> com -> pe_state -> Prop :=
  | PE_Skip : forall pe_st,
      <{skip}> / pe_st ==> <{skip}> / pe_st
  | PE_AsgnStatic : forall pe_st a1 (n1 : nat) l,
      pe_aexp pe_st a1 = <{ n1 }> ->
      <{l := a1}> / pe_st ==> <{skip}> / pe_add pe_st l n1
  | PE_AsgnDynamic : forall pe_st a1 a1' l,
      pe_aexp pe_st a1 = a1' ->
      (forall n : nat , a1' <> <{ n }>) ->
      <{l := a1}> / pe_st ==> <{l := a1'}> / pe_remove pe_st l
  | PE_Seq : forall pe_st pe_st' pe_st'' c1 c2 c1' c2',
      c1 / pe_st ==> c1' / pe_st' ->
      c2 / pe_st' ==> c2' / pe_st'' ->
      <{c1 ; c2}> / pe_st ==> <{c1' ; c2'}> / pe_st''
  | PE_IfTrue : forall pe_st pe_st' b1 c1 c2 c1',
      pe_bexp pe_st b1 = <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' ->
      <{if b1 then c1 else c2 end}> / pe_st ==> c1' / pe_st'
  | PE_IfFalse : forall pe_st pe_st' b1 c1 c2 c2',
      pe_bexp pe_st b1 = <{ false }> ->
      c2 / pe_st ==> c2' / pe_st' ->
      <{if b1 then c1 else c2 end}> / pe_st ==> c2' / pe_st'
  | PE_If : forall pe_st pe_st1 pe_st2 b1 c1 c2 c1' c2',
      pe_bexp pe_st b1 <> <{ true }> ->
      pe_bexp pe_st b1 <> <{ false }> ->
      c1 / pe_st ==> c1' / pe_st1 ->
      c2 / pe_st ==> c2' / pe_st2 ->
      <{if b1 then c1 else c2 end}> / pe_st
        ==> <{if pe_bexp pe_st b1
             then c1' ; assign pe_st1 (pe_compare pe_st1 pe_st2)
             else c2' ; assign pe_st2 (pe_compare pe_st1 pe_st2) end}>
            / pe_removes pe_st1 (pe_compare pe_st1 pe_st2)

  where "c1 '/' st '==>' c1' '/' st'" := (pe_com c1 st c1' st').

Local Hint Constructors pe_com : core.
Local Hint Constructors ceval : core.

Example pe_example1:
  <{X := 3 ; Y := Z * (X + X)}>
  / [] ==> <{skip; Y := Z * 6}> / [(X,3)].
Proof.
eapply PE_Seq.
- apply PE_AsgnStatic. simpl. reflexivity.
- apply PE_AsgnDynamic.
  -- simpl. reflexivity.
  -- intros. unfold not. intros. inversion H.
Qed.

Example pe_example2:
  <{X := 3 ; if X <= 4 then X := 4 else skip end}>
  / [] ==> <{skip; skip}> / [(X,4)].
Proof.
eapply PE_Seq.
- apply PE_AsgnStatic. simpl. reflexivity.
- apply PE_IfTrue.
  -- simpl. reflexivity.
  -- apply PE_AsgnStatic. simpl. reflexivity.
Qed.

Compute (pe_compare [(Y,4) ; (X,3)] [(X,3)]).

Compute (pe_disagree_at [(Y,4) ; (X,3)] [(X,3)] Y).

Example pe_example3:
  <{X := 3;
   if Y <= 4 then
     Y := 4;
     if X = Y then Y := 999 else skip end
   else skip end}> / []
  ==> <{skip;
       if Y <= 4 then
         (skip; skip); (skip; Y := 4)
       else skip; skip end}>
      / [(X,3)].
Proof.
eapply PE_Seq.
- apply PE_AsgnStatic. simpl. reflexivity.
- unfold pe_add. simpl.
  assert (<{if Y <= 4 then
             Y := 4;
             if X = Y then Y := 999 else skip end
             else skip end}> / [(X,3)]
          ==> <{if Y <= 4 then
                  (skip;
                  skip); assign [(Y,4) ; (X,3)] (pe_compare [(Y,4) ; (X,3)] [(X,3)])
                else 
                  skip;  
                  assign [(X,3)] (pe_compare [(Y,4) ; (X,3)] [(X,3)])
                  end }> / (pe_removes [(Y,4) ; (X,3)] (pe_compare [(Y,4) ; (X,3)] [(X,3)]))).
    apply PE_If.
    -- simpl. unfold not. intros. inversion H.
    -- simpl. unfold not. intros. inversion H.
    -- eapply PE_Seq.
       + apply PE_AsgnStatic. simpl. reflexivity.
       + unfold pe_add. simpl.
         apply PE_IfFalse.
         ++ simpl. reflexivity.
         ++ apply PE_Skip.
    -- apply PE_Skip.
    -- simpl in H.
       assumption.
Qed.   

Reserved Notation "c' '/' pe_st' '/' st '==>' st''"
  (at level 40, pe_st' at level 39, st at level 39).
  
Inductive pe_ceval
  (c':com) (pe_st':pe_state) (st:state) (st'':state) : Prop :=
  | pe_ceval_intro : forall st',
    st =[ c' ]=> st' ->
    pe_update st' pe_st' = st'' ->
    c' / pe_st' / st ==> st''
  where "c' '/' pe_st' '/' st '==>' st''" := (pe_ceval c' pe_st' st st'').
  
Local Hint Constructors pe_ceval : core.

(* initial parts taken from book proof *)
Theorem pe_com_complete:
  forall c pe_st pe_st' c', c / pe_st ==> c' / pe_st' ->
  forall st st'',
  (pe_update st pe_st =[ c ]=> st'') ->
  (c' / pe_st' / st ==> st'').
Proof.
intros c pe_st pe_st' c' Hpe.
  induction Hpe; intros st st'' Heval.
  - inversion Heval. subst. eauto.
  - inversion Heval. subst. eapply pe_ceval_intro. apply E_Skip. rewrite pe_aexp_correct.
    rewrite H. simpl. apply functional_extensionality. intros. compare l x.
    -- rewrite !t_update_eq. reflexivity.
    -- rewrite !t_update_neq.
       + rewrite !pe_update_correct.
         destruct (pe_lookup pe_st x) eqn: Heq1.
         ++ destruct (pe_lookup (pe_remove pe_st l) x) eqn: Heq2.
            +++ rewrite pe_remove_correct in Heq2.
                rewrite <- String.eqb_neq in Heqlx. rewrite Heqlx in Heq2. rewrite Heq1 in Heq2.
                inversion Heq2. auto.
            +++ rewrite pe_remove_correct in Heq2. 
                rewrite <- String.eqb_neq in Heqlx. rewrite Heqlx in Heq2. rewrite Heq1 in Heq2.
                inversion Heq2.
         ++ destruct (pe_lookup (pe_remove pe_st l) x) eqn: Heq2.
            +++ rewrite pe_remove_correct in Heq2.
                rewrite <- String.eqb_neq in Heqlx. rewrite Heqlx in Heq2. rewrite Heq1 in Heq2.
                inversion Heq2.
            +++ auto.
      + auto.
      + auto. 
  - inversion Heval. subst.
    apply pe_ceval_intro with (st' := (l !-> (aeval st (pe_aexp pe_st a1)); st)).
    -- apply E_Asgn. reflexivity.
    -- apply functional_extensionality. intros.
       compare l x.
       + rewrite pe_update_update_remove. rewrite pe_aexp_correct. reflexivity.
       + rewrite pe_update_update_remove. rewrite pe_aexp_correct. reflexivity. 
  - inversion Heval. subst.
    edestruct IHHpe1. eassumption. subst.
    edestruct IHHpe2. eassumption. eauto.
  - inversion Heval; subst.
    -- apply IHHpe. auto.
    -- apply IHHpe. rewrite pe_bexp_correct in H5. rewrite H in H5. inversion H5.
  - inversion Heval; subst.
    -- apply IHHpe. rewrite pe_bexp_correct in H5. rewrite H in H5. inversion H5.
    -- apply IHHpe. auto.    
  - inversion Heval; subst.
    -- apply IHHpe1 in H7. inversion H7.
       eapply pe_ceval_intro.
       + apply E_IfTrue.
         ++ rewrite pe_bexp_correct in H6. auto.
         ++ eapply E_Seq with (st' := st').
            +++ auto.
            +++ apply eval_assign.
       + rewrite <- assign_removes with (ids := (pe_compare pe_st1 pe_st2)). auto.
    -- apply IHHpe2 in H7. inversion H7.
       eapply pe_ceval_intro.
       + apply E_IfFalse.
         ++ rewrite pe_bexp_correct in H6. auto.
         ++ eapply E_Seq with (st' := st').
            +++ auto.
            +++ apply eval_assign.
       + rewrite pe_compare_update. 
         rewrite <- assign_removes with (ids := (pe_compare pe_st1 pe_st2)).
         auto.
Qed.

Theorem pe_com_sound:
  forall c pe_st pe_st' c', c / pe_st ==> c' / pe_st' ->
  forall st st'',
  (c' / pe_st' / st ==> st'') ->
  (pe_update st pe_st =[ c ]=> st'').
Proof.
intros c pe_st pe_st' c' Hpe.
induction Hpe; intros st st'' [st' Heval Heq].
- inversion Heval. subst. apply E_Skip.
- inversion Heval. subst.
  rewrite <- pe_update_update_add. apply E_Asgn. rewrite pe_aexp_correct. rewrite H. reflexivity.
- inversion Heval. subst. 
  rewrite <- pe_update_update_remove. apply E_Asgn. rewrite pe_aexp_correct. reflexivity.
- inversion Heval. subst.
  eapply E_Seq.
  -- apply IHHpe1. eapply pe_ceval_intro with (st' := st'0).
     + apply H1.
     + reflexivity.
  -- apply IHHpe2. eapply pe_ceval_intro.
     + apply H4.
     + reflexivity.
- eapply E_IfTrue.
  -- rewrite pe_bexp_correct. rewrite H. reflexivity.
  -- apply IHHpe. eapply pe_ceval_intro. apply Heval. apply Heq.
- eapply E_IfFalse.
  -- rewrite pe_bexp_correct. rewrite H. reflexivity.
  -- apply IHHpe. eapply pe_ceval_intro. apply Heval. apply Heq.
(* book version; have simplified/expanded it for better understanding *)
(*
- inversion Heval; subst; inversion H7;
  (eapply ceval_deterministic in H8; [| apply eval_assign]); subst.
  -- apply E_IfTrue.
     + rewrite pe_bexp_correct. assumption.
     + rewrite <- assign_removes.
       apply IHHpe1. eapply pe_ceval_intro.
       ++ apply H3.
       ++ reflexivity.
  -- rewrite -> pe_compare_update. 
     apply E_IfFalse.
     + rewrite pe_bexp_correct. assumption.
     + rewrite <- assign_removes.
       apply IHHpe2. eapply pe_ceval_intro.
       ++ apply H3.
       ++ reflexivity.
*)
- inversion Heval.
  -- subst. inversion H7.
     assert (st' = assigned pe_st1 (pe_compare pe_st1 pe_st2) st'0).
       pose proof (eval_assign pe_st1 (pe_compare pe_st1 pe_st2) st'0).
       pose proof (ceval_deterministic (assign pe_st1 (pe_compare pe_st1 pe_st2))
                                       st'0
                                       st'
                                       (assigned pe_st1 (pe_compare pe_st1 pe_st2) st'0)
                                       H8
                                       H9).
       assumption.
     rewrite H9.                                   
     apply E_IfTrue.
     + rewrite pe_bexp_correct. assumption.
     + rewrite <- assign_removes.
       apply IHHpe1. eapply pe_ceval_intro.
       ++ apply H3.
       ++ reflexivity.
  -- (* same thing as above can be done here as well *)
     subst. inversion H7. 
     eapply ceval_deterministic in H8. 2 : { apply eval_assign. } 
     subst.
     rewrite -> pe_compare_update. 
     apply E_IfFalse.
     + rewrite pe_bexp_correct. assumption.
     + rewrite <- assign_removes.
       apply IHHpe2. eapply pe_ceval_intro.
       ++ apply H3.
       ++ reflexivity.
Qed.

Corollary pe_com_correct:
  forall c pe_st pe_st' c', c / pe_st ==> c' / pe_st' ->
  forall st st'',
  (pe_update st pe_st =[ c ]=> st'') <->
  (c' / pe_st' / st ==> st'').
Proof.
intros c pe_st pe_st' c' H st st''. split.
- apply pe_com_complete. assumption.
- apply pe_com_sound. assumption.
Qed.

Module Loop.

Reserved Notation "c1 '/' st '==>' c1' '/' st' '/' c''"
  (at level 40, st at level 39, c1' at level 39, st' at level 39).

Inductive pe_com : com -> pe_state -> com -> pe_state -> com -> Prop :=
  | PE_Skip : forall pe_st,
      <{ skip }> / pe_st ==> <{ skip }> / pe_st / <{skip}>
  | PE_AsgnStatic : forall pe_st a1 (n1 : nat) l,
      pe_aexp pe_st a1 = <{ n1 }> ->
      <{ l := a1 }> / pe_st ==> <{ skip }> / pe_add pe_st l n1 / <{skip}>
  | PE_AsgnDynamic : forall pe_st a1 a1' l,
      pe_aexp pe_st a1 = a1' ->
      (forall n : nat, a1' <> <{ n }> ) ->
      <{l := a1}> / pe_st ==> <{l := a1'}> / pe_remove pe_st l / <{skip}>
  | PE_Seq : forall pe_st pe_st' pe_st'' c1 c2 c1' c2' c'',
      c1 / pe_st ==> c1' / pe_st' / <{skip}> ->
      c2 / pe_st' ==> c2' / pe_st'' / c'' ->
      <{c1 ; c2}> / pe_st ==> <{c1' ; c2'}> / pe_st'' / c''
  | PE_IfTrue : forall pe_st pe_st' b1 c1 c2 c1' c'',
      pe_bexp pe_st b1 = <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' / c'' ->
      <{if b1 then c1 else c2 end}> / pe_st ==> c1' / pe_st' / c''
  | PE_IfFalse : forall pe_st pe_st' b1 c1 c2 c2' c'',
      pe_bexp pe_st b1 = <{ false }> ->
      c2 / pe_st ==> c2' / pe_st' / c'' ->
      <{if b1 then c1 else c2 end}> / pe_st ==> c2' / pe_st' / c''
  | PE_If : forall pe_st pe_st1 pe_st2 b1 c1 c2 c1' c2' c'',
      pe_bexp pe_st b1 <> <{ true }> ->
      pe_bexp pe_st b1 <> <{ false }> ->
      c1 / pe_st ==> c1' / pe_st1 / c'' ->
      c2 / pe_st ==> c2' / pe_st2 / c'' ->
      <{if b1 then c1 else c2 end}> / pe_st
        ==> <{if pe_bexp pe_st b1
             then c1' ; assign pe_st1 (pe_compare pe_st1 pe_st2)
             else c2' ; assign pe_st2 (pe_compare pe_st1 pe_st2) end}>
            / pe_removes pe_st1 (pe_compare pe_st1 pe_st2)
            / c''
  | PE_WhileFalse : forall pe_st b1 c1,
      pe_bexp pe_st b1 = <{ false }> ->
      <{while b1 do c1 end}> / pe_st ==> <{skip}> / pe_st / <{skip}>
  | PE_WhileTrue : forall pe_st pe_st' pe_st'' b1 c1 c1' c2' c2'',
      pe_bexp pe_st b1 = <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' / <{skip}> ->
      <{while b1 do c1 end}> / pe_st' ==> c2' / pe_st'' / c2'' ->
      pe_compare pe_st pe_st'' <> [] ->
      <{while b1 do c1 end}> / pe_st ==> <{c1';c2'}> / pe_st'' / c2''
  | PE_While : forall pe_st pe_st' pe_st'' b1 c1 c1' c2' c2'',
      pe_bexp pe_st b1 <> <{ false }> ->
      pe_bexp pe_st b1 <> <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' / <{skip}> ->
      <{while b1 do c1 end}> / pe_st' ==> c2' / pe_st'' / c2'' ->
      pe_compare pe_st pe_st'' <> [] ->
      (c2'' = <{skip}> \/ c2'' = <{while b1 do c1 end}>) ->
      <{while b1 do c1 end}> / pe_st
        ==> <{if pe_bexp pe_st b1
             then c1'; c2'; assign pe_st'' (pe_compare pe_st pe_st'')
             else assign pe_st (pe_compare pe_st pe_st'') end}>
            / pe_removes pe_st (pe_compare pe_st pe_st'')
            / c2''
  | PE_WhileFixedEnd : forall pe_st b1 c1,
      pe_bexp pe_st b1 <> <{ false }> ->
      <{while b1 do c1 end}> / pe_st ==> <{skip}> / pe_st / <{while b1 do c1 end}>
  | PE_WhileFixedLoop : forall pe_st pe_st' pe_st'' b1 c1 c1' c2',
      pe_bexp pe_st b1 = <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' / <{skip}> ->
      <{while b1 do c1 end}> / pe_st'
        ==> c2' / pe_st'' / <{while b1 do c1 end}>->
      pe_compare pe_st pe_st'' = [] ->
      <{while b1 do c1 end}> / pe_st
        ==> <{while true do skip end}> / pe_st / <{skip}>
      (* Because we have an infinite loop, we should actually
         start to throw away the rest of the program:
         (while b1 do c1 end) / pe_st
         ==> skip / pe_st / (while true do skip end) *)
  | PE_WhileFixed : forall pe_st pe_st' pe_st'' b1 c1 c1' c2',
      pe_bexp pe_st b1 <> <{ false }> ->
      pe_bexp pe_st b1 <> <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' / <{skip}> ->
      <{while b1 do c1 end}> / pe_st'
        ==> c2' / pe_st'' / <{while b1 do c1 end}> ->
      pe_compare pe_st pe_st'' = [] ->
      <{while b1 do c1 end}> / pe_st
        ==> <{while pe_bexp pe_st b1 do c1'; c2' end}> / pe_st / <{skip}>

  where "c1 '/' st '==>' c1' '/' st' '/' c''" := (pe_com c1 st c1' st' c'').
  
Local Hint Constructors pe_com : core.

Ltac step i :=
  (eapply i; intuition eauto; try solve_by_invert);
  repeat (try eapply PE_Seq;
          try (eapply PE_AsgnStatic; simpl; reflexivity);
          try (eapply PE_AsgnDynamic;
               [ simpl; reflexivity
               | intuition eauto; solve_by_invert])).

Definition square_loop: com :=
  <{while 1 <= X do
    Y := Y * Y;
    X := X - 1
  end}>.

Example pe_loop_example1:
  square_loop / []
  ==> <{while 1 <= X do
         (Y := Y * Y;
          X := X - 1); skip
       end}> / [] / <{skip}>.
Proof.
eapply PE_WhileFixed.
- unfold not. intros. inversion H.
- unfold not. intros. inversion H.
- eapply PE_Seq.
  -- apply PE_AsgnDynamic.
     + simpl. reflexivity.
     + intros. unfold not. intros. inversion H.
  -- eapply PE_AsgnDynamic.
     + simpl. reflexivity.
     + intros. unfold not. intros. inversion H.
- simpl. eapply PE_WhileFixedEnd.
  unfold not. intros. simpl in H. inversion H.
- auto.
Qed.

Example pe_loop_example2:
  <{X := 3; square_loop}> / []
  ==> <{skip;
       (Y := Y * Y; skip);
       (Y := Y * Y; skip);
       (Y := Y * Y; skip);
       skip}> / [(X,0)] / <{skip}>.
Proof.
eapply PE_Seq.
- apply PE_AsgnStatic. simpl. reflexivity.
- unfold square_loop.
  eapply PE_WhileTrue.
  -- simpl. reflexivity.
  -- eapply PE_Seq.
     --- eapply PE_AsgnDynamic.
         + simpl. reflexivity.
         + intros. unfold not. intros. inversion H.
     --- simpl. eapply PE_AsgnStatic. simpl. reflexivity.
  -- eapply PE_WhileTrue.
     --- simpl. reflexivity.
     --- eapply PE_Seq.
         + eapply PE_AsgnDynamic.
           ++ simpl. reflexivity.
           ++ intros. unfold not. intros. inversion H.
         + simpl. eapply PE_AsgnStatic. simpl. reflexivity.
     --- eapply PE_WhileTrue.
         + simpl. reflexivity.
         + eapply PE_Seq.
           ++ eapply PE_AsgnDynamic.
              +++ simpl. reflexivity.
              +++ intros. unfold not. intros. inversion H.
           ++ simpl. eapply PE_AsgnStatic. simpl. reflexivity.
         + eapply PE_WhileFalse. simpl. reflexivity.
         + unfold not. intros. inversion H.
     --- unfold not. intros. inversion H.
  -- unfold not. intros. inversion H.
Qed.

Example pe_loop_example3:
  <{Z := 3; subtract_slowly}> / []
  ==> <{skip;
       if X <> 0 then
         (skip; X := X - 1);
         if X <> 0 then
           (skip; X := X - 1);
           if X <> 0 then
             (skip; X := X - 1);
             while X <> 0 do
               (skip; X := X - 1); skip
             end;
             skip; Z := 0
           else skip; Z := 1 end; skip
         else skip; Z := 2 end; skip
       else skip; Z := 3 end}> / [] / <{skip}>.
Proof.
erewrite f_equal2 with (f := fun c st => _ / _ ==> c / st / <{skip}>).
- eapply PE_Seq. 
  -- apply PE_AsgnStatic. reflexivity.
  -- unfold pe_add. simpl.
     unfold subtract_slowly. 
     step PE_While.
       step PE_While.
         step PE_While.
         simpl. step PE_WhileFixed.
         step PE_WhileFixedEnd. reflexivity.
         inversion H. inversion H. inversion H.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

Example pe_loop_example4:
  <{X := 0;
   while X <= 2 do
     X := 1 - X
   end}> / [] ==> <{skip; while true do skip end}> / [(X,0)] / <{skip}>.
Proof.
erewrite f_equal2 with (f := fun c st => _ / _ ==> c / st / <{skip}>).
- eapply PE_Seq.
  -- eapply PE_AsgnStatic. reflexivity.
  -- step PE_WhileFixedLoop.
     + step PE_WhileTrue.
       ++ step PE_WhileFixedEnd.
       ++ inversion H.
     + reflexivity.
- reflexivity.
- reflexivity.
Qed.

Reserved Notation "c1 '/' st '==>' st' '#' n"
  (at level 40, st at level 39, st' at level 39).
  
Inductive ceval_count : com -> state -> state -> nat -> Prop :=
  | E'Skip : forall st,
      <{skip}> / st ==> st # 0
  | E'Asgn : forall st a1 n l,
      aeval st a1 = n ->
      <{l := a1}> / st ==> (t_update st l n) # 0
  | E'Seq : forall c1 c2 st st' st'' n1 n2,
      c1 / st ==> st' # n1 ->
      c2 / st' ==> st'' # n2 ->
      <{c1 ; c2}> / st ==> st'' # (n1 + n2)
  | E'IfTrue : forall st st' b1 c1 c2 n,
      beval st b1 = true ->
      c1 / st ==> st' # n ->
      <{if b1 then c1 else c2 end}> / st ==> st' # n
  | E'IfFalse : forall st st' b1 c1 c2 n,
      beval st b1 = false ->
      c2 / st ==> st' # n ->
      <{if b1 then c1 else c2 end}> / st ==> st' # n
  | E'WhileFalse : forall b1 st c1,
      beval st b1 = false ->
      <{while b1 do c1 end}> / st ==> st # 0
  | E'WhileTrue : forall st st' st'' b1 c1 n1 n2,
      beval st b1 = true ->
      c1 / st ==> st' # n1 ->
      <{while b1 do c1 end}> / st' ==> st'' # n2 ->
      <{while b1 do c1 end}> / st ==> st'' # S (n1 + n2)

  where "c1 '/' st '==>' st' # n" := (ceval_count c1 st st' n).  
  
Local Hint Constructors ceval_count : core.

Theorem ceval_count_complete: forall c st st',
  st =[ c ]=> st' -> exists n, c / st ==> st' # n.
Proof.
intros.
induction H.
- exists 0. apply E'Skip.
- exists 0. apply E'Asgn. assumption.
- destruct IHceval1. destruct IHceval2.
  exists (x + x0). eapply E'Seq. apply H1. apply H2.
- destruct IHceval. exists x.
  apply E'IfTrue. assumption. assumption.
- destruct IHceval. exists x.
  apply E'IfFalse. assumption. assumption.
- exists 0. apply E'WhileFalse. assumption.
- destruct IHceval1. destruct IHceval2.
  exists (S (x + x0)).
  eapply E'WhileTrue. assumption. apply H2. assumption.
Qed.

Theorem ceval_count_sound: forall c st st' n,
  c / st ==> st' # n -> st =[ c ]=> st'.
Proof.
intros.
induction H.
- apply E_Skip.
- apply E_Asgn. assumption.
- eapply E_Seq. apply IHceval_count1. apply IHceval_count2.
- apply E_IfTrue. assumption. assumption.
- apply E_IfFalse. assumption. assumption.
- eapply E_WhileFalse. assumption.
- eapply E_WhileTrue. assumption. apply IHceval_count1. apply IHceval_count2. 
 Qed.

Theorem pe_compare_nil_lookup: forall pe_st1 pe_st2,
  pe_compare pe_st1 pe_st2 = [] ->
  forall V, pe_lookup pe_st1 V = pe_lookup pe_st2 V.
Proof.
intros.
rewrite pe_compare_correct.
unfold not.
intros.
rewrite H in H0. inversion H0.
Qed.

Theorem pe_compare_nil_update: forall pe_st1 pe_st2,
  pe_compare pe_st1 pe_st2 = [] ->
  exists st, pe_update st pe_st1 = pe_update st pe_st2.
Proof.
intros.
pose proof (pe_compare_nil_lookup pe_st1 pe_st2 H) as H1.
exists empty_st.
apply functional_extensionality.
intros.
rewrite !pe_update_correct.
pose proof (H1 x) as H2.
rewrite H1.
reflexivity.
Qed.

Reserved Notation "c' '/' pe_st' '/' c'' '/' st '==>' st'' '#' n"
  (at level 40, pe_st' at level 39, c'' at level 39,
   st at level 39, st'' at level 39).
   
Inductive pe_ceval_count (c':com) (pe_st':pe_state) (c'':com)
                         (st:state) (st'':state) (n:nat) : Prop :=
  | pe_ceval_count_intro : forall st' n',
    st =[ c' ]=> st' ->
    c'' / pe_update st' pe_st' ==> st'' # n' ->
    n' <= n ->
    c' / pe_st' / c'' / st ==> st'' # n
  where "c' '/' pe_st' '/' c'' '/' st '==>' st'' '#' n" :=
        (pe_ceval_count c' pe_st' c'' st st'' n).
        
Local Hint Constructors pe_ceval_count : core.

Lemma pe_ceval_count_le: forall c' pe_st' c'' st st'' n n',
  n' <= n ->
  c' / pe_st' / c'' / st ==> st'' # n' ->
  c' / pe_st' / c'' / st ==> st'' # n.
Proof. intros c' pe_st' c'' st st'' n n' Hle H. inversion H.
assert (n'0 <= n).
  lia.
eapply pe_ceval_count_intro.
- apply H0.
- apply H1.
- assumption.
Qed.

(* need this version to prove pe_com_complete and pe_com_sound*)
Theorem pe_compare_nil_update_forall: forall pe_st1 pe_st2,
  pe_compare pe_st1 pe_st2 = [] ->
  forall st, pe_update st pe_st1 = pe_update st pe_st2.
Proof.
intros.
pose proof (pe_compare_nil_lookup pe_st1 pe_st2 H) as H1.
apply functional_extensionality.
intros.
rewrite !pe_update_correct.
pose proof (H1 x) as H2.
rewrite H1.
reflexivity.
Qed.

(* book version *)
Theorem pe_com_complete:
  forall c pe_st pe_st' c' c'', c / pe_st ==> c' / pe_st' / c'' ->
  forall st st'' n,
  (c / pe_update st pe_st ==> st'' # n) ->
  (c' / pe_st' / c'' / st ==> st'' # n).
Proof. intros c pe_st pe_st' c' c'' Hpe.
  induction Hpe; intros st st'' n Heval;
  try (inversion Heval; subst;
       try (rewrite -> pe_bexp_correct, -> H in *; solve_by_invert);
       []);
  eauto.
  - (* PE_AsgnStatic *) econstructor. econstructor.
    rewrite -> pe_aexp_correct. rewrite <- pe_update_update_add.
    rewrite -> H. apply E'Skip. auto.
  - (* PE_AsgnDynamic *) econstructor. econstructor. reflexivity.
    rewrite -> pe_aexp_correct. rewrite <- pe_update_update_remove.
    apply E'Skip. auto.
  - (* PE_Seq *)
    edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
    inversion Hskip. subst.
    edestruct IHHpe2. eassumption.
    econstructor; eauto. lia.
  - (* PE_If *) inversion Heval; subst.
    + (* E'IfTrue *) edestruct IHHpe1. eassumption.
      econstructor. apply E_IfTrue. rewrite <- pe_bexp_correct. assumption.
      eapply E_Seq. eassumption. apply eval_assign.
      rewrite <- assign_removes. eassumption. eassumption.
    + (* E_IfFalse *) edestruct IHHpe2. eassumption.
      econstructor. apply E_IfFalse. rewrite <- pe_bexp_correct. assumption.
      eapply E_Seq. eassumption. apply eval_assign.
      rewrite -> pe_compare_update.
      rewrite <- assign_removes. eassumption. eassumption.
  - (* PE_WhileTrue *)
    edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
    inversion Hskip. subst.
    edestruct IHHpe2. eassumption.
    econstructor; eauto. lia.
  - (* PE_While *) inversion Heval; subst.
    + (* E_WhileFalse *) econstructor. apply E_IfFalse.
      rewrite <- pe_bexp_correct. assumption.
      apply eval_assign.
      rewrite <- assign_removes. inversion H2; subst; auto.
      auto.
    + (* E_WhileTrue *)
      edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
      inversion Hskip. subst.
      edestruct IHHpe2. eassumption.
      econstructor. apply E_IfTrue.
      rewrite <- pe_bexp_correct. assumption.
      repeat eapply E_Seq; eauto. apply eval_assign.
      rewrite -> pe_compare_update, <- assign_removes. eassumption.
      lia.
  - (* PE_WhileFixedLoop *) exfalso.
    generalize dependent (S (n1 + n2)). intros n.
    clear - H H0 IHHpe1 IHHpe2. generalize dependent st.
    induction n using lt_wf_ind; intros st Heval. inversion Heval; subst.
    + (* E'WhileFalse *) rewrite pe_bexp_correct, H in H7. inversion H7.
    + (* E'WhileTrue *)
      edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
      inversion Hskip. subst.
      edestruct IHHpe2. eassumption.
      rewrite <- (pe_compare_nil_update_forall _ _ H0) in H7. (* <-- NOTE CHANGE HERE *)
      apply H1 in H7; [| lia]. inversion H7.
  - (* PE_WhileFixed *) generalize dependent st.
    induction n using lt_wf_ind; intros st Heval. inversion Heval; subst.
    + (* E'WhileFalse *) rewrite pe_bexp_correct in H8. eauto.
    + (* E'WhileTrue *) rewrite pe_bexp_correct in H5.
      edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
      inversion Hskip. subst.
      edestruct IHHpe2. eassumption.
      rewrite <- (pe_compare_nil_update_forall _ _ H1) in H8. (* <-- NOTE CHANGE HERE *)
      apply H2 in H8; [| lia]. inversion H8.
      econstructor; [ eapply E_WhileTrue; eauto | eassumption | lia].
Qed.

(* book version *)
Theorem pe_com_sound:
  forall c pe_st pe_st' c' c'', c / pe_st ==> c' / pe_st' / c'' ->
  forall st st'' n,
  (c' / pe_st' / c'' / st ==> st'' # n) ->
  (pe_update st pe_st =[ c ]=> st'').
Proof. intros c pe_st pe_st' c' c'' Hpe.
  induction Hpe;
    intros st st'' n [st' n' Heval Heval' Hle];
    try (inversion Heval; []; subst);
    try (inversion Heval'; []; subst); eauto.
  - (* PE_AsgnStatic *) rewrite <- pe_update_update_add. apply E_Asgn.
    rewrite -> pe_aexp_correct. rewrite -> H. reflexivity.
  - (* PE_AsgnDynamic *) rewrite <- pe_update_update_remove. apply E_Asgn.
    rewrite <- pe_aexp_correct. reflexivity.
  - (* PE_Seq *) eapply E_Seq; eauto.
  - (* PE_IfTrue *) apply E_IfTrue.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
    eapply IHHpe. eauto.
  - (* PE_IfFalse *) apply E_IfFalse.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
    eapply IHHpe. eauto.
  - (* PE_If *) inversion Heval; subst; inversion H7; subst; clear H7.
    + (* E_IfTrue *)
      eapply ceval_deterministic in H8; [| apply eval_assign]. subst.
      rewrite <- assign_removes in Heval'.
      apply E_IfTrue. rewrite -> pe_bexp_correct. assumption.
      eapply IHHpe1. eauto.
    + (* E_IfFalse *)
      eapply ceval_deterministic in H8; [| apply eval_assign]. subst.
      rewrite -> pe_compare_update in Heval'.
      rewrite <- assign_removes in Heval'.
      apply E_IfFalse. rewrite -> pe_bexp_correct. assumption.
      eapply IHHpe2. eauto.
  - (* PE_WhileFalse *) apply E_WhileFalse.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
  - (* PE_WhileTrue *) eapply E_WhileTrue.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
    eapply IHHpe1. eauto. eapply IHHpe2. eauto.
  - (* PE_While *) inversion Heval; subst.
    + (* E_IfTrue *)
      inversion H9. subst. clear H9.
      inversion H10. subst. clear H10.
      eapply ceval_deterministic in H11; [| apply eval_assign]. subst.
      rewrite -> pe_compare_update in Heval'.
      rewrite <- assign_removes in Heval'.
      eapply E_WhileTrue. rewrite -> pe_bexp_correct. assumption.
      eapply IHHpe1. eauto.
      eapply IHHpe2. eauto.
    + (* E_IfFalse *) apply ceval_count_sound in Heval'.
      eapply ceval_deterministic in H9; [| apply eval_assign]. subst.
      rewrite <- assign_removes in Heval'.
      inversion H2; subst.
      * (* c2'' = skip *) inversion Heval'. subst. apply E_WhileFalse.
        rewrite -> pe_bexp_correct. assumption.
      * (* c2'' = while b1 do c1 end *) assumption.
  - (* PE_WhileFixedEnd *) eapply ceval_count_sound. apply Heval'.
  - (* PE_WhileFixedLoop *)
    apply loop_never_stops in Heval. inversion Heval.
  - (* PE_WhileFixed *)
    clear - H1 IHHpe1 IHHpe2 Heval.
    remember <{while pe_bexp pe_st b1 do c1'; c2' end}> as c'.
    induction Heval;
      inversion Heqc'; subst; clear Heqc'.
    + (* E_WhileFalse *) apply E_WhileFalse.
      rewrite pe_bexp_correct. assumption.
    + (* E_WhileTrue *)
      assert (IHHeval2' := IHHeval2 (refl_equal _)).
      apply ceval_count_complete in IHHeval2'. inversion IHHeval2'.
      clear IHHeval1 IHHeval2 IHHeval2'.
      inversion Heval1. subst.
      eapply E_WhileTrue. rewrite pe_bexp_correct. assumption. eauto.
      eapply IHHpe2. econstructor. eassumption.
      rewrite <- (pe_compare_nil_update_forall _ _ H1). eassumption. apply le_n. (* <-- NOTE CHANGE HERE *)
Qed.

Corollary pe_com_correct:
  forall c pe_st pe_st' c', c / pe_st ==> c' / pe_st' / <{skip}> ->
  forall st st'',
  (pe_update st pe_st =[ c ]=> st'') <->
  (exists st', st =[ c' ]=> st' /\ pe_update st' pe_st' = st'').
Proof.
intros.
split.
- intros.
  pose proof (pe_com_complete c pe_st pe_st' c' <{skip}> H).
  destruct (ceval_count_complete c (pe_update st pe_st) st'' H0).
  pose proof (H1 st st'' x H2).
  inversion H3.
  exists st'. split. 
  -- assumption.
  -- inversion H5. reflexivity.
- intros. destruct H0. destruct H0.
  pose proof (pe_com_sound c pe_st pe_st' c' <{skip}> H).
  apply H2 with (n := 0).
  apply pe_ceval_count_intro with (st' := x) (n' := 0).
  -- apply H0.
  -- rewrite H1. apply E'Skip.
  -- lia.    
Qed.

End Loop.

Inductive block (Label:Type) : Type :=
  | Goto : Label -> block Label
  | If : bexp -> Label -> Label -> block Label
  | Assign : string -> aexp -> block Label -> block Label.
  
Arguments Goto {Label} _.
Arguments If {Label} _ _ _.
Arguments Assign {Label} _ _ _.

Inductive parity_label : Type :=
  | entry : parity_label
  | loop : parity_label
  | body : parity_label
  | done : parity_label.


Definition parity_body : block parity_label :=
  Assign Y <{Y - 1}>
   (Assign X <{1 - X}>
     (Goto loop)).   
  
Fixpoint keval {L:Type} (st:state) (k : block L) : state * L :=
  match k with
  | Goto l => (st, l)
  | If b l1 l2 => (st, if beval st b then l1 else l2)
  | Assign i a k => keval (t_update st i (aeval st a)) k
  end.  

Example keval_example:
  keval empty_st parity_body
  = ((X !-> 1 ; Y !-> 0), loop).
Proof. simpl. reflexivity. Qed.

Definition program (L:Type) : Type := L -> option (block L).

Definition parity : program parity_label := fun l =>
  match l with
  | entry => Some (Assign X 0 (Goto loop))
  | loop => Some (If <{1 <= Y}> body done)
  | body => Some parity_body
  | done => None (* halt *)
  end.

Inductive peval {L:Type} (p : program L)
  : state -> L -> state -> L -> Prop :=
  | E_None: forall st l,
    p l = None ->
    peval p st l st l
  | E_Some: forall st l k st' l' st'' l'',
    p l = Some k ->
    keval st k = (st', l') ->
    peval p st' l' st'' l'' ->
    peval p st l st'' l''.

Example parity_eval: peval parity empty_st entry empty_st done.
Proof.
erewrite f_equal with (f := fun st => peval _ _ _ st _).
eapply E_Some.
- simpl. reflexivity.
- simpl. reflexivity.
- eapply E_Some.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- eapply E_None. 
     + simpl. reflexivity.
- apply functional_extensionality. intros.
  rewrite t_update_same.
  reflexivity.    
Qed.  

Fixpoint pe_block {L:Type} (pe_st:pe_state) (k : block L)
  : block (pe_state * L) :=
  match k with
  | Goto l => Goto (pe_st, l)
  | If b l1 l2 =>
    match pe_bexp pe_st b with
    | BTrue => Goto (pe_st, l1)
    | BFalse => Goto (pe_st, l2)
    | b' => If b' (pe_st, l1) (pe_st, l2)
    end
  | Assign i a k =>
    match pe_aexp pe_st a with
    | ANum n => pe_block (pe_add pe_st i n) k
    | a' => Assign i a' (pe_block (pe_remove pe_st i) k)
    end
  end.  

Example pe_block_example:
  pe_block [(X,0)] parity_body
  = Assign Y <{Y - 1}> (Goto ([(X,1)], loop)).
Proof. simpl. unfold pe_add. simpl. reflexivity. Qed.

(* book version (expanded) *)
Theorem pe_block_correct: forall (L:Type) st pe_st k st' pe_st' (l':L),
  keval st (pe_block pe_st k) = (st', (pe_st', l')) ->
  keval (pe_update st pe_st) k = (pe_update st' pe_st', l').
Proof.
intros.
generalize dependent pe_st.
generalize dependent st.
induction k.
- intros. simpl. simpl in H. inversion H. reflexivity.
- intros. assert (keval st (pe_block pe_st (If b l l0)) =
            keval st (If (pe_bexp pe_st b) (pe_st, l) (pe_st, l0))).
  {
    simpl. destruct (pe_bexp pe_st b); simpl; reflexivity.
  }
  rewrite H0 in H. simpl in H.
  simpl in *. rewrite pe_bexp_correct.
  destruct (beval st (pe_bexp pe_st b)).
  -- inversion H. reflexivity.
  -- inversion H. reflexivity.
- intros.       
  simpl in *. rewrite pe_aexp_correct.
  destruct (pe_aexp pe_st a); simpl;
      try solve [rewrite pe_update_update_add; apply IHk; apply H];
      solve [rewrite pe_update_update_remove; apply IHk; apply H].
Qed.

Definition pe_program {L:Type} (p : program L)
  : program (pe_state * L) :=
  fun pe_l => match pe_l with | (pe_st, l) =>
                option_map (pe_block pe_st) (p l)
              end.

Inductive pe_peval {L:Type} (p : program L)
  (st:state) (pe_st:pe_state) (l:L) (st'o:state) (l':L) : Prop :=
  | pe_peval_intro : forall st' pe_st',
    peval (pe_program p) st (pe_st, l) st' (pe_st', l') ->
    pe_update st' pe_st' = st'o ->
    pe_peval p st pe_st l st'o l'.

(* book version *)
Theorem pe_program_correct:
  forall (L:Type) (p : program L) st pe_st l st'o l',
  peval p (pe_update st pe_st) l st'o l' <->
  pe_peval p st pe_st l st'o l'.
Proof. intros.
  split.
  - (* -> *) intros Heval.
    remember (pe_update st pe_st) as sto.
    generalize dependent pe_st. generalize dependent st.
    induction Heval as
      [ sto l Hlookup | sto l k st'o l' st''o l'' Hlookup Hkeval Heval ];
      intros st pe_st Heqsto; subst sto.
    + (* E_None *) eapply pe_peval_intro. apply E_None.
      simpl. rewrite Hlookup. reflexivity. reflexivity.
    + (* E_Some *)
      remember (keval st (pe_block pe_st k)) as x.
      destruct x as [st' [pe_st' l'_] ].
      symmetry in Heqx. erewrite pe_block_correct in Hkeval by apply Heqx.
      inversion Hkeval. subst st'o l'_. clear Hkeval.
      edestruct IHHeval. reflexivity. subst st''o. clear IHHeval.
      eapply pe_peval_intro; [| reflexivity]. eapply E_Some; eauto.
      simpl. rewrite Hlookup. reflexivity.
  - (* <- *) intros [st' pe_st' Heval Heqst'o].
    remember (pe_st, l) as pe_st_l.
    remember (pe_st', l') as pe_st'_l'.
    generalize dependent pe_st. generalize dependent l.
    induction Heval as
      [ st [pe_st_ l_] Hlookup
      | st [pe_st_ l_] pe_k st' [pe_st'_ l'_] st'' [pe_st'' l'']
        Hlookup Hkeval Heval ];
      intros l pe_st Heqpe_st_l;
      inversion Heqpe_st_l; inversion Heqpe_st'_l'; repeat subst.
    + (* E_None *) apply E_None. simpl in Hlookup.
      destruct (p l'); [ solve [ inversion Hlookup ] | reflexivity ].
    + (* E_Some *)
      simpl in Hlookup. remember (p l) as k.
      destruct k as [k|]; inversion Hlookup; subst.
      eapply E_Some; eauto. apply pe_block_correct. apply Hkeval.
Qed.

  