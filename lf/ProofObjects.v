Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Theorem ev_8 : ev 8.
Proof.
apply ev_SS.
apply ev_SS.
apply ev_SS.
apply ev_SS.
apply ev_0.
Qed.

Definition ev_8' : ev 8 :=
  ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).
  
Print ev_8.

Print ev_8'.

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Show Proof. Defined.

Module Props.

Module And.

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.
  
Arguments conj [P] [Q].
Notation "P /\ Q" := (and P Q) : type_scope.

Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ. destruct HPQ as [HP HQ]. apply HP.
  Show Proof.
Qed.

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.
End And.

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.
  
Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

Print and_comm'.

Theorem myproj1 : forall P Q, P /\ Q -> P.
Proof.
  intros. destruct H as [HP HQ]. apply HP.
Qed.

Theorem myproj2 : forall P Q, P /\ Q -> Q.
Proof.
  intros. destruct H as [HP HQ]. apply HQ.
Qed.

Print myproj1.

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
 fun (P Q R : Prop) (H1 : P /\ Q) (H2 : Q /\ R) => 
    conj (myproj1 P Q H1) (myproj2 Q R H2).
    
Print conj_fact.

Module Or.
Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.
Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].
Notation "P \/ Q" := (or P Q) : type_scope.

Definition inj_l : forall (P Q : Prop), P -> P \/ Q :=
  fun P Q HP => or_introl HP.
  
Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
Proof.
  intros P Q HP. left. apply HP.
Qed.

Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or_introl HP => HPR HP
    | or_intror HQ => HQR HQ
    end.

Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R HPQ HPR HQR.
  destruct HPQ as [HP | HQ].
  - apply HPR. apply HP.
  - apply HQR. apply HQ.
Qed.

End Or.

Definition myinj_l : forall (P Q : Prop), P -> P \/ Q :=
  fun P Q HP => or_introl HP.

Definition myinj_r : forall (P Q : Prop), P -> Q \/ P :=
  fun P Q HP => or_intror HP.

Definition or_commut' : forall P Q, P \/ Q -> Q \/ P :=
  fun P Q HPQ =>
    match HPQ with
    | or_introl HP => myinj_r P Q HP
    | or_intror HQ => myinj_l Q P HQ
    end.

Print or_commut'.

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

Notation "'exists' x , p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.

End Ex.

Check ex (fun n => ev n) : Prop.

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Print some_nat_is_even.

Definition some_nat_is_even' : exists n, ev n :=
  ex_intro ev 2 (ev_SS 0 ev_0).

Print some_nat_is_even'.

Theorem ex_ev_Sn' : exists n, ev (S n).
Proof.
exists 1.
apply (ev_SS 0).
apply ev_0.
Qed.

Print ex_ev_Sn'.
  
Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).
 
Print ex_ev_Sn. 

Inductive True : Prop :=
  | I : True.
  
Definition p_implies_true : forall P, P -> True :=
  fun P HP => I.

Inductive False : Prop := .

Fail Definition contra : False :=
  0 = 1.

Definition false_implies_zero_eq_one : False -> 0 = 1 :=
  fun contra => match contra with end.

Definition ex_falso_quodlibet' : forall P, False -> P :=
  fun P contra => match contra with end.
  
Print ex_falso_quodlibet'. 

End Props.

Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                       (at level 70, no associativity)
                     : type_scope.

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.
  
Definition singleton : forall (X:Type) (x:X), []++[x] == x::[] :=
  fun (X:Type) (x:X) => eq_refl [x].

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall P:X->Prop, P x -> P y.
Proof.
intros.
destruct H.
apply H0.
Qed.

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x == y.
Proof.
intros.
pose proof (H (fun z => eq x z)) as H1.
simpl in H1.
apply H1.
apply eq_refl.
Qed.

End MyEquality.






