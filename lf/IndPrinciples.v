Theorem mul_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
apply nat_ind.
- reflexivity.
- intros. simpl. assumption.
Qed.

Theorem mul_0_r'' : forall n:nat,
  n * 0 = 0.
Proof.
induction n.
- reflexivity.
- simpl. assumption.
Qed.

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
apply nat_ind.
- reflexivity.
- intros. simpl. rewrite H. reflexivity.
Qed.

Inductive rgb : Type :=
  | red
  | green
  | blue.
  
(* forall P : rgb -> Prop,
   P red -> P green -> P blue -> forall r : rgb, P r *)
   
Check rgb_ind.

Inductive booltree : Type :=
  | bt_empty
  | bt_leaf (b : bool)
  | bt_branch (b : bool) (t1 t2 : booltree).
  
(*
   forall P : booltree -> Prop,
   P bt_empty ->
   (forall (b : bool), P (bt_leaf b)) ->
   (forall (b : bool) (t1 : booltree), P t1 -> 
     (forall (t2: booltree), P t2 -> P (bt_branch b t1 t2))) ->
   forall (bt : booltree), P bt.
*)

Check booltree_ind.

Inductive Toy : Type :=
  | con1 (b : bool)
  | con2 (n : nat) (t : Toy).
  
Check Toy_ind.

Inductive tree (X:Type) : Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).

(* forall (X:Type) (P : tree X -> Prop),
   (forall (x:X), P (leaf X x)) ->
   (forall (t1 : tree X), P t1 -> forall (t2 : tree X), P t2 -> P (node t1 t2)) ->
   forall (t : tree X), P t.
*)

Check tree_ind.

Inductive my_type (X:Type) : Type :=
  | constr1 (x : X)
  | constr2 (n : nat) 
  | constr3 (m : my_type X) (n : nat).

Check my_type_ind.

Inductive foo (X:Type) (Y:Type) :=
  | bar (x : X)
  | baz (y : Y)
  | quux (f1 : nat->foo X Y).
  
Check foo_ind.
  
Inductive foo' (X:Type) : Type :=
  | C1 (l : list X) (f : foo' X)
  | C2.

(*
   forall (X : Type) (P : foo' X → Prop),
   (forall (l : list X) (f : foo' X),
     P f -> 
     P (C1 X l f)) ->
   P (C2 X) ->
   forall f1 : foo', P f1.
*)
  
Check foo'_ind.

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.
  
Theorem mul_0_r''' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros. unfold P_m0r in H. unfold P_m0r. simpl. assumption. 
Qed.

Definition P_assoc (n m p : nat) : Prop :=
  n + (m + p) = (n + m) + p.
  
Theorem add_assoc' : forall (m n p : nat), P_assoc m n p.
Proof.
intros.
induction n.
- unfold P_assoc. simpl. rewrite <- plus_n_O. reflexivity.
- unfold P_assoc in IHn. unfold P_assoc.
  rewrite plus_Sn_m. rewrite <- plus_n_Sm.
  rewrite IHn.
  rewrite <- plus_n_Sm.
  rewrite plus_Sn_m.
  reflexivity.
Qed.

Definition P_comm (m n : nat): Prop :=
  n + m = m + n.
  
Theorem add_comm' : forall (m n : nat), P_comm m n.
Proof.
induction n.
- unfold P_comm. simpl. rewrite <- plus_n_O. reflexivity.
- unfold P_comm in IHn.
  unfold P_comm.
  rewrite plus_Sn_m.
  rewrite IHn.
  rewrite plus_n_Sm.
  reflexivity.
Qed.


   