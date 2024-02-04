From LF Require Export Lists.

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list.

Check nil.
Check cons.

Module MumbleGrumble.

Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).


Fail Check d (b a 5). (* No *)
Check d mumble (b a 5). (* Yes *)
Check d bool (b a 5). (* Yes *)
Check e bool true. (* Yes *)
Check e mumble (b c 0). (* Yes *)
Fail Check e bool (b c 0). (* No *)
Check c. (* Yes *)

End MumbleGrumble.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
intros.
induction l1.
simpl.
reflexivity.
simpl.
rewrite IHl1.
reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
intros.
induction l1.
simpl.
rewrite app_nil_r.
reflexivity.
assert (H: rev (x :: l1) = rev l1 ++ [x]). { reflexivity. }
rewrite H. clear H.
rewrite app_assoc.
rewrite <- IHl1.
reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite rev_app_distr.
rewrite IHl.
reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Check @combine.

Compute (combine [1;2] [false;false;true;true]).

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
match l with
| nil => (nil, nil)
| (x,y)::t => (x :: fst (split t), y :: snd (split t))
end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X}.
Arguments None {X}.

End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Definition hd_error {X : Type} (l : list X) : option X :=
match l with
| nil => None
| a :: l' => Some a
end.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Fixpoint filter {X:Type} (test: X -> bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Search gt.

Definition filter_even_gt7 (l : list nat) : list nat :=
filter (fun n => if (even n) 
                 then (if (leb n 7) 
                       then false 
                       else true)
                 else false) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
(filter test l, filter (fun n => if (test n) then false else true) l).

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Lemma map_app : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = (map f l1) ++ (map f l2).
intros.
induction l1.
simpl.
reflexivity.
simpl.
rewrite IHl1.
reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl rev.
rewrite map_app.
rewrite IHl.
assert (H: map f [x] = [f x]). { reflexivity. }
rewrite H. clear H.
reflexivity.
Qed.

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X) : list Y :=
match l with
| nil => nil
| a :: l' => (f a) ++ (flat_map f l')
end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

(* explicit versions of filter and map *)
Fixpoint filter' (X:Type) (test: X -> bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter' X test t)
    else filter' X test t
  end.

Definition filter_even_gt7' (l : list nat) : list nat :=
filter' nat (fun n => if (even n) 
                      then (if (leb n 7) 
                            then false 
                            else true)
                      else false) l.

Example test_filter_even_gt7_1' :
  filter_even_gt7' [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2' :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition' (X : Type)
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
(filter' X test l, filter' X (fun n => if (test n) then false else true) l).

Example test_partition1': partition' nat odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2': partition' nat (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map' (X Y : Type) (f : X->Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map' X Y f t)
  end.

Lemma map_app' : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map' X Y f (l1 ++ l2) = (map' X Y f l1) ++ (map' X Y f l2).
intros.
induction l1.
simpl.
reflexivity.
simpl.
rewrite IHl1.
reflexivity.
Qed.

Theorem map_rev' : forall (X Y : Type) (f : X -> Y) (l : list X),
  map' X Y f (rev l) = rev (map' X Y f l).
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl rev.
rewrite map_app'.
rewrite IHl.
assert (H: map' X Y f [x] = [f x]). { reflexivity. }
rewrite H. clear H.
reflexivity.
Qed.

Fixpoint flat_map' (X Y: Type) (f: X -> list Y) (l: list X) : list Y :=
match l with
| nil => nil
| a :: l' => (f a) ++ (flat_map' X Y f l')
end.

Example test_flat_map1':
  flat_map' nat nat (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

(* end explicit versions *)

(* Observe that the type of fold is parameterized by two type variables, X and Y, and the parameter f is a binary operator that takes an X and a Y and returns a Y. Can you think of a situation where it would be useful for X and Y to be different?
  Answer: cons
*)

Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
intros.
induction l.
reflexivity.
simpl.
rewrite <- IHl.
reflexivity.
Qed.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun x l' => cons (f x) l') l nil.

Compute fold_map (fun n => 2 * n) [1; 2; 3].

Theorem fold_map_correct : forall (X Y : Type) (f : X -> Y) (l : list X),
  fold_map f l = map f l.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite <- IHl.
reflexivity.
Qed.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
intros.
reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
intros.
destruct p.
reflexivity.
Qed.

(* 

Informal proof of 
Theorem nth_error_theorem : forall X l n, length l = n -> @nth_error X l n = None.

1. If the list is empty, by definition, nth_error is None
2. If the list is not empty, we need to compute nth_error (tail list) (n-1) (since n <> 0 as the list is not empty)
3. Thus we keep recursing to the end of the tail, and we reach the end of the tail, while the third parameter to nth_error goes to 0, and the last call is 'nth_error [] 0', which computes to None. Qed.

Semi-formally,
  nth_error l n
= nth_error <last n-1 of l> n-1
= nth_error <last n-2 of l> n-2
= ...
= nth_error <last n-n of l> n-n
= nth_error [] 0
= None

*)

Module Church.

Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition three : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f (f x)).

Definition succ (n : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.

Example succ_2 : succ one = two.
Proof. reflexivity. Qed.

Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

Definition plus (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => n X f (m X f x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.

Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

Definition mult (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => n X (fun (x : X) => m X f x) x.

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.

Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.

Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

Definition exp (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) 
    => (m (X->X) (fun (g : X->X) 
                   => fun (x1: X) 
                        => n X g x1) (fun (x0: X) => f x0)) x.

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.

Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.

Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

End Church.
