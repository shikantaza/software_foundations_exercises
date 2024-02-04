Set Implicit Arguments.
From SLF Require Import LibSepReference.
Import ProgramSyntax DemoPrograms.
From SLF Require Import Basic.
Open Scope liblist_scope.

(* Require Import Le Gt Minus Min Bool. *)

Set Implicit Arguments.

Implicit Types n m : int.
Implicit Types p q s c : loc.
Implicit Types x : val.

Definition head : field := 0%nat.
Definition tail : field := 1%nat.

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p ~~~> `{ head := x; tail := q}) \* (MList L' q)
  end.

Lemma MList_nil : forall p,
  (MList nil p) = \[p = null].
Proof. intros. unfold MList. reflexivity. Qed.

Lemma MList_cons : forall p x L',
  MList (x::L') p =
  \exists q, (p ~~~> `{ head := x; tail := q}) \* (MList L' q).
Proof. intros. unfold MList. reflexivity. Qed.

Lemma MList_if : forall (p:loc) (L:list val),
      (MList L p)
  ==> (If p = null
        then \[L = nil]
        else \exists x q L', \[L = x::L']
             \* (p ~~~> `{ head := x; tail := q}) \* (MList L' q)).
Proof using.
  intros. destruct L as [|x L'].
  - rewrite MList_nil. xpull. (* can also use xchange MList_nil *)
    intros. case_if. xsimpl. reflexivity.
  - rewrite MList_cons. xpull.
    xchange hrecord_not_null. intros. case_if. xsimpl. reflexivity.
Qed.

Global Opaque MList.

Definition append : val :=
  <{ fix 'f 'p1 'p2 =>
       let 'q1 = 'p1`.tail in
       let 'b = ('q1 = null) in
       if 'b
         then 'p1`.tail := 'p2
         else 'f 'q1 'p2 }>.

Lemma triple_append : forall (L1 L2:list val) (p1 p2:loc),
  p1 <> null ->
  triple (append p1 p2)
    (MList L1 p1 \* MList L2 p2)
    (fun _ => MList (L1++L2) p1).
Proof using.
  introv K. gen p1.  induction_wf IH: list_sub L1. introv N. xwp.
  xchange (MList_if p1). case_if. xpull. intros x q1 L1' ->.
  xapp. xapp. xif; intros Cq1.
  - xchange (MList_if q1). case_if. xpull. intros ->.
    xapp. xchange <- MList_cons.
  - xapp. xchange <- MList_cons.
Qed.

Definition mnil : val :=
  <{ fun 'u =>
       null }>.

Lemma triple_mnil :
  triple (mnil ())
    \[]
    (funloc p => MList nil p).
Proof using.
  xwp. xval. xsimpl. reflexivity. rewrite MList_nil. xsimpl. reflexivity.
Qed.

#[global] Hint Resolve triple_mnil : triple.

Definition mcons : val :=
  <{ fun 'x 'q =>
       `{ head := 'x; tail := 'q } }>.

Lemma triple_mcons : forall x q,
  triple (mcons x q)
    \[]
    (funloc p => p ~~~> `{ head := x ; tail := q }).
Proof using.
  intros.
  xwp. xapp triple_new_hrecord_2.
  - reflexivity.
  - reflexivity.
  - intros. xsimpl. reflexivity.
Qed.

Lemma triple_mcons' : forall L x q,
  triple (mcons x q)
    (MList L q)
    (funloc p => MList (x::L) p).
Proof using.
  intros. xwp.
  xapp triple_new_hrecord_2.
  - reflexivity.
  - reflexivity.
  - intros. xsimpl.
    -- reflexivity.
    -- xchange <- MList_cons.
Qed.

(* book version *)
Lemma triple_mcons'' : forall L x q,
  triple (mcons x q)
    (MList L q)
    (funloc p => MList (x::L) p).
Proof using.
  intros. xapp triple_mcons.
  intros p. xchange <- MList_cons. xsimpl*.
Qed.

#[global] Hint Resolve triple_mcons' : triple.

Definition mcopy : val :=
  <{ fix 'f 'p =>
       let 'b = ('p = null) in
       if 'b
         then mnil ()
         else
           let 'x = 'p`.head in
           let 'q = 'p`.tail in
           let 'q2 = ('f 'q) in
           mcons 'x 'q2 }>.

Lemma triple_mcopy : forall L p,
  triple (mcopy p)
    (MList L p)
    (funloc p' => (MList L p) \* (MList L p')).
Proof using.
  intros. gen p. induction_wf IH: list_sub L.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros ->. xapp. xsimpl*. subst. xchange* <- MList_nil. }
  { intros x q L' ->. xapp. xapp. xapp. intros q'.
    xapp. intros p'. xchange <- MList_cons. xsimpl*. }
Qed.  

Definition mlength : val :=
  <{ fix 'f 'p =>
       let 'b = ('p = null) in
       if 'b
         then 0
         else (let 'q = 'p`.tail in
               let 'n = 'f 'q in
               'n + 1) }>.

Lemma triple_mlength : forall L p,
  triple (mlength p)
    (MList L p)
    (fun r => \[r = val_int (length L)] \* (MList L p)).
Proof using.
  intros. gen p. induction_wf IH: list_sub L.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros ->. xval. xsimpl*. subst. xchange* <- MList_nil. }
  { intros. xapp. xapp. 
    - rewrite H. auto.
    - xapp. xsimpl.
      + rewrite H. rew_list. math.
      + rewrite H. rewrite MList_cons. xsimpl. }
Qed.

Definition acclength : val :=
  <{ fix 'f 'c 'p =>
       let 'b = ('p <> null) in
       if 'b then
         incr 'c;
         let 'q = 'p`.tail in
         'f 'c 'q
       end }>.

Definition mlength' : val :=
  <{ fun 'p =>
       let 'c = ref 0 in
       acclength 'c 'p;
       get_and_free 'c }>.      

Lemma triple_acclength : forall c n L p,
  triple (acclength c p)
    ((c ~~> n) \* (MList L p))
    (fun _ => (c ~~> (n + (length L))) \* (MList L p)).
Proof using.
  intros. gen p. gen n. induction_wf IH: list_sub L. intros.
  xwp. xapp. xchange (MList_if p). xif; intros C; case_if; xpull.
  - intros. xapp. xapp. xapp. 
    -- rewrite H. auto.
    -- xsimpl. 
       + rewrite H. rew_list. math.
       + rewrite H. xchange <- MList_cons.
  - intros. xval. xsimpl.
    -- rewrite H. rew_list. math.
    -- rewrite H. xchange <- MList_nil. auto.
Qed.

#[global] Hint Resolve triple_acclength : triple.

Lemma triple_mlength' : forall L p,
  triple (mlength' p)
    (MList L p)
    (fun r => \[r = val_int (length L)] \* (MList L p)).
Proof using.
  intros. xwp. xapp. intro. xapp triple_acclength.
  xapp. xsimpl. math.
Qed.

Definition mrev_aux : val :=
  <{ fix 'f 'p1 'p2 =>
       let 'b = ('p2 = null) in
       if 'b
         then 'p1
         else (
           let 'p3 = 'p2`.tail in
           'p2`.tail := 'p1;
           'f 'p2 'p3) }>.
           
Definition mrev : val :=
  <{ fun 'p =>
       mrev_aux null 'p }>.

Compute (rev (1::2::3::nil)).

(*
Lemma triple_mrev_aux : forall p1 p2 L1 L2,
  triple (mrev_aux p1 p2)
    ((MList L1 p1) \* (MList L2 p2))
    (funloc q => \exists L1' L2', (MList L1' p1) \* (MList L2' p2) 
                                      \* \[rev L2 = rev L2' ++ L1']).
Admitted.
*)

Lemma triple_mrev_aux : forall p1 p2 L1 L2,
  triple (mrev_aux p1 p2)
    ((MList L1 p1) \* (MList L2 p2))
    (funloc q => (MList ((rev L2) ++ L1) q)).
Proof using. 

  intros. gen L1. gen p2. gen p1. induction_wf IH: list_sub L2.
  intros. xwp. xapp. xchange (MList_if p2). case_if.
  - xpull. intros. xif.
    -- intros. xval. rewrite H. rewrite app_nil_l. xsimpl. auto.
    -- intros. unfold "~" in H0. exfalso. apply H0. auto.
  - xpull. intros. xif.
    -- intros. xsimpl.
    -- intros. xapp. xapp. xchange <- (MList_cons p2). xapp.
       + rewrite H. apply list_sub_cons.
       + intros. rewrite H. rew_list. xsimpl. auto.
Qed.

#[global] Hint Resolve triple_mrev_aux : triple.

Lemma triple_mrev : forall L p,
  triple (mrev p)
    (MList L p)
    (funloc q => MList (rev L) q).
Proof using.
  intros. xwp.
  pose proof (@triple_mrev_aux null p nil L).
  xapp. rewrite app_nil_r. xchange <- MList_nil.
  - auto.
  - xsimpl. intros. assumption. 
Qed.

Module SizedStack.

Definition data : field := 0%nat.
Definition size : field := 1%nat.

Definition Stack (L:list val) (s:loc) : hprop :=
  \exists p, s ~~~>`{ data := p; size := length L } \* (MList L p).
  
Definition create : val :=
  <{ fun 'u =>
      `{ data := null; size := 0 } }>.
      
Lemma triple_create :
  triple (create ())
    \[]
    (funloc s => Stack nil s).
Proof using.
  xwp. xapp triple_new_hrecord_2.
  - auto.
  - auto.
  - intros. unfold Stack. xsimpl.
    -- auto.
    -- xchange <- MList_nil. auto.
Qed.

Definition sizeof : val :=
  <{ fun 'p =>
      'p`.size }>.
      
Lemma triple_sizeof : forall L s,
  triple (sizeof s)
    (Stack L s)
    (fun r => \[r = length L] \* Stack L s).
Proof using.
  intros. xwp. unfold Stack.
  xpull. intros. xapp.
  xsimpl. auto. 
Qed.

Definition push : val :=
  <{ fun 's 'x =>
       let 'p = 's`.data in
       let 'p2 = mcons 'x 'p in
       's`.data := 'p2;
       let 'n = 's`.size in
       let 'n2 = 'n + 1 in
       's`.size := 'n2 }>.  

Lemma triple_push : forall L s x,
  triple (push s x)
    (Stack L s)
    (fun u => Stack (x::L) s).
Proof using.
  intros. xwp. unfold Stack.
  xapp. intros.
  rewrite H. xapp triple_mcons. intros.
  xapp. xapp. xapp. xapp. xsimpl.
  - rew_list. math.
  - xchange <- MList_cons.
Qed.

Definition pop : val :=
  <{ fun 's =>
       let 'p = 's`.data in
       let 'x = 'p`.head in
       let 'p2 = 'p`.tail in
       delete 'p;
       's`.data := 'p2;
       let 'n = 's`.size in
       let 'n2 = 'n - 1 in
       's`.size := 'n2;
       'x }>.

Lemma triple_pop : forall L s,
  L <> nil ->
  triple (pop s)
    (Stack L s)
    (fun x => \exists L', \[L = x::L'] \* Stack L' s).
Proof using.
  intros. xwp. unfold Stack. xsimpl. intros.
  xapp. xchange (MList_if x). case_if.
  - xpull.
  - xpull. intros.
    xapp. xapp. xapp. xapp. xapp. xapp. xapp.
    xval.
    xsimpl.
    -- auto.
    -- rewrite H0. rew_list. math.  
Qed.

Definition top : val :=
  <{ fun 's =>
       let 'p = 's`.data in
       'p`.head }>.

Lemma triple_top : forall L s,
  L <> nil ->
  triple (top s)
    (Stack L s)
    (fun x => \exists L', \[L = x::L'] \* Stack L s).
Proof using.
  intros. xwp. unfold Stack. xsimpl. intros.
  xapp. xchange (MList_if x). case_if.
  - xpull.
  - xpull. intros. xapp. xsimpl.
    -- apply H0.
    -- rewrite H0. xchange <- MList_cons.
Qed.

End SizedStack.

Inductive tree : Type :=
  | Leaf : tree
  | Node : int -> tree -> tree -> tree.
  
Implicit Types T : tree.

Definition item : field := 0%nat.
Definition left : field := 1%nat.
Definition right : field := 2%nat.

Fixpoint MTree (T:tree) (p:loc) : hprop :=
  match T with
  | Leaf => \[p = null]
  | Node n T1 T2 => \exists p1 p2,
         (p ~~~>`{ item := n; left := p1; right := p2 })
      \* (MTree T1 p1)
      \* (MTree T2 p2)
  end.

Lemma MTree_Leaf : forall p,
  (MTree Leaf p) = \[p = null].
Proof using.
  intros. unfold MTree. reflexivity.
Qed.

Lemma MTree_Node : forall p n T1 T2,
  (MTree (Node n T1 T2) p) =
  \exists p1 p2,
       (p ~~~>`{ item := n; left := p1; right := p2 })
    \* (MTree T1 p1) \* (MTree T2 p2).
Proof using.
  intros. unfold MTree. reflexivity.
Qed.

Lemma MTree_if : forall (p:loc) (T:tree),
      (MTree T p)
  ==> (If p = null
        then \[T = Leaf]
        else \exists n p1 p2 T1 T2, \[T = Node n T1 T2]
             \* (p ~~~>`{ item := n; left := p1; right := p2 })
             \* (MTree T1 p1) \* (MTree T2 p2)).
Proof using.
  intros. destruct T.
  - xchange MTree_Leaf. intros. case_if. xsimpl*.
  - xchange MTree_Node. intros. xchange hrecord_not_null.
    intros. case_if. xsimpl*.
Qed.

Opaque MTree.

Inductive tree_sub : binary (tree) :=
  | tree_sub_1 : forall n T1 T2,
      tree_sub T1 (Node n T1 T2)
  | tree_sub_2 : forall n T1 T2,
      tree_sub T2 (Node n T1 T2). 

Lemma tree_sub_wf : wf tree_sub.
Proof using.
  intros T. induction T.
  - constructor. intros. inversion~H.
  - constructor. intros. inversion~H.
Qed.

#[global] Hint Resolve tree_sub_wf : wf.

Definition mnode : val :=
  val_new_hrecord_3 item left right.
  
Lemma triple_mnode : forall n p1 p2,
  triple (mnode n p1 p2)
    \[]
    (funloc p => p ~~~> `{ item := n ; left := p1 ; right := p2 }).
Proof using.
  intros. apply triple_new_hrecord_3. auto. auto. auto.
Qed.

Lemma triple_mnode' : forall T1 T2 n p1 p2,
  triple (mnode n p1 p2)
    (MTree T1 p1 \* MTree T2 p2)
    (funloc p => MTree (Node n T1 T2) p).
Proof using.
  intros. xapp triple_mnode.
  intros. xchange <- MTree_Node. xsimpl. reflexivity.
Qed.

#[global] Hint Resolve triple_mnode' : triple.

Definition tree_copy :=
  <{ fix 'f 'p =>
       let 'b = ('p = null) in
       if 'b then null else (
         let 'n = 'p`.item in
         let 'p1 = 'p`.left in
         let 'p2 = 'p`.right in
         let 'q1 = 'f 'p1 in
         let 'q2 = 'f 'p2 in
         mnode 'n 'q1 'q2
      ) }>.

Lemma triple_tree_copy : forall p T,
  triple (tree_copy p)
    (MTree T p)
    (funloc q => (MTree T p) \* (MTree T q)).
Proof using.
  intros. gen p. induction_wf IH: tree_sub T.
  xwp. xapp. xchange MTree_if. xif; intros C; case_if; xpull.
  - intros. rewrite C0. xval. xsimpl. auto. rewrite H. xchange <- MTree_Leaf.
    -- auto.
    -- xsimpl. xchange <- MTree_Leaf. reflexivity.
  - intros.  xapp. xapp. xapp. xapp.
    -- rewrite H. apply tree_sub_1.
    -- intros. xapp.
       + rewrite H. apply tree_sub_2.
       + intros. xapp. intros. xsimpl.
         ++ reflexivity.
         ++ xchange <- MTree_Node. rewrite H. xsimpl.
Qed.

Definition treeacc : val :=
  <{ fix 'f 'c 'p =>
       let 'b = ('p <> null) in
       if 'b then
         let 'm = ! 'c in
         let 'x = 'p`.item in
         let 'm2 = 'm + 'x in
         'c := 'm2;
         let 'p1 = 'p`.left in
         'f 'c 'p1;
         let 'p2 = 'p`.right in
         'f 'c 'p2
       end }>.

Definition mtreesum : val :=
  <{ fun 'p =>
       let 'c = ref 0 in
       treeacc 'c 'p;
       get_and_free 'c }>.

Fixpoint treesum (T:tree) : int :=
  match T with
  | Leaf => 0
  | Node n T1 T2 => n + treesum T1 + treesum T2
  end. 

Lemma triple_treeacc : forall c n T p,
  triple (treeacc c p)
    ((c ~~> n) \* (MTree T p))
    (fun _ => (c ~~> (n + (treesum T))) \* (MTree T p)).
Proof using.
  intros. gen p. gen n. induction_wf IH: tree_sub T. intros.
  xwp. xapp. xchange (MTree_if p). xif; intros C; case_if; xpull.
  -- intros. xapp. xapp. xapp. xapp. xapp. xapp.
     + rewrite H. apply tree_sub_1.
     + xapp. xapp.
       ++ rewrite H. apply tree_sub_2.
       ++ xsimpl. 
          +++ rewrite H. unfold treesum. fold treesum. math.
          +++ xchange <- MTree_Node. rewrite H. xsimpl.
  -- intros. xval. rewrite H. simpl. xsimpl.
     + math.
     + rewrite C0. xchange <- MTree_Leaf. reflexivity.
Qed.

#[global] Hint Resolve triple_treeacc : triple.

Lemma triple_mtreesum : forall T p,
  triple (mtreesum p)
    (MTree T p)
    (fun r => \[r = treesum T] \* (MTree T p)).
Proof using.
  intros. xwp. xapp. intros. xapp triple_treeacc.
  xapp. xsimpl. math.
Qed.

Definition create_counter : val :=
  <{ fun 'u =>
       let 'p = ref 0 in
       (fun_ 'u => (incr 'p; !'p)) }>.

Definition CounterSpec (f:val) (p:loc) : Prop :=
  forall m, triple (f ())
                    (p ~~> m)
                    (fun r => \[r = m+1] \* p ~~> (m+1)).

Implicit Type f : val.

Lemma triple_create_counter :
  triple (create_counter ())
    \[]
    (fun f => \exists p, (p ~~> 0) \* \[CounterSpec f p]).
Proof using.
  xwp. xapp. intros p.
  xfun. intros f Hf. xsimpl.
  { intros m. xapp. xapp. xapp. xsimpl. auto. }
Qed.  

Definition IsCounter (f:val) (n:int) : hprop :=
  \exists p, p ~~> n \* \[CounterSpec f p].

Lemma triple_create_counter_abstract :
  triple (create_counter ())
    \[]
    (fun f => IsCounter f 0).
Proof using.
  (*
  xwp. xapp. intros.
  xfun. intros. unfold IsCounter.
  xsimpl.
  { intros m. xapp. xapp. xapp. xsimpl. auto. }
  *)
  (* book version *)
  unfold IsCounter. apply triple_create_counter.
Qed.

Lemma triple_apply_counter_abstract : forall f n,
  triple (f ())
    (IsCounter f n)
    (fun r => \[r = n+1] \* (IsCounter f (n+1))).
Proof using.
  intros. unfold IsCounter. unfold CounterSpec.
  xtriple. xsimpl. intros.
  xapp. xsimpl.
  - auto.
  - auto.
Qed.

Opaque IsCounter.

Definition test_counter : val :=
  <{ fun 'u =>
       let 'c1 = create_counter () in
       let 'c2 = create_counter () in
       let 'n1 = 'c1 () in
       let 'n2 = 'c2 () in
       let 'n3 = 'c1 () in
       'n2 + 'n3 }>.

Lemma triple_test_counter :
  triple (test_counter ())
    \[]
    (fun r => \[r = 3] \* (\exists H, H)).
Proof using.
  xwp. xapp triple_create_counter_abstract.
  intros. xapp triple_create_counter_abstract.
  intros. xapp triple_apply_counter_abstract.
  xapp triple_apply_counter_abstract.
  xapp triple_apply_counter_abstract.
  xapp. xsimpl. math.
Qed.  
  
Definition repeat : val :=
  <{ fix 'g 'f 'n =>
       let 'b = ('n > 0) in
       if 'b then
         'f ();
         let 'n2 = 'n - 1 in
         'g 'f 'n2
       end }>.

Lemma triple_repeat : forall (I:int->hprop) (f:val) (n:int),
  n >= 0 ->
  (forall i, 0 <= i < n ->
    triple (f ())
      (I i)
      (fun u => I (i+1))) ->
  triple (repeat f n)
    (I 0)
    (fun u => I n).
Proof using.
  introv Hn Hf.
  cuts G: (forall m, 0 <= m <= n ->
    triple (repeat f m)
      (I (n-m))
      (fun u => I n)).
  { replace 0 with (n - n). { eapply G. math. } { math. } }
  intros m. induction_wf IH: (downto 0) m. intros Hm.
  xwp. xapp. xif; intros C.
  - xapp.
    -- math.
    -- xapp. xapp.
       + math.
       + math.
       + math_rewrite ((n - m) + 1 = n - (m - 1)). xsimpl.
  - xval. math_rewrite (n - m = n). xsimpl.
Qed.

Definition miter : val :=
  <{ fix 'g 'f 'p =>
       let 'b = ('p <> null) in
       if 'b then
         let 'x = 'p`.head in
         'f 'x;
         let 'q = 'p`.tail in
         'g 'f 'q
       end }>.

Compute take 3 (0::1::2::3::nil).

Definition is_prefix (l L : list val) : Prop :=
  exists m:nat, l = take m L.
  
Definition is_suffix (l L : list val) : Prop :=
  exists m:nat, m > 0%nat /\ l = drop m L.

Definition is_sub_list (l L : list val) : Prop :=
  list_sub l L \/ l = L.  

Lemma list_sub_impl_not_nil : forall (l L : list val), list_sub l L -> L <> nil.
Proof.
intros. inversion H.
- unfold "~". intros. inversion H2.
- unfold "~". intros. inversion H3.
Qed.

Example list_sub_ex1 : list_sub (2::3::4::nil) (1::2::3::4::nil).
Proof. apply list_sub_cons. Qed.

Example list_sub_ex2 : list_sub (3::4::nil) (1::2::3::4::nil).
Proof. apply list_sub_tail. apply list_sub_cons. Qed.

Example list_sub_ex3 : list_sub (4::nil) (1::2::3::4::nil).
Proof. apply list_sub_tail. apply list_sub_tail. apply list_sub_cons. Qed.

Example list_sub_ex4 : list_sub nil (1::2::3::4::nil).
Proof. apply list_sub_tail. apply list_sub_tail. apply list_sub_tail. apply list_sub_cons. Qed.

Lemma list_sub_ex5 : forall (x : val), list_sub nil (x::nil).
Proof. intros. apply list_sub_cons. Qed.

Lemma list_sub_nil : forall (l:list val), ~ (list_sub l nil).
Proof. intros. unfold "~". intros. inversion H. Qed.

(* takeaways from proving this:
1. Analogy with the proof of the 'repeat' function's specification
2. Need to frame G is the right way, no need to use take/drop functions
3. Correct generalization
4. Well-founded induction on the list l2, with list_sub as the function to use
5. Pushing to solve the final subgoal - figuring out q = null implies l2 is nil.
6. Related to #5, all the steps till the final subgoal felt right, and the final
   subgoal seemed the right one to land up in.
*)

Lemma triple_miter : forall (I:list val->hprop) L (f:val) p,
  (forall x L1 L2, L = L1++x::L2 ->
    triple (f x)
      (I L1)
      (fun u => I (L1++(x::nil)))) ->
  triple (miter f p)
    (MList L p \* I nil)
    (fun u => MList L p \* I L).
Proof using.

  intros.

  cuts G : (forall l1 l2 q,
              L = l1 ++ l2 ->
              triple (miter f q)
                (MList l2 q \* I l1)
                (fun u => MList l2 q \* I L)).
  {
    apply (G nil L p). rewrite app_nil_l. auto.
  }

  intros. gen q. gen l1. induction_wf IH: list_sub l2. intros.
  xwp. xapp. xif.
  - intros. xchange (MList_if q). case_if. xapp. intros.
    xchange <- (MList_cons q). xapp.
    -- rewrite <- H3 in H2. rewrite <- H2. auto.
    -- xchange (MList_cons q). intros.
       xapp. xapp.
       + rewrite H2. apply list_sub_cons.
       + rewrite <- H3 in H2. rewrite H0. rewrite H2. rew_list. auto.
       + xsimpl. xchange <- (MList_cons q). rewrite H2. xsimpl.
  - intros. xval. xchange (MList_if q). case_if.
    xsimpl. intros. rewrite H2. rewrite C. rewrite H2 in H0.
    rewrite app_nil_r in H0. rewrite H0. xsimpl. xchange <- (MList_nil). auto.
Qed.

Definition mlength_using_miter : val :=
  <{ fun 'p =>
       let 'c = ref 0 in
       let 'f = (fun_ 'x => incr 'c) in
       miter 'f 'p;
       get_and_free 'c }>.

Lemma triple_mlength_using_miter : forall p L,
  triple (mlength_using_miter p)
    (MList L p)
    (fun r => \[r = length L] \* MList L p).
Proof using.
  xwp. xapp. intros.
  xfun; intros f Hf.
  xapp (triple_miter (fun K => x0 ~~> (length K))).
  - intros. xtriple. xapp. xapp. xsimpl. rew_list. math.
  - xapp. xsimpl. auto. 
Qed.

Definition cps_facto_aux : val :=
  <{ fix 'f 'n 'k =>
       let 'b = 'n <= 1 in
       if 'b
         then 'k 1
         else let 'k2 = (fun_ 'r => let 'r2 = 'n * 'r in 'k 'r2) in
              let 'n2 = 'n - 1 in
              'f 'n2 'k2 }>.
              
Definition cps_facto : val :=
  <{ fun 'n =>
       let 'k = (fun_ 'r => 'r) in
       cps_facto_aux 'n 'k }>.
       
(*
Hint: you can use the syntax
    xapp (>> IH F') to instantiate the induction hypothesis IH on a specific
    function F'. *)
    
Import Facto.

Lemma cps_facto_helper1 : forall n : int, n >= 0 -> n <= 1 -> n = 0 \/ n = 1.
Proof.
  induction n; intros.
  - left. auto.
  - induction p.
    -- right. math.
    -- right. math.
    -- right. auto.
  - induction p.
    -- left. math.
    -- left. math.
    -- left. math.
Qed.

Lemma cps_facto_helper2 : forall n : int, ~ n <= 1 -> n > 1.
Proof.
  intros.
  unfold "~" in H.
  math. 
Qed.

Lemma triple_cps_facto_aux : forall (n:int) (k:val) (F:int->int),
  n >= 0 ->
  (forall (a:int), triple (k a) \[] (fun r => \[r = F a])) ->
  triple (cps_facto_aux n k)
    \[]
    (fun r => \[r = F (facto n)]).
Proof using.
  intro n. induction_wf IH: (downto 0) n. intros.
  xwp. xapp. xif.
  - intros. xapp. xsimpl.
    assert (n = 0 \/ n = 1). { apply cps_facto_helper1. auto. auto. }
    destruct H2.
    -- rewrite H2. rewrite facto_init. auto. math.
    -- rewrite H2. rewrite facto_init. auto. math.
  - intros. xfun. intros.
    xapp. xapp (>> IH (fun m:int => F (n * m) )).
    -- unfold downto. math.
    -- assert (n > 1). { apply cps_facto_helper2. auto. } math.
    -- intros. xapp. xapp. xapp. xsimpl. auto.
    -- xsimpl. rewrite (@facto_step n).
       + auto.
       + math.
Qed.

Lemma triple_cps_facto : forall n,
  n >= 0 ->
  triple (cps_facto n)
    \[]
    (fun r => \[r = facto n]).
Proof using.
  intros n. induction_wf IH: (downto 0) n. intros.
  xwp. xfun. intros. xapp (>> triple_cps_facto_aux (fun m:int => m)).
  - auto.
  - intros. xtriple. xapp. xval. xsimpl. auto.
  - xsimpl. auto.
Qed.

Definition cps_append_aux : val :=
  <{ fix 'f 'p1 'p2 'k =>
       let 'b = ('p1 = null) in
       if 'b
         then 'k 'p2
         else
           let 'q1 = 'p1`.tail in
           let 'k2 = (fun_ 'r => ('p1`.tail := 'r; 'k 'p1)) in
           'f 'q1 'p2 'k2 }>.
           
Definition cps_append : val :=
  <{ fun 'p1 'p2 =>
      let 'f = (fun_ 'r => 'r) in
      cps_append_aux 'p1 'p2 'f }>.

Lemma triple_cps_append_aux : forall H Q (L1 L2:list val) (p1 p2:loc) (k:val),
  (forall (p3:loc), triple (k p3) (MList (L1 ++ L2) p3 \* H) Q) ->
  triple (cps_append_aux p1 p2 k)
    (MList L1 p1 \* MList L2 p2 \* H)
    Q.
Proof using.
  intros. gen H. gen p2. gen p1. gen k. gen L2. induction_wf IH: list_sub L1.
  intros. xwp. xchange (MList_if p1). case_if.
  - xpull. intros. xapp. xif.
    -- intros. xapp. rewrite H1. rewrite app_nil_l. xsimpl.
    -- intros. unfold "~" in H2. inversion C. exfalso. apply H2. auto.
  - xpull. intros. xapp. xif.
    -- intros. unfold "~" in C. inversion H2. exfalso. apply C. auto.
    -- intros. xapp. xfun. intros. rewrite H1 in IH.
       pose proof (IH x1).
       assert (list_sub x1 (x :: x1)). { apply list_sub_cons. }
       pose proof (H4 H5).
       pose proof (H6 L2 vf x0 p2). 
       clear H4 H5 H6.
       pose proof (H7 ((p1 ~~~> `{ head := x; tail := x0} \* H))).
       xapp. clear H4 H7.
       + intros. xtriple. xapp. xapp. xapp. xchange <- (MList_cons p1).
         rewrite H1. xsimpl.
       + xsimpl.
Qed.

#[global] Hint Resolve triple_cps_append_aux : triple.

(* not needed *)
Lemma cps_append_helper1 : forall (L1 L2:list val) (p1 p2:loc),
  (MList L1 p1 \* MList L2 p2 \* \[]) ==> (MList L1 p1 \* MList L2 p2).
Proof using.
  intros. xsimpl.
Qed.

(* not needed *)
Lemma cps_append_helper2 : forall (L1 L2:list val) (p1 p2:loc),
  (MList L1 p1 \* MList L2 p2) ==> (MList L1 p1 \* MList L2 p2 \* \[]).
Proof using.
  intros. xsimpl.
Qed.   

Lemma triple_cps_append : forall (L1 L2:list val) (p1 p2:loc),
  triple (cps_append p1 p2)
    (MList L1 p1 \* MList L2 p2)
    (funloc p3 => MList (L1++L2) p3).
Proof using.
  intros. xwp. xfun. intros.  
  pose proof (@triple_cps_append_aux 
                \[]
                (funloc p3 => (MList (L1 ++ L2) p3))
                L1 L2 p1 p2 vf).
  xapp.
  - intros. xtriple. xsimpl. xapp. xval. xsimpl. auto.
  - intros. xsimpl. auto.
Qed.  


     