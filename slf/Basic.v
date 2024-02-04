Set Implicit Arguments.
From SLF Require Import LibSepReference.
Import ProgramSyntax DemoPrograms.

Implicit Types n m : int.
Implicit Types p q : loc.

Definition incr : val :=
  <{ fun 'p =>
      let 'n = ! 'p in
      let 'm = 'n + 1 in
      'p := 'm }>.

Lemma triple_incr : forall (p:loc) (n:int),
  triple <{ incr p }>
    (p ~~> n)
    (fun _ => (p ~~> (n+1))).
Proof. xwp. xapp. xapp. xapp. xsimpl. Qed.

#[global] Hint Resolve triple_incr : triple.

Lemma triple_incr' : forall (p:loc) (n:int),
  triple (incr p)
    (p ~~> n)
    (fun _ => (p ~~> (n+1))).
Proof.
  (* Here, to view coercions, use Set Printing Coercions., or in CoqIDE use
     Shift+Alt+C, which corresponds to the menu View / Display Coerctions. *)
  xwp. xapp. xapp. xapp. xsimpl.
Qed.

Definition example_let : val :=
  <{ fun 'n =>
      let 'a = 'n + 1 in
      let 'b = 'n - 1 in
      'a + 'b }>.

Lemma triple_example_let : forall (n:int),
  triple (example_let n)
    \[]
    (fun r => \[r = 2*n]).
Proof. xwp. xapp. xapp. xapp. xsimpl. math. Qed.

Definition quadruple : val :=
  <{ fun 'n =>
       let 'm = 'n + 'n in
       'm + 'm }>.

Lemma quadruple_spec : forall (n:int),
  triple (quadruple n)
     \[]
     (fun r => \[r = 4*n]).
Proof. xwp. xapp. xapp. xsimpl. math. Qed.

Definition inplace_double : val :=
  <{ fun 'p =>
       let 'n = !'p in
       let 'm = 'n + 'n in
       'p := 'm }>.

Lemma inplace_double_spec : forall (p:loc) (n:int),
  triple (inplace_double p)
    (p ~~> n)
    (fun _ => (p ~~> (n+n))).
Proof. xwp. xapp. xapp. xapp. xsimpl. Qed.

Definition incr_two : val :=
  <{ fun 'p 'q =>
       incr 'p;
       incr 'q }>.

Lemma triple_incr_two : forall (p q:loc) (n m:int),
  triple (incr_two p q)
    (p ~~> n \* q ~~> m)
    (fun _ => p ~~> (n+1) \* q ~~> (m+1)).
Proof using.
  xwp. xapp. xapp. xsimpl.
Qed.

#[global] Hint Resolve triple_incr_two : triple.

Definition aliased_call : val :=
  <{ fun 'p =>
       incr_two 'p 'p }>.

Lemma triple_aliased_call : forall (p:loc) (n:int),
  triple (aliased_call p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof. xwp. xapp. Abort.

Lemma triple_incr_two_aliased : forall (p:loc) (n:int),
  triple (incr_two p p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp. xapp. xapp. xsimpl. math.
Qed.

Lemma triple_aliased_call : forall (p:loc) (n:int),
  triple (aliased_call p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp. xapp triple_incr_two_aliased. xsimpl.
Qed.

Definition incr_first : val :=
  <{ fun 'p 'q =>
       incr 'p }>.

Lemma triple_incr_first : forall (p q:loc) (n m:int),
  triple (incr_first p q)
    (p ~~> n \* q ~~> m)
    (fun _ => p ~~> (n+1) \* q ~~> m).
Proof using.
  xwp. xapp. xsimpl.
Qed.

Lemma triple_incr_first' : forall (p q:loc) (n:int),
  triple (incr_first p q)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  xwp. xapp. xsimpl.
Qed.

Lemma triple_incr_first_derived : forall (p q:loc) (n m:int),
  triple (incr_first p q)
    (p ~~> n \* q ~~> m)
    (fun _ => p ~~> (n+1) \* q ~~> m).
Proof using.
  intros. xapp triple_incr_first'. xsimpl.
Qed.

Definition transfer : val :=
  <{ fun 'p 'q =>
       let 'n = !'p in
       let 'm = !'q in
       let 's = 'n + 'm in
       'p := 's;
       'q := 0 }>.

Lemma triple_transfer : forall (p q:loc) (n m:int),
  triple (transfer p q)
    (p ~~> n \* q ~~> m)
    (fun _ => p ~~> (n+m) \* q ~~> 0).
Proof.
  xwp. xapp. xapp. xapp. xapp. xapp. xsimpl.
Qed.

Lemma triple_transfer_aliased : forall (p : loc) (n : int),
  triple (transfer p p)
    (p ~~> n)
    (fun _ => p ~~> 0).
Proof.
  xwp. xapp. xapp. xapp. xapp. xapp. xsimpl.
Qed.

Parameter triple_ref : forall (v:val),
  triple <{ ref v }>
    \[]
    (fun r => \exists p, \[r = val_loc p] \* p ~~> v).

Notation "'funloc' p '=>' H" :=
  (fun (r:val) => \exists p, \[r = val_loc p] \* H)
  (at level 200, p name, format "'funloc' p '=>' H").

Parameter triple_ref' : forall (v:val),
  triple <{ ref v }>
    \[]
    (funloc p => p ~~> v).

Definition ref_greater : val :=
  <{ fun 'p =>
       let 'n = !'p in
       let 'm = 'n + 1 in
       ref 'm }>.

Lemma triple_ref_greater : forall (p:loc) (n:int),
  triple (ref_greater p)
    (p ~~> n)
    (funloc q => p ~~> n \* q ~~> (n+1)).
Proof using.
  xwp. xapp. xapp. xapp. intros q. xsimpl. auto.
Qed.

Lemma triple_ref_greater_abstract : forall (p:loc) (n:int),
  triple (ref_greater p)
    (p ~~> n)
    (funloc q => p ~~> n  \* \exists m, \[m > n] \* q ~~> m ).
Proof using.
  intros. xapp triple_ref_greater. xsimpl.
  - reflexivity.
  - math.
Qed.

Definition succ_using_incr_attempt :=
  <{ fun 'n =>
       let 'p = ref 'n in
       incr 'p;
       ! 'p }>.

Lemma triple_succ_using_incr_attempt : forall (n:int),
  triple (succ_using_incr_attempt n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xsimpl. { auto. }
Abort.

Lemma triple_succ_using_incr_attempt' : forall (n:int),
  triple (succ_using_incr_attempt n)
    \[]
    (fun r => \[r = n+1] \* \exists p, (p ~~> (n+1))).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xsimpl. reflexivity.
Qed.

Definition succ_using_incr :=
  <{ fun 'n =>
       let 'p = ref 'n in
       incr 'p;
       let 'x = ! 'p in
       free 'p;
       'x }>.

Lemma triple_succ_using_incr : forall n,
  triple (succ_using_incr n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  xwp. xapp. intros p. xapp. xapp.
  xapp. (* reasoning about the call free p *)
  xval. (* reasoning about the return value, named x. *)
  xsimpl. auto.
Qed.

Definition get_and_free : val :=
  <{ fun 'p =>
      let 'v = ! 'p in
      free 'p;
      'v }>.

Lemma triple_get_and_free : forall p v,
  triple (get_and_free p)
    (p ~~> v)
    (fun r => \[r = v]).
Proof using.
  xwp. xapp. xapp. xval. xsimpl. reflexivity.
Qed.

#[global] Hint Resolve triple_get_and_free : triple.

Module Import Facto.

Parameter facto : int -> int.

Parameter facto_init : forall n,
  0 <= n <= 1 ->
  facto n = 1.
  
Parameter facto_step : forall n,
  n > 1 ->
  facto n = n * (facto (n-1)).

End Facto.

Definition factorec : val :=
  <{ fix 'f 'n =>
       let 'b = 'n <= 1 in
       if 'b
         then 1
         else let 'x = 'n - 1 in
              let 'y = 'f 'x in
              'n * 'y }>.

Lemma triple_factorec : forall n,
  n >= 0 ->
  triple (factorec n)
    \[]
    (fun r => \[r = facto n]).
Proof using.
  intros n. induction_wf IH: (downto 0) n.
  unfold downto in IH. (* optional *)
  intros Hn. xwp.
  xapp.
  xif.
  - intros C. xval. xsimpl. rewrite facto_init. auto. auto.
  - intros C. xapp. xapp.
    -- math.
    -- math.
    -- xapp. xsimpl. rewrite (@facto_step n). math. math.
Qed.

Definition repeat_incr : val :=
  <{ fix 'f 'p 'm =>
       let 'b = 'm > 0 in
       if 'b then
         incr 'p;
         let 'x = 'm - 1 in
         'f 'p 'x
       end }>.

Lemma triple_repeat_incr : forall (m n:int) (p:loc),
  m >= 0 ->
  triple (repeat_incr p m)
    (p ~~> n)
    (fun _ => p ~~> (n + m)).
Proof using.
  intros m. induction_wf IH: (downto 0) m.
  unfold downto in IH.
  intros. xwp. xapp. xif.
  - intros. xapp. xapp. xapp. math. math. xsimpl. math.
  - intros. xval. xsimpl. assert (m = 0) by math. rewrite H1. math.
Qed.

Lemma triple_repeat_incr' : forall (p:loc) (n m:int),
  m >= 0 ->
  triple (repeat_incr p m)
    (p ~~> n)
    (fun _ => p ~~> (n + m)).
Proof using.
  intros p n. intros. generalize H. generalize dependent p. generalize dependent n.
  clear H. induction_wf IH: (downto 0) m.
  unfold downto in IH.
  intros. xwp. xapp. xif.
  - intros. xapp. xapp. xapp. math. math. xsimpl. math.
  - intros. xval. xsimpl. assert (m = 0) by math. rewrite H1. math.
Qed.

Lemma triple_repeat_incr_incorrect : forall (p:loc) (n m:int),
  triple (repeat_incr p m)
    (p ~~> n)
    (fun _ => p ~~> (n + m)).
Proof using.
  intros. revert n. induction_wf IH: (downto 0) m. unfold downto in IH.
  intros. xwp. xapp. xif; intros C.
  { (* In the 'then' branch: m > 0 *)
    xapp. xapp. xapp. { math. } xsimpl. math. }
  { (* In the 'else' branch: m ≤ 0 *)
    xval.
    xsimpl.
Abort.

Lemma max_l : forall n m,
  n >= m ->
  max n m = n.
Proof.
  intros. unfold max. case_if. math. auto.
Qed.

Lemma max_r : forall n m,
  n <= m ->
  max n m = m.
Proof. intros. unfold max. case_if. auto. math. Qed.

Lemma triple_repeat_incr'' : forall (p:loc) (n m:int),
  triple (repeat_incr p m)
    (p ~~> n)
    (fun _ => p ~~> (n + max 0 m)).
Proof using.
  intros p n. intros. generalize dependent p. generalize dependent n.
  induction_wf IH: (downto 0) m.
  unfold downto in IH.
  intros. xwp. xapp. xif.
  - intros. xapp. xapp. xapp.
    -- math.
    -- xsimpl. rewrite max_r. unfold max.
       case_if.
       + math.
       + assert (m = 0) by math. rewrite H0. math.
       + math.
  - intros. xval. xsimpl. unfold max. case_if.
    -- assert (m = 0) by math. rewrite H0. math.
    -- math.
Qed.

Definition step_transfer :=
  <{ fix 'f 'p 'q =>
       let 'm = !'q in
       let 'b = 'm > 0 in
       if 'b then
         incr 'p;
         decr 'q;
         'f 'p 'q
       end }>.

Lemma triple_step_transfer : forall p q n m,
  m >= 0 ->
  triple (step_transfer p q)
    (p ~~> n \* q ~~> m)
    (fun _ => p ~~> (n + m) \* q ~~> 0).
Proof using.
  intros. revert n. generalize H. clear H.
  induction_wf IH: (downto 0) m. unfold downto in IH.
  intros. xwp. xapp. xapp. xif.
  - intros. xapp. xapp. xapp. math. math. xsimpl. math.
  - intros. xval. xsimpl.
    assert (m = 0) by math. math. math.
Qed.

         