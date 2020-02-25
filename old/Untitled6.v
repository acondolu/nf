Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Definition var := nat.
Definition lev := nat.

Inductive vvar (i: var->nat) n :=
  | Universal : forall v, i v = n -> vvar i n
  | Existential : forall v m, i v + m = n -> vvar i n
.

Inductive f (i: var -> nat) : Set :=
| T | F
| fconj: f i -> f i -> f i
| fiff: f i -> f i -> f i
| fthen: f i -> f i -> f i
| fall: var -> f i -> f i
| fex: var -> f i -> f i
| feq: forall n: nat, vvar i n -> vvar i n -> f i
| fin: forall n, vvar i n -> vvar i (S n) -> f i
.

Fixpoint u n a := match n with
| O => a
| S m => u m a -> Prop
end.

Lemma comp: forall n m a, u n (u m a) = u (n + m) a.
Proof.
  induction n. intro m.
  - auto.
  - intros. rewrite plus_Sn_m. simpl. rewrite IHn. auto.
Qed.

Definition ass_fo i K := forall v: var, u (i v) K.
Definition ass_ex i := forall v: var, forall K, u (i v) K.

Require Import Coq.Arith.Peano_dec.

Definition alter_fo {i K} (a: ass_fo i K) v (x: u (i v) K) : ass_fo i K.
Proof.
  intro n.
  destruct (eq_nat_dec n v).
  - rewrite e. assumption.
  - apply (a n).
Defined. 

Definition alter_ex {i} (a: ass_ex i) v (x: forall K, u (i v) K) : ass_ex i.
Proof.
  intro n.
  Search ({_ = _} + {_}).
  destruct (eq_nat_dec n v).
  - rewrite e. apply x.
  - apply (a n).
Defined. 

Definition mk_var {n i K} (af: ass_fo i K) (ae: ass_ex i) (v: vvar i n): u n K.
Proof. 
destruct v.
- rewrite<- e. exact (af v).
- rewrite<- e. rewrite<- comp. apply (ae v (u m K)).
Defined.


Fixpoint mk {i} K (af: ass_fo i K) (ae: ass_ex i) f := match f with
| T _ => True
| F _ => False
| fconj _ x y => mk K af ae x /\ mk K af ae y
| fthen _ x y => mk K af ae x -> mk K af ae y
| fiff _ x y => mk K af ae x <-> mk K af ae y
| fall _ v f' => forall x, mk K (alter_fo af v x) ae f'
| fex _ v f' => exists x, mk K af (alter_ex ae v x) f'
| fin _ n v w => mk_var af ae w (mk_var af ae v)
| feq _ n v w => mk_var af ae v = mk_var af ae w
end.

Definition eval {i} (f': f i) := forall K a a', @mk i K a a' f'.

Definition vu {n} i v x := Universal i n v x.
Check vu.

Check eq_trans.

Require Import Coq.Program.Equality.

Axiom gosh: forall {T} {a b: T} {eq1: a = b}, eq_trans eq_refl eq1 = eq1.
Axiom gosh2: forall {T} {a: T}, @eq_sym T a a eq_refl = eq_refl.
Check eq_rect.
Lemma auxx: forall {A} {P: A -> Type} {a b c eq1 eq2}, forall {m: P c},
eq_rect c P m b eq2 = 
  eq_rect a _ (eq_rect c P m a eq1) b (eq_trans (eq_sym eq1) eq2).
Proof.
  intros. dependent destruction eq1. dependent destruction eq2.
  simpl. auto.
Qed. 

Lemma aux: forall {T T2} {x y: T -> T2}, x = y -> forall f, x f = y f.
Proof.
  intros. rewrite H. auto.
Qed.
Lemma ext i: forall x y z, forall eq1: i x = i y, forall eq2: i x = S (i z),
  eval (fall _ x (fall _ y (fiff _
    (feq _ _ (vu i x eq1) (vu i y (eq_refl _)))
    (fall _ z (fiff _ (fin _ _ (vu i z (eq_refl _)) (vu i x eq2)) (fin _ _ (vu i z (eq_refl _)) (vu i y (eq_trans (eq_sym eq1) eq2)))))
  ))).
Proof.
  intros. unfold eval. intro a. simpl mk. intros.
  unfold alter_fo. 
  destruct (PeanoNat.Nat.eq_dec y y). dependent destruction e.
  destruct (PeanoNat.Nat.eq_dec z z). dependent destruction e.
  
  -
  rename x into x'. rename x2 into x. clear x3 x'.
  destruct (PeanoNat.Nat.eq_dec x y). destruct e.
  destruct (PeanoNat.Nat.eq_dec x z). destruct e.
  destruct (PeanoNat.Nat.neq_succ_diag_r _ eq2). 
  -- (* case x = y *)
  destruct (PeanoNat.Nat.eq_dec x x). dependent destruction e.
  split; intros. split; intros; dependent destruction eq1.
  * rewrite<- H. simpl. rewrite (gosh). apply H0.
  * unfold eq_rect_r in *. rewrite gosh2. rewrite gosh2.  simpl in *. rewrite<- gosh. apply H0.
  * dependent destruction eq1. unfold eq_rect_r in *. simpl. auto.
  * destruct n0; trivial.
  -- (* case x <> y *)
  destruct (PeanoNat.Nat.eq_dec x x). dependent destruction e.
  rename x into x'. rename x2 into x. clear x'.
  destruct (PeanoNat.Nat.eq_dec x z). destruct e.
  destruct (PeanoNat.Nat.neq_succ_diag_r _ eq2).
  destruct (PeanoNat.Nat.eq_dec y z). destruct e.
  destruct (PeanoNat.Nat.neq_succ_diag_r _ (eq_trans (eq_sym eq1) eq2)).
  unfold eq_rect_r. rewrite gosh2. simpl.
  split; intros. split; intros.
  * rewrite<- H. simpl.
  rewrite<- (@auxx _ (fun n2 : nat => u n2 a) _ _ _ eq1 eq2).
  apply H0.
  * dependent destruction eq1. dependent destruction eq2.
    simpl in *. rewrite gosh in H0. rewrite H. assumption.
  * dependent destruction eq1. dependent destruction eq2.
   simpl in *. rewrite gosh in H.
   destruct (i x0).
   ** destruct (PeanoNat.Nat.neq_0_succ _ eq0).
   **  unfold eq_rect in H. dependent destruction eq0.
      extensionality zz. fold u in zz. apply propositional_extensionality.
      apply (H zz).
   * destruct n0; auto.
  -   destruct n; auto.
  - destruct n; auto.
Qed. 

Inductive vvar (i: var->nat) n :=
  | Universal : forall v, i v = n -> vvar i n
  | Existential : forall v m, i v + m = n -> vvar i n
.

Inductive f (i: var -> nat) : Set :=
| T | F
| fconj: f i -> f i -> f i
| fiff: f i -> f i -> f i
| fthen: f i -> f i -> f i
| fall: var -> f i -> f i
| fex: var -> f i -> f i
| feq: forall n: nat, vvar i n -> vvar i n -> f i
| fin: forall n, vvar i n -> vvar i (S n) -> f i
.