Require Import Coq.Program.Tactics.
Require Coq.Program.Wf.
Require Import Coq.Program.Equality.

Inductive set : nat -> Type :=
  (* reflect lattice structure *)
  | prop : forall i, Prop -> set i
  | binop : forall i,
      (Prop -> Prop -> Prop) -> (set i -> set i -> set i)
  (* sets *)
  | sin : forall i, set i -> set (S i)
  | cos : forall i, set i -> set (S i)
.

(* ----------------------------------------------------------- *)

(* In and Eq at level 0 *)

Definition eval0 : set O -> Prop.
Proof.
  intro x. dependent induction x; apply P.
  apply IHx1; auto. apply IHx2; auto.
Defined.

Lemma eval0_prop: forall P, eval0 (prop 0 P) = P.
Proof. cbv; apply @eq_refl. Qed.
Lemma eval0_binop: forall P x y,
  eval0 (binop 0 P x y) = P (eval0 x) (eval0 y).
Proof. intros. cbv. apply @eq_refl. Qed.
Opaque eval0.
Hint Rewrite eval0_prop eval0_binop: nf.

Definition in0 (y x: set O) := eval0 y.
Definition eq0 (x y: set O) := eval0 x <-> eval0 y.

(* ----------------------------------------------------------- *)

(* Fixpoint iim k (y: set (S k)) : (set k -> Prop) -> Prop :=
  match y return (set k -> Prop) -> Prop with
  | prop _ c => fun _ => c
  | binop _ P y' y'' => fun X => P (iim _ y' X) (iim k y'' X)
  | sin _ y' => fun _ => False
  | cos _ y' => fun X => X y'  (* FIXME: missing eeq *)
end. *)
Definition iim2 : forall k,
(set k -> set k -> Prop) ->
set (S k) -> (set k -> Prop) -> Prop.
Proof.
  intros k _eq1 y x. dependent induction y.
  - exact P.
  - apply P. apply (IHy1 k); auto. apply (IHy2 k); auto.
  - exact False.
  - exact (exists z, _eq1 z y /\ x z).
Defined.
Definition iim1 : forall k, 
  (set (S k) -> set k -> Prop) ->
    set (S k) -> (set (S k) -> Prop) -> Prop.
Proof.
  intros k eq' y X. dependent induction y.
  - exact P.
  - apply P. apply (IHy1 k eq'); auto. apply (IHy2 k eq'); auto.
  - exact False.
  - exact (exists z, eq' z y /\ X z).
Defined.

Definition eeq' : forall k,
  (set (S k) -> (set k -> Prop) -> Prop) ->
  (set k -> (set k -> Prop) -> Prop) ->
  (set (S k) -> set k -> Prop) ->
  (set k -> set k -> Prop) ->
  set (S k) -> set k -> Prop.
Proof.
  intros k _im2 _im1 iin' iin'' x y.
  exact (
    (forall z, iin' x z <-> iin'' y z)
    /\ (forall Z, _im2 x Z <-> _im1 y Z)
    ).
Defined.

Definition eeq'' : forall k,
  (set (S k) -> (set k -> Prop) -> Prop) ->
  (set (S k) -> set k -> Prop) ->
  (set k -> set k -> Prop) ->
  set (S k) -> set (S k) -> Prop.
Proof.
  intros k _im2 iin' iin'' x y.
  exact (
    (forall z, iin' x z <-> iin' y z)
    /\ (forall Z, _im2 x Z <-> _im2 y Z)
    ).
Defined.

Definition iin2 : forall k,
  (set k -> set k -> Prop) ->
  (set k -> set k -> Prop) ->
  set (S k) -> set k -> Prop.
Proof.
  intros k _eeq _iin y x.
  dependent induction y.
  - exact P.
  - apply P. apply (IHy1 k); auto. apply (IHy2 k); auto.
  - apply _eeq. exact x. exact y.
  - apply _iin. exact x. exact y.
Defined.

Lemma iin2_prop: forall k a b p z, iin2 k a b (prop _ p) z = p.
Proof. intros. cbv. auto. Qed.

Definition iin1 : forall k,
  (set (S k) -> set k -> Prop) ->
  (set (S k) -> set k -> Prop) ->
  set (S k) -> set (S k) -> Prop.
Proof.
  intros k _eeq _iin y x.
  dependent induction y.
  - exact P.
  - apply P. apply (IHy1 k); auto. apply (IHy2 k); auto.
  - apply _eeq. exact x. exact y.
  - apply _iin. exact x. exact y.
Defined.

(* ----------------------------------------------------------- *)
(* The miracle fixpoint *)

Fixpoint Iin1 k : set k -> set k -> Prop :=
  match k return set k -> set k -> Prop with 
  | O => in0
  | S m =>
  let Iin2m := iin2 m (Eeq1 m) (Iin1 m) in
  let Iim2m := iim2 m (Eeq1 m) in
  let Eeq2m := eeq' m (Iim2m) (Iim1 m) Iin2m (Iin1 m) in
  iin1 m Eeq2m Iin2m
  end
(* with Iin2 k : set (S k) -> set k -> Prop :=
  iin2 k (Eeq1 k) (Iin1 k) *)
with Eeq1 k : set k -> set k -> Prop :=
  match k with
  | O => eq0
  | S m =>
  let Iin2m := iin2 m (Eeq1 m) (Iin1 m) in
  let Iim2m := iim2 m (Eeq1 m) in
  eeq'' m (Iim2m) (Iin2m) (Iin1 m)
  end
with Iim1 k : set k -> (set k -> Prop) -> Prop :=
  match k with 
  | O => fun y _ => eval0 y
  | S m =>
      let Iin2m := iin2 m (Eeq1 m) (Iin1 m) in
      let Iim2m := iim2 m (Eeq1 m) in
      let Eeq2m := eeq' m (Iim2m) (Iim1 m) Iin2m (Iin1 m) in
      iim1 m (Eeq2m)
  end
(* with Iim2 k : set (S k) -> (set k -> Prop) -> Prop :=
  iim2 k (Eeq1 k) *)
(* with Eeq2 k : set (S k) -> set k -> Prop :=
  eeq' k (Iin2 k) (Iin1 k) *)
.

Definition Iim2 k : set (S k) -> (set k -> Prop) -> Prop :=
iim2 k (Eeq1 k).
Definition Iin2 k : set (S k) -> set k -> Prop :=
iin2 k (Eeq1 k) (Iin1 k).
Definition Eeq2 k : set (S k) -> set k -> Prop :=
eeq' k (Iim2 k) (Iim1 k) (Iin2 k) (Iin1 k).

(* ----------------------------------------------------------- *)

Lemma Iin1_0 : Iin1 0 = in0.
Proof. auto. Qed.
Lemma Eeq1_0 : Eeq1 0 = eq0.
Proof. auto. Qed.
Lemma Iim1_0 : forall x y, Iim1 0 x y = eval0 x.
Proof. auto. Qed.
Lemma ext_0 : forall x y, Eeq1 0 x y <-> forall z, Iin1 0 x z <-> Iin1 0 y z.
Proof.
  intros. rewrite Eeq1_0. rewrite Iin1_0. unfold eq0, in0. tauto.
Qed.
Lemma ext_m_0 : forall x y, Eeq1 0 x y <-> forall z, Iim1 0 x z <-> Iim1 0 y z.
Proof.
intros. rewrite Eeq1_0. split; auto; intros. pose proof (H (fun _=> True)). rewrite Iim1_0 in H0. rewrite Iim1_0 in H0. unfold eq0. auto.
Qed.
Lemma ext_comb_0: forall x y, Eeq1 0 x y <-> (
  (forall z, Iin1 0 x z <-> Iin1 0 y z) /\
  (forall Z, Iim1 0 x Z <-> Iim1 0 y Z)
).
Proof.
  intros. split; intros.
  - split. apply ext_0; auto. apply ext_m_0; auto.
  - destruct H. apply ext_0; auto.
Qed.



Require Import Setoid Morphisms Program.Syntax.
Lemma ext_n n: forall x y, Eeq1 n x y <-> (
  (forall z, Iin1 n x z <-> Iin1 n y z) /\
  (forall Z, Iim1 n x Z <-> Iim1 n y Z)
).
(* Proof.
  destruct n.
  - apply ext_comb_0.
  - dependent destruction x; dependent destruction y; simpl.
  -- unfold eeq''. setoid_rewrite iin2_prop. apply @eq_refl.
  - simpl Eeq1. simpl Iin1. simpl Iim1. unfold eeq'.  *)
Admitted.


(* ----------------------------------------------------------- *)
(* Lift *)


Fixpoint lift {k} (y: set k) : set (S k) :=
  match y with
  | prop _ c => prop _ c
  | binop _ P y' y'' => binop _ P (lift y') (lift y'')
  | sin _ y' => sin _ (lift y')
  | cos _ y' => cos _ (lift y')
end.

Inductive Iin : forall {i j}, set i -> set j -> Prop :=
  | real: forall i x y, Iin1 i x y -> @Iin i i x y
  | lower_l: forall i j x y, Iin (lift x) y -> @Iin i j x y
  | lower_r: forall i j x y, Iin x (lift y) -> @Iin i j x y
  | raise_l: forall i j x y, @Iin i j x y -> Iin (lift x) y
  | raise_r: forall i j x y, @Iin i j x y -> Iin x (lift y)
.

Definition setX := { i : nat & set i }.

Definition IN (x y : setX) := match x, y with
  | existT _ _ t, existT _ _ u => Iin t u
end.

Definition EQ (x y : setX) := forall z, IN x z <-> IN y z.
