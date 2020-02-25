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

Inductive set_ : Type :=
  (* reflect lattice structure *)
  | prop_ : Prop -> set_
  | binop_ : 
      (Prop -> Prop -> Prop) -> (set_ -> set_ -> set_)
  (* sets *)
  | sin_ : set_ -> set_
  | cos_ : set_ -> set_
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

Axiom undecorate: forall {i}, set i -> set_.

Inductive IN_ : set_ -> set_ -> Prop :=
  | Cc : forall i x y, @Iin1 i x y -> IN_ (undecorate x) (undecorate y)
.
(* Lemma IN_' : forall x y, IN_ x y <-> exists i x y,  *)

Definition EQ (x y : setX) := forall z, IN x z <-> IN y z.

(* 
Theorem magari k: forall x : set k, forall y,
  (Eeq1 k x y <-> Eeq2 k (lift x) y)
  (* /\ (Iin1 k x y <-> Iin2 k (lift x) y)
  /\ forall Y, (Iim1 k x Y <-> Iim2 k (lift x) Y) *)
.
Proof.
  (* unfold Eeq2, Iin2, Iim2. *)
  induction k; intros.
  - simpl. unfold eq0.
    dependent induction x; dependent induction y.
    -- cbv. tauto.
    -- simpl eval0 in *. rewrite eval0_prop. simpl lift. cbv. tauto.
    -- rewrite eval0_binop. rewrite eval0_prop. simpl lift. unfold Eeq2.
       simpl. unfold eeq'. unfold Iin2, Eeq1, Iin1, Iim2. rewrite eval0_prop. simpl. split; intros. --- split; intros. unfold iin2. simpl.
       unfold solution_left. unfold eq_rect_r. unfold eq_rect. simpl. unfold set_rect. simpl. 
    -- simpl eval0 in *. cbv. tauto.

  intros x y. induc
  
  
  dependent induction x; simpl lift; simpl Eeq1; simpl Eeq2.
  - induction i. simpl. unfold eq0. unfold Eeq2. simpl. unfold eeq'. 
    rewrite wtf. unfold Iin2. simpl iin2. simpl. unfold Iim2. simpl iim2.
    

(* --------------- *)

Fixpoint iin i : set (S i) -> set i -> Prop :=
match i return set (S i) -> set i -> Prop with
  | O => fun y =>
    match y with
    | prop _ p => fun _ => p
    | binop i P y1 y2 =>
    match i return set i -> Prop with O => fun x => eval0 y | S m => fun x => P (iin _ x y1) (iin _ x y2) end
    | sin _ z => fun _ => True
    | cos _ z => fun _ => True
  end
  | S m => fun y x => True
end.
(* match y in set i return match i with O => set O -> Prop | S m => set (S m) -> Prop end with 
  | prop i p => match i with O => fun _ => p | S _ => fun _ => p end
  | binop i P y1 y2 =>
  match i return set i -> Prop with O => fun x => eval0 y | S m => fun x => P (iin _ x y1) (iin _ x y2) end
  | sin _ z => fun _ => True
  | cos _ z => fun _ => True
end. *)

Lemma iin : forall k (x: set k) (y: set (S k)), Prop
with iin' : forall k (x: set k) (y: set k), Prop
(* with eeq : forall k (x: set k) (y: set k), Prop
with eeq' : forall k (x: set k) (y: set (S k)), Prop *)
with iim : forall k (x: set k -> Prop) (y: set (S k)), Prop.
Proof.
  - intros k x y. dependent induction y.
    -- exact P.
    -- apply P. apply (IHy1 k). exact x. auto.
                apply (IHy2 k). exact x. auto.
    -- exact (forall z, iin' k z x <-> iin' k z y). (* TODO *)
        (* exact (eeq _ x y). *)
    -- exact (iin' k y x).
  - intros k x y. dependent induction y.
    -- exact P.
    -- apply P. apply (IHy1). exact x.
                apply (IHy2). exact x.
    -- exact (forall z, iin i z x <-> iin' i z y). (* TODO *)
      (* exact (eeq' _ y x). *)
    -- exact (iin i y x).
  (* - induction k.
    -- exact eq0.
    -- intros x y. exact (forall z, iin _ z x <-> iin _ z y). (* TODO *)
  - intros k x y.  exact (forall z, iin' _ z x <-> iin _ z y). TODO *)
  - intros k X y. dependent induction y.
  -- exact P.
  -- apply P. apply (IHy1 k). exact X. auto.
              apply (IHy2 k). exact X. auto.
  -- exact False.
  -- exact (exists y', eeq y y' /\ X y').
Defined.

Program Fixpoint iin k1 k2 (x: set k1) (y: set k2) {measure (k1+k2)} := match y with 
  | prop _ p => p
  | binop i j _ p1 p2 P y1 y2 => P (iin i j x y1) (iin i j x y2)
  | sin i _ d z => eeq i (j-1) x z
  | cos i _ d z => iin (j-1) i z x
end with eeq i j (x: set i) (y: set j) := match i,j with
  | O, O => eq0 x y
  | O, S j' => forall z, eval0 x <-> iin z y
  | O, S j' => forall z, iin z x <-> eval0 y
  | S i', S j' => forall z : set (max i' j'), iin _ _ z x <-> iin _ _ z y
end with iim k1 k2 (x: set k1) (Q: set k2 -> Prop) := match y with 
| prop _ p => p
| binop i j _ p1 p2 P y1 y2 => P (iin i j x y1) (iin i j x y2)
| sin i _ d z => False
| cos i _ d z => Q z
end .

Definition imprecise {i} (x: set (S i)) : (set i -> Prop) -> Prop.
Proof.
  dependent induction x; intro y.
  - exact P. 
  - apply P. apply (IHx1 i (eq_refl) y). apply (IHx2 i (eq_refl) y).
  - exact False.
  - exact (y x).
Defined.

Lemma iin : forall i, set (S i) -> set i -> Prop
with eeq: forall i, set i -> set i -> Prop.
Proof.
  - intros i x y. dependent induction x.
  -- exact P.
  -- apply P. apply (IHx1 i); auto. apply (IHx2 i); auto.
  -- exact (eeq i x y).
  -- exact (iin _ x y). (* iin j i *)
  - intros. apply (den _ x = den _ y /\ imprecise x = imprecise y).
Qed. 
(* 
  eeq x y := forall z, iin x z -> 
 *)

(* Parameter den : forall i (x: set (S i)), set i -> Prop *)
Definition Eeq : forall i j, forall (x: set i) (y: set j), Prop.
Proof.
  intros.


Fixpoint den {i} (x: set (S i)) : set i -> Prop :=
  match x with
  | nul _ => K False
  | one _ => K True
  | impl _ y z => Impl (den y) (den z)
  | conj _ y z => Meet (den y) (den z)
  | disj _ y z => Join (den y) (den z)
  | sin _ y => eq y
  | cos _ y => fun z => den z y
end. *)
