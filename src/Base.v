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

Definition respects {X} (f: X -> Prop) R :=
  forall x y, R x y -> (f x <-> f y).

Definition respects2 {X Y} f g (R: X -> Y -> Prop) :=
  forall x y, R x y -> (f x <-> g y).

(* ----------------------------------------------------------- *)

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

Lemma respects_eval0_eq0: respects eval0 eq0.
Proof.
  unfold respects. unfold eq0. intros.
  dependent induction x; dependent induction y;
  repeat rewrite eval0_prop in *; auto. 
Qed.

(* ----------------------------------------------------------- *)

(* Fixpoint iim k (y: set (S k)) : (set k -> Prop) -> Prop :=
  match y return (set k -> Prop) -> Prop with
  | prop _ c => fun _ => c
  | binop _ P y' y'' => fun X => P (iim _ y' X) (iim k y'' X)
  | sin _ y' => fun _ => False
  | cos _ y' => fun X => X y'  (* FIXME: missing eeq *)
end. *)
(* Tentativo di definizione diretta, fallito *)
(* Fixpoint iimS k (eq: set k -> set k -> Prop) (y: set (S k)) : (set k -> Prop) -> Prop :=
  match y with
  | prop n c =>
      match n with
      | O   => fun _ _ => c
      | S _ => fun _ _ => c
      end
  | binop m P y1 y2 =>
      match m with
      | O   => fun y1 y2 eq X => P (eval0 y1) (eval0 y2)
      | S m => fun y1 y2 eq X => P (iimS m eq y1 X) (iimS m eq y2 X)
      end y1 y2
  | sin n y' =>
      match n with
      | O   => fun _ => False
      | S _ => fun _ => False
      end
  | cos _ y' => fun X => exists z, eq z y /\ X z
end eq.
Proof.
  intros k _eq1 y x. dependent induction y.
  - exact P.
  - apply P. apply (IHy1 k); auto. apply (IHy2 k); auto.
  - exact False.
  - exact (exists z, _eq1 z y /\ x z).
Defined. *)


Local Definition smatch {i} (f g: set i -> Prop) (y: set (S i)) : Prop.
Proof.
  dependent induction y.
  - exact P.
  - apply P.
      apply (IHy1 i f g eq_refl).
      apply (IHy2 i f g eq_refl).
  - apply (f y).
  - apply (g y).
Defined.
Lemma smatch_prop: forall i p f g, smatch f g (prop (S i) p) = p.
Proof. intros. cbv. apply @eq_refl. Qed.
Lemma smatch_binop: forall i x y P f g,
  smatch f g (binop (S i) P x y) =
  P (smatch f g x) (smatch f g y).
Proof. intros. cbv. apply @eq_refl. Qed.
Lemma smatch_sin: forall i x f g,
  smatch f g (sin (S i) x) = f x.
Proof. intros. cbv. apply @eq_refl. Qed.
Lemma smatch_cos: forall i x f g,
  smatch f g (cos (S i) x) = g x.
Proof. intros. cbv. apply @eq_refl. Qed.
Opaque smatch.

(* Fixpoint Eeq k : set k -> set k -> Prop :=
match k with
  | O => eq0
  | S m =>
      fun x y => forall (f g: set m -> Prop),
        (forall x y, f x -> f y -> Eeq m x y) ->
        (forall x y, Eeq m x y -> f x -> f y) -> 
        (* (forall x y, IIn m x y -> f x -> g y) ->  *)
          (@smatch m x f g <-> smatch y f g)
end. *)

(* ----------------------------------------------------------- *)
(* The miracle fixpoint *)

(* Definition
smatchX i (P Q: set i -> set i -> Prop) F G: set (S i) -> set i -> Prop :=
      fun x y => forall (f g: set i -> Prop),
        (forall x y, f x -> f y -> Q x y) ->
        (forall x y, Q x y -> g x -> g y) -> 
        (forall x y, P x y -> f x -> g y) -> 
          (F x f g <-> G y f g)
. *)

Definition
EeqSaux {i} (P Q: set i -> set i -> Prop): set (S i) -> set i -> Prop :=
  fun x y => forall (f g: set i -> Prop),
    (forall x y, f x -> f y -> Q x y) ->
    (forall x y, Q x y -> g x -> g y) -> 
    (forall x y, P x y -> f x -> g y) -> 
      (@smatch _ f g x <->
        (exists z, P y z /\ (f z \/ forall z', g z' <-> Q z z')))
.


Fixpoint Iin k : set k -> set k -> Prop :=
  match k return set k -> set k -> Prop with 
  | O => in0
  | S m => 
    let IinSm x y := smatch (Eeq m y) (Iin m y) x in
    let EeqSm := EeqSaux (Iin m) (Eeq m) in 
    fun x y => smatch (EeqSm y) (IinSm y) x
  end
with Eeq k : set k -> set k -> Prop :=
match k with
  | O => eq0
  | S m =>
      fun x y => forall (f g: set m -> Prop),
        (forall x y, f x -> f y -> Eeq m x y) ->
        (forall x y, Eeq m x y -> g x -> g y) -> 
        (forall x y, Iin m x y -> f x -> g y) -> 
          (smatch f g x <-> smatch f g y)
end
.

Definition IinS k : set (S k) -> set k -> Prop :=
  fun x y => smatch (Eeq k y) (Iin k y) x.
Definition EeqS k : set (S k) -> set k -> Prop :=
EeqSaux (Iin k) (Eeq k).

Theorem Iin_O : Iin 0 = in0.
Proof. auto. Qed.
Theorem Iin_S {i x y} : Iin (S i) x y = smatch (EeqS _ y) (IinS _ y) x.
Proof. simpl Iin. intros. fold (EeqS i). unfold IinS. apply eq_refl. Qed.
Opaque Iin.

(* Eeq is equivalence relation *)

Lemma Eeq_refl: forall k x, Eeq k x x.
Proof.
  destruct k; intro x.
  - simpl. unfold eq0. tauto. 
  - simpl Eeq. tauto.
Qed.

Lemma Eeq_sym: forall k x y, Eeq k x y -> Eeq k y x.
Proof.
  destruct k; intros x y.
  - simpl. unfold eq0. tauto. 
  - simpl Eeq. intros. pose proof (H f g H0 H1). tauto. 
Qed.

Lemma Eeq_trans: forall k x y z, Eeq k x y -> Eeq k y z -> Eeq k x z.
Proof.
  destruct k; intros x y z.
  - simpl. unfold eq0. tauto. 
  - simpl Eeq. intros.
  pose proof (H f g H1 H2). pose proof (H0 f g H1 H2). tauto. 
Qed.


Definition IinS0 : set 1 -> set 0 -> Prop :=
  fun x y => smatch (eq0 y) (in0 y) x
.

Definition EeqS0 : set 1 -> set 0 -> Prop :=
      fun x y => forall (f g: set 0 -> Prop),
        (forall x y, f x -> f y -> Eeq 0 x y) ->
        (forall x y, Eeq 0 x y -> g x -> g y) -> 
        (forall x y, Iin 0 x y -> f x -> g y) -> 
          (smatch f g x <-> eval0 y)
.

(* ONE LAST PROBLEM: DEFINE EeqS k ... *)



(* Previous definition of Iin/S and Iim/S and EeqS, to simplify as well *)

(* Axiom tmp: set 1 -> set 0 -> Prop.

Fixpoint EeqS k : set (S k) -> set k -> Prop :=
match k with
  | O => tmp
  | S m =>
      fun x y => forall f f' g g',
        respects2 f f' (EeqS m) -> respects2 g g' (EeqS m) -> 
          (@smatch _ x f g <-> smatch y f' g')
end. *)

(* ----------------------------------------------------------- *)

Lemma Iin_0 : Iin 0 = in0.
Proof. auto. Qed.
Lemma Eeq_0 : Eeq 0 = eq0.
Proof. auto. Qed.
Lemma ext_0 : forall x y, Eeq 0 x y <-> forall z, Iin 0 x z <-> Iin 0 y z.
Proof.
  intros. rewrite Eeq_0. rewrite Iin_0. unfold eq0, in0. tauto.
Qed.

(* Auxiliary lemmas, again *)

Lemma Iin_prop: forall i x p, 
Iin _ (prop i p) x = p.
Proof. intros; induction i; auto. Qed.

Lemma IinS_prop: forall i x p, 
IinS i (prop _ p) x = p.
Proof. intros; induction i; auto. Qed.

Lemma Iin_binop: forall i P x y1 y2, 
Iin i (binop i P y1 y2) x = 
P (Iin i y1 x) (Iin i y2 x).
Proof. intros; destruct i; auto. Qed.

Lemma IinS_binop: forall i P x y1 y2, 
IinS i (binop _ P y1 y2) x = 
P (IinS _ y1 x) (IinS _ y2 x).
Proof. intros; destruct i; auto. Qed.

Lemma Iin_sin: forall i x y, 
Iin _ (sin i y) x = EeqS _ x y.
Proof. intros. apply eq_refl. Qed.

Lemma Iin_cos: forall i x y, 
Iin _ (cos i y) x = IinS _ x y.
Proof. intros. apply eq_refl. Qed.

Lemma IinS_sin: forall i x y, 
IinS i (sin _ y) x = Eeq _ x y.
Proof. intros. apply eq_refl. Qed.

Lemma IinS_cos: forall i x y, 
IinS i (cos _ y) x = Iin _ x y.
Proof. intros. apply eq_refl. Qed.

Opaque Iin IinS Eeq EeqS.
