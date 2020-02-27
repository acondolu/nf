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

Local Definition iini {i} (y: set (S i)) (f g: set i -> Prop) : Prop.
Proof.
  dependent induction y.
  - exact P.
  - apply P.
      apply (IHy1 i eq_refl f g).
      apply (IHy2 i eq_refl f g).
  - apply (f y).
  - apply (g y).
Defined.
Lemma iini_prop: forall i p f g, iini (prop (S i) p) f g = p.
Proof. intros. cbv. apply @eq_refl. Qed.
Lemma iini_binop: forall i x y P f g,
  iini (binop (S i) P x y) f g =
  P (iini x f g) (iini y f g).
Proof. intros. cbv. apply @eq_refl. Qed.
Lemma iini_sin: forall i x f g,
  iini (sin (S i) x) f g = f x.
Proof. intros. cbv. apply @eq_refl. Qed.
Lemma iini_cos: forall i x f g,
  iini (cos (S i) x) f g = g x.
Proof. intros. cbv. apply @eq_refl. Qed.
Opaque iini.

(* Fixpoint Eeq k : set k -> set k -> Prop :=
match k with
  | O => eq0
  | S m =>
      fun x y => forall (f g: set m -> Prop),
        (forall x y, f x -> f y -> Eeq m x y) ->
        (forall x y, Eeq m x y -> f x -> f y) -> 
        (* (forall x y, IIn m x y -> f x -> g y) ->  *)
          (@iini m x f g <-> iini y f g)
end. *)


Local Definition iimS : forall k,
(set k -> set k -> Prop) ->
set (S k) -> (set k -> Prop) -> Prop.
Proof.
  intros k eq y x. dependent induction y.
  - exact P.
  - apply P. apply (IHy1 k eq). auto. apply x. apply (IHy2 k eq). auto. apply x.
  - exact False.
  - exact (exists z, eq z y /\ x z).
Defined.
Local Definition iim : forall k, 
  (set (S k) -> set k -> Prop) ->
    set (S k) -> (set (S k) -> Prop) -> Prop.
Proof.
  intros k eq y X. dependent induction y.
  - exact P.
  - apply P. apply (IHy1 k eq); auto. apply (IHy2 k eq); auto.
  - exact False.
  - exact (exists z, eq z y /\ X z).
Defined.

Local Definition eeqS : forall k,
  (set (S k) -> (set k -> Prop) -> Prop) ->
  (set k -> (set k -> Prop) -> Prop) ->
  (set (S k) -> set k -> Prop) ->
  (set k -> set k -> Prop) ->
  set (S k) -> set k -> Prop.
Proof.
  intros k iimS iim iinS iin x y.
  exact (
    (forall z, iinS x z <-> iin y z)
    /\ (forall Z, iimS x Z <-> iim y Z)
    ).
Defined.


Local Definition iinS : forall k,
  (set k -> set k -> Prop) ->
  (set k -> set k -> Prop) ->
  set (S k) -> set k -> Prop.
Proof.
  intros k eeq iin y x.
  dependent induction y.
  - exact P.
  - apply P.
    apply (IHy1 k eeq iin eq_refl x).
    apply (IHy2 k eeq iin eq_refl x).
  - apply (eeq x y).
  - apply (iin x y).
Defined.

Local Definition iin : forall k,
  (set (S k) -> set k -> Prop) ->
  (set (S k) -> set k -> Prop) ->
  set (S k) -> set (S k) -> Prop.
Proof.
  intros k eeqS iinS y x.
  dependent induction y.
  - exact P.
  - apply P.
    apply (IHy1 k eeqS iinS eq_refl x).
    apply (IHy2 k eeqS iinS eq_refl x).
  - apply (eeqS x y).
  - apply (iinS x y).
Defined.

(* Auxiliary lemmas

Lemma iin_binop: forall i f g P x y1 y2, 
iin i f g (binop (S i) P y1 y2) x = 
P (iin i f g y1 x) (iin i f g y2 x).
Proof. intros. apply eq_refl. Qed.

Lemma iin_sin: forall i f g x y, 
iin i f g (sin _ y) x = f x y.
Proof. intros. apply eq_refl. Qed.

Lemma iin_cos: forall i f g x y, 
iin i f g (cos _ y) x = g x y.
Proof. intros. apply eq_refl. Qed.

Lemma iinS_prop: forall k a b p z, iinS k a b (prop _ p) z = p.
Proof. intros. cbv. auto. Qed.

Lemma iinS_binop: forall i f g P x y1 y2, 
  iinS i f g (binop _ P y1 y2) x =
  P (iinS i f g y1 x) (iinS i f g y2 x).
Proof. intros. apply eq_refl. Qed. *)

(* ----------------------------------------------------------- *)
(* The miracle fixpoint *)


Fixpoint Iin k : set k -> set k -> Prop :=
  match k return set k -> set k -> Prop with 
  | O => in0
  | S m => 
    let IinSm := iinS m (Eeq m) (Iin m) in
    let IimSm := iimS m (Eeq m) in
    let EeqSm := eeqS m IimSm (Iim m) IinSm (Iin m) in
    fun x y => iini x (EeqSm y) (IinSm y)
  end
with Iim k : set k -> (set k -> Prop) -> Prop :=
  match k with 
  | O => fun y _ => eval0 y
  | S m =>
      let IinSm := iinS m (Eeq m) (Iin m) in
      let IimSm := iimS m (Eeq m) in
      let EeqSm := eeqS m IimSm (Iim m) IinSm (Iin m) in
      iim m EeqSm
  end
with Eeq k : set k -> set k -> Prop :=
match k with
  | O => eq0
  | S m =>
      fun x y => forall (f g: set m -> Prop),
        (forall x y, f x -> f y -> Eeq m x y) ->
        (forall x y, Eeq m x y -> g x -> g y) -> 
        (forall x y, Iin m x y -> f x -> g y) -> 
          (@iini m x f g <-> iini y f g)
end
.

Definition IimS k : set (S k) -> (set k -> Prop) -> Prop :=
iimS k (Eeq k).
Definition IinS k : set (S k) -> set k -> Prop :=
iinS k (Eeq k) (Iin k).
Definition EeqS k : set (S k) -> set k -> Prop :=
eeqS k (IimS k) (Iim k) (IinS k) (Iin k).

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

(* Previous definition of Iin/S and Iim/S and EeqS, to simplify as well *)

(* Axiom tmp: set 1 -> set 0 -> Prop.

Fixpoint EeqS k : set (S k) -> set k -> Prop :=
match k with
  | O => tmp
  | S m =>
      fun x y => forall f f' g g',
        respects2 f f' (EeqS m) -> respects2 g g' (EeqS m) -> 
          (@iini _ x f g <-> iini y f' g')
end. *)

(* ----------------------------------------------------------- *)

Lemma Iin_0 : Iin 0 = in0.
Proof. auto. Qed.
Lemma Eeq_0 : Eeq 0 = eq0.
Proof. auto. Qed.
Lemma Iim_0 : forall x y, Iim 0 x y = eval0 x.
Proof. auto. Qed.
Lemma ext_0 : forall x y, Eeq 0 x y <-> forall z, Iin 0 x z <-> Iin 0 y z.
Proof.
  intros. rewrite Eeq_0. rewrite Iin_0. unfold eq0, in0. tauto.
Qed.
Lemma ext_m_0 : forall x y, Eeq 0 x y <-> forall z, Iim 0 x z <-> Iim 0 y z.
Proof.
intros. rewrite Eeq_0. split; auto; intros. pose proof (H (fun _=> True)). rewrite Iim_0 in H0. rewrite Iim_0 in H0. unfold eq0. auto.
Qed.
Lemma ext_comb_0: forall x y, Eeq 0 x y <-> (
  (forall z, Iin 0 x z <-> Iin 0 y z) /\
  (forall Z, Iim 0 x Z <-> Iim 0 y Z)
).
Proof.
  intros. split; intros.
  - split. apply ext_0; auto. apply ext_m_0; auto.
  - destruct H. apply ext_0; auto.
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

Opaque Iin IinS Eeq EeqS Iim IimS.
