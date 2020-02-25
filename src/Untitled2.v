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

Definition iimS : forall k,
(set k -> set k -> Prop) ->
set (S k) -> (set k -> Prop) -> Prop.
Proof.
  intros k eq y x. dependent induction y.
  - exact P.
  - apply P. apply (IHy1 k); auto. apply (IHy2 k); auto.
  - exact False.
  - exact (exists z, eq z y /\ x z).
Defined.
Definition iim : forall k, 
  (set (S k) -> set k -> Prop) ->
    set (S k) -> (set (S k) -> Prop) -> Prop.
Proof.
  intros k eq y X. dependent induction y.
  - exact P.
  - apply P. apply (IHy1 k eq); auto. apply (IHy2 k eq); auto.
  - exact False.
  - exact (exists z, eq z y /\ X z).
Defined.

Definition eeqS : forall k,
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

Definition eeq : forall k,
  (set (S k) -> (set k -> Prop) -> Prop) ->
  (set (S k) -> set k -> Prop) ->
  set (S k) -> set (S k) -> Prop.
Proof.
  intros k iimS iinS x y.
  exact (
    (forall z, iinS x z <-> iinS y z)
    /\ (forall Z, iimS x Z <-> iimS y Z)
    ).
Defined.

Definition iinS : forall k,
  (set k -> set k -> Prop) ->
  (set k -> set k -> Prop) ->
  set (S k) -> set k -> Prop.
Proof.
  intros k eeq iin y x.
  dependent induction y.
  - exact P.
  - apply P. apply (IHy1 k); auto. apply (IHy2 k); auto.
  - apply eeq. exact x. exact y.
  - apply iin. exact x. exact y.
Defined.

Definition iin : forall k,
  (set (S k) -> set k -> Prop) ->
  (set (S k) -> set k -> Prop) ->
  set (S k) -> set (S k) -> Prop.
Proof.
  intros k eeqS iinS y x.
  dependent induction y.
  - exact P.
  - apply P. apply (IHy1 k); auto. apply (IHy2 k); auto.
  - apply eeqS. exact x. exact y.
  - apply iinS. exact x. exact y.
Defined.

(* Auxiliary lemmas *)

Lemma iinS_prop: forall k a b p z, iinS k a b (prop _ p) z = p.
Proof. intros. cbv. auto. Qed.

(* ----------------------------------------------------------- *)
(* The miracle fixpoint *)

Fixpoint Iin k : set k -> set k -> Prop :=
  match k return set k -> set k -> Prop with 
  | O => in0
  | S m =>
    let IinSm := iinS m (Eeq m) (Iin m) in
    let IimSm := iimS m (Eeq m) in
    let EeqSm := eeqS m IimSm (Iim m) IinSm (Iin m) in
    iin m EeqSm IinSm
  end
with Eeq k : set k -> set k -> Prop :=
  match k with
  | O => eq0
  | S m =>
    let IinSm := iinS m (Eeq m) (Iin m) in
    let IimSm := iimS m (Eeq m) in
    eeq m IimSm IinSm
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
.

Definition IimS k : set (S k) -> (set k -> Prop) -> Prop :=
iimS k (Eeq k).
Definition IinS k : set (S k) -> set k -> Prop :=
iinS k (Eeq k) (Iin k).
Definition EeqS k : set (S k) -> set k -> Prop :=
eeqS k (IimS k) (Iim k) (IinS k) (Iin k).

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

(* Lemma Iin1_S : forall k y x, Iin1 k y x = (match y with
  | prop _ p => fun _ => p
  | binop _ P y1 y2 => fun x => P (Iin1 _ y1 x) (Iin1 _ y2 x)
  | sin _ z => fun x => Eeq2 _ x z
  | cos _ z => fun x => Iin2 _ x z
end) x.
Proof.
  destruct k.
  - simpl. dependent induction y; cbv; auto.
  - induction y.
    -- cbv. auto.
    -- simpl. fold (Iin2 k). fold(Iim2 k). fold (Eeq2 k). fold (Iin1 k). simpl Iin1 in IHy2.
      pose proof (IHy1 k y1).
    admit.
    -- auto.
    -- auto.
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
Admitted. *)


(* ----------------------------------------------------------- *)
(* Lift *)


Fixpoint lift {k} (y: set k) : set (S k) :=
  match y with
  | prop _ c => prop _ c
  | binop _ P y' y'' => binop _ P (lift y') (lift y'')
  | sin _ y' => sin _ (lift y')
  | cos _ y' => cos _ (lift y')
end.

Check iin.

Lemma iin_binop: forall i f g P x y1 y2, 
iin i f g (binop (S i) P y1 y2) x = 
P (iin i f g y1 x) (iin i f g y2 x).
Admitted.
  (* intro i. destruct i.
  - intros. unfold iin at 1. simpl. unfold solution_left.
  unfold eq_rect_r. unfold eq_rect. simpl.
  apply f_equal2.
  Search (_ = _ -> _ _ = _ _).
  
  apply eq_refl. *)

Axiom iinS_binop: forall i f g P x y1 y2, 
  iinS i f g (binop _ P y1 y2) x =
  P (iinS i f g y1 x) (iinS i f g y2 x).

Lemma Iin_binop: forall i P x y1 y2, 
Iin i (binop i P y1 y2) x = 
P (Iin i y1 x) (Iin i y2 x).
Proof.
 intros. destruct i. auto. simpl Iin.
 rewrite iin_binop. auto.
Qed.

Lemma IinS_binop: forall i P x y1 y2, 
IinS i (binop _ P y1 y2) x = 
P (IinS _ y1 x) (IinS _ y2 x).
Proof.
 intros. destruct i. auto. unfold IinS.
 rewrite iinS_binop. auto.
 unfold IinS. rewrite iinS_binop. auto.
Qed.

Theorem ambiguityIinR:
  forall i x y, Iin _ x (lift y) = IinS i x y.
Proof.
  intros.
  dependent induction x.
  - simpl. apply eq_refl.
  - rewrite Iin_binop. rewrite IinS_binop.
    apply f_equal2.
    -- apply IHx1. auto. admit.
    -- apply IHx2. auto. admit.
  - admit.
  - admit.
Admitted.

Theorem ambiguityEeqR:
  forall i x y, Eeq _ x (lift y) = EeqS i x y.
Proof.
  intros.
  induction i.
  - dependent induction y.
    -- apply eq_refl.
    -- pose proof (IHy1 y1 eq_refl). simpl. unfold EeqS.
        unfold eeq. unfold eeqS.
        
       simpl lift. simpl Eeq.
       simpl in H.
Admitted.

Theorem ambiguityEeqL:
  forall i x y, Eeq _ x y <-> EeqS i (lift x) y.
Proof.
  intros.
  induction i.
  - simpl. unfold EeqS. simpl. unfold eeqS. unfold IimS. unfold Eeq. dependent induction x.
    -- cbv. tauto.
    -- cbv.
Admitted.