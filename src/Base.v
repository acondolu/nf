Require Import Coq.Program.Tactics.
Require Coq.Program.Wf.
Require Import Coq.Program.Equality.

Inductive set : Type :=
  | prop : Prop -> set
  | binop: (Prop -> Prop -> Prop) -> (set -> set -> set)
  | sin : set -> set
  | cos : set -> set
.
(* better: {X} ((X -> Prop) -> Prop) -> ((X -> Set) -> Set) *)

(* binop f (prop x) (prop y) = prop (f x y) *)

(* ----------------------------------------------------------- *)

Fixpoint smatch f g x := match x with
  | prop p => p
  | binop P x1 x2 => P (smatch f g x1) (smatch f g x2)
  | sin y => f y
  | cos y => g y
end.

Check smatch.

Fixpoint level x := match x with 
  | prop _ => 0
  | binop _ x1 x2 => level x1 + level x2
  | sin y => S (level y)
  | cos y => S (level y)
end.

Definition Rlevel (x y: set): Prop := level x < level y.

Axiom aux: forall n m o, n < m -> n < m + o.
Axiom aux2: forall n m o, n < o -> n < m + o.

Definition smatch' x (f g: forall y, Rlevel y x -> Prop): Prop.
Proof.
  dependent induction x; unfold Rlevel in f, g; simpl level in *.
  - exact P.
  - apply P.
    -- apply IHx1. intros. apply (f y). apply aux. auto.
      intros. apply (g y). apply aux. auto.
    -- apply IHx2. intros. apply (f y). apply aux2. auto.
      intros. apply (g y). apply aux2. auto.
  - apply (f x). auto.
  - apply (g x). cbv. auto.
Qed.

Check smatch'.

Lemma Rlevel_wf: well_founded Rlevel.
Admitted.
  (* intro x. apply Acc_intro. induction x.  intros y;
  unfold Rlevel; simpl level.
  - intro K. cbv in K. admit.
  - 
  
  apply Acc_intro. intro y. induction y.
  intros.
  admit.
Admitted. *)

Definition R2 (a b: set * set): Prop :=
  level (fst a) + level (snd a) < level (fst b) + level (snd b).

Lemma Rwf: well_founded R2.
Admitted.

Require Import Coq.Init.Wf.

Axiom comb2: forall {a b c d}, Rlevel a c -> Rlevel b d -> R2 (a, b) (c, d).

Definition myf z z' (rec: forall a a', R2 (a, a') (z, z') -> Prop): Prop :=
forall (f g: forall w : set, Rlevel w z -> Prop)
  (f' g': forall w : set, Rlevel w z' -> Prop),
(forall x y kx ky, f x kx -> f y ky -> rec x y (comb2 kx ky)) ->
(forall x y (k: R2 (x, y) (z, z')), rec x y k -> g x -> g y) -> 

  (* let Iin := fix Iin : set * set -> Prop :=
    let IinSm x y := smatch (fun z => rec y z) (Iin m y) x in
    fun (x, y) => smatch (fun z => EeqSS _ y (Lift z)) (IinSm y) x
  in *)
  (* (forall x y, Iin x y -> f x -> g y) ->  *)

  (smatch f g z <-> smatch f g z')
.
Check well_founded_induction_type_2.
Check Rwf.
Definition Eeq := @well_founded_induction_type_2 _ _ R2 _ Rwf myf.
Check Eeq.

Fixpoint EeqSS k (a b: set (S k)) {struct k}: Prop :=
(match k with
  | O =>
    fun x y => forall (f g: set O -> Prop),
    (forall x y, f x -> f y -> Eeq0 x y) ->
    (forall x y, Eeq0 x y -> g x -> g y) -> 
    (forall x y, Iin0 x y -> f x -> g y) -> 
      (smatch f g x <-> smatch f g y)
  | S m =>
    let Iin := fix Iin k : set k -> set k -> Prop :=
    match k return set k -> set k -> Prop with 
  match k return set k -> set k -> Prop with 
    match k return set k -> set k -> Prop with 
    | O => Iin0
    | S m => 
  | S m => 
    | S m => 
      let IinSm x (y: set m) := smatch (fun z => EeqSS m y z) (Iin m y) x in
      fun x y => smatch (fun z => EeqSS _ y (Lift z)) (IinSm y) x
    end in
      fun x y => forall (f g: set m -> Prop),
        (forall x y, f x -> f y -> EeqSS m x y) ->
        (forall x y, EeqSS m x y -> g x -> g y) -> 
        (forall x y, Iin m x y -> f x -> g y) -> 
          (smatch f g x <-> smatch f g y)
end) a b.