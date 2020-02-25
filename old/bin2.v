
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
