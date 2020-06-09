Add LoadPath "src/NFO/".
Require Import Bool.

Inductive set :=
  | C : forall A (p : prop A) (h: A -> set) X (f: X -> set), set
.

Definition emptyset := C False (Bot _) (fun x => match x with end) False (fun x => match x with end).

Definition compl x := match x with
  | C A p h X f => C A (Not _ p) h X f
  end.

Require Import Coq.Program.Tactics .
Require Import Coq.Program.Wf.
Require Import Coq.Program.Equality.


(* Require Wff. *)
Inductive le_set : set -> set -> Prop :=
  | Ff : forall A p h X f i, le_set (f i) (C A p h X f)
  | Hh : forall A p h X f i, le_set (h i) (C A p h X f)
.
Lemma wf_le_set : well_founded le_set.
Proof.
  unfold well_founded.
  induction a.
  apply Acc_intro. intros.
  dependent destruction H1.
  apply H0. apply H.
Qed.

Inductive le_two : (set * set) -> (set * set) -> Prop :=
  | Aa : forall a1 a2 b1 b2, le_set a1 b1 -> le_set a2 b2 -> le_two (a1, a2) (b1, b2)
  | Bb : forall a1 a2 b1 b2, le_set a1 b2 -> le_set a2 b1 -> le_two (a1, a2) (b1, b2)
  | Bb' : forall a1 a2 b1 b2, le_set a1 b1 -> le_set a2 b1 -> le_two (a1, a2) (b1, b2)
  | Bb'' : forall a1 a2 b1 b2, le_set a1 b2 -> le_set a2 b2 -> le_two (a1, a2) (b1, b2)
.

Axiom wf_two: well_founded le_two.

Program Fixpoint eeq' x { wf le_two x } := match x with
  | (C A p h X f, C A' p' h' X' f') =>
          (forall x, exists y, eeq' (f x, f' y))
          /\ (forall y, exists x, eeq' (f x, f' y))
          /\ let w (i j: A + A') := match i, j with
            | inl i', inl j' => eeq' (h i', h j')
            | inl i', inr j' => eeq' (h i', h' j')
            | inr i', inl j' => eeq' (h' i', h j')
            | inr i', inr j' => eeq' (h' i', h' j')
            end in 
            eeq_prop (prop_map inl p) (prop_map inr p') w
end.
Next Obligation. apply Aa; apply Ff. Qed.
Next Obligation. apply Aa; apply Ff. Qed.
Next Obligation. apply Bb'; apply Hh. Qed.
Next Obligation. apply Aa; apply Hh. Qed.
Next Obligation. apply Bb; apply Hh. Qed.
Next Obligation. apply Bb''; apply Hh. Qed.
Next Obligation. apply wf_two. Qed.

Definition eeq x y := eeq' (x, y).

Axiom eeq_def : forall x y, eeq x y = match x, y with
| C A p h X f, C A' p' h' X' f' =>
        (forall x, exists y, eeq (f x) (f' y))
        /\ (forall y, exists x, eeq (f x) (f' y))
        /\  
          eeq_prop (prop_map inl p) (prop_map inr p') (sum_i eeq h h')
end.

Lemma eeq_refl : forall x, eeq x x.
Proof.
  induction x.
  rewrite eeq_def. split.
  intro. exists x. apply H0.
  split. intro x. exists x. apply H0.
  apply (eeq_prop_refl p eeq h H).
Qed.

Lemma wf_two_ind: forall P : set -> set -> Prop,
(forall x1 x2 : set,
 (forall y1 y2 : set, le_two (y1, y2) (x1, x2) -> P y1 y2) -> P x1 x2) ->
forall x y : set, P x y.
Proof.
  intros P H.
  cut (forall z, P (fst z) (snd z)).
  intros. apply (H0 (x, y)).
  apply (well_founded_ind wf_two).
  intros. destruct x. apply (H s s0). intros.
  apply (H0 (y1, y2)). assumption.
Qed.

Lemma eeq_sym : forall x y, eeq x y -> eeq y x.
Proof.
  apply (wf_two_ind (fun x y => eeq x y -> eeq y x)). intros.
  destruct x1. destruct x2.
  rewrite eeq_def in *. destruct H0. destruct H1. 
  split.
  - intro x. destruct (H1 x). exists x0. apply H. apply Aa ; apply Ff. assumption.
  - split. intro x0. destruct (H0 x0). exists x. apply H. apply Aa ; apply Ff. assumption.
  revert H2. apply eeq_prop_sym.
Qed.

Lemma eeq_trans : forall x y z, eeq x y -> eeq y z -> eeq x z.
Proof.
  apply (wf_two_ind (fun x y => forall z, eeq x y -> eeq y z -> eeq x z)). intros.
  destruct x1. destruct x2.
  rewrite eeq_def in *. destruct H0.
Admitted.
