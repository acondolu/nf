Require Import Coq.Logic.Classical_Pred_Type.

Add LoadPath "src/".
Require Import Simplest.

Definition 𝒰 : 𝓥 := Neg False (fun x => match x with end).
Definition Ø : 𝓥 := Pos False (fun x => match x with end).

Lemma univ_okay : forall x, x ∈ 𝒰.
Proof. intros x H. destruct H. Qed.

Lemma empty_ok : forall x, x ∈ Ø -> False.
Proof. intros x H. apply H. Qed.

Definition neg : 𝓥 -> 𝓥 :=
  fun x => match x with
  | Pos X f => Neg X f
  | Neg X f => Pos X f
  end
.

Lemma neg_ok : forall x y, x ∈ neg y <-> (x ∈ y -> False).
Proof.
  intros x y. destruct y; simpl neg; simpl iin; split.
  - apply all_not_not_ex.
  - apply not_ex_all_not.
  - intros. revert H. apply all_not_not_ex. assumption. 
  - apply not_all_not_ex.
Qed.

Definition sing : 𝓥 -> 𝓥 :=
  fun x => Pos unit (fun _ => x).

Definition sing_ok : forall x y, x ∈ sing y <-> x ≡ y.
Proof.
  intros. simpl. split; intros. destruct H. apply eeq_sym.
  assumption. exists tt. apply eeq_sym. assumption.
Qed.

Definition pow X (f: X -> set) :=
  Pos (X -> Prop)
    (fun s => Pos { x : X & s x }
      (fun ex => match ex with existT _ x _ => f x end) )
.