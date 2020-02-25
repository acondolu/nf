Require Import Coq.Program.Tactics.
Require Coq.Program.Wf.
Require Import Coq.Program.Equality.

Add LoadPath "src/".
Require Untitled2.

Module Type QuotSig.
Parameter 𝓥 : Type.
Parameter Universe: 𝓥.
Parameter Empty: 𝓥.
Parameter Intersection: 𝓥 -> 𝓥 -> 𝓥.
Parameter Union: 𝓥 -> 𝓥 -> 𝓥.
Parameter Arrow: 𝓥 -> 𝓥 -> 𝓥.
Parameter Singleton: 𝓥 -> 𝓥.
Parameter CoSingleton: 𝓥 -> 𝓥.
Parameter IN: 𝓥 -> 𝓥 -> Prop.
Parameter EQ: 𝓥 -> 𝓥 -> Prop.

Parameter Universe_ok: forall x: 𝓥, IN Universe x.
End QuotSig.

Module Quot <: QuotSig.

Private Inductive set : Type :=
  (* reflect lattice structure *)
  | prop : Prop -> set
  | binop : 
      (Prop -> Prop -> Prop) -> (set -> set -> set)
  (* sets *)
  | sin : set -> set
  | cos : set -> set
.

Definition 𝓥 := set.
Definition Universe := prop True.
Definition Empty := prop False.
Definition Intersection := binop and.
Definition Union := binop or.
Definition Arrow := binop (fun x y => x -> y).
Definition Singleton := sin.
Definition CoSingleton := cos.

Fixpoint undecorate {i} (x:Untitled2.set i): set :=
match x with
  | Untitled2.prop _ c => prop c
  | Untitled2.binop _ P y z => binop P (undecorate y) (undecorate z)
  | Untitled2.sin _ y => sin (undecorate y)
  | Untitled2.cos _ y => cos (undecorate y)
end.

Inductive In : set -> set -> Prop :=
  | Cc : forall i x y, @Untitled2.Iin1 i x y -> In (undecorate x) (undecorate y)
.
Definition IN := In.
(* Notation "A € B" := (In B A) (at level 85). *)
(* Lemma IN_' : forall x y, IN_ x y <-> exists i x y,  *)

Axiom Eq : set -> set -> Prop.
Definition EQ := Eq.

Axiom ex: forall x, exists i y, @undecorate i y = x.

Lemma mk_prop: forall p x, In (prop p) x <-> p.
Proof.
  intros p x. split; intro H.
  - dependent destruction H.
  dependent destruction x0; simpl undecorate in x.
   -- injection x. intro. destruct i.
   --- cbv in H. rewrite<- H0. exact H.
   --- cbv in H. rewrite<- H0. exact H. 
 -- discriminate x.
 -- discriminate x.
 -- discriminate x.
 - destruct (ex x). destruct H0.
   rewrite<- H0.
   cut (undecorate (Untitled2.prop x0 p) = prop p).
   intros. rewrite<- H1. apply Cc.
   destruct x0. cbv. auto. cbv. auto.
   simpl undecorate. auto.
Qed.

Lemma Universe_ok: forall x: 𝓥, In Universe x.
Proof.
  intros. pose proof (mk_prop True).
  pose proof (H x). apply H0. auto.
Qed.

Lemma mk_binop:
  forall (P : Prop -> Prop -> Prop) x y z,
  P (In x z) (In y z) -> In (binop P x y) z. 
Admitted.

End Quot.