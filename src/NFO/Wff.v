Add LoadPath "src/NFO/".
Require Import Model.
Require Import Coq.Init.Wf.

(* Variant of Coq.Init.Wf.Fix_F_inv with iff instead of eq *)
Lemma Fix_F_inv_iff {A} {R: A -> A -> Prop} {Rwf: well_founded R} {F : forall x:A, (forall y:A, R y x -> Prop) -> Prop} : forall (F_ext :
forall (x:A) (f g:forall y:A, R y x -> Prop),
  (forall (y:A) (p:R y x), f y p <-> g y p) -> F x f <-> F x g)
  (x:A) (r s:Acc R x), Fix_F (fun _ => Prop) F r <-> Fix_F (fun _ => Prop) F s.
Proof.
intros. induction (Rwf x); intros.
rewrite <- (Fix_F_eq _ F r); rewrite <- (Fix_F_eq _ F s); intros.
  apply F_ext; auto.
Qed.

(* Variant of Coq.Init.Wf.Fix_eq *)
Lemma Fix_iff {A} {R: A -> A -> Prop} {Rwf: well_founded R} {F : forall x:A, (forall y:A, R y x -> Prop) -> Prop} : forall (F_ext :
forall (x:A) (f g:forall y:A, R y x -> Prop),
  (forall (y:A) (p:R y x), f y p <-> g y p) -> F x f <-> F x g) (x:A), Fix Rwf (fun _ => Prop) F x <-> F x (fun (y:A) (p: R y x) => Fix Rwf (fun _ => Prop) F y).
Proof.
  intros. unfold Fix.
  rewrite <- Fix_F_eq.
  apply F_ext; intros.
  apply (@Fix_F_inv_iff _ _ Rwf _ F_ext).
Qed.

(* 
TODO: use the multiset order extension in https://www21.in.tum.de/~nipkow/misc/multiset.ps
*)

(* 2 *)

Definition le12 : set -> set * set -> Prop := fun a bs =>
  match bs with (b1, b2) => a < b1 \/ a < b2 end.

Definition le22 : set * set -> set * set -> Prop := fun a bs =>
  match a with (a1, a2) => le12 a1 bs \/ le12 a2 bs end.
Infix "<<" := le22 (at level 50) : type_scope.

Axiom wf_two: well_founded le22.

Lemma wf_two_ind: forall P : set -> set -> Prop,
  (forall x1 x2,
    (forall y1 y2, (y1, y2) << (x1, x2) -> P y1 y2) -> P x1 x2)
      -> forall x y, P x y.
Proof.
  intros P H.
  cut (forall z, match z with (z1, z2) => P z1 z2 end).
  - intros. apply (H0 (x, y)).
  - apply (well_founded_ind wf_two).
    destruct x. intros. apply (H s s0). intros.
    apply (H0 (y1, y2)). assumption.
Qed.

Ltac auto2 := unfold le22; unfold le12; tauto.
Lemma AA {a a' b b'}: a < a' -> b < a' -> (a, b) << (a', b').
Proof. auto2. Qed. Hint Resolve AA : Wff.
Lemma AB {a a' b b'}: a < a' -> b < b' -> (a, b) << (a', b').
Proof. auto2. Qed. Hint Resolve AB : Wff.
Lemma BA {a a' b b'}: a < b' -> b < a' -> (a, b) << (a', b').
Proof. auto2. Qed. Hint Resolve BA : Wff.
Lemma BB {a a' b b'}: a < b' -> b < b' -> (a, b) << (a', b').
Proof. auto2. Qed. Hint Resolve BB : Wff.

(* 3 *)

Definition le13 : set -> set * set * set -> Prop := fun a bs =>
  match bs with (b1, b2, b3) => a < b1 \/ a < b2 \/ a < b3 end.

Definition le33 : set * set * set -> set * set * set -> Prop := fun a bs =>
  match a with (a1, a2, a3) => le13 a1 bs \/ le13 a2 bs \/ le13 a3 bs end.
Infix "<<<" := le33 (at level 50) : type_scope.

Axiom wf_three: well_founded le33.

Lemma wf_three_ind:
  forall P : set -> set -> set -> Prop,
  (forall x1 x2 x3,
    (forall y1 y2 y3, (y1, y2, y3) <<< (x1, x2, x3) -> P y1 y2 y3) -> P x1 x2 x3)
    -> forall x y z : set, P x y z.
Proof.
  intros P H.
  cut (forall a, match a with (a1, a2, a3) => P a1 a2 a3 end).
  - intros. apply (H0 (x, y, z)).
  - apply (well_founded_ind wf_three).
    intros. destruct x, p. apply (H s0 s1 s). intros.
    apply (H0 (y1, y2, y3)). assumption.
Qed.

Ltac auto3 := unfold le33; unfold le13; tauto.
Hint Extern 1 (_ <<< _) => unfold le33; unfold le13; tauto : Wff.

Lemma AAA {a a' b b' c c'}: a < a' -> b < a' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma AAB {a a' b b' c c'}: a < a' -> b < a' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma AAC {a a' b b' c c'}: a < a' -> b < a' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ABA {a a' b b' c c'}: a < a' -> b < b' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ABB {a a' b b' c c'}: a < a' -> b < b' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ABC {a a' b b' c c'}: a < a' -> b < b' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ACA {a a' b b' c c'}: a < a' -> b < c' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ACB {a a' b b' c c'}: a < a' -> b < c' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ACC {a a' b b' c c'}: a < a' -> b < c' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.

Lemma BAA {a a' b b' c c'}: a < b' -> b < a' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BAB {a a' b b' c c'}: a < b' -> b < a' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BAC {a a' b b' c c'}: a < b' -> b < a' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BBA {a a' b b' c c'}: a < b' -> b < b' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BBB {a a' b b' c c'}: a < b' -> b < b' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BBC {a a' b b' c c'}: a < b' -> b < b' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BCA {a a' b b' c c'}: a < b' -> b < c' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BCB {a a' b b' c c'}: a < b' -> b < c' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BCC {a a' b b' c c'}: a < b' -> b < c' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.

Lemma CAA {a a' b b' c c'}: a < c' -> b < a' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CAB {a a' b b' c c'}: a < c' -> b < a' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CAC {a a' b b' c c'}: a < c' -> b < a' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CBA {a a' b b' c c'}: a < c' -> b < b' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CBB {a a' b b' c c'}: a < c' -> b < b' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CBC {a a' b b' c c'}: a < c' -> b < b' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CCA {a a' b b' c c'}: a < c' -> b < c' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CCB {a a' b b' c c'}: a < c' -> b < c' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CCC {a a' b b' c c'}: a < c' -> b < c' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.

Hint Resolve AAA AAB AAC ABA ABB ABC ACA ACB ACC BAA BAB BAC BBA BBB BBC BCA BCB BCC CAA CAB CAC CBA CBB CBC CCA CCB CCC : Wff.