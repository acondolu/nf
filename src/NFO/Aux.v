Definition invF {X Y} (f: X -> Y) (x: Y) := exists y, f y = x.

Definition inv2 {X Y W} (f: X -> W) (g : Y -> W) x :=
  invF f x \/ invF g x.

Definition inv3 {X Y Z W} (f: X -> W) (g : Y -> W) (h : Z -> W) x :=
  invF f x \/ invF g x \/ invF h x.

Lemma inv2_1 {X Y W} (f: X -> W) (g : Y -> W) x:
  inv2 f g (f x).
Proof. unfold inv2. unfold invF. left. exists x. auto. Qed.
Lemma inv2_2 {X Y W} (f: X -> W) (g : Y -> W) x:
  inv2 f g (g x).
Proof. unfold inv2. unfold invF. right. exists x. auto. Qed.
Hint Resolve inv2_1. Hint Resolve inv2_2.

Lemma inv3_1 {X Y Z W} (f: X -> W) (g : Y -> W) (h : Z -> W) x:
  inv3 f g h (f x).
Proof. unfold inv3. unfold invF. left. exists x. auto. Qed.
Lemma inv3_2 {X Y Z W} (f: X -> W) (g : Y -> W) (h : Z -> W) x:
  inv3 f g h (g x).
Proof. unfold inv3. unfold invF. right. left. exists x. auto. Qed.
Lemma inv3_3 {X Y Z W} (f: X -> W) (g : Y -> W) (h : Z -> W) x:
  inv3 f g h (h x).
Proof. unfold inv3. unfold invF. right. right. exists x. auto. Qed.
Hint Resolve inv3_1. Hint Resolve inv3_2. Hint Resolve inv3_3.