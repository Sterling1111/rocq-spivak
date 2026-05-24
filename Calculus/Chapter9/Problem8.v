From Calculus.Chapter9 Require Import Prelude.
From Calculus.Chapter5 Require Import Problem14.

Lemma lemma_9_8_a : forall f f' g g' c,
  g = (fun x => f (x + c)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> forall x, g' x = f' (x + c).
Proof.
  intros f f' g g' c H1 H2 H3 x. subst g.
  pose proof (H2 (x + c)) as H4. unfold derivative_at in H4.
  pose proof (H3 x) as H5. unfold derivative_at in H5.
  apply limit_unique with (f := fun h => (f (x + c + h) - f (x + c)) / h) (a := 0).
  - apply limit_eq' with (f1 := fun h => (f (x + h + c) - f (x + c)) / h).
    + intros h. replace (x + h + c) with (x + c + h) by lra. reflexivity.
    + apply H5.
  - apply H4.
Qed.

Lemma lemma_9_8_b : forall f f' g g' c,
  g = (fun x => f (c * x)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> forall x, g' x = c * f' (c * x).
Proof.
  intros f f' g g' c H1 H2 H3 x. subst.
  destruct (Req_dec c 0) as [H4 | H4].
  - subst. simp_zero.
    apply derivative_at_unique with (f := λ y, f (0 * y)) (f1' := g') (f2' := λ _, 0) (x := x); auto.
    unfold derivative_at.
    apply limit_eq with (f1 := λ h, 0); [ | apply limit_const ].
    exists 1; split; [lra | intros h H4; simp_zero; lra ]. 
  - apply derivative_at_unique with (f := λ y, f (c * y)) (f1' := g') (f2' := λ y, c * f' (c * y)) (x := x); auto.
    unfold derivative_at.
    apply limit_eq with (f1 := λ h, (f (c * x + c * h) - f (c * x)) / h).
    + exists 1; split; [lra |].
      intros h H5. 
      replace (c * (x + h)) with (c * x + c * h); lra.
    + apply lemma_5_14_a with (f := λ k, f (c * x + k) - f (c * x)) (l := f' (c * x)) (b := c); auto.
      exact (H2 (c * x)).
Qed.

Lemma lemma_9_8_c : forall f f' a,
  (forall x, f (x + a) = f x) -> differentiable f -> ⟦ der ⟧ f = f' -> (forall x, f' (x + a) = f' x).
Proof.
  intros f f' a H1 H2 H3 x.
  pose proof (H3 (x + a)) as H5. unfold derivative_at in H5.
  pose proof (H3 x) as H6. unfold derivative_at in H6.
  apply limit_unique with (f := fun h => (f (x + a + h) - f (x + a)) / h) (a := 0).
  - apply H5.
  - apply limit_eq' with (f1 := fun h => (f (x + h) - f x) / h).
    + intros h. replace (x + a + h) with (x + h + a) by lra. rewrite H1, H1. reflexivity.
    + apply H6.
Qed.