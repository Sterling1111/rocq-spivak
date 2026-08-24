From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_16_a : forall x b F' G',
  let F := λ x, ∫ 1 x (λ t, 1 / t) in
  let G := λ x, ∫ b (b * x) (λ t, 1 / t) in
  ⟦ der ⟧ F = F' ->
  ⟦ der ⟧ G = G' ->
  x > 0 ->
  b > 0 ->
  F' x = 1 / x /\ G' x = 1 / x.
Proof.
  intros x b F' G' F B H1 H2 H3 H4.
  split.
  - apply (derivative_at_unique F F' (λ y : ℝ, 1 / y) x).
    + auto.
    + unfold F. apply FTC1_at with (c := Rmin 1 x / 2) (d := Rmax 1 x + 1); auto_cont.
  - admit. 
Abort.

Lemma lemma_14_16_b : forall a b,
  a > 0 -> b > 0 ->
  ∫ 1 a (fun t => 1 / t) + ∫ 1 b (fun t => 1 / t) = ∫ 1 (a * b) (fun t => 1 / t).
Proof.
Abort.
