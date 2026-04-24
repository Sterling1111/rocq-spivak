From Calculus.Chapter15 Require Import Prelude.
From Calculus.Chapter15 Require Import Problem11.

Lemma lemma_15_12_a : forall (m n : nat),
  m <> n ->
  ∫ (-π) π (λ x, sin (m * x) * sin (n * x)) = 0.
Proof.
  intros m n H1.
  replace (λ x, sin (m * x) * sin (n * x)) with (λ x, (cos ((m - n) * x) - cos ((m + n) * x)) / 2).
  2 : { extensionality x. rewrite lemma_15_11_a. lra. }
  assert (H2 : - π < π). { solve_denoms. }
  set (g := λ x, (sin ((m - n) * x) / (m - n) - sin ((m + n) * x) / (m + n)) / 2).
  assert (H3 : continuous_on (λ x, (cos ((m - n) * x) - cos ((m + n) * x)) / 2) [- π, π]) by auto_cont.
  assert (H4 : ⟦ der ⟧ g [- π, π] = (λ x, (cos ((m - n) * x) - cos ((m + n) * x)) / 2)).
  { unfold g; auto_diff; solve_R. apply differentiable_domain_closed; admit. }
  rewrite FTC2 with (g := g).
  unfold g.
  assert (H5 : sin ((m - n) * π) = 0) by admit.
  assert (H6 : sin ((m + n) * π) = 0) by admit.
  assert (H7 : sin ((m - n) * - π) = 0) by admit.
  assert (H8 : sin ((m + n) * - π) = 0) by admit.
rewrite H5, H6, H7, H8.
lra.

  auto_int.


  
  
Abort.

Lemma lemma_15_12_a' : forall (n : nat),
  (n > 0)%nat ->
  ∫ (-π) π (λ x, sin (n * x) * sin (n * x)) = π.
Abort.

Lemma lemma_15_12_b : forall (m n : nat),
  m <> n ->
  ∫ (-π) π (λ x, cos (m * x) * cos (n * x)) = 0.
Abort.

Lemma lemma_15_12_b' : forall (n : nat),
  (n > 0)%nat ->
  ∫ (-π) π (λ x, cos (n * x) * cos (n * x)) = π.
Abort.

Lemma lemma_15_12_c : forall (m n : nat),
  ∫ (-π) π (λ x, sin (m * x) * cos (n * x)) = 0.
Abort.
