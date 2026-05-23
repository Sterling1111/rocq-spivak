From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_30_i : ∀ n,
  ⟦ der ⟧ (λ x, x^n) = (λ x, n * x^(n - 1)).
Proof.
  auto_diff.
Qed.

Lemma lemma_9_30_ii : forall x,
  x <> 0 ->
  ⟦ der x ⟧ (λ y, 1 / y) = (λ y, -1 / y^2).
Proof.
  auto_diff.
Qed.

Lemma lemma_9_30_iii : ∀ f f' c,
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ (λ x, f x + c) = f'.
Proof.
  intros f f' c H1.
  replace f' with (λ x, f' x + 0) by (extensionality x; lra).
  apply derivative_plus; auto.
  apply derivative_const.
Qed.

Lemma lemma_9_30_iv : ∀ f f' c,
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ (λ x, c * f x) = (λ x, c * f' x).
Proof.
  auto_diff.
Qed.

Lemma lemma_9_30_v : ∀ f f' c,
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ (λ y, f y + c) = f'.
Proof.
  apply lemma_9_30_iii.
Qed.

Lemma lemma_9_30_vi : ∀ a,
  ⟦ Der (a^2) ⟧ (λ x, x^3) = 3 * a^4.
Proof.
  intros a.
  compute_Der.
  lra.
Qed.

Lemma lemma_9_30_vii : ∀ f f' a b,
  ⟦ der ⟧ f = f' ->
  ⟦ Der b ⟧ (λ x, f (x + a)) = f' (b + a).
Proof.
  intros f f' a b H1. compute_Der. lra.
Qed.

Lemma lemma_9_30_viii : ∀ f f' c b,
  ⟦ der ⟧ f = f' ->
  ⟦ Der b ⟧ (λ x, f (c * x)) = c * f' (c * b).
Proof.
  intros f f' c b H1. compute_Der. lra.
Qed.

Lemma lemma_9_30_ix : ∀ f f' c,
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ (λ x, f (c * x)) = (λ x, c * f' (c * x)).
Proof.
  auto_diff.
Qed.

Lemma lemma_9_30_x : ∀ n k,
  (k <= n)%nat ->
  ⟦ der ^ k ⟧ (λ x, x^n) = (λ x, (fact n / fact (n - k)) * x^(n - k)).
Proof.
  apply nth_derivative_pow.
Qed.