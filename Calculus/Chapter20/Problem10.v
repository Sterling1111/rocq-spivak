From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_10 : ∀ x,
  P(3, 0, λ x, x^3 - cos x) x = -1 + x^2 / 2 + x^3.
Proof.
  compute_tp.
Qed.

Lemma lemma_20_10_a : ∀ x,
  P(5,0,λ y, exp y + sin y) x = 1 + 2*x + x^2/2 + x^4/24 + x^5/60.
Proof.
  compute_tp.
Qed.

Lemma lemma_20_10_b : ∀ x,
  P(5,0,λ y, exp y * sin y) x = x + x^2 + x^3/3 - x^5/30.
Proof.
  compute_tp.
Qed.

Lemma lemma_20_10_c : ∀ x, P(5,0,tan) x = x + x^3/3 + 2*x^5/15.
Proof.
Abort.

Lemma lemma_20_10_d : ∀ x,
  P(4,0,λ y, exp (2*y) * cos y) x = 1 + 2*x + 3*x^2/2 + x^3/3 - 7*x^4/24.
Proof.
  compute_tp.
Qed.

Lemma lemma_20_10_e : ∀ x,
  P(5,0,λ y, sin y / cos (2*y)) x = x + 11*x^3/6 + 361*x^5/120.
Proof.
Abort.

Lemma lemma_20_10_f : ∀ x,
  P(6,0,λ y, y^3 / ((1+y^2)*exp y)) x = x^3 - x^4 - x^5/2 + 5*x^6/6.
Proof.
Abort.
