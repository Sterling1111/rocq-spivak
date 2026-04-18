From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_4_i : forall c,
  ∫ (λ x, 1 / √(1 - x^2)) (-1, 1) = (λ x, arcsin x + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_4_ii : forall c,
  ∫ (λ x, √(1 - x^2)) (-1, 1) = (λ x, x * √(1 - x^2) / 2 + arcsin x / 2 + c).
Proof.
  auto_int.
  assert (H1 : √(1 - x * (x * 1)) <> 0).
  { pose proof sqrt_lt_R0 (1 - x * (x * 1)); solve_R. }
  apply Rmult_eq_reg_r with (r := √(1 - x * (x * 1))); 
  try field_simplify; try rewrite pow2_sqrt; solve_R.
Qed.

Lemma lemma_19_4_iii : forall c,
  ∫ (λ x, 1 / √(1 + x^2)) = (λ x, log (x + √(1 + x^2)) + c).
Proof.
  auto_int.
Abort.

Lemma lemma_19_4_iv : forall c,
  ∫ (λ x, √(1 + x^2)) = (λ x, x * √(1 + x^2) / 2 + log (x + √(1 + x^2)) / 2 + c).
Proof.
  auto_int.
Abort.
