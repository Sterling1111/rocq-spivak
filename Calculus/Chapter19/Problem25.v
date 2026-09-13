From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_25 : ∀ r,
  r > 0 ->
  2 * ∫ (-r) r (λ x, √(r^2 - x^2)) = π * r^2.
Proof.
  intros r H1.
  assert (H2 : ∫ (-r) r (λ x, √(r^2 - x^2)) = π / 2 * r^2).
  {
    pose proof (substitution_formula
      (λ x, √(r^2 - x^2)) (λ x, r*x) (λ _, r)
      (λ x, ∫ 0 x (λ t, √(r^2 - t^2))) (-1) 1
      ltac:(auto_cont) ltac:(auto_cont)
      ltac:(apply FTC1_global; auto_cont) ltac:(auto_diff)) as H3.
    cbn beta in H3.
    replace (r * -1) with (-r) in H3 by ring.
    rewrite Rmult_1_r in H3. rewrite H3.
    transitivity (∫ (-1) 1 (λ x, r^2 * √(1-x^2))).
    - apply integral_ext; [lra |]. intros x Hx.
      unfold compose; cbn beta.
      replace (r^2 - (r*x)^2) with (r^2 * (1-x^2)) by ring.
      rewrite sqrt_mult, sqrt_pow2; solve_R.
    - rewrite integral_mult_scalar; [unfold π; field | lra | auto_int].
  }
  lra.
Qed.
