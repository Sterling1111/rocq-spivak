From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_2_i :
  ⟦ lim 0 ⟧ (fun x => (sin x - x + x^3 / 6) / x^3) = 0.
Proof.
  step_lhopital (λ x, cos x - 1 + x^2 / 2) (λ x, 3 * x^2).
  step_lhopital (λ x, - sin x + x) (λ x, 6 * x).
  step_lhopital (λ x : R, - cos x + 1) (λ x : R, 6).
Qed.

Lemma lemma_15_2_ii :
  ⟦ lim 0 ⟧ (fun x => (sin x - x + x^3 / 6) / x^4) = 0.
Proof.
  step_lhopital (λ x, cos x - 1 + x^2 / 2) (λ x, 4 * x^3).
  admit.
  step_lhopital (λ x, - sin x + x) (λ x, 12 * x^2).
  step_lhopital (λ x, - cos x + 1) (λ x, 24 * x).
  step_lhopital (λ x, sin x) (λ x : R, 24).
Abort.

Lemma lemma_15_2_iii :
  ⟦ lim 0 ⟧ (fun x => (cos x - 1 + x^2 / 2) / x^2) = 0.
Proof.
  step_lhopital (λ x, - sin x + x) (λ x, 2 * x).
  step_lhopital (λ x, - cos x + 1) (λ x : R, 2).
Qed.

Lemma lemma_15_2_iv :
  ⟦ lim 0 ⟧ (fun x => (cos x - 1 + x^2 / 2) / x^4) = 1/24.
Proof.
  step_lhopital (λ x, - sin x + x) (λ x, 4 * x^3).
  admit.
  step_lhopital (λ x, - cos x + 1) (λ x, 12 * x^2).
  step_lhopital (λ x, sin x) (λ x, 24 * x).
  step_lhopital (λ x, cos x) (λ x : R, 24).
Abort.

Lemma lemma_15_2_v :
  ⟦ lim 0 ⟧ (fun x => (arctan x - x + x^3 / 3) / x^3) = 0.
Proof.
  step_lhopital (λ x, 1 / (1 + x^2) - 1 + x^2) (λ x, 3 * x^2).
  admit.
  step_lhopital (λ x, - (2 * x) / (1 + x^2)^2 + 2 * x) (λ x, 6 * x).
  step_lhopital (λ x, -2 / (1 + x^2)^2 + 8 * x^2 / (1 + x^2)^3 + 2) (λ x : R, 6).
Abort.

Lemma lemma_15_2_vi :
  ⟦ lim 0 ⟧ (fun x => 1 / x - 1 / sin x) = 0.
Proof.
  replace (fun x => 1 / x - 1 / sin x) with (fun x => (sin x - x) / (x * sin x)) by admit.

  
  step_lhopital (λ x, cos x - 1) (λ x, sin x + x * cos x).
  admit.
  step_lhopital (λ x, - sin x) (λ x, 2 * cos x - x * sin x).
  admit.
Abort.