From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_15_a : ∀ φ n,
  continuous φ ->
  (∃ k, n = (2 * k + 1)%nat) ->
  ⟦ lim ∞ ⟧ (λ x, φ x / x ^ n) = 0 ->
  ⟦ lim -∞ ⟧ (λ x, φ x / x ^ n) = 0 ->
  ∃ x, x ^ n + φ x = 0.
Proof.
  intros φ n H1 [k H2] H3 H4.
  specialize (H3 (1 / 2) ltac:(lra)) as [N1 H3].
  specialize (H4 (1 / 2) ltac:(lra)) as [N2 H4].
  set (a := Rmin N2 0 - 1).
  set (b := Rmax N1 0 + 1).
  assert (H5 : a < 0 < b) by (unfold a, b; solve_R).
  specialize (H3 b ltac:(unfold b; solve_R)).
  specialize (H4 a ltac:(unfold a; solve_R)).
  assert (H6 : a ^ n < 0).
  { apply Rpow_odd_lt_0; [lra | exists k; exact H2]. }
  assert (H7 : 0 < b ^ n) by (apply pow_lt; lra).
  assert (H8 : a ^ n + φ a = a ^ n * (1 + φ a / a ^ n)) by (field; lra).
  assert (H9 : b ^ n + φ b = b ^ n * (1 + φ b / b ^ n)) by (field; lra).
  assert (H10 : a ^ n + φ a < 0 < b ^ n + φ b).
  { rewrite H8, H9. solve_R. }
  pose proof (intermediate_value_theorem_zero (λ x, x ^ n + φ x) a b
    ltac:(lra) ltac:(apply continuous_on_plus; [auto_cont | apply continuous_imp_continuous_on; auto])
    H10) as [x [H11 H12]].
  exists x. exact H12.
Qed.

Lemma lemma_7_15_b : ∀ φ n,
  continuous φ ->
  (∃ k, n = (2 * k)%nat) ->
  ⟦ lim ∞ ⟧ (λ x, φ x / x ^ n) = 0 ->
  ⟦ lim -∞ ⟧ (λ x, φ x / x ^ n) = 0 ->
  ∃ y, ∀ x, y ^ n + φ y <= x ^ n + φ x.
Proof.
  intros φ n H1 [k H2] H3 H4.
Abort.
