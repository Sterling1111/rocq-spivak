From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_1_i : ∀ x,
  ⟦ der x ⟧ (λ x, arctan (arctan (arctan x))) =
    (λ x, 1 / (1 + (arctan (arctan x))^2) *
              (1 / (1 + (arctan x)^2)) *
              (1 / (1 + x^2))).
Proof.
  auto_diff.
Qed.

Lemma lemma_15_1_ii : ∀ x,
  -1 < x < 1 ->
  ⟦ der x ⟧ (λ x, arcsin (arctan (arccos x))) =
    (λ x, 1 / √(1 - (arctan (arccos x))^2) *
              (1 / (1 + (arccos x)^2)) *
              (-1 / √(1 - x^2))).
Proof.
  auto_diff.
Abort.

Lemma lemma_15_1_iii : ∀ x,
  cos x <> 0 ->
  ⟦ der x ⟧ (λ x, arctan (tan x * arctan x)) =
    (λ x, 1 / (1 + (tan x * arctan x)^2) *
              (sec x^2 * arctan x + tan x * (1 / (1 + x^2)))).
Proof.
  auto_diff. unfold tan, sec. solve_R.
Qed.

Lemma lemma_15_1_iv : ∀ x,
  x > 0 ->
  ⟦ der x ⟧ (λ x, arcsin (1 / √(1 + x^2))) =
    (λ x, -1 / (1 + x^2)).
Proof.
  intros x H1. auto_diff.
  assert (H2 : 0 < √(1 + x * x)) by (apply sqrt_lt_R0; nra).
  assert (H3 : √(1 + x * x)^2 = 1 + x * x) by (apply pow2_sqrt; nra).
  replace (1 - 1 / √(1 + x * x) * (1 / √(1 + x * x))) with
    ((x / √(1 + x * x))^2).
  2 : { apply Rmult_eq_reg_r with (r := √(1 + x * x)^2); [field_simplify; nra | nra]. }
  rewrite sqrt_pow2; [| apply Rlt_le, Rdiv_pos_pos; lra].
  field_simplify; try nra. rewrite H3. field; nra.
Qed.

Lemma lemma_15_1_v : ∀ a b,
  a < b ->
  ⟦ der ⟧ (λ x, ∫ a b (λ t, x / (1 + t^2 + (sin t)^2))) =
    (λ x, ∫ a b (λ t, 1 / (1 + t^2 + (sin t)^2))).
Proof.
  intros a b H1.
  replace (λ x, ∫ a b (λ t, x / (1 + t^2 + (sin t)^2))) with
    (λ x, x * ∫ a b (λ t, 1 / (1 + t^2 + (sin t)^2))).
  - auto_diff.
  - extensionality x.
    replace (λ t, x / (1 + t^2 + (sin t)^2)) with
      (λ t, x * (1 / (1 + t^2 + (sin t)^2)))
      by (extensionality t; unfold Rdiv; ring).
    rewrite integral_mult_scalar; auto.
    apply theorem_13_3; [lra | auto_cont].
Qed.

Lemma lemma_15_1_vi : ∀ x,
  ⟦ der x ⟧ (λ x, sin (∫ 0 x (λ y, sin (∫ 0 y (λ t, (sin t)^3))))) =
    (λ x, cos (∫ 0 x (λ y, sin (∫ 0 y (λ t, (sin t)^3)))) *
              sin (∫ 0 x (λ t, (sin t)^3))).
Proof.
  intros x.
  assert (H1 : continuous (λ t, (sin t)^3)) by auto_cont.
  assert (H2 : ⟦ der ⟧ (λ y, ∫ 0 y (λ t, (sin t)^3)) = (λ y, (sin y)^3))
    by (apply FTC1_global; auto).
  assert (H3 : continuous (λ y, sin (∫ 0 y (λ t, (sin t)^3)))).
  { apply differentiable_imp_continuous.
    apply derivative_imp_differentiable with
      (f' := λ y, cos (∫ 0 y (λ t, (sin t)^3)) * (sin y)^3).
    apply (derivative_comp _ sin _ cos H2 derivative_sin). }
  pose proof FTC1_global _ 0 H3 as H4.
  apply (derivative_at_comp _ sin _ cos x (H4 x) (derivative_sin _)).
Qed.

Lemma lemma_15_1_vii : ∀ F F_inv,
  (∀ x, x > 0 -> F x = ∫ 1 x (λ t, 1 / t)) ->
  inverse F F_inv ->
  ⟦ der ⟧ F_inv = (λ y, F_inv y).
Proof.
  intros F F_inv H1 H2.
Abort.

Lemma lemma_15_1_viii : ∀ F F_inv,
  (∀ x, -1 < x < 1 -> F x = ∫ 0 x (λ t, 1 / √(1 - t^2))) ->
  inverse F F_inv ->
  ⟦ der ⟧ F_inv = (λ y, √(1 - (F_inv y)^2)).
Abort.