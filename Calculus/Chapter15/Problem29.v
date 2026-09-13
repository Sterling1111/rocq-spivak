From Calculus.Chapter15 Require Import Prelude Problem19.

Lemma lemma_15_29_a :
  let α := λ x, ∫ 0 x (λ t, 1 / (1 + t^2)) in
  (∀ x, α (-x) = - α x) /\
  increasing α /\
  ⟦ lim ∞ ⟧ α = π / 2.
Proof.
  assert (H1 : ∀ a b, a < b ->
    ∫ a b (λ t, 1 / (1 + t^2)) = arctan b - arctan a).
  { intros a b H1. apply FTC2; [lra | auto_cont | auto_diff]. }
  assert (H2 : ∀ x, ∫ 0 x (λ t, 1 / (1 + t^2)) = arctan x).
  { intro x. destruct (Rtotal_order x 0) as [H2 | [H2 | H2]].
    - rewrite integral_b_a_neg, H1; [rewrite arctan_0; lra | lra].
    - subst x. rewrite integral_n_n, arctan_0. reflexivity.
    - rewrite H1; [rewrite arctan_0; lra | lra]. }
  split.
  - intro x. rewrite !H2. apply arctan_neg.
  - split.
    + replace (λ x, ∫ 0 x (λ t, 1 / (1 + t^2))) with arctan
        by (extensionality x; symmetry; apply H2).
      apply derivative_pos_imp_increasing with (f' := λ x, 1 / (1 + x^2)).
      * apply derivative_arctan.
      * intro x. apply Rdiv_pos_pos; nra.
    + apply lemma_15_19_b.
Qed.

Lemma lemma_15_29_b : ∀ α α_inv,
  (∀ x, α x = ∫ 0 x (λ t, 1 / (1 + t^2))) ->
  inverse_on α α_inv (-π / 2, π / 2) ℝ ->
  ∀ x, x ∈ (-π / 2, π / 2) ->
  ⟦ der x ⟧ α_inv = (λ x, 1 + (α_inv x)^2).
Abort.

Lemma lemma_15_29_c_i :
  ⟦ lim (π/2)⁻ ⟧ sin = 1.
Proof.
  replace 1 with (sin (π / 2)) by apply sin_π_over_2.
  apply limit_iff. apply limit_sin.
Qed.

Lemma lemma_15_29_c_ii :
  ⟦ lim (-π/2)⁺ ⟧ sin = -1.
Proof.
  replace (-1) with (sin (-π / 2)) by
    (replace (-π / 2) with (- (π / 2)) by lra; rewrite sin_even_odd, sin_π_over_2; reflexivity).
  apply limit_iff. apply limit_sin.
Qed.

Lemma lemma_15_29_c_iv : ∀ x,
  ⟦ Der^2 x ⟧ sin = - sin x.
Proof.
  intro x.
  apply nth_derivative_at_imp_nth_derive_at with (f' := λ x, - sin x).
  apply nth_derivative_imp_at.
  exists cos. split; [| auto_diff].
  exists sin. split; [reflexivity | auto_diff].
Qed.
