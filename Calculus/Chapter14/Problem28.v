From Calculus.Chapter14 Require Import Prelude.
From Lib Require Import Exponential.

Lemma lemma_14_28_a : ∀ a,
  a > 0 ->
  ⟦ lim 0⁺ ⟧ (λ ε, ∫ ε a (λ x, 1 / √x)) = 2 * √a.
Proof.
  intros a H1.
  apply limit_right_eq with (f1 := λ ε, 2 * √a - 2 * √ε).
  - exists a. split; [lra |]. intros ε H2.
    symmetry. apply FTC2 with (g := λ x, 2 * √x);
      [lra | auto_cont | auto_diff].
  - auto_limit.
Qed.

Lemma lemma_14_28_b : ∀ a r,
  a > 0 -> -1 < r < 0 ->
  ⟦ lim 0⁺ ⟧ (λ ε, ∫ ε a (λ x, x ^^ r)) = a ^^ (r+1) / (r+1).
Proof.
  intros a r H1 H2.
  assert (H3 : ⟦ lim 0⁺ ⟧ (λ x, x ^^ (r + 1)) = 0).
  {
    apply limit_right_eq with (f1 := λ x, (|x|) ^^ (r + 1)).
    - exists 1. split; [lra |]. intros x H3. rewrite Rabs_right; [reflexivity | lra].
    - apply limit_iff. apply limit_Rabs_Rpower_zero. lra.
  }
  apply limit_right_eq with (f1 := λ ε, a ^^ (r + 1) / (r + 1) - ε ^^ (r + 1) / (r + 1)).
  - exists a. split; [lra |]. intros ε H4.
    symmetry. apply FTC2 with (g := λ x, x ^^ (r + 1) / (r + 1));
      [lra | auto_cont | auto_diff].
  - apply limit_right_subst with (L1 := a ^^ (r + 1) / (r + 1) - 0 / (r + 1)); [lra |].
    apply limit_right_minus; [apply limit_right_const |].
    apply limit_right_div; [exact H3 | apply limit_right_const | lra].
Qed.

Lemma lemma_14_28_c :
  ~ ∃ L, ⟦ lim 0⁺ ⟧ (λ ε, ∫ ε 1 (λ x, 1 / x)) = L.
Proof.
  intros [L H1].
  assert (H2 : ∀ (n : ℕ), ∫ (1 / 2^n) 1 (λ x, 1 / x) = n * ∫ 1 2 (λ x, 1 / x)).
  {
    intros n. rewrite integral_b_a_neg, <- log_spec, corollary_18_2;
      [| lra | apply pow_lt; lra | solve_R].
    rewrite log_1, corollary_18_1, <- log_spec; [lra | lra | lra].
  }
  assert (H3 : ∫ 1 2 (λ x, 1 / x) > 0).
  {
    apply integral_pos; [lra | intros x H3; solve_R | auto_cont |].
    apply theorem_13_3; [lra | auto_cont].
  }
  destruct (H1 1 ltac:(lra)) as [δ [H4 H5]].
  destruct (INR_unbounded (Rmax (1 / δ) ((|L| + 2) / ∫ 1 2 (λ x, 1 / x)))) as [n H6].
  pose proof n_lt_pow2_n n as H7.
  specialize (H5 (1 / 2^n) ltac:(solve_R)). rewrite H2 in H5. solve_R.
Qed.

Lemma lemma_14_28_d : ∀ a r,
  a < 0 -> -1 < r < 0 ->
  ⟦ lim 0⁺ ⟧ (λ ε, ∫ a (-ε) (λ x, (|x|) ^^ r)) = (-a) ^^ (r+1) / (r+1).
Proof.
  intros a r H1 H2.
  apply limit_right_eq with (f1 := λ ε, ∫ ε (-a) (λ x, x ^^ r)).
  - exists (-a). split; [lra |]. intros ε H3.
    assert (H4 : ∫ ε (-a) (λ x, x ^^ r) =
      (-a) ^^ (r + 1) / (r + 1) - ε ^^ (r + 1) / (r + 1)).
    {
      apply FTC2 with (g := λ x, x ^^ (r + 1) / (r + 1));
        [lra | auto_cont | auto_diff].
    }
    rewrite H4. symmetry.
    replace ((-a) ^^ (r + 1) / (r + 1) - ε ^^ (r + 1) / (r + 1)) with
      ((λ x, - ((-x) ^^ (r + 1) / (r + 1))) (-ε) -
       (λ x, - ((-x) ^^ (r + 1) / (r + 1))) a)
      by (cbn beta; rewrite Ropp_involutive; lra).
    apply FTC2 with (g := λ x, - ((-x) ^^ (r + 1) / (r + 1)));
      [lra | auto_cont |].
    apply derivative_on_ext with (f1' := λ x, (-x) ^^ r).
    + intros x H5. rewrite Rabs_left; [reflexivity | solve_R].
    + auto_diff.
  - apply lemma_14_28_b; lra.
Qed.

Lemma lemma_14_28_e :
  ∃ L,
  ⟦ lim 0⁺ ⟧ (λ ε, ∫ (-1 + ε) (1 - ε) (λ x, 1 / √(1 - x^2))) = L.
Abort.
