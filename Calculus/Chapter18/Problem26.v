From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_26 : ∀ f,
  (integrable_on 0 1 f /\
  ⟦ der ⟧ f = (λ t, f t + ∫ 0 1 f)) <->
  (∃ c, ∀ t, f t = c * (exp t - (e - 1) / 2)).
Proof.
  intros f. split.
  - intros [H1 H2].
    set (g := λ t, f t + ∫ 0 1 f).
    assert (H3 : ⟦ der ⟧ g = g) by (unfold g; auto_diff).
    assert (H4 : ⟦ der ⟧ (λ t, g t / exp t) = (λ _, 0)) by auto_diff.
    pose proof derivative_zero_imp_const' _ H4 as [c H5].
    assert (H6 : ∀ t, g t = c * exp t).
    {
      intros t. specialize (H5 t).
      pose proof exp_pos t as H6.
      apply Rmult_eq_compat_r with (r := exp t) in H5.
      field_simplify in H5; lra.
    }
    assert (H7 : ⟦ der ⟧ (λ t, f t - c * exp t) = (λ _, 0)).
    {
      assert (H7 : ⟦ der ⟧ f = (λ t, c * exp t)).
      { apply derivative_ext with (f1' := g); auto. }
      auto_diff.
    }
    pose proof derivative_zero_imp_const' _ H7 as [a H8].
    assert (H9 : ∀ t, f t = a + c * exp t).
    { intros t. specialize (H8 t). lra. }
    assert (H10 : ∫ 0 1 f = a + c * (e - 1)).
    {
      replace f with (λ t, a + c * exp t) by (extensionality t; auto).
      replace (a + c * (e - 1)) with
        ((λ t, a * t + c * exp t) 1 - (λ t, a * t + c * exp t) 0)
        by (cbn beta; rewrite exp_0; unfold e; ring).
      apply FTC2 with (g := λ t, a * t + c * exp t); [lra | auto_cont | auto_diff].
    }
    assert (H11 : a = c * (1 - e) / 2).
    {
      specialize (H6 0). unfold g in H6.
      rewrite H9, H10, exp_0 in H6. lra.
    }
    exists c. intros t. rewrite H9, H11. field.
  - intros [c H1].
    assert (H2 : f = (λ t, c * (exp t - (e - 1) / 2)))
      by (extensionality t; auto).
    rewrite H2.
    assert (H3 : ∫ 0 1 (λ t, c * (exp t - (e - 1) / 2)) = c * (e - 1) / 2).
    {
      replace (c * (e - 1) / 2) with
        ((λ t, c * (exp t - (e - 1) / 2 * t)) 1 -
         (λ t, c * (exp t - (e - 1) / 2 * t)) 0)
        by (cbn beta; rewrite exp_0; unfold e; field).
      apply FTC2 with (g := λ t, c * (exp t - (e - 1) / 2 * t));
        [lra | auto_cont | auto_diff].
    }
    split.
    + apply theorem_13_3; [lra | auto_cont].
    + rewrite H3. auto_diff.
Qed.
