From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_20_a : ∀ f (n : ℕ),
  (n > 0)%nat ->
  continuous_on f [0, 1] ->
  f 0 = f 1 ->
  ∃ x, x ∈ [0, 1 - 1 / n] /\ f x = f (x + 1 / n).
Proof.
  intros f n H1 H2 H3.
  destruct (Nat.eq_dec n 1) as [H4 | H4].
  - subst n. exists 0. simpl. split; [solve_R |].
    replace (0 + 1 / 1) with 1 by field. exact H3.
  - assert (H5 : 1 < n).
    { replace 1 with (1%nat : ℝ) by reflexivity. apply lt_INR. lia. }
    set (h := 1 / n).
    assert (H6 : 0 < h < 1) by (unfold h; solve_R).
    set (g := λ x, f x - f (x + h)).
    assert (H7 : continuous_on g [0, 1 - h]).
    {
      apply continuous_on_minus.
      - apply continuous_on_subset with (A2 := [0, 1]); auto. intros x H7. solve_R.
      - change (continuous_on (f ∘ (λ x, x + h)) [0, 1 - h]).
        apply continuous_on_comp with (D2 := [0, 1]); auto; [auto_cont |].
        intros x H7. solve_R.
    }
    destruct (classic (∃ x, x ∈ [0, 1 - h] /\ g x = 0)) as [H8 | H8].
    + destruct H8 as [x [H8 H9]]. exists x. split; auto. unfold g in H9. lra.
    + exfalso.
      assert (H9 : ∀ x, x ∈ [0, 1 - h] -> g x <> 0).
      { intros x H9 H10. apply H8. exists x. auto. }
      assert (H10 : ∀ x, x ∈ [0, 1 - h] -> g 0 * g x > 0).
      {
        intros x H10. pose proof (H9 0 ltac:(solve_R)) as H11.
        pose proof (H9 x H10) as H12.
        destruct (Rlt_dec 0 (g 0 * g x)) as [H13 | H13]; auto.
        destruct (intermediate_value_theorem_unordered g 0 x 0
          ltac:(apply continuous_on_subset with (A2 := [0, 1 - h]); auto; intros y H14; solve_R)
          ltac:(solve_R)) as [y [H14 H15]].
        exfalso. apply (H9 y ltac:(solve_R)). exact H15.
      }
      assert (H11 : ∀ (k : ℕ), (k < n)%nat -> g 0 * (f (k * h) - f ((S k)%nat * h)) > 0).
      {
        intros k H11.
        assert (H12 : k + 1 <= n).
        { rewrite <- S_INR. apply le_INR. lia. }
        assert (H13 : 0 <= k) by apply pos_INR.
        pose proof (H10 (k * h) ltac:(unfold h; solve_R)) as H14.
        unfold g in H14. rewrite S_INR.
        replace ((k + 1) * h) with (k * h + h) by ring. exact H14.
      }
      assert (H12 : ∀ (k : ℕ), (0 < k <= n)%nat -> g 0 * (f 0 - f (k * h)) > 0).
      {
        intros k. induction k as [| k IH]; intros H12; [lia |].
        destruct (Nat.eq_dec k 0) as [H13 | H13].
        - subst k. pose proof (H11 0%nat ltac:(lia)) as H14.
          simpl in H14. rewrite Rmult_0_l in H14. exact H14.
        - specialize (IH ltac:(lia)). pose proof (H11 k ltac:(lia)) as H14. nra.
      }
      specialize (H12 n ltac:(lia)).
      replace (n * h) with 1 in H12 by (unfold h; field; lra).
      rewrite H3 in H12. nra.
Qed.

Lemma lemma_7_20_b : ∀ a,
  0 < a < 1 ->
  ~ (∃ (n : ℕ), (n > 0)%nat /\ a = 1 / n) ->
  ∃ f, continuous_on f [0, 1] /\
    f 0 = f 1 /\
    (∀ x, x ∈ [0, 1 - a] -> f x <> f (x + a)).
Proof. Abort.
