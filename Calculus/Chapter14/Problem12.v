From Calculus.Chapter14 Require Import Prelude.

Definition periodic (f : R -> R) (a : R) : Prop :=
  ∀ x, f (x + a) = f x.

Lemma lemma_14_12_a : ∀ f a b,
  a > 0 ->
  periodic f a ->
  integrable_on 0 a f ->
  ∫ 0 a f = ∫ b (b + a) f.
Abort.

Lemma lemma_14_12_b : ∃ f : R -> R, ∃ a : R,
  a > 0 /\
  ~ (∃ T, T > 0 /\ periodic f T) /\
  periodic (⟦ Der ⟧ f) a.
Proof.
  exists (λ x, x), 1. split; [lra |]. split.
  - intros [T [H1 H2]]. specialize (H2 0). unfold periodic in H2. lra.
  - unfold periodic. intros x.
    repeat rewrite (derivative_at_imp_derive_at _ (λ _, 1)); auto_diff.
Qed.

Lemma lemma_14_12_c : ∀ f f' a,
  a > 0 ->
  ⟦ der ⟧ f = f' ->
  periodic f' a ->
  f a = f 0 ->
  periodic f a.
Proof.
  intros f f' a H1 H2 H3 H4.
  assert (H5 : ⟦ der ⟧ (λ x, f (x + a) - f x) = (λ _, 0)).
  {
    apply derivative_ext with (f1' := λ x, f' (x + a) - f' x).
    - intros x. rewrite H3. lra.
    - auto_diff.
  }
  pose proof derivative_zero_imp_const' _ H5 as [c H6].
  pose proof H6 0 as H7. rewrite Rplus_0_l, H4 in H7.
  intros x. specialize (H6 x). lra.
Qed.

Lemma lemma_14_12_d : ∀ f f' a,
  a > 0 ->
  ⟦ der ⟧ f = f' ->
  periodic f' a ->
  (∃ T, T > 0 /\ periodic f T) ->
  f a = f 0.
Proof.
  intros f f' a H1 H2 H3 [T [H4 H5]].
  assert (H6 : continuous f).
  { apply differentiable_imp_continuous. apply derivative_imp_differentiable with (f' := f'). exact H2. }
  assert (H7 : continuous_on (λ x, |f x|) [0, T]) by auto_cont.
  destruct (continuous_on_interval_bounded_above _ 0 T H4 H7) as [M H8].
  assert (H9 : ∀ (n : ℕ) x, f (x + n * T) = f x).
  {
    induction n as [| n IH]; intros x.
    - replace (x + 0%nat * T) with x by (rewrite INR_0; lra). reflexivity.
    - rewrite S_INR.
      replace (x + (n + 1) * T) with ((x + n * T) + T) by ring.
      rewrite H5. apply IH.
  }
  assert (H10 : ∀ x, x >= 0 -> |f x| < M).
  {
    intros x H10.
    pose proof floor_spec (x / T) ltac:(solve_R) as H11.
    pose proof H9 (⌊x / T⌋) (x - (⌊x / T⌋)%nat * T) as H12.
    replace (x - (⌊x / T⌋)%nat * T + (⌊x / T⌋)%nat * T) with x in H12 by ring.
    rewrite H12. apply H8. solve_R.
  }
  assert (H11 : ⟦ der ⟧ (λ x, f (x + a) - f x) = (λ _, 0)).
  {
    apply derivative_ext with (f1' := λ x, f' (x + a) - f' x).
    - intros x. rewrite H3. lra.
    - auto_diff.
  }
  destruct (derivative_zero_imp_const' _ H11) as [d H12].
  assert (H13 : ∀ (n : ℕ), f (n * a) = f 0 + n * d).
  {
    induction n as [| n IH].
    - rewrite INR_0. replace (0 * a) with 0 by ring. lra.
    - pose proof H12 (n * a) as H13. rewrite S_INR.
      replace ((n + 1) * a) with (n * a + a) by ring. lra.
  }
  assert (H14 : d = 0).
  {
    destruct (Req_dec d 0) as [H14 | H14]; [exact H14 | exfalso].
    destruct (INR_unbounded ((M + |f 0| + 1) / |d|)) as [n H15].
    pose proof pos_INR n as H16.
    specialize (H10 (n * a) ltac:(nra)). rewrite H13 in H10. solve_R.
  }
  specialize (H12 0). rewrite Rplus_0_l in H12. lra.
Qed.
