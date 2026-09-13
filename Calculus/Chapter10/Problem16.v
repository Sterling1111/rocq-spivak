From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_16_a : ∀ f a,
  differentiable_at f a ->
  f a ≠ 0 ->
  differentiable_at (λ x, | f x |) a.
Proof. 
  intros f a [L H1] H2.
  assert (H3 : ⟦ der a ⟧ f = (λ _, L)) by auto.
  assert (H4 : ⟦ der (f a) ⟧ (λ x, |x|) = (λ t, t / |t|)) by auto_diff.
  pose proof derivative_at_comp f (λ x, |x|) (λ _, L) (λ t, t / |t|) a H3 H4 as H5.
  eapply derivative_at_imp_differentiable_at; eauto.
Qed.

Lemma lemma_10_16_b : ∃ f a,
  differentiable_at f a /\ f a = 0 /\ ~ differentiable_at (λ x, | f x |) a.
Proof.
  exists (λ x, x), 0. split; [apply differentiable_at_id |].
  split; [reflexivity |]. intros [L H1].
  assert (H2 : ⟦ lim 0⁺ ⟧ (λ h, (|0 + h| - |0|) / h) = 1).
  {
    apply limit_right_eq with (f1 := λ _, 1); try auto_limit.
    exists 1. split; solve_R.
  }
  assert (H3 : ⟦ lim 0⁻ ⟧ (λ h, (|0 + h| - |0|) / h) = -1).
  {
    apply limit_left_eq with (f1 := λ _, -1); try auto_limit.
    exists 1. split; solve_R.
  }
  apply limit_iff in H1 as [H1 H4].
  pose proof (limit_right_unique _ _ _ _ H4 H2).
  pose proof (limit_left_unique _ _ _ _ H1 H3). lra.
Qed.

Lemma lemma_10_16_c : ∀ f g a,
  differentiable_at f a ->
  differentiable_at g a ->
  f a ≠ g a ->
  differentiable_at (λ x, Rmax (f x) (g x)) a /\ differentiable_at (λ x, Rmin (f x) (g x)) a.
Proof.
  intros f g a H1 H2 H3.
  assert (H4 : differentiable_at (λ x, |f x - g x|) a).
  { apply lemma_10_16_a; [apply differentiable_at_minus; auto | lra]. }
  apply differentiable_at_imp_derivative_at in H1 as [f' H1].
  apply differentiable_at_imp_derivative_at in H2 as [g' H2].
  apply differentiable_at_imp_derivative_at in H4 as [h' H4].
  rewrite calculus_max_fun, calculus_min_fun. split.
  - apply derivative_at_imp_differentiable_at with (f' := λ x, (f' x + g' x + h' x) / 2).
    auto_diff.
  - apply derivative_at_imp_differentiable_at with (f' := λ x, (f' x + g' x - h' x) / 2).
    auto_diff.
Qed.

Lemma lemma_10_16_d : ∃ f g a,
  differentiable_at f a /\ differentiable_at g a /\ f a = g a /\
  ~ differentiable_at (λ x, Rmax (f x) (g x)) a.
Proof.
  exists (λ x, x), (λ _, 0), 0.
  split; [apply differentiable_at_id |].
  split; [apply differentiable_at_const |].
  split; [reflexivity |]. intros [L H1].
  assert (H2 : ⟦ lim 0⁺ ⟧ (λ h, (Rmax (0 + h) 0 - Rmax 0 0) / h) = 1).
  {
    apply limit_right_eq with (f1 := λ _, 1); try auto_limit.
    exists 1. split; solve_R.
  }
  assert (H3 : ⟦ lim 0⁻ ⟧ (λ h, (Rmax (0 + h) 0 - Rmax 0 0) / h) = 0).
  {
    apply limit_left_eq with (f1 := λ _, 0); try auto_limit.
    exists 1. split; solve_R.
  }
  apply limit_iff in H1 as [H1 H4].
  pose proof (limit_right_unique _ _ _ _ H4 H2).
  pose proof (limit_left_unique _ _ _ _ H1 H3). lra.
Qed.
