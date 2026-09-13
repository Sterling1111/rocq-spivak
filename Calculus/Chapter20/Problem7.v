From Calculus.Chapter20 Require Import Prelude.

Definition taylor_coefficient (f : ℝ -> ℝ) (a : ℝ) (k : ℕ) :=
  ⟦ Der ^ k a ⟧ f / (fact k).

Lemma lemma_20_7_i : ∀ f g a k,
  nth_differentiable k f -> nth_differentiable k g ->
  taylor_coefficient (λ x, f x + g x) a k =
    taylor_coefficient f a k + taylor_coefficient g a k.
Proof.
  intros f g a k H1 H2. unfold taylor_coefficient, nth_derive_at.
  rewrite (nth_derivative_imp_nth_derive k (f + g)
    (⟦ Der ^ k ⟧ f + ⟦ Der ^ k ⟧ g)).
  - unfold plus, Rdiv. ring.
  - apply nth_derivative_plus; apply nth_derive_spec; auto.
Qed.

Lemma lemma_20_7_ii : ∀ f g a k,
  nth_differentiable k f -> nth_differentiable k g ->
  taylor_coefficient (λ x, f x * g x) a k =
    ∑ 0 k (λ j, taylor_coefficient f a j * taylor_coefficient g a (k-j)).
Abort.

Lemma lemma_20_7_iii : ∀ f a k, nth_differentiable (S k) f ->
  taylor_coefficient (λ x, ⟦ Der x ⟧ f) a k = (S k) * taylor_coefficient f a (S k).
Proof.
  intros f a k H1. unfold taylor_coefficient, nth_derive_at.
  rewrite <- nth_derive_succ.
  replace (fact (S k)) with (S k * fact k)%nat by reflexivity.
  rewrite mult_INR. field. split.
  - apply INR_fact_neq_0.
  - apply not_0_INR. lia.
Qed.

Lemma lemma_20_7_iv : ∀ f a k,
  continuous f -> nth_differentiable k f ->
  taylor_coefficient (λ x, ∫ a x f) a 0 = 0 /\
  taylor_coefficient (λ x, ∫ a x f) a (S k) = taylor_coefficient f a k / (S k).
Proof.
  intros f a k H1 H2. unfold taylor_coefficient, nth_derive_at.
  split.
  - rewrite nth_derive_0, integral_eq; lra.
  - rewrite nth_derive_succ, (derivative_imp_derive _ _ (FTC1_global f a H1)).
    replace (fact (S k)) with (S k * fact k)%nat by reflexivity.
    rewrite mult_INR. field. split.
    + apply INR_fact_neq_0.
    + apply not_0_INR. lia.
Qed.

Lemma lemma_20_7_v : ∀ f a k,
  continuous f -> nth_differentiable k f ->
  taylor_coefficient (λ x, ∫ 0 x f) a 0 = ∫ 0 a f /\
  taylor_coefficient (λ x, ∫ 0 x f) a (S k) = taylor_coefficient f a k / (S k).
Proof.
  intros f a k H1 H2. unfold taylor_coefficient, nth_derive_at.
  split.
  - rewrite nth_derive_0. simpl. lra.
  - rewrite nth_derive_succ, (derivative_imp_derive _ _ (FTC1_global f 0 H1)).
    replace (fact (S k)) with (S k * fact k)%nat by reflexivity.
    rewrite mult_INR. field. split.
    + apply INR_fact_neq_0.
    + apply not_0_INR. lia.
Qed.
