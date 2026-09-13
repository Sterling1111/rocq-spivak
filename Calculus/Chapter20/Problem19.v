From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_19_term : ∀ f k x,
  nth_differentiable (S k) f ->
  ⟦ der ⟧ (λ t, ⟦ Der ^ k t ⟧ f / (fact k) * (x-t)^k) =
    (λ t, - (⟦ Der ^ k t ⟧ f / (fact k)) * k * (x-t)^(k-1) +
      ⟦ Der ^ (S k) t ⟧ f / (fact k) * (x-t)^k).
Proof.
  intros f k x H1.
  assert (H2 : ⟦ der ⟧ (⟦ Der ^ k ⟧ f) = ⟦ Der ^ (S k) ⟧ f).
  {
    apply derive_spec. apply nth_differentiable_imp_differentiable with (n := 1%nat); try lia.
    apply nth_derive_nth_differentiable. replace (k + 1)%nat with (S k) by lia. auto.
    reflexivity.
  }
  unfold nth_derive_at. auto_diff; apply INR_fact_neq_0.
Qed.

Lemma lemma_20_19_a_derivative : ∀ f n x,
  nth_differentiable (S n) f ->
  ⟦ der ⟧ (λ t, R(n,t,f) x) =
    (λ t, - (⟦ Der ^ (S n) t ⟧ f / (fact n)) * (x-t)^n).
Abort.

Lemma lemma_20_19_a : ∀ f n a x δ,
  a < x -> δ > 0 -> nth_differentiable_on (S n) f (a-δ,x+δ) ->
  ∃ t, a < t < x /\ R(n,a,f) x = ⟦ Der ^ (S n) t ⟧ f / (fact (S n)) * (x-a)^(S n).
Proof.
  intros f n a x δ H1 H2 H3.
  destruct (Taylors_Theorem n a x f H1) as [t [H4 H5]].
  - exists δ. auto.
  - exists t. replace (n + 1)%nat with (S n) in H5 by lia.
    split; auto.
Qed.

Lemma lemma_20_19_b : ∀ f n a x δ,
  a < x -> δ > 0 -> nth_differentiable_on (S n) f (a-δ,x+δ) ->
  ∃ t, a < t < x /\ R(n,a,f) x = ⟦ Der ^ (S n) t ⟧ f / (fact n) * (x-t)^n * (x-a).
Proof.
Abort.