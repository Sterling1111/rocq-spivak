From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_16_a : ∀ f a,
  differentiable_at f a ->
  f a ≠ 0 ->
  differentiable_at (λ x, | f x |) a.
Proof. 
  intros f a [L H1] H2.
  assert (H3 : ⟦ der a ⟧ f = (λ _, L)) by auto.
  assert (H4 : ⟦ der (f a) ⟧ (λ x, |x|) = (fun t => t / |t|)) by auto_diff.
  pose proof derivative_at_comp f (λ x, |x|) (fun _ => L) (fun t => t / |t|) a H3 H4 as H5.
  eapply derivative_at_imp_differentiable_at; eauto.
Qed.

Lemma lemma_10_16_b : ∃ f a,
  differentiable_at f a /\ f a = 0 /\ ~ differentiable_at (λ x, | f x |) a.
Proof. Abort.

Lemma lemma_10_16_c : ∀ f g a,
  differentiable_at f a ->
  differentiable_at g a ->
  f a ≠ g a ->
  differentiable_at (λ x, Rmax (f x) (g x)) a /\ differentiable_at (λ x, Rmin (f x) (g x)) a.
Proof. Abort.

Lemma lemma_10_16_d : ∃ f g a,
  differentiable_at f a /\ differentiable_at g a /\ f a = g a /\
  ~ differentiable_at (λ x, Rmax (f x) (g x)) a.
Proof. Abort.
