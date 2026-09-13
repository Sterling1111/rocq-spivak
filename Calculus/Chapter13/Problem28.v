From Calculus.Chapter13 Require Import Prelude.

From Calculus.Chapter13 Require Import Problem26.

Lemma lemma_13_28_a : ∀ s1 s2 a b,
  step_function_on s1 a b -> step_function_on s2 a b ->
  step_function_on (s1 + s2)%function a b.
Abort.

Lemma lemma_13_28_b : ∀ s1 s2 a b,
  step_function_on s1 a b -> step_function_on s2 a b ->
  ∫ a b (s1 + s2)%function = ∫ a b s1 + ∫ a b s2.
Abort.

Lemma lemma_13_28_c : ∀ f g a b,
  a < b -> integrable_on a b f -> integrable_on a b g ->
  integrable_on a b (f + g)%function /\
  ∫ a b (f + g)%function = ∫ a b f + ∫ a b g.
Proof.
  intros f g a b H1 H2 H3. split.
  - apply integrable_plus; auto.
  - apply integral_plus; auto; lra.
Qed.
