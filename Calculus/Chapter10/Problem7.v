From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_7_a : ∀ r A, (∀ t, A t = π * (r t)^2) ->
  (∀ t, r t = 6 -> ⟦ der t ⟧ r = λ _, 4) -> (∀ t, r t = 6 -> ⟦ der t ⟧ A = λ _, 48 * π).
Proof.
  intros r A H1 H2 t H3.
  replace A with (λ t, π * (r t)^2).
  2 : { extensionality x. symmetry. apply H1. }
  specialize (H2 t H3).
  apply derivative_at_ext_val with (f' := λ x, 2 * π * r x * 4).
  - auto_diff.
  - rewrite H3. ring.
Qed.

Lemma lemma_10_7_b : ∀ r V, (∀ t, V t = 4 / 3 * π * (r t)^3) ->
  (∀ t, r t = 6 -> ⟦ Der t ⟧ V = 2) -> (∀ t, r t = 6 -> ⟦ Der t ⟧ r = 1 / (72 * π)).
Proof. Abort.

Lemma lemma_10_7_c : ∀ r A V, (∀ t, A t = π * (r t)^2) ->
  (∀ t, V t = 4 / 3 * π * (r t)^3) ->
  (∀ t, r t = 3 -> ⟦ Der t ⟧ A = 5) -> (∀ t, r t = 3 -> ⟦ Der t ⟧ V = 10).
Proof. Abort.
