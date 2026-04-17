From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_3_a : ∃ x, x^179 + 163 / (1 + x^2 + (sin x)^2) = 119.
Proof.
  set (f := fun x => x^179 + 163 / (1 + x^2 + (sin x)^2) - 119).
  assert (H1 : continuous f) by (unfold f; auto_cont).
  assert (f 0 > 0 /\ f (-2) < 0) as H2 by (unfold f; rewrite sin_compat; split; interval).
  pose proof (intermediate_value_theorem_unordered f (-2) 0 0 H1 ltac:(solve_R)) as [x [H3 H4]].
  exists x. unfold f in H4. lra.
Qed.

Lemma lemma_7_3_b : ∃ x, sin x = x - 1.
Proof.
  set (f := fun x => sin x - x + 1).
  assert (H1 : continuous f) by (unfold f; auto_cont).
  assert (f 0 > 0 /\ f 2 < 0) as H2 by (unfold f; rewrite sin_compat; split; interval).
  pose proof (intermediate_value_theorem_unordered f 0 2 0 H1 ltac:(solve_R)) as [x [H3 H4]].
  exists x. unfold f in H4. lra.
Qed.