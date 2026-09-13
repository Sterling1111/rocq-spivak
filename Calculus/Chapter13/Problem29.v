From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_29 : ∀ f a b,
  a < b ->
  integrable_on a b f ->
  ∃ x, x ∈ [a, b] /\ ∫ a x f = ∫ x b f.
Abort.

Lemma lemma_13_29_counterexample : ∀ a b,
  a < b -> ∃ f : R -> R,
  integrable_on a b f /\
  (∀ x, x ∈ (a, b) -> ∫ a x f <> ∫ x b f).
Proof.
  intros a b H1. set (f := λ x, (a+b)/2-x).
  exists f. split.
  - apply theorem_13_3; try lra. unfold f. auto_cont.
  - intros x H2 H3.
    assert (H4 : ∫ a x f = (x-a)*(b-x)/2).
    {
      replace ((x-a)*(b-x)/2) with
        (((a+b)*x/2-x^2/2) - ((a+b)*a/2-a^2/2)) by field.
      apply FTC2 with (g := λ t, (a+b)*t/2-t^2/2).
      - solve_R.
      - unfold f. auto_cont.
      - unfold f. auto_diff.
    }
    assert (H5 : ∫ x b f = -(x-a)*(b-x)/2).
    {
      replace (-(x-a)*(b-x)/2) with
        (((a+b)*b/2-b^2/2) - ((a+b)*x/2-x^2/2)) by field.
      apply FTC2 with (g := λ t, (a+b)*t/2-t^2/2).
      - solve_R.
      - unfold f. auto_cont.
      - unfold f. auto_diff.
    }
    assert (H6 : 0 < (x-a)*(b-x)) by (apply Rmult_lt_0_compat; solve_R).
    rewrite H4, H5 in H3. nra.
Qed.
