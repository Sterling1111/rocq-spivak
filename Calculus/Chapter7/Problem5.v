From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_5 : ∀ f a b,
  a < b -> continuous_on f [a, b] -> (∀ x, rational (f x)) -> ∃ c, ∀ x, x ∈ [a, b] -> f x = c.
Proof.
  intros f a b H1 H2 H3. pose proof classic (∃ c : ℝ, ∀ x : ℝ, x ∈ [a, b] → f x = c) as [H4 | H4]; auto.
  assert (H5 : ∀ c, ∃ x, x ∈ [a, b] /\ f x ≠ c).
  {
    intros c. apply not_all_not_ex. intros H5. apply H4. exists c.
    intros x H6. specialize (H5 x). apply not_and_or in H5 as [H5 | H5]; tauto.
  }
  clear H4. specialize (H5 (f a)) as [x [H4 H5]].
  pose proof exists_irrational_between (Rmin (f x) (f a)) (Rmax (f x) (f a)) ltac:(solve_R) as [c [H6 H7]].
  assert (H8 : a < x). { pose proof Rtotal_order a x as [H8 | [H8 | H8]]; subst; solve_R. }
  assert (H9 : continuous_on f [Rmin a x, Rmax a x]). { apply continuous_on_subset with (A2 := [a, b]); auto. intros y. solve_R. }
  pose proof intermediate_value_theorem_unordered f a x c H9 ltac:(solve_R) as [d [H10 H11]].
  specialize (H3 d). subst. contradiction.
Qed.