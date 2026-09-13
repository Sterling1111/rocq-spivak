From Calculus.Chapter22 Require Import Prelude.

From Calculus.Chapter8 Require Import Problem18.

Definition limit_point_of_set (x : ℝ) (A : Ensemble ℝ) : Prop :=
  ∀ ε, ε > 0 -> ∃ a, a ∈ A /\ |x - a| < ε /\ x <> a.

Lemma lemma_22_30_a_i : ∀ x,
  limit_point_of_set x (λ y, ∃ n : ℕ, (0 < n)%nat /\ y = 1 / n) <->
  x = 0.
Abort.

Lemma lemma_22_30_a_ii : ∀ x,
  limit_point_of_set x (λ y, ∃ n m : ℕ,
    (0 < n)%nat /\ (0 < m)%nat /\ y = 1 / n + 1 / m) <->
  x = 0 \/ ∃ n : ℕ, (0 < n)%nat /\ x = 1 / n.
Abort.

Lemma lemma_22_30_a_iii : ∀ x,
  limit_point_of_set x (λ y, ∃ n : ℕ,
    (0 < n)%nat /\ y = (-1)^n * (1 + 1 / n)) <->
  x = -1 \/ x = 1.
Abort.

Lemma lemma_22_30_a_iv : ∀ x,
  ~ limit_point_of_set x (λ y, ∃ n : ℤ, y = n).
Proof.
  intros x H1.
  destruct (H1 (1/2) ltac:(lra)) as [y [[i H2] [H3 H4]]].
  assert (H5 : 0 < Rmin (1/2) (Rabs (x-y))) by solve_R.
  destruct (H1 (Rmin (1/2) (Rabs (x-y))) H5) as [z [[j H6] [H7 H8]]].
  assert (H9 : -1 < i-j < 1) by (rewrite <- H2, <- H6; solve_R).
  assert (H10 : (j-1 < i < j+1)%Z).
  { split; apply lt_IZR; rewrite ?minus_IZR, ?plus_IZR; simpl; lra. }
  assert (H11 : i = j) by lia.
  assert (H12 : y = z) by congruence. subst z. solve_R.
Qed.

Lemma lemma_22_30_a_v : ∀ x, limit_point_of_set x rational.
Proof.
  intros x ε H1.
  destruct (exists_rational_between x (x+ε) ltac:(lra)) as [r [H2 H3]].
  exists r. repeat split; auto; solve_R.
Qed.

Lemma lemma_22_30_b : ∀ x A,
  limit_point_of_set x A <->
  ∀ ε, ε > 0 -> Infinite_set (λ a, a ∈ A /\ |x - a| < ε).
Abort.

Lemma lemma_22_30_c : ∀ A l u,
  Infinite_set A -> has_lower_bound A -> has_upper_bound A ->
  lim_sup A u -> is_lub (λ x, almost_lower_bound A x) l ->
  limit_point_of_set u A /\ limit_point_of_set l A /\
  ∀ x, limit_point_of_set x A -> l <= x <= u.
Abort.

Lemma lemma_22_30_d : ∀ A a b,
  a <= b -> Infinite_set A -> A ⊆ [a, b] ->
  ∃ x, x ∈ [a, b] /\ limit_point_of_set x A.
Abort.

Lemma lemma_22_30_e : ∀ A a b,
  a <= b -> Infinite_set A -> A ⊆ [a, b] ->
  ∃ x, x ∈ [a, b] /\ limit_point_of_set x A.
Abort.
