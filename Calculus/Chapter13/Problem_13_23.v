From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_23_a : forall f a b m M,
  a < b ->
  integrable_on a b f ->
  (forall x, x ∈ [a, b] -> m <= f x <= M) ->
  exists μ, m <= μ <= M /\ ∫ a b f = (b - a) * μ.
Proof.
  intros f a b m M H1 H2 H3.
  pose proof theorem_13_7 a b f m M ltac:(lra) H2 H3 as [H4 H5].
  exists ((∫ a b f) / (b - a)). repeat split; [ | | solve_R ];
  (apply Rmult_le_reg_r with (r := (b - a)); field_simplify; lra).
Qed.

Lemma lemma_13_23_b : forall f a b,
  a < b ->
  continuous_on f [a, b] ->
  exists ξ, ξ ∈ [a, b] /\ ∫ a b f = (b - a) * f ξ.
Proof.
  intros f a b H1 H2.
  
  pose proof continuous_on_interval_attains_minimum f a b H1 H2 as [m [H3 H4]].
  pose proof continuous_on_interval_attains_maximum f a b H1 H2 as [M [H5 H6]].

  assert (H7 : integrable_on a b f) by (apply theorem_13_3; solve_R).

  assert (H8 : (∀ x : ℝ, x ∈ [a, b] → f m ≤ f x ≤ f M)).
  { intros x H8. specialize (H4 x H8). specialize (H6 x H8). lra. }

  pose proof lemma_13_23_a f a b (f m) (f M) H1 H7 H8 as [μ [H9 H10]].

  destruct (Rtotal_order m M) as [H11 | [H11 | H11]].
  - assert (H12 : continuous_on f [m, M]).
    { apply continuous_on_subset with (A2 := [a, b]); intros x; solve_R. }
    pose proof intermediate_value_theorem f m M μ H11 H12 H9 as [x [H13 H14]].
    exists x; solve_R.
  - exists m; subst; solve_R.
  - assert (H12 : continuous_on f [M, m]).
    { apply continuous_on_subset with (A2 := [a, b]); intros x; solve_R. }
    pose proof intermediate_value_theorem_decreasing f M m μ H11 H12 H9 as [x [H13 H14]].
    exists x; solve_R.
Qed.

Lemma lemma_13_23_c : forall a b,
  a < b ->
  exists (f : ℝ -> ℝ),
    integrable_on a b f /\ ~ continuous_on f [a, b] /\
    ~ (exists ξ, ξ ∈ [a, b] /\ ∫ a b f = (b - a) * f ξ).
Proof.

Admitted.

Lemma lemma_13_23_d : forall f g a b,
  a < b ->
  continuous_on f [a, b] ->
  integrable_on a b g ->
  nonnegative_on g [a, b] ->
 exists ξ, ξ ∈ [a, b] /\ ∫ a b (f ⋅ g) = f ξ * ∫ a b g.
Proof.
Admitted.

Lemma lemma_13_23_e : forall f g a b,
  a < b ->
  continuous_on f [a, b] ->
  integrable_on a b g ->
  nonpositive_on g [a, b] ->
 exists ξ, ξ ∈ [a, b] /\ ∫ a b (f ⋅ g) = f ξ * ∫ a b g.
Proof.
Admitted.

Lemma lemma_13_23_f : forall a b,
  a < b ->
  exists (f g : ℝ -> ℝ),
    continuous_on f [a, b] /\
    integrable_on a b g /\
    ~ (exists ξ, ξ ∈ [a, b] /\ ∫ a b (f ⋅ g) = f ξ * ∫ a b g).
Proof.
Admitted.