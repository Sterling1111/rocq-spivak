From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_28_a : ∀ f (I : Ensemble ℝ) x a,
  x ∈ I ->
  uniformly_continuous_on f (λ q, q ∈ I /\ rational q) ->
  (∀ n, a n ∈ I /\ rational (a n)) ->
  ⟦ lim ⟧ a = x -> convergent_sequence (λ n, f (a n)).
Proof.
  intros f I x a H1 H2 H3 H4. apply cauchy_convergence_criterion.
  assert (H5 : cauchy_sequence a).
  { apply cauchy_convergence_criterion. exists x. auto. }
  intros ε H6. destruct (H2 ε H6) as [δ [H7 H8]].
  destruct (H5 δ H7) as [N H9]. exists N.
  intros n m H10 H11. apply H8; [exact (H3 n) | exact (H3 m) | auto].
Qed.

Lemma lemma_22_28_b : ∀ f (I : Ensemble ℝ) x a b L M,
  x ∈ I ->
  uniformly_continuous_on f (λ q, q ∈ I /\ rational q) ->
  (∀ n, a n ∈ I /\ rational (a n)) ->
  (∀ n, b n ∈ I /\ rational (b n)) ->
  ⟦ lim ⟧ a = x -> ⟦ lim ⟧ b = x ->
  ⟦ lim ⟧ (λ n, f (a n)) = L ->
  ⟦ lim ⟧ (λ n, f (b n)) = M -> L = M.
Proof.
  intros f I x a b L M H1 H2 H3 H4 H5 H6 H7 H8.
  apply NNPP. intros H9.
  assert (H10 : 0 < |L-M|) by (apply Rabs_pos_lt; lra).
  destruct (H2 (|L-M|/3) ltac:(lra)) as [δ [H11 H12]].
  destruct (H5 (δ/2) ltac:(lra)) as [N1 H13].
  destruct (H6 (δ/2) ltac:(lra)) as [N2 H14].
  destruct (H7 (|L-M|/3) ltac:(lra)) as [N3 H15].
  destruct (H8 (|L-M|/3) ltac:(lra)) as [N4 H16].
  destruct (INR_unbounded (Rmax (Rmax N1 N2) (Rmax N3 N4))) as [n H17].
  specialize (H13 n ltac:(solve_R)). specialize (H14 n ltac:(solve_R)).
  specialize (H15 n ltac:(solve_R)). specialize (H16 n ltac:(solve_R)).
  specialize (H12 (a n) (b n) (H3 n) (H4 n) ltac:(solve_R)). solve_R.
Qed.

Lemma lemma_22_28_c : ∀ f (I : Ensemble ℝ),
  (∀ x, x ∈ I -> ∃ a : sequence,
    (∀ n, a n ∈ I /\ rational (a n)) /\ ⟦ lim ⟧ a = x) ->
  uniformly_continuous_on f (λ q, q ∈ I /\ rational q) ->
  ∃ F,
    (∀ q, q ∈ I -> rational q -> F q = f q) /\
    (∀ x a, x ∈ I ->
      (∀ n, a n ∈ I /\ rational (a n)) ->
      ⟦ lim ⟧ a = x -> ⟦ lim ⟧ (λ n, f (a n)) = F x) /\
    uniformly_continuous_on F I.
Abort.
