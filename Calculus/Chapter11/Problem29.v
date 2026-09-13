From Calculus.Chapter11 Require Import Prelude Problem28.

Lemma lemma_11_29 : ∀ f f' M,
  ⟦ der ⟧ f = f' ->
  (∀ x, x ∈ [0, 1] -> f' x >= M > 0) ->
  ∃ a b, b - a = 1/4 /\ ∀ x, x ∈ [a, b] -> |f x| >= M / 4.
Proof.
  intros f f' M H1 H2.
  destruct (Rgt_le_dec (f (1/2)) 0) as [H4 | H4].
  - exists (3/4), 1. split; [ lra | intros x H5 ].
    assert (H6 : 1/2 < x) by solve_R.
    pose proof lemma_11_28_a (1/2) x M f f' H6 H1 as H7.
    assert (H8 : ∀ t, t ∈ [1/2, x] -> f' t >= M).
    { intros t H8. destruct (H2 t ltac:(solve_R)) as [H9 _]. exact H9. }
    specialize (H7 H8).
    destruct (H2 0 ltac:(solve_R)) as [_ H10].
    solve_R.
  - exists 0, (1/4). split; [ lra | intros x H5 ].
    assert (H6 : x < 1/2) by solve_R.
    pose proof lemma_11_28_a x (1/2) M f f' H6 H1 as H7.
    assert (H8 : ∀ t, t ∈ [x, 1/2] -> f' t >= M).
    { intros t H8. destruct (H2 t ltac:(solve_R)) as [H9 _]. exact H9. }
    specialize (H7 H8).
    destruct (H2 0 ltac:(solve_R)) as [_ H10].
    solve_R.
Qed.
