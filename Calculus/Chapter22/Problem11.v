From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_11_a : ∀ a L,
  ⟦ lim ⟧ a = L -> bounded a.
Proof.
  intros a L H1. apply convergent_bounded. exists L. auto.
Qed.

Lemma lemma_22_11_b : ∀ a,
  ⟦ lim ⟧ a = 0 -> (∃ n, a n > 0) ->
  ∃ n, ∀ m, a m <= a n.
Proof.
  intros a H1 [k H2]. destruct (H1 (a k) H2) as [N H3].
  destruct (INR_unbounded N) as [m H4].
  destruct (exists_max_of_sequence_on_interval a 0 (Nat.max k m) ltac:(lia))
    as [j [H5 H6]].
  exists j. intros n. destruct (le_lt_dec n (Nat.max k m)) as [H7 | H7].
  - apply H6. lia.
  - pose proof (lt_INR _ _ H7) as H8.
    pose proof (le_INR _ _ (Nat.le_max_r k m)) as H9.
    specialize (H3 n ltac:(lra)). specialize (H6 k ltac:(lia)). solve_R.
Qed.
