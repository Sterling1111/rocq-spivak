From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_11_a : ∀ a : sequence,
  (∀ n, a n > 0) -> 
  (∀ n, a (S n) <= a n / 2) ->
  ∀ ε : ℝ, ε > 0 -> ∃ n : ℕ, a n < ε.
Proof.
  intros a H1 H2 ε H3.
  assert (H4 : ∀ n, a n * 2 ^ n <= a 0%nat).
  { induction n as [| n IH].
    - simpl. lra.
    - specialize (H2 n). pose proof Rpow_gt_0 n 2 ltac:(lra) as H5.
      simpl. nra. }
  destruct (INR_unbounded (a 0%nat / ε)) as [n H5].
  exists n. specialize (H4 n).
  pose proof n_lt_pow2_n n as H6.
  assert (H7 : a 0%nat / ε * ε = a 0%nat) by (field; lra).
  pose proof Rpow_gt_0 n 2 ltac:(lra) as H8. nra.
Qed.
