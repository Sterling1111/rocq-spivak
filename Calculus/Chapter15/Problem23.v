From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_23_a : ∀ a b,
  b - a > π ->
  ~ one_to_one_on sin [a, b].
Abort.

Lemma lemma_15_23_b : ∀ g g_inv (k : Z),
  (∀ x, x ∈ (k * 2 * π - π / 2, k * 2 * π + π / 2) -> g x = sin x) ->
  inverse_on g g_inv (k * 2 * π - π / 2, k * 2 * π + π / 2) (-1, 1) ->
  ∀ y, y ∈ (-1, 1) ->
  ⟦ der y ⟧ g_inv = (λ y, 1 / √(1 - y^2)).
Proof.
  intros g g_inv k H1 H2 y H3.
  set (K := k * 2 * π) in *.
  assert (H4 : sin (k * π) = 0).
  { apply sin_eq_0. exists k. reflexivity. }
  assert (H5 : sin K = 0 /\ cos K = 1).
  { unfold K. replace (k * 2 * π) with (2 * (k * π)) by ring.
    rewrite sin_2x, cos_2x_3, H4. split; ring. }
  destruct H5 as [H5 H6].
  assert (H7 : ∀ z, z ∈ (-1, 1) -> g_inv z = arcsin z + K).
  { intros z H7.
    destruct H2 as [H8 [H9 [H10 H11]]].
    pose proof H9 z H7 as H12.
    pose proof H11 z H7 as H13.
    rewrite H1 in H13; auto.
    assert (H14 : sin (g_inv z - K) = z).
    { rewrite sin_minus, H5, H6, H13. ring. }
    assert (H15 : arcsin (sin (g_inv z - K)) = g_inv z - K).
    { apply arcsin_spec. split; solve_R. }
    rewrite H14 in H15. lra. }
  apply derivative_at_eq with (f1 := λ z, arcsin z + K).
  - exists (Rmin (y + 1) (1 - y)). split; [solve_R |].
    intros z H8. symmetry. apply H7. split; solve_R.
  - auto_diff.
Qed.
