From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_9_a : forall x y,
  cos x <> 0 -> cos y <> 0 -> cos (x + y) <> 0 ->
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y).
Proof.
  intros x y H1 H2 H3. unfold tan.
  rewrite sin_plus, cos_plus in *.
  field; repeat split; auto.
Qed.

Lemma lemma_15_9_b : forall x y,
  x * y < 1 ->
  arctan x + arctan y = arctan ((x + y) / (1 - x * y)).
Proof.
  intros x y H1.
  pose proof arctan_spec as [H2 [H3 [H4 H5]]].
  pose proof cos_gt_0 as H6.
  assert (H7 : cos (arctan x) > 0) by (apply H6; apply H3; apply Full_intro).
  assert (H8 : cos (arctan y) > 0) by (apply H6; apply H3; apply Full_intro).
  assert (H9 : tan (arctan x) = x) by (apply H5; apply Full_intro).
  assert (H10 : tan (arctan y) = y) by (apply H5; apply Full_intro).
  assert (H11 : cos (arctan x + arctan y) > 0).
  {
    rewrite cos_plus.
    assert (H12 : sin (arctan x) = x * cos (arctan x)).
    { replace (x * cos (arctan x)) with ((sin (arctan x) / cos (arctan x)) * cos (arctan x)) by (unfold tan in H9; rewrite H9; reflexivity); solve_R. }
    assert (H13 : sin (arctan y) = y * cos (arctan y)).
    { replace (y * cos (arctan y)) with ((sin (arctan y) / cos (arctan y)) * cos (arctan y)) by (unfold tan in H10; rewrite H10; reflexivity); solve_R. }
    rewrite H12, H13.
    replace (cos (arctan x) * cos (arctan y) - x * cos (arctan x) * (y * cos (arctan y)))
      with (cos (arctan x) * cos (arctan y) * (1 - x * y)) by ring.
    apply Rmult_gt_0_compat; nra. 
  }
  assert (H12 : (arctan x + arctan y) ∈ (-(π/2), π/2)).
  {
    assert (H13 : -(π/2) < arctan x < π/2) by (apply H3; apply Full_intro).
    assert (H14 : -(π/2) < arctan y < π/2) by (apply H3; apply Full_intro).
    assert (H15 : -π < arctan x + arctan y < π) by lra.
    set (S := arctan x + arctan y) in *.
    assert (S <= -(π/2) \/ -(π/2) < S < π/2 \/ π/2 <= S) as [H17 | [H17 | H17]] by lra.
    - assert (H18 : π <= S + 2 * π <= 3 * π / 2) by lra.
      pose proof π_pos as H19.
      assert ( S + 2 * π = π \/ π < S + 2 * π) as [H21 | H21] by lra.
      + assert (H22 : cos S = -1). { rewrite <- cos_periodic, H21, cos_π; reflexivity. } lra.
      + assert (H22 : π < S + 2 * π < 2 * π) by lra.
        rewrite <- cos_periodic in H11; rewrite cos_on_π_2π in H11; auto.
        assert (H23 : 2 * π - (S + 2 * π) = - S) by lra.
        rewrite H23 in H11.
        assert (H24 : 0 <= - S <= π) by lra.
        rewrite <- cos_on_0_π in H11; auto.
        assert (H25 : - S = π / 2 \/ - S > π / 2) by lra.
        destruct H25 as [H26 | H26].
        * rewrite H26, cos_π_over_2 in H11; lra.
        * assert (H27 : π / 2 ∈ [0, π]) by (split; lra).
          assert (H28 : - S ∈ [0, π]) by (split; lra).
          pose proof cos_decreasing_on (π / 2) (- S) H27 H28 H26 as H29.
          rewrite cos_π_over_2 in H29; lra.
    - split; lra.
    - assert (H18 : π/2 <= S <= π) by lra.
      assert (H19 : S = π / 2 \/ S > π / 2) by lra.
      destruct H19 as [H20 | H20].
      + rewrite H20, cos_π_over_2 in H11; lra.
      + assert (H21 : π / 2 ∈ [0, π]) by (split; lra).
        assert (H22 : S ∈ [0, π]) by (split; lra).
        pose proof cos_decreasing_on (π / 2) S H21 H22 H20 as H23.
        rewrite cos_π_over_2 in H23; lra.
  }
  rewrite <- (H4 (arctan x + arctan y)); [f_equal | exact H12].
  rewrite tan_plus; try lra.
  rewrite H9, H10; reflexivity.
Qed.