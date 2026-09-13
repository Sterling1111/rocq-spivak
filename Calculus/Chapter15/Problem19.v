From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_19_a :
  ∫ 0 1 (λ t, 1 / (1 + t^2)) = π / 4.
Proof.
  auto_int.
Qed.

Lemma lemma_15_19_b :
  ∫ 0 ∞ (λ t, 1 / (1 + t^2)) = π / 2.
Proof.
  split.
  - intros x H1. apply theorem_13_3; [lra | auto_cont].
  - assert (H1 : ⟦ lim 0 ⟧ arctan = 0).
    { replace 0 with (arctan 0) at 2 by apply arctan_0. apply continuous_at_arctan. }
    intros ε H2. destruct (H1 ε H2) as [δ [H3 H4]].
    exists (1 / δ). intros x H5.
    assert (H6 : 0 < x) by (pose proof Rdiv_pos_pos 1 δ ltac:(lra) H3; lra).
    assert (H7 : 0 < 1 / x < δ) by solve_R.
    assert (H8 : ∫ 0 x (λ t, 1 / (1 + t^2)) = arctan x).
    { replace (arctan x) with (arctan x - arctan 0) by (rewrite arctan_0; lra).
      apply FTC2; [lra | auto_cont | auto_diff]. }
    rewrite H8.
    assert (H9 : arctan (1 / x) = π / 2 - arctan x).
    { rewrite StdlibCompat.arctan_compat, StdlibCompat.π_compat.
      replace (1 / x) with (/ x) by (field; lra). apply atan_inv; lra. }
    specialize (H4 (1 / x) ltac:(solve_R)). rewrite H9 in H4. solve_R.
Qed.