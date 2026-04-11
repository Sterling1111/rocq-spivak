From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_30_i : ∀ f L,
  ⟦ lim 0⁺ ⟧ f = L <-> ⟦ lim 0⁻ ⟧ (fun x => f (-x)) = L.
Proof.
  intros f L. split.
  - intros H1 ε H2.
    specialize (H1 ε H2) as [δ [H3 H4]].
    exists δ; split; auto.
    intros x H5.
    specialize (H4 (-x) ltac:(solve_R)).
    solve_R.
  - intros H1 ε H2.
    specialize (H1 ε H2) as [δ [H3 H4]].
    exists δ; split; auto.
    intros x H5.
    specialize (H4 (-x) ltac:(solve_R)).
    rewrite Ropp_involutive in H4.
    apply H4.
Qed.

Lemma lemma_5_30_ii : ∀ f L,
  ⟦ lim 0 ⟧ (fun x => f (|x|)) = L <-> ⟦ lim 0⁺ ⟧ f = L.
Proof.
  intros f L. split.
  - intros H1 ε H2.
    specialize (H1 ε H2) as [δ [H3 H4]].
    exists δ; split; auto.
    intros x H5.
    specialize (H4 x ltac:(solve_R)).
    replace (|x|) with x in H4 by solve_R.
    apply H4.
  - intros H1 ε H2.
    specialize (H1 ε H2) as [δ [H3 H4]].
    exists δ; split; auto.
    intros x H5.
    specialize (H4 (|x|) ltac:(solve_R)).
    apply H4.
Qed.

Lemma lemma_5_30_iii : ∀ (f : R -> R) L,
  ⟦ lim 0 ⟧ (fun x => f (x^2)) = L <-> ⟦ lim 0⁺ ⟧ f = L.
Proof.
  intros f L. split.
  - intros H1 ε H2.
    specialize (H1 ε H2) as [δ [H3 H4]].
    exists (δ^2); split; [solve_R |].
    intros x H5.
    assert (H6 : 0 < √x < δ).
    {
      destruct H5 as [H5 H6]. split; [apply sqrt_lt_R0; lra | ].
      rewrite <- sqrt_pow2; try lra.
      apply (sqrt_lt_1_alt x (δ^2)). lra.
    }
    specialize (H4 (√x) ltac:(solve_R)).
    replace ((√x)^2) with x in H4. 2 : { rewrite pow2_sqrt; solve_R. }
    solve_R.
  - intros H1 ε H2.
    specialize (H1 ε H2) as [δ [H3 H4]].
    exists (√δ); split; [ apply sqrt_lt_R0; auto |].
    intros x H5.
    assert (H6 : x^2 < δ).
    {
      apply Rlt_le_trans with ((√δ) ^ 2); [solve_R |].
      rewrite pow2_sqrt; solve_R.
    }
    specialize (H4 (x^2) ltac:(solve_R)).
    apply H4.
Qed.