From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_17 : ∀ f β,
  0 < β < 1 → (∀ x, |f x| ≥ |x| ^^ β) → f 0 = 0 → ¬ differentiable_at f 0.
Proof.
  intros f β H1 H2 H3 [L H4].
  pose proof (limit_locally_bounded (λ h, (f (0 + h) - f 0) / h) 0 L H4) as [δ1 [M [H5 [H6 H7]]]].
  assert (H8 : β - 1 < 0) by lra.
  pose proof (Rpower_negative_unbounded_zero (β - 1) M H8) as [δ2 [H9 H10]].
  set (h := Rmin (δ1 / 2) (δ2 / 2)).
  assert (H11 : h > 0) by (unfold h; apply Rmin_pos; lra).
  assert (H12 : 0 < |h - 0| < δ1) by (unfold h; solve_R).
  assert (H13 : 0 < h < δ2) by (unfold h; solve_R).
  specialize (H7 h H12).
  specialize (H10 h H13).
  pose proof (H2 h) as H14.
  replace (|h|) with h in H14 by solve_R.
  assert (H15 : |(f h - f 0) / h| >= h ^^ (β - 1)).
  {
    rewrite H3.
    replace (f h - 0) with (f h) by lra.
    pose proof Rinv_pos h H11 as H15.
    unfold Rdiv. rewrite Rabs_mult.
    replace (|/ h|) with (/ h) by solve_R.
    replace (h ^^ (β - 1)) with (h ^^ β * / h).
    2: { rewrite Rpower_minus; [|lra]. unfold Rdiv. rewrite Rpower_1; [|lra]. reflexivity. }
    solve_R.
  }
  rewrite Rplus_0_l in H7. lra.
Qed.