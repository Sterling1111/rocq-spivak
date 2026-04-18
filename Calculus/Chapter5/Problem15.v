From Calculus.Chapter5 Require Import Prelude Problem14.

Section Problem15.

Variable α : R.
Hypothesis H1 : ⟦ lim 0 ⟧ (λ x, sin x / x) = α.
Hypothesis H2 : α ≠ 0.

Lemma lemma_5_15_i : ⟦ lim 0 ⟧ (fun x => sin (3 * x) / x) = 3 * α.
Proof.
  apply lemma_5_14_a; solve_R.
Qed.

Lemma lemma_5_15_ii : forall a b,
  b <> 0 -> ⟦ lim 0 ⟧ (fun x => sin (a * x) / sin (b * x)) = a / b.
Proof.
  intros a b H3. destruct (Req_dec a 0) as [H4 | H4].
  - rewrite H4.
    replace (0 / b) with 0 by solve_R.
    apply limit_eq with (f1 := fun x => 0).
    2 : { apply limit_const. }
    exists 1. split; [solve_R |].
    intros x H5. rewrite Rmult_0_l, sin_0, Rdiv_0_l. reflexivity.
  - apply limit_eq with (f1 := fun x => (sin (a * x) / x) / (sin (b * x) / x)).
    {
      exists (Rmin 1 (π / (2 * |b|))). split.
      - pose proof π_bounds; pose proof Rdiv_pos_pos π (2 * |b|); solve_R.
      - intros x H5. field; split; [| solve_R]. apply lemma_sin_neq_0_neighborhood; solve_R.
    }
    replace (a / b) with ((a * α) / (b * α)) by solve_R.
    apply limit_div.
    + apply lemma_5_14_a; auto.
    + apply lemma_5_14_a; auto.
    + solve_R.
Qed.

Lemma lemma_5_15_iii : ⟦ lim 0 ⟧ (fun x => (sin x)^2 / x) = 0.
Proof. Abort.

Lemma lemma_5_15_iv : ⟦ lim 0 ⟧ (fun x => (sin (2 * x))^2 / x^2) = 4 * α^2.
Proof. Abort.

Lemma lemma_5_15_v : ⟦ lim 0 ⟧ (fun x => (1 - cos x) / x^2) = α^2 / 2.
Proof. Abort.

Lemma lemma_5_15_vi : ⟦ lim 0 ⟧ (fun x => ((tan x)^2 + 2 * x) / (x + x^2)) = 2.
Proof. Abort.

Lemma lemma_5_15_vii : ⟦ lim 0 ⟧ (fun x => x * sin x / (1 - cos x)) = 2 / α.
Proof. Abort.

Lemma lemma_5_15_viii (x : R) : ⟦ lim 0 ⟧ (fun h => (sin (x + h) - sin x) / h) = α * cos x.
Proof. Abort.

Lemma lemma_5_15_ix : ⟦ lim 1 ⟧ (fun x => sin (x^2 - 1) / (x - 1)) = 2 * α.
Proof. Abort.

Lemma lemma_5_15_x : ⟦ lim 0 ⟧ (fun x => x^2 * (3 + sin x) / (x + sin x)^2) = 3 / (1 + α)^2.
Proof. Abort.

Lemma lemma_5_15_xi : ⟦ lim 1 ⟧ (fun x => (x^2 - 1)^3 * (sin (1 / (x - 1)))^3) = 0.
Proof. Abort.

End Problem15.