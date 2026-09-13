From Calculus.Chapter22 Require Import Prelude.

Definition newton_step (f : ℝ -> ℝ) (x : ℝ) : ℝ :=
  x - f x / (⟦ Der ⟧ f) x.

Fixpoint newton_sequence (f : ℝ -> ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  match n with
  | O => x
  | S k => newton_step f (newton_sequence f x k)
  end.

Lemma lemma_22_14_a : ∀ f x y,
  differentiable_at f x -> (⟦ Der ⟧ f) x <> 0 ->
  (tangent_line f x y = 0 <-> y = newton_step f x).
Proof.
  intros f x y H1 H2. unfold tangent_line, newton_step, derive_at.
  change ((⟦ Der ⟧ f) x * (y-x) + f x = 0 <->
    y = x - f x / (⟦ Der ⟧ f) x).
  assert (H3 : (f x / (⟦ Der ⟧ f) x) * (⟦ Der ⟧ f) x = f x)
    by (field; auto).
  split; intros H4; nra.
Qed.

Section NewtonConvergence.
  Variables (f : ℝ -> ℝ) (c x : ℝ).
  Hypothesis Hf : nth_differentiable 2 f.
  Hypothesis Hpos : ∀ t, 0 < (⟦ Der ⟧ f) t /\ 0 < (⟦ Der ^ 2 ⟧ f) t.
  Hypothesis Hroot : f c = 0.
  Hypothesis Hstart : f x > 0.

  Lemma lemma_22_14_b :
    decreasing (newton_sequence f x) /\
    ∀ n, c < newton_sequence f x n.
  Abort.

  Lemma lemma_22_14_c : ∀ k,
    let xk := newton_sequence f x k in
    let δk := xk - c in
    let δnext := newton_sequence f x (S k) - c in
    ∃ ξ η,
      c < ξ < xk /\ c < η < xk /\
      δk = f xk / (⟦ Der ⟧ f) ξ /\
      δnext = f xk / (⟦ Der ⟧ f) ξ - f xk / (⟦ Der ⟧ f) xk /\
      δnext = f xk / ((⟦ Der ⟧ f) ξ * (⟦ Der ⟧ f) xk) *
                (⟦ Der ^ 2 ⟧ f) η * (xk - ξ) /\
      δnext <= (⟦ Der ^ 2 ⟧ f) η / (⟦ Der ⟧ f) xk * δk ^ 2.
  Abort.

  Lemma lemma_22_14_d : ∀ m M,
    m = (⟦ Der ⟧ f) c ->
    is_glb (λ y, ∃ t, t ∈ [c, x] /\ y = (⟦ Der ⟧ f) t) m ->
    is_lub (λ y, ∃ t, t ∈ [c, x] /\ y = (⟦ Der ^ 2 ⟧ f) t) M ->
    x - c < m / M ->
    ⟦ lim ⟧ (newton_sequence f x) = c.
  Abort.

End NewtonConvergence.

Lemma lemma_22_14_e : ∀ A x,
  x <> 0 -> newton_step (λ t, t^2 - A) x = (x + A / x) / 2.
Proof.
  intros A x H1. unfold newton_step.
  assert (H2 : ⟦ der ⟧ (λ t, t^2 - A) = (λ t, 2*t)) by auto_diff.
  rewrite (derivative_imp_derive _ _ H2).
  field. auto.
Qed.
