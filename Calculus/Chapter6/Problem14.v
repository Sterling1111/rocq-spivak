From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_14_a : ∀ f g h a,
  continuous_at g a -> continuous_at h a -> g a = h a ->
  (∀ x, x >= a -> f x = g x) ->
  (∀ x, x <= a -> f x = h x) ->
  continuous_at f a.
Proof.
  intros f g h a H1 H2 H3 H4 H5. intros ε H6.
  destruct (H1 ε H6) as [δ1 [H7 H8]]. destruct (H2 ε H6) as [δ2 [H9 H10]].
  exists (Rmin δ1 δ2). split; [solve_R|]. intros x H11.
  assert (x = a \/ x > a \/ x < a) as [H12 | [H12 | H12]] by lra.
  - rewrite H12, H4; [|lra]. assert (g a - f a = 0) by (rewrite H4; lra). solve_R.
  - rewrite H4 by lra. assert (f a = g a) by (rewrite H4; lra). rewrite H.
    specialize (H8 x). assert (0 < |x - a| < δ1) by solve_R. apply H8 in H0. solve_R.
  - rewrite H5 by lra. assert (f a = h a) by (rewrite H5; lra). rewrite H.
    specialize (H10 x). assert (0 < |x - a| < δ2) by solve_R. apply H10 in H0. solve_R.
Qed.

Lemma lemma_6_14_b : ∀ f g h a b c,
  a < b < c ->
  continuous_on g [a, b] -> continuous_on h [b, c] ->
  g b = h b ->
  (∀ x, x ∈ [a, b] -> f x = g x) ->
  (∀ x, x ∈ [b, c] -> f x = h x) ->
  continuous_on f [a, c].
Proof.
  intros f g h a b c H1 H2 H3 H4 H5 H6 x H7.
  assert (x ∈ [a, b) \/ x ∈ (b, c] \/ x = b) as [H9 | [H9 | H9]] by solve_R.
  - specialize (H2 x ltac:(solve_R)).
    replace (f x) with (g x) by (rewrite H5; solve_R).
    apply limit_on_local_eq with (D2 := [a, b]) (f2 := g); auto.
    exists (b - x); split; [ solve_R |].
    intros y H10 H11; split; [solve_R | apply H5; solve_R ].
  - specialize (H3 x ltac:(solve_R)).
    replace (f x) with (h x) by (rewrite H6; solve_R).
    apply limit_on_local_eq with (D2 := [b, c]) (f2 := h); auto.
    exists (x - b); split; [ solve_R |].
    intros y H10 H11; split; [solve_R | apply H6; solve_R ].
  - subst. apply limit_imp_limit_on, limit_iff. split.
    + replace (f b) with (g b) by (rewrite H5; solve_R).
      apply limit_left_eq with (f1 := g).
      * exists (b - a); split; [solve_R | intros x H8; rewrite H5; solve_R ].
      * apply continuous_on_closed_interval_iff in H2 as [_ [_ H10]]; solve_R.
    + replace (f b) with (h b) by (rewrite H6; solve_R).
      apply limit_right_eq with (f1 := h).
      * exists (c - b); split; [solve_R | intros x H8; rewrite H6; solve_R ].
      * apply continuous_on_closed_interval_iff in H3 as [_ [H10 _]]; solve_R.
Qed.