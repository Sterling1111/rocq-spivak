From Calculus.Chapter9 Require Import Prelude.
From Calculus.Chapter3 Require Import Problem7.

Lemma lemma_9_20_a : ∀ a,
  let f := (λ x : ℝ, x^4) in
  let d := (λ x, f x - tangent_line f a x) in
  ∃ l, ∀ x, let P := polynomial l in d x = (x - a)^2 * P x.
Proof.
  intros a f d.
  exists [1; 2 * a; 3 * a^2].
  intros x P.
  replace (P x) with (x^2 + 2*a*x + 3*a^2).
  2 : { unfold P, polynomial; simpl; sum_simpl; reflexivity. }
  unfold d, tangent_line, f.
  compute_Der.
  field_simplify.
  reflexivity.
Qed.

Lemma lemma_9_20_b : ∀ l1 a,
  let f := polynomial l1 in
  let d := (λ x, f x - tangent_line f a x) in
  (∀ x, x <> a -> d x / (x - a) = (f x - f a) / (x - a) - ⟦ Der a ⟧ f) /\
  (∃ l2, let P1 := polynomial l2 in
    (∀ x, x <> a -> P1 x = d x / (x - a)) /\ 
    ⟦ lim a ⟧ P1 = 0 /\ 
    P1 a = 0) /\
  (∃ l3, let P2 := polynomial l3 in 
    ∀ x, d x = (x - a)^2 * P2 x).
Proof.
  intros l1 a f d.
  repeat split.
  - intros x H1.
    unfold d, tangent_line. solve_R.
  - assert (H1 : polynomial (poly_sub l1 [f a]) a = 0).
    { rewrite eval_poly_sub, poly_const_eval. unfold f. lra. }
    destruct (lemma_3_7_b (poly_sub l1 [f a]) a H1) as [l2 H2].
    assert (H3 : ∀ x, f x = (x - a) * polynomial l2 x + f a).
    { intros x. pose proof (H2 x) as H3. rewrite eval_poly_sub, poly_const_eval in H3. unfold f in *. lra. }
Abort.