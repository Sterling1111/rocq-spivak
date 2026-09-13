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
  assert (H1 : polynomial (poly_sub l1 [f a]) a = 0).
  { rewrite eval_poly_sub, poly_const_eval. unfold f. lra. }
  destruct (lemma_3_7_b (poly_sub l1 [f a]) a H1) as [l2 H2].
  assert (H3 : ∀ x, f x = (x - a) * polynomial l2 x + f a).
  { intros x. pose proof (H2 x) as H3. rewrite eval_poly_sub, poly_const_eval in H3. unfold f in *. lra. }
  assert (H4 : ⟦ der a ⟧ f = (λ _, ⟦ Der a ⟧ f)).
  { apply derive_at_spec; [apply differentiable_poly | reflexivity]. }
  assert (H5 : ⟦ lim a ⟧ (λ x, (f x - f a) / (x - a)) = ⟦ Der a ⟧ f).
  {
    replace a with (0 + a) at 1 by lra.
    rewrite <- limit_shift with (a := 0) (c := a).
    apply limit_eq' with (f1 := λ h, (f (a + h) - f a) / h); auto.
    intros h. replace (h + a - a) with h by lra. rewrite Rplus_comm. reflexivity.
  }
  set (l3 := poly_sub l2 [⟦ Der a ⟧ f]).
  assert (H6 : ∀ x, polynomial l3 x = polynomial l2 x - ⟦ Der a ⟧ f).
  { intros x. unfold l3. rewrite eval_poly_sub, poly_const_eval. reflexivity. }
  assert (H7 : ⟦ lim a ⟧ (polynomial l3) = 0).
  {
    replace 0 with (⟦ Der a ⟧ f - ⟦ Der a ⟧ f) by lra.
    apply limit_eq with (f1 := λ x, (f x - f a) / (x - a) - ⟦ Der a ⟧ f).
    - exists 1. split; [lra |]. intros x H7. rewrite H6, (H3 x). solve_R.
    - apply limit_minus; [exact H5 | apply limit_const].
  }
  assert (H8 : polynomial l3 a = 0).
  { eapply limit_unique; [apply continuous_at_polynomial | exact H7]. }
  split.
  - intros x H9. unfold d, tangent_line. solve_R.
  - split.
    + exists l3. simpl. split; [| auto].
      intros x H9. rewrite H6. unfold d, tangent_line. rewrite (H3 x). solve_R.
    + destruct (lemma_3_7_b l3 a H8) as [l4 H9].
      exists l4. intros P2 x.
      pose proof (H9 x) as H10. rewrite H6 in H10.
      unfold d, tangent_line, P2. rewrite (H3 x). nra.
Qed.
