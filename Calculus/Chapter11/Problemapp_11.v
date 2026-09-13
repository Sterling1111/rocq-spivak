From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_app_11_a : ∀ f D,
  weakly_convex_on f D ->
  (∀ a b, a ∈ D -> b ∈ D -> a <> b ->
   ∃ x, x ∈ D /\ (Rmin a b) < x < (Rmax a b) /\ f x <> (f b - f a) / (b - a) * (x - a) + f a) ->
  convex_on f D.
Proof.
  intros f D H1 H2 a x b H3 H4 H5 H6.
  pose proof H1 a x b H3 H4 H5 H6 as H7.
  destruct (Rlt_dec ((f x - f a) / (x - a)) ((f b - f a) / (b - a))) as [H8 | H8]; auto.
  assert (H9 : (f x - f a) / (x - a) = (f b - f a) / (b - a)) by lra.
  destruct (H2 x b H4 H5 ltac:(solve_R)) as [y [H10 [H11 H12]]].
  assert (H13 : x < y < b) by solve_R.
  pose proof H1 a x y H3 H4 H10 ltac:(lra) as H14.
  pose proof H1 a y b H3 H10 H5 ltac:(lra) as H15.
  assert (H16 : (f y - f a) / (y - a) = (f b - f a) / (b - a)) by lra.
  exfalso. apply H12.
  set (m := (f b - f a) / (b - a)) in *.
  assert (H17 : f x = m * (x - a) + f a).
  { apply Rmult_eq_compat_r with (r := x - a) in H9. field_simplify in H9; lra. }
  assert (H18 : f y = m * (y - a) + f a).
  { apply Rmult_eq_compat_r with (r := y - a) in H16. field_simplify in H16; lra. }
  assert (H19 : f b = m * (b - a) + f a) by (unfold m; field; lra).
  rewrite H17, H18, H19. field; lra.
Qed.
