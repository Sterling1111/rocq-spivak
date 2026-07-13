From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_14 : forall f,
  (forall x, rational x -> f x = x^2) ->
  (forall x, ~ rational x -> f x = 0) ->
  differentiable_at f 0.
Proof.
  intros f H1 H2.
  exists 0.
  assert (H3 : f 0 = 0).
  { rewrite H1; try lra. exists 0%Z, 1%Z. lra. }
  replace (λ h, (f (0 + h) - f 0) / h) with (λ h, f h / h).
  2 : { extensionality h. rewrite H3. simp_zero. reflexivity. }
  apply limit_squeeze with (a := -1) (b := 1) (f1 := λ h, -|h|) (f3 := λ h, |h|); 
  try solve [ auto_limit ].
  intros x H4. apply In_Union_def in H4.
  destruct (classic (rational x)) as [H5 | H5].
  - rewrite (H1 x H5). replace (x^2 / x) with x by solve_R.
    solve_R.
  - rewrite (H2 x H5). solve_R.
Qed.