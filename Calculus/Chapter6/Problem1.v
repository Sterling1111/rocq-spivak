From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_1_i :
  exists f, continuous f /\ forall x, x <> 2 -> f x = (x^2 - 4) / (x - 2).
Proof. 
  exists (λ x, x + 2). split.
  - auto_cont.
  - intros x H1. field; lra.
Qed.

Lemma lemma_6_1_ii :
  ~ (exists f, continuous f /\ forall x, x <> 0 -> f x = |x| / x).
Proof.
  intros [f [H1 H2]].
  specialize (H1 0 1 ltac:(lra)) as [δ [H1 H3]].
  specialize (H2 (δ / 2) ltac:(lra)) as H4.
  specialize (H2 (-δ / 2) ltac:(lra)).
  replace (|(- δ / 2)| / (- δ / 2)) with (-1) in H2 by solve_R.
  replace (|(δ / 2)| / (δ / 2)) with (1) in H4 by solve_R.
  specialize (H3 (δ / 2) ltac:(solve_R)) as H5.
  specialize (H3 (-δ / 2) ltac:(solve_R)).
  rewrite H2, H4 in *.
  solve_R.
Qed.

Lemma lemma_6_1_iii :
  exists f, continuous f /\ forall x, irrational x -> f x = 0.
Proof.
  exists (λ _, 0). split.
  - auto_cont.
  - intros x _. reflexivity.
Qed.