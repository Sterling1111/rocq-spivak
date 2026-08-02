From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_16 : ∀ f a b,
  ¬ bounded_on f [a, b] ->
  ¬ bounded_on f [a, (a + b)/2] \/ 
  ¬ bounded_on f [(a + b)/2, b].
Proof.
  intros f a b H1.
  apply not_and_or.
  intros [[[m1 H2] [M1 H3]] [[m2 H4] [M2 H5]]].
  apply H1.
  split; [exists (Rmin m1 m2) | exists (Rmax M1 M2)]; intros y [x [H6 H7]]; subst y;
  destruct (Rle_dec x ((a + b) / 2)) as [H8 | H8];
    [ specialize (H2 (f x) ltac:(exists x; solve_R)) | 
      specialize (H4 (f x) ltac:(exists x; solve_R)) | 
      specialize (H3 (f x) ltac:(exists x; solve_R)) |
      specialize (H5 (f x) ltac:(exists x; solve_R))
    ]; 
  solve_R.
Qed.