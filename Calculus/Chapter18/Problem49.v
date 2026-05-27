From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_49 : irrational (log_ 10 2).
Proof.
  intros [a [b H1]].
  symmetry in H1.
  apply log_b_spec in H1; try solve_R. 
  assert (H2 : 2 ^^ b = (10 ^^ (a / b)) ^^ b).
  { rewrite H1. reflexivity. }
  rewrite Rpower_mult in H2; try lra.
  assert (b = 0 \/ b <> 0)%Z as [H3 | H3] by lia.
  - subst. rewrite Rdiv_0_r, Rpower_0 in H1; lra.
  - replace (a / b * b) with (IZR a) in H2 by (field; apply not_0_IZR; auto).
Abort.