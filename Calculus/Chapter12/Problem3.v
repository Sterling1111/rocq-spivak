From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_3_a : forall f f_inv,
  increasing f ->
  inverse f f_inv ->
  increasing f_inv.
Proof.
  intros f f_inv H1 [H2 [H3 [H4 H5]]] x y H6 H7 H8.
  destruct (Rlt_dec (f_inv x) (f_inv y)) as [H9 | H9].
  - exact H9.
  - assert (H10 : f_inv y <= f_inv x) by lra.
    destruct H10 as [H10 | H10].
    + specialize
        (H1 (f_inv y) (f_inv x)
            ltac:(apply Full_intro)
            ltac:(apply Full_intro)
            H10).
      rewrite H5 in H1; try apply Full_intro.
      rewrite H5 in H1; try apply Full_intro.
      lra.
    + assert (H11 : x = y).
      {
        rewrite <- (H5 x ltac:(apply Full_intro)).
        rewrite <- (H5 y ltac:(apply Full_intro)).
        rewrite H10.
        reflexivity.
      }
      lra.
Qed.

Lemma lemma_12_3_b : forall f f_inv,
  decreasing f ->
  inverse f f_inv ->
  decreasing f_inv.
Proof.
  intros f f_inv H1 [H2 [H3 [H4 H5]]] x y H6 H7 H8.
  destruct (Rlt_dec (f_inv y) (f_inv x)) as [H9 | H9].
  - exact H9.
  - assert (H10 : f_inv x <= f_inv y) by lra.
    destruct H10 as [H10 | H10].
    + specialize
        (H1 (f_inv x) (f_inv y)
            ltac:(apply Full_intro)
            ltac:(apply Full_intro)
            H10).
      rewrite H5 in H1; try apply Full_intro.
      rewrite H5 in H1; try apply Full_intro.
      lra.
    + assert (H11 : x = y).
      {
        rewrite <- (H5 x ltac:(apply Full_intro)).
        rewrite <- (H5 y ltac:(apply Full_intro)).
        rewrite H10.
        reflexivity.
      }
      lra.
Qed.