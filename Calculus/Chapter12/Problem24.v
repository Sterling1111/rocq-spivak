From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_24_a : ∀ f,
  continuous f -> inverse f f -> ∃ x, f x = x.
Proof.
  intros f H1 H2.
  unfold inverse in H2. destruct H2 as [H3 [H4 [H5 H6]]].
  destruct (Rlt_dec (f 0) 0) as [H7 | H7].
  - destruct (intermediate_value_theorem_decreasing (λ x, f x - x) (f 0) 0 0) as [x [H8 H9]].
    + auto.
    + auto_cont.
    + split.
      * replace (f 0 - 0) with (f 0) by lra. lra.
      * replace (f (f 0) - f 0) with (0 - f 0). 2: { rewrite H5; auto. apply Full_intro. } lra.
    + exists x. lra.
  - destruct (Req_dec (f 0) 0) as [H8 | H8].
    + exists 0. auto.
    + destruct (intermediate_value_theorem_decreasing (λ x, f x - x) 0 (f 0) 0) as [x [H9 H10]].
      * lra.
      * auto_cont.
      * split.
        -- replace (f (f 0) - f 0) with (0 - f 0). 2: { rewrite H5; auto. apply Full_intro. } lra.
        -- replace (f 0 - 0) with (f 0) by lra. lra.
      * exists x. lra.
Qed.

Lemma lemma_12_24_c : ∀ f,
  increasing f ->
  inverse f f ->
  ∀ x, f x = x.
Proof.
  intros f H1 H2 x.
  pose proof inverse_spec f f H2 as [H3 H4].
  destruct (Rtotal_order (f x) x) as [H5 | [H5 | H5]]; auto.
  - specialize (H1 (f x) x ltac:(apply Full_intro) ltac:(apply Full_intro) H5).
    rewrite H3 in H1. lra.
  - specialize (H1 x (f x) ltac:(apply Full_intro) ltac:(apply Full_intro) H5).
    rewrite H3 in H1. lra.
Qed.
