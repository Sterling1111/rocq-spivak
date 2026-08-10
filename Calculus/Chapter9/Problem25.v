From Calculus.Chapter9 Require Import Prelude.
From Calculus.Chapter9 Require Import Problem23 Problem24.

Lemma problem_9_25 : ∀ f f' k,
  ⟦ der ^ k ⟧ f = f' ->
  (even f ->
    ((Nat.Even k -> even f') /\
     (Nat.Odd k  -> odd f'))) /\
  (odd f ->
    ((Nat.Even k -> odd f') /\
     (Nat.Odd k  -> even f'))).
Proof.
  intros f f' k H1.
  revert f f' H1.
  induction k as [| k IH].
  - intros f f' H1.
    simpl in H1.
    subst f'.
    split; intros H2; split; intros H3; auto.
    all: destruct H3 as [n H3]; lia.
  - intros f f' H1.
    destruct H1 as [fk [H1 H2]].
    pose proof IH f fk H1 as [IH1 IH2].
    assert (H3 : even fk -> odd f').
    { intros H3 x. rewrite problem_9_23 with (f := fk); auto. rewrite Ropp_involutive. auto. }
    assert (H4 : odd fk -> even f').
    { intros H4 x. rewrite problem_9_24 with (f := fk); auto. rewrite Ropp_involutive; auto. }
    split.
    + intros H5.
      specialize (IH1 H5) as [H6 H7].
      split; intros H8.
      * rewrite Nat.Even_succ in H8.
        apply H4, H7, H8.
      * rewrite Nat.Odd_succ in H8.
        apply H3, H6, H8.
    + intros H5.
      specialize (IH2 H5) as [H6 H7].
      split; intros H8.
      * rewrite Nat.Even_succ in H8.
        apply H3, H7, H8.
      * rewrite Nat.Odd_succ in H8.
        apply H4, H6, H8.
Qed.