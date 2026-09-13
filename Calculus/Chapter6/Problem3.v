From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_3_a : ∀ f,
  (∀ x, |f x| <= |x|) -> continuous_at f 0.
Proof.
  intros f H1 ε H2. exists ε. split; [lra|]. intros x H3.
  assert (f 0 = 0) as H4. { pose proof (H1 0). solve_R. }
  rewrite H4. pose proof (H1 x). solve_R.
Qed.

Lemma lemma_6_3_b :
  ∃ f, (∀ x, |f x| <= |x|) /\ (∀ a, a <> 0 -> ~ continuous_at f a).
Proof.
  set (f := λ x : R, if excluded_middle_informative (rational x) then x else 0).
  exists f. split.
  - intros x. unfold f. destruct (excluded_middle_informative (rational x)); solve_R.
  - intros a H1 H2. specialize (H2 (|a| / 4) ltac:(solve_R)) as [δ [H3 H4]].
    set (δ' := Rmin δ (|a| / 4)).
    destruct (exists_irrational_between a (a + δ') ltac:(unfold δ'; solve_R)) as [x [H5 H6]].
    destruct (exists_rational_between a (a + δ') ltac:(unfold δ'; solve_R)) as [y [H7 H8]].
    unfold δ' in *.
    specialize (H4 x ltac:(solve_R)) as H9.
    specialize (H4 y ltac:(solve_R)) as H10.
    unfold f in H9, H10.
    destruct (excluded_middle_informative (rational x)); try contradiction.
    destruct (excluded_middle_informative (rational y)); try contradiction.
    solve_R.
Qed.

Lemma lemma_6_3_c : ∀ f g,
  continuous_at g 0 -> g 0 = 0 ->
  (∀ x, |f x| <= |g x|) ->
  continuous_at f 0.
Proof.
  intros f g H1 H2 H3 ε H4. specialize (H1 ε H4) as [δ [H5 H6]].
  exists δ. split; [lra|]. intros x H7.
  assert (f 0 = 0) as H8. { pose proof (H3 0). rewrite H2 in H. solve_R. }
  rewrite H8, H2 in *. pose proof (H3 x). specialize (H6 x H7). solve_R.
Qed.
