From Calculus.Chapter8 Require Import Prelude.

Definition dense (A : Ensemble ℝ) :=
  ∀ x y : ℝ, x < y -> ∃ z, z ∈ A /\ z ∈ (x, y).

Lemma lemma_8_6_a : ∀ f A,
  continuous f -> dense A -> (∀ x, x ∈ A -> f x = 0) -> ∀ x, f x = 0.
Proof.
  intros f A H1 H2 H3 x.
  pose proof classic (f x = 0) as [H4 | H4]; [exact H4 | exfalso].
  set (ε := |f x|).
  assert (H5 : ε > 0) by (unfold ε; solve_R).
  specialize (H1 x ε H5) as [δ [H6 H7]].
  specialize (H2 x (x + δ) ltac:(lra)) as [z [H8 H9]].
  specialize (H7 z ltac:(solve_R)).
  specialize (H3 z ltac:(solve_R)).
  rewrite H3 in H7.
  unfold ε in H7.
  solve_R.
Qed.

Lemma lemma_8_6_b : ∀ f g A,
  continuous f -> continuous g -> dense A -> (∀ x, x ∈ A -> f x = g x) -> ∀ x, f x = g x.
Proof. 
  intros f g A H1 H2 H3 H4 x.
  set (h := (f - g)%function).
  assert (H5 : continuous h) by (unfold h; auto_cont).
  assert ( H6 : ∀ x, x ∈ A -> h x = 0).
  { intros y H6. unfold h. rewrite H4; solve_R. }
  pose proof lemma_8_6_a h A H5 H3 H6 as H7.
  specialize (H7 x).
  unfold h in H7. 
  lra.
Qed.

Lemma lemma_8_6_c : ∀ f g A,
  continuous f -> continuous g -> dense A -> (∀ x, x ∈ A -> f x >= g x) -> ∀ x, f x >= g x.
Proof.
  intros f g A H1 H2 H3 H4 x.
  set (h := (f - g)%function).
  assert (H5 : continuous h) by (unfold h; auto_cont).
  assert (H6 : ∀ y, y ∈ A -> h y >= 0).
  { intros y H6. unfold h. specialize (H4 y H6). solve_R. }
  pose proof classic (h x >= 0) as [H7 | H7]; [unfold h in H7; solve_R | exfalso].
  set (ε := - h x).
  assert (H8 : ε > 0) by (unfold ε; solve_R).
  specialize (H5 x ε H8) as [δ [H9 H10]].
  specialize (H3 x (x + δ) ltac:(lra)) as [z [H11 H12]].
  specialize (H10 z ltac:(solve_R)).
  specialize (H6 z H11).
  unfold ε in H10.
  solve_R.
Qed.

Lemma lemma_8_6_c_strict_cannot_replace_nonstrict :
  ∃ f g A,
    continuous f /\ continuous g /\ dense A /\
    (∀ x, x ∈ A -> f x > g x) /\
    ¬ (∀ x, f x > g x).
Proof. Abort.
