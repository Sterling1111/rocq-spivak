From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_5_a : forall f g,
  one_to_one f ->
  one_to_one g ->
  one_to_one (f ∘ g).
Proof.
  intros f g H1 H2 x y H3 H4 H5.
  specialize (H1 (g x) (g y) ltac:(apply Full_intro) ltac:(apply Full_intro) H5) as H6.
  specialize (H2 x y ltac:(apply Full_intro) ltac:(apply Full_intro) H6) as H7.
  exact H7.
Qed.

Lemma lemma_12_5_a' : forall f g f_inv g_inv,
  inverse f f_inv ->
  inverse g g_inv ->
  inverse (f ∘ g)%function (g_inv ∘ f_inv)%function.
Proof.
  intros f g f_inv g_inv [H1 [H2 [H3 H4]]] [H5 [H6 [H7 H8]]].
  repeat split; intros x H9; unfold compose.
  - specialize (H3 (g x) ltac:(apply Full_intro)) as H10.
    rewrite H10, H7; [reflexivity | apply H9].
  - specialize (H8 (f_inv x) ltac:(apply Full_intro)) as H10.
    rewrite H10, H4; [reflexivity | apply H9].
Qed.

Lemma lemma_12_5_a'' : forall f g f_inv g_inv,
  inverse f f_inv ->
  inverse g g_inv ->
  inverse (f ∘ g)%function (g_inv ∘ f_inv)%function.
Proof.
  intros f g f_inv g_inv [H1 [H2 [H3 H4]]] [H5 [H6 [H7 H8]]].
  repeat split; intros x H9; unfold compose; [rewrite H3 | rewrite H8]; auto.
Qed.

Lemma lemma_12_5_c : forall f f_inv g,
  inverse f f_inv ->
  g = (fun x => 1 + f x) ->
  inverse g (fun x => f_inv (x - 1)).
Proof.
  intros f f_inv g H1 H2.
  pose proof inverse_spec f f_inv H1 as [H3 H4].
  repeat split; intros x _; rewrite H2.
  - replace (1 + f x - 1) with (f x) by lra. apply H3.
  - rewrite H4. lra.
Qed.

Lemma lemma_12_5_c' : forall f f_inv g,
  inverse f f_inv ->
  g = (fun x => 1 + f x) ->
  inverse g (fun x => f_inv (x - 1)).
Proof.
  intros f f_inv g H1 H2.
  set (g_inv := λ x, f_inv (x - 1)).
  set (h := λ x, 1 + x).
  set (h_inv := λ x, x - 1).
  assert (H3 : inverse g g_inv).
  {
    repeat split; intros x _; rewrite H2; unfold g_inv;
    pose proof inverse_spec f f_inv H1 as [H3 H4].
    - replace (1 + f x - 1) with (f x) by lra; auto.
    - specialize (H4 (x - 1)). lra.
  }
  assert (H4 : inverse h h_inv).
  { repeat split; intros x _; unfold h, h_inv; lra. }
  assert (H5 : g = h ∘ f) by auto.
  assert (H6 : g_inv = f_inv ∘ h_inv) by auto.
  rewrite H6, H5; unfold compose, h, h_inv.
  repeat split; intros x _; pose proof inverse_spec f f_inv H1 as [H7 H8].
  - specialize (H7 x). replace (1 + f x - 1) with (f x); lra.
  - rewrite H8; lra.
Qed.