From Calculus.Chapter3 Require Export Prelude.
From Lib Require Import Field.

Lemma lemma_3_28_a_P1 : ∀ f g h : R -> R,
  ((f + g)%function + h)%function = (f + (g + h)%function)%function.
Proof.
  intros. apply functional_extensionality. intro x. ring.
Qed.

Lemma lemma_3_28_a_P2 : ∀ f : R -> R,
  (f + (λ _, 0))%function = f.
Proof.
  intros. apply functional_extensionality. intro x. ring.
Qed.

Lemma lemma_3_28_a_P3 : ∀ f : R -> R,
  (f + (- f)%function)%function = (λ _, 0).
Proof.
  intros. apply functional_extensionality. intro x. ring.
Qed.

Lemma lemma_3_28_a_P4 : ∀ f g : R -> R,
  (f + g)%function = (g + f)%function.
Proof.
  intros. apply functional_extensionality. intro x. ring.
Qed.

Lemma lemma_3_28_a_P5 : ∀ f g h : R -> R,
  ((f ⋅ g)%function ⋅ h)%function = (f ⋅ (g ⋅ h)%function)%function.
Proof.
  intros. apply functional_extensionality. intro x. ring.
Qed.

Lemma lemma_3_28_a_P6 :
  (λ _ : R, 1) <> (λ _ : R, 0) /\
  ∀ f : R -> R, (f ⋅ (λ _, 1))%function = f.
Proof.
  split.
  - intro H1. apply (f_equal (λ f, f 0)) in H1. lra.
  - intro f. apply functional_extensionality. intro x. ring.
Qed.

Lemma lemma_3_28_a_P8 : ∀ f g : R -> R,
  (f ⋅ g)%function = (g ⋅ f)%function.
Proof.
  intros. apply functional_extensionality. intro x. ring.
Qed.

Lemma lemma_3_28_a_P9 : ∀ f g h : R -> R,
  (f ⋅ (g + h)%function)%function = ((f ⋅ g)%function + (f ⋅ h)%function)%function.
Proof.
  intros. apply functional_extensionality. intro x. ring.
Qed.

Lemma lemma_3_28_b : ∃ f : R -> R,
  f <> (λ _, 0) /\ ~ ∃ g : R -> R, (f ⋅ g)%function = (λ _, 1).
Proof.
  exists (λ x, x). split.
  - intro H1. apply (f_equal (λ f, f 1)) in H1. lra.
  - intros [g H1]. apply (f_equal (λ f, f 0)) in H1. simpl in H1. lra.
Qed.

Lemma lemma_3_28_c : ~ ∃ P : Ensemble (R -> R),
  (∀ f : R -> R,
    one_and_only_one_3 (f = (λ _, 0)) (f ∈ P) ((- f)%function ∈ P)) /\
  (∀ f g : R -> R, f ∈ P -> g ∈ P -> (f + g)%function ∈ P) /\
  (∀ f g : R -> R, f ∈ P -> g ∈ P -> (f ⋅ g)%function ∈ P).
Proof.
  intros [P [H1 [H2 H3]]].
  set (f := λ x : R, if Req_EM_T x 0 then 1 else 0).
  set (g := λ x : R, if Req_EM_T x 1 then 1 else 0).
  assert (H4 : f <> (λ _, 0)).
  { intro H4. apply (f_equal (λ h, h 0)) in H4.
    unfold f in H4. destruct Req_EM_T in H4; lra. }
  assert (H5 : g <> (λ _, 0)).
  { intro H5. apply (f_equal (λ h, h 1)) in H5.
    unfold g in H5. destruct Req_EM_T in H5; lra. }
  assert (H6 : ~ (λ _ : R, 0) ∈ P).
  { pose proof (H1 (λ _, 0)) as H6. unfold one_and_only_one_3 in H6. tauto. }
  assert (H7 : ∀ a b : R, (λ x, (a * f x) * (b * g x)) = (λ _, 0)).
  { intros a b. apply functional_extensionality. intro x. unfold f, g.
    repeat destruct Req_EM_T; try ring; exfalso; lra. }
  pose proof (H1 f) as H8. pose proof (H1 g) as H9.
  unfold one_and_only_one_3 in H8, H9.
  assert (H10 : f ∈ P \/ (-f)%function ∈ P) by tauto.
  assert (H11 : g ∈ P \/ (-g)%function ∈ P) by tauto.
  destruct H10 as [H10 | H10]; destruct H11 as [H11 | H11];
    pose proof (H3 _ _ H10 H11) as H12; apply H6.
  - replace (λ _ : R, 0) with (f ⋅ g)%function; auto.
    rewrite <- (H7 1 1). apply functional_extensionality. intro x. ring.
  - replace (λ _ : R, 0) with (f ⋅ (-g)%function)%function; auto.
    rewrite <- (H7 1 (-1)). apply functional_extensionality. intro x. ring.
  - replace (λ _ : R, 0) with ((-f)%function ⋅ g)%function; auto.
    rewrite <- (H7 (-1) 1). apply functional_extensionality. intro x. ring.
  - replace (λ _ : R, 0) with ((-f)%function ⋅ (-g)%function)%function; auto.
    rewrite <- (H7 (-1) (-1)). apply functional_extensionality. intro x. ring.
Qed.

Local Definition function_lt (f g : R -> R) : Prop := ∀ x, f x < g x.

Lemma lemma_3_28_d_P10 : ~ (∀ f g : R -> R,
  one_and_only_one_3 (f = g) (function_lt f g) (function_lt g f)).
Proof.
  intro H1. specialize (H1 (λ x, x) (λ _, 0)).
  unfold one_and_only_one_3 in H1.
  destruct H1 as [[H1 _] | [[_ [H1 _]] | [_ [_ H1]]]].
  - apply (f_equal (λ f, f 1)) in H1. lra.
  - specialize (H1 0). lra.
  - specialize (H1 0). lra.
Qed.

Lemma lemma_3_28_d_P11 : ∀ f g h : R -> R,
  function_lt f g -> function_lt g h -> function_lt f h.
Proof.
  intros f g h H1 H2 x. specialize (H1 x). specialize (H2 x). lra.
Qed.

Lemma lemma_3_28_d_P12 : ∀ f g h : R -> R,
  function_lt f g -> function_lt (f + h)%function (g + h)%function.
Proof.
  intros f g h H1 x. specialize (H1 x). lra.
Qed.

Lemma lemma_3_28_d_P13 : ∀ f g h : R -> R,
  function_lt f g -> function_lt (λ _, 0) h ->
  function_lt (f ⋅ h)%function (g ⋅ h)%function.
Proof.
  intros f g h H1 H2 x. specialize (H1 x). specialize (H2 x). nra.
Qed.

Lemma lemma_3_28_e_left : ∃ f g h : R -> R,
  function_lt f g /\ ~ function_lt (h ∘ f) (h ∘ g).
Proof.
  exists (λ _, 0), (λ _, 1), (λ x, -x). split.
  - intro x. lra.
  - intro H1. specialize (H1 0). unfold compose in H1. lra.
Qed.

Lemma lemma_3_28_e_right : ∀ f g h : R -> R,
  function_lt f g -> function_lt (f ∘ h) (g ∘ h).
Proof.
  intros f g h H1 x. apply H1.
Qed.
