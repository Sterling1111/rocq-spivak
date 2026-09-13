From Calculus.Chapter3 Require Export Prelude.

Local Definition characteristic (A : Ensemble R) (x : R) : R :=
  if excluded_middle_informative (x ∈ A) then 1 else 0.

Lemma lemma_3_9_a_intersection : ∀ (A B : Ensemble R) x,
  characteristic (A ⋂ B)%set x = characteristic A x * characteristic B x.
Proof.
  intros A B x. unfold characteristic.
  repeat destruct excluded_middle_informative; try solve [exfalso; autoset]; try ring.
  all: exfalso; unfold Ensembles.In, Setminus in *; firstorder.
Qed.

Lemma lemma_3_9_a_union : ∀ (A B : Ensemble R) x,
  characteristic (A ⋃ B)%set x =
    characteristic A x + characteristic B x - characteristic A x * characteristic B x.
Proof.
  intros A B x. unfold characteristic.
  repeat destruct excluded_middle_informative; try solve [exfalso; autoset]; try ring.
  all: exfalso; unfold Ensembles.In, Setminus in *; firstorder.
Qed.

Lemma lemma_3_9_a_complement : ∀ (A : Ensemble R) x,
  characteristic (Full_set R − A)%set x = 1 - characteristic A x.
Proof.
  intros A x. assert (H1 : x ∈ Full_set R) by constructor. unfold characteristic.
  repeat destruct excluded_middle_informative; try solve [exfalso; autoset]; try ring.
  all: exfalso; unfold Ensembles.In, Setminus in *; firstorder.
Qed.

Lemma lemma_3_9_b : ∀ f : R -> R, 
  (∀ x, f x = 0 \/ f x = 1) -> 
  ∃ A : Ensemble R, ∀ x, (x ∈ A -> f x = 1) /\ (~ x ∈ A -> f x = 0).
Proof.
  intros f H1. exists (λ x, f x = 1). intros x.
  unfold Ensembles.In. split; auto. specialize (H1 x). tauto.
Qed.

Lemma lemma_3_9_c : ∀ f : R -> R, 
  (∀ x, f x = (f x)^2) <-> 
  ∃ A : Ensemble R, ∀ x, (x ∈ A -> f x = 1) /\ (~ x ∈ A -> f x = 0).
Proof.
  intros f. split.
  - intros H1. apply lemma_3_9_b. intros x. specialize (H1 x). nra.
  - intros [A H1] x. destruct (classic (x ∈ A)) as [H2 | H2];
    destruct (H1 x) as [H3 H4]; [rewrite (H3 H2) | rewrite (H4 H2)]; ring.
Qed.
