From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_12_a : ∀ f g,
  (even f -> even g -> even (f + g)) /\
  (odd f -> odd g -> odd (f + g)).
Proof.
  intros f g. repeat split; intros H1 H2 x;
  specialize (H1 x); specialize (H2 x); lra.
Qed.

Lemma lemma_3_12_a' :
  ~ (∀ f g, even f -> odd g -> even (f + g)) /\
  ~ (∀ f g, even f -> odd g -> odd (f + g)) /\
  ~ (∀ f g, odd f -> even g -> even (f + g)) /\
  ~ (∀ f g, odd f -> even g -> odd (f + g)).
Proof.
  repeat split; intros H1.
  - assert (H2: even (fun _ => 0)) by (intro x; lra).
    assert (H3: odd (fun x => x)) by (intro x; lra).
    specialize (H1 _ _ H2 H3 1); lra.
  - assert (H2: even (fun _ => 1)) by (intro x; lra).
    assert (H3: odd (fun _ => 0)) by (intro x; lra).
    specialize (H1 _ _ H2 H3 1); lra.
  - assert (H2: odd (fun x => x)) by (intro x; lra).
    assert (H3: even (fun _ => 0)) by (intro x; lra).
    specialize (H1 _ _ H2 H3 1); lra.
  - assert (H2: odd (fun _ => 0)) by (intro x; lra).
    assert (H3: even (fun _ => 1)) by (intro x; lra).
    specialize (H1 _ _ H2 H3 1); lra.
Qed.
  
Lemma lemma_3_12_b : ∀ f g,
  (even f -> even g -> even (f ⋅ g)) /\
  (even f -> odd g -> odd (f ⋅ g)) /\
  (odd f -> even g -> odd (f ⋅ g)) /\
  (odd f -> odd g -> even (f ⋅ g)).
Proof.
  intros f g. repeat split; intros H1 H2 x;
  specialize (H1 x); specialize (H2 x); nra.
Qed.

Lemma lemma_3_12_c : ∀ f g,
  (even f -> even g -> even (f ∘ g)) /\
  (even f -> odd g -> even (f ∘ g)) /\
  (odd f -> even g -> even (f ∘ g)) /\
  (odd f -> odd g -> odd (f ∘ g)).
Proof.
  intros f g. repeat split; intros H1 H2 x; unfold compose.
  - rewrite H2; lra.
  - rewrite H2; rewrite H1; lra.
  - rewrite H2; lra.
  - rewrite H2; rewrite H1; lra.
Qed.

Fixpoint max_val (l : list (R -> R)) : R :=
  match l with
  | nil => 0
  | h :: t => Rmax (h (-1)) (max_val t)
  end.

Lemma max_val_ge : ∀ f l, In f l -> f (-1) <= max_val l.
Proof.
  induction l as [| h t IH]; intros H1.
  - contradiction.
  - destruct H1 as [H1 | H1].
    + subst. solve_R.
    + specialize (IH H1). solve_R. 
Qed.

Lemma lemma_3_12_d : ∀ f l,
  even f -> ∃ g, ~ In g l /\ (∀ x, f x = g (|x|)).
Proof.
  intros f l H1.
  set (M := max_val l + 1).
  set (g := fun x => if Rle_dec 0 x then f x else M).
  exists g; split.
  - intros H2. 
    pose proof max_val_ge g l H2 as H3.
    unfold g, M in *; solve_R.
  - unfold g; solve_R.
Qed.