From Calculus.Chapter3 Require Export Prelude.

Local Definition g (x : R) := x^2.
Local Definition h (x : R) := if excluded_middle_informative (rational x) then 0 else 1.

Lemma lemma_3_2_i : ∀ y,
  h y <= y <-> (rational y /\ 0 <= y) \/ (~ rational y /\ 1 <= y).
Proof.
  intros y. unfold h. destruct (excluded_middle_informative (rational y)); tauto.
Qed.

Lemma lemma_3_2_ii : ∀ y,
  h y <= g y <-> rational y \/ y <= -1 \/ 1 <= y.
Proof.
  intros y. unfold h, g. destruct (excluded_middle_informative (rational y)) as [H1 | H1].
  - split; auto. intros _. nra.
  - split; intro H2; [right | destruct H2 as [H2 | [H2 | H2]]]; try contradiction; nra.
Qed.

Lemma lemma_3_2_iii : ∀ z, g (h z) - h z = 0.
Proof.
  intros z. unfold g, h. destruct (excluded_middle_informative (rational z)); ring.
Qed.

Lemma lemma_3_2_iv : ∀ w, g w <= w <-> 0 <= w <= 1.
Proof.
  intros w. unfold g. split; nra.
Qed.

Lemma lemma_3_2_v : ∀ e, g (g e) = g e <-> e = -1 \/ e = 0 \/ e = 1.
Proof.
  intros e. unfold g. split; intros H1.
  - assert (H2 : e^2 = 0 \/ e^2 = 1) by nra. destruct H2; nra.
  - destruct H1 as [H1 | [H1 | H1]]; subst; ring.
Qed.
