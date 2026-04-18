From Calculus.Chapter8 Require Import Prelude.
From Calculus.Chapter8 Require Import Problem18.

Definition lim_inf (A : Ensemble ℝ) (l : ℝ) :=
  is_lub (fun x => almost_lower_bound A x) l.

Lemma lemma_8_19_a : ∀ A li ls,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  lim_inf A li -> lim_sup A ls -> li <= ls.
Proof. Abort.

Lemma lemma_8_19_b : ∀ A ls supa,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  lim_sup A ls -> is_lub A supa -> ls <= supa.
Proof. Abort.

Lemma lemma_8_19_c : ∀ A ls supa,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  lim_sup A ls -> is_lub A supa -> ls < supa ->
  supa ∈ A.
Proof. Abort.
