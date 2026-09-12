From Calculus.Chapter8 Require Import Prelude Problem18.

Lemma lemma_8_19_a : ∀ A li ls,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  lim_inf A li -> lim_sup A ls -> li <= ls.
Proof. Abort.

Lemma lemma_8_19_b : ∀ A ls sup_A,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  lim_sup A ls -> is_lub A sup_A -> ls <= sup_A.
Proof. Abort.

Lemma lemma_8_19_c : ∀ A ls sup_A,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  lim_sup A ls -> is_lub A sup_A -> ls < sup_A ->
  sup_A ∈ A.
Proof. Abort.

Lemma lemma_8_19_d_1 : ∀ A li inf_A,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  lim_inf A li -> is_glb A inf_A -> inf_A <= li.
Proof. Abort.

Lemma lemma_8_19_d_2 : ∀ A li inf_A,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  lim_inf A li -> is_glb A inf_A -> inf_A < li ->
  inf_A ∈ A.
Proof. Abort.
