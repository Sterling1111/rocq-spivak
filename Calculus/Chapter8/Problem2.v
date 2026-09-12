From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_2_a : ∀ A sup_B,
  let B := (fun x => -x ∈ A) in
  A ≠ ∅ ->
  has_lower_bound A ->
  is_lub B sup_B ->
  B ≠ ∅ /\ has_upper_bound B /\ is_glb A (-sup_B).
Proof. Abort.

Lemma lemma_8_2_b : ∀ A sup_B,
  let B := (fun x => is_lower_bound A x) in
  A ≠ ∅ ->
  has_lower_bound A ->
  is_lub B sup_B ->
  B ≠ ∅ /\ has_upper_bound B /\ is_glb A sup_B.
Proof. Abort.
