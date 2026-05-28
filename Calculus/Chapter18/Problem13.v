From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_13_a : forall a, 0 < a < 1 ->
  ⟦ lim ∞ ⟧ (fun x => a ^^ x) = 0.
Proof.
Abort.

Lemma lemma_18_13_b : forall n : nat,
  ⟦ lim ∞ ⟧ (fun x => x / (log x) ^ n) = ∞.
Proof.
Abort.

Lemma lemma_18_13_c : forall n : nat,
  ⟦ lim ∞ ⟧ (fun x => (log x) ^ n / x) = 0.
Proof.
Abort.

Lemma lemma_18_13_d : forall n : nat,
  ⟦ lim 0⁺ ⟧ (fun x => x * (log x) ^ n) = 0.
Proof.
Abort.

Lemma lemma_18_13_e :
  ⟦ lim 0⁺ ⟧ (fun x => x ^^ x) = 1.
Proof.
Abort.
