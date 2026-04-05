From Calculus.Chapter14 Require Import Prelude.
Require Import Interval.Tactic.

Lemma lemma_14_7_i :
  1 / (7 * √2) <= ∫ 0 1 (fun x => x^6 / √(1 + x^2)) <= 1 / 7.
Proof.
Admitted.

Lemma lemma_14_7_ii :
  3 / 8 <= ∫ 0 (1/2) (fun x => √((1 - x) / (1 + x))) <= √3 / 4.
Admitted.
