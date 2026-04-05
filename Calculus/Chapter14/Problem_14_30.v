From Calculus.Chapter14 Require Import Prelude.

(* Problem 30: Combining both types of improper integrals *)

(* (a) If f(x) = 1/√x for 0 ≤ x ≤ 1 and f(x) = 1/x^2 for x ≥ 1,
   find ∫ 0 ∞ f(x) dx *)
Lemma lemma_14_30_a : exists L1 L2,
  ⟦ lim 0⁺ ⟧ (fun ε => ∫ ε 1 (fun x => 1 / √x)) = L1 /\
  ⟦ lim ∞ ⟧ (fun N => ∫ 1 N (fun x => 1 / x^2)) = L2.
Admitted.

(* (b) Show that ∫ 0 ∞ x^r dx never makes sense *)
Lemma lemma_14_30_b : forall r,
  ~ ((exists L1, ⟦ lim 0⁺ ⟧ (fun ε => ∫ ε 1 (fun x => Rpower x r)) = L1) /\
     (exists L2, ⟦ lim ∞ ⟧ (fun N => ∫ 1 N (fun x => Rpower x r)) = L2)).
Admitted.
