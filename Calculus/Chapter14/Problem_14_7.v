From Calculus.Chapter14 Require Import Prelude.

(* Problem 7: Use Problem 13-23 to prove the following integral inequalities. *)

(* (i) 1/(7√2) ≤ ∫ 0 1 (x^6 / √(1+x^2)) dx ≤ 1/7 *)
Lemma lemma_14_7_i :
  1 / (7 * √2) <= ∫ 0 1 (fun x => x^6 / √(1 + x^2)) <= 1 / 7.
Admitted.

(* (ii) 3/8 ≤ ∫ 0 (1/2) √((1-x)/(1+x)) dx ≤ √3/4 *)
Lemma lemma_14_7_ii :
  3 / 8 <= ∫ 0 (1/2) (fun x => √((1 - x) / (1 + x))) <= √3 / 4.
Admitted.
