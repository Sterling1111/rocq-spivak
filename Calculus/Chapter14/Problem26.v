From Calculus.Chapter14 Require Import Prelude.

(* Problem 26: Decide whether or not the following improper integrals exist. *)

(* (i) ∫ 0 ∞ (1/√(1+x^3)) dx *)
Lemma lemma_14_26_i :
  ~ improper_integrable_pinf 0 (fun x => 1 / √(1 + x^3)).
Abort.

(* (ii) ∫ 0 ∞ (x/(1+x^(3/2))) dx *)
Lemma lemma_14_26_ii :
  ~ improper_integrable_pinf 0 (fun x => x / (1 + Rpower x (3/2))).
Abort.

(* (iii) ∫ 0 ∞ (1/(x*√(1+x))) dx *)
(* This is really a type considered in Problem 28 — it diverges *)
Lemma lemma_14_26_iii :
  ~ improper_integrable_pinf 0 (fun x => 1 / (x * √(1 + x))).
Abort.
