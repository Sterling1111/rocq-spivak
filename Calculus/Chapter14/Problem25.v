From Calculus.Chapter14 Require Import Prelude.

(* Problem 25: Improper integrals ∫ a ∞ f *)

(* (a) Determine ∫ 1 ∞ x^r dx if r < -1. *)
Lemma lemma_14_25_a : forall r,
  r < -1 ->
  ∫ 1 ∞ (fun x => Rpower x r) = (1 / (-(r + 1))).
Abort.

(* (b) Use Problem 13-15 to show that ∫ 1 ∞ (1/x) dx does not exist. *)
Lemma lemma_14_25_b :
  ~ improper_integrable_pinf 1 (fun x => 1 / x).
Abort.

(* (c) If f(x) ≥ 0 for x ≥ 0 and ∫ 0 ∞ f exists, then
   0 ≤ g(x) ≤ f(x) and g integrable on each [0, N] implies ∫ 0 ∞ g exists. *)
Lemma lemma_14_25_c : forall f g,
  (forall x, x >= 0 -> f x >= 0) ->
  improper_integrable_pinf 0 f ->
  (forall x, x >= 0 -> 0 <= g x <= f x) ->
  (forall N, N > 0 -> integrable_on 0 N g) ->
  improper_integrable_pinf 0 g.
Abort.

(* (d) Explain why ∫ 0 ∞ (1/(1+x^2)) dx exists. *)
Lemma lemma_14_25_d :
  improper_integrable_pinf 0 (fun x => 1 / (1 + x^2)).
Abort.
