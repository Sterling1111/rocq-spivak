From Calculus.Chapter14 Require Import Prelude.

(* Problem 4: Find (f^{-1})'(0) *)

(* (i) f(x) = ∫ 0 x (1 + sin(sin t)) dt *)
Lemma lemma_14_4_i : forall f f_inv,
  (forall x, f x = ∫ 0 x (fun t => 1 + sin (sin t))) ->
  inverse f f_inv ->
  ⟦ Der 0 ⟧ f_inv = 1.
Abort.

(* (ii) f(x) = ∫ 1 x cos(cos t) dt *)
Lemma lemma_14_4_ii : forall f f_inv,
  (forall x, f x = ∫ 1 x (fun t => cos (cos t))) ->
  inverse f f_inv ->
  ⟦ Der 0 ⟧ f_inv = 1 / cos (cos 1).
Abort.
