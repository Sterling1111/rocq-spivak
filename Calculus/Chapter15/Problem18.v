From Calculus.Chapter15 Require Import Prelude.

(* Problem 18 *)

(* (a) sin(x + π/2) = cos x *)
Lemma lemma_15_18_a : forall x,
  sin (x + π / 2) = cos x.
Abort.

(* (b) Simplifications *)
Lemma lemma_15_18_b_arcsin_sin : forall x,
  -π / 2 <= x <= π / 2 ->
  arcsin (sin x) = x.
Abort.

Lemma lemma_15_18_b_arcsin_cos : forall x,
  0 <= x <= π ->
  arcsin (cos x) = π / 2 - x.
Abort.

Lemma lemma_15_18_b_arccos_sin : forall x,
  -π / 2 <= x <= π / 2 ->
  arccos (sin x) = π / 2 - x.
Abort.
