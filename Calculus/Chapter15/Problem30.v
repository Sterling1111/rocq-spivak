From Calculus.Chapter15 Require Import Prelude.

(* Problem 30: Defining sin and cos via the ODE s'' + s = 0 *)

(* (a) y₀² + (y₀')² is constant *)
Lemma lemma_15_30_a : forall y₀ y₀',
  ⟦ der ⟧ y₀ = y₀' ->
  (forall x, ⟦ der x ⟧ y₀' = (fun x => - y₀ x)) ->
  exists c, forall x, (y₀ x)^2 + (y₀' x)^2 = c.
Abort.

(* (d) sin(π/2) = 1 *)
Lemma lemma_15_30_d : sin (π / 2) = 1.
Abort.

(* (e) Values at π and 2π *)
Lemma lemma_15_30_e :
  cos π = -1 /\ sin π = 0 /\ cos (2 * π) = 1 /\ sin (2 * π) = 0.
Abort.

(* (f) Periodicity *)
Lemma lemma_15_30_f :
  (forall x, cos (x + 2 * π) = cos x) /\
  (forall x, sin (x + 2 * π) = sin x).
Abort.
