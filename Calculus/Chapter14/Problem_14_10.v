From Calculus.Chapter14 Require Import Prelude.

(* Problem 10: Use Problem 9 to prove that
   ∫ 0 x f(u)(x-u)^2 du = 2 ∫ 0 x (∫ 0 u2 (∫ 0 u1 f(t) dt) du1) du2 *)

Lemma lemma_14_10 : forall f x,
  continuous f ->
  ∫ 0 x (fun u => f u * (x - u)^2) =
  2 * ∫ 0 x (fun u2 => ∫ 0 u2 (fun u1 => ∫ 0 u1 f)).
Admitted.
