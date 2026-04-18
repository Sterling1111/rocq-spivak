From Calculus.Chapter14 Require Import Prelude.

(* Problem 9: Prove that if f is continuous, then
   ∫ 0 x f(u)(x-u) du = ∫ 0 x (∫ 0 u f(t) dt) du *)

Lemma lemma_14_9 : forall f x,
  continuous f ->
  ∫ 0 x (fun u => f u * (x - u)) = ∫ 0 x (fun u => ∫ 0 u f).
Abort.
