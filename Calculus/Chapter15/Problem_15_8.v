From Calculus.Chapter15 Require Import Prelude.

(* Problem 8 *)

(* (a) A sin(x + B) = a sin x + b cos x for suitable a and b *)
Lemma lemma_15_8_a : forall A B,
  exists a b, forall x,
    A * sin (x + B) = a * sin x + b * cos x.
Admitted.

(* (b) Given a and b, find A and B *)
Lemma lemma_15_8_b : forall a b,
  exists A B, forall x,
    a * sin x + b * cos x = A * sin (x + B).
Admitted.
