From Calculus.Chapter14 Require Import Prelude.

(* Problem 20: Let f(x) = cos(1/x) for x ≠ 0, f(0) = 0.
   Is F(x) = ∫ 0 x f differentiable at 0? *)

Definition f_20 (x : R) : R :=
  match Req_dec_T x 0 with left _ => 0 | right _ => cos (1 / x) end.

Lemma lemma_14_20 :
  differentiable_at (fun x => ∫ 0 x f_20) 0.
Abort.
