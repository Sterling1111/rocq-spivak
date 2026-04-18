From Calculus.Chapter15 Require Import Prelude.

(* Problem 3: Let f(x) = sin x / x for x ≠ 0 and f(0) = 1. *)

Definition f_sinc (x : R) : R :=
  match Req_dec_T x 0 with
  | left _ => 1
  | right _ => sin x / x
  end.

(* (a) Find f'(0). *)
Lemma lemma_15_3_a :
  ⟦ der 0 ⟧ f_sinc = (fun _ => 0).
Abort.

(* (b) Find f''(0). *)
Lemma lemma_15_3_b :
  ⟦ der^2 0 ⟧ f_sinc = (fun _ => -1/3).
Abort.
