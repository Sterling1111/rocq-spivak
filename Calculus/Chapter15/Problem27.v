From Calculus.Chapter15 Require Import Prelude.

(* Problem 27 *)

(* (b) cos x < sin x / x < 1 for 0 < x < π/2 *)
Lemma lemma_15_27_b : forall x,
  0 < x < π / 2 ->
  cos x < sin x / x < 1.
Abort.

(* (c) lim_{x->0} (1 - cos x) / x = 0 *)
Lemma lemma_15_27_c :
  ⟦ lim 0 ⟧ (fun x => (1 - cos x) / x) = 0.
Abort.

(* (d) sin'(x) = cos x from the definition *)
Lemma lemma_15_27_d :
  ⟦ der ⟧ sin = cos.
Abort.
