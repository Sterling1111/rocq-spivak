From Calculus.Chapter15 Require Import Prelude.

(* Problem 2: Find the following limits by l'Hôpital's Rule. *)

(* (i) lim_{x->0} (sin x - x + x^3/6) / x^3 *)
Lemma lemma_15_2_i :
  ⟦ lim 0 ⟧ (fun x => (sin x - x + x^3 / 6) / x^3) = 0.
Admitted.

(* (ii) lim_{x->0} (sin x - x + x^3/6) / x^4 *)
Lemma lemma_15_2_ii :
  ⟦ lim 0 ⟧ (fun x => (sin x - x + x^3 / 6) / x^4) = 0.
Admitted.

(* (iii) lim_{x->0} (cos x - 1 + x^2/2) / x^2 *)
Lemma lemma_15_2_iii :
  ⟦ lim 0 ⟧ (fun x => (cos x - 1 + x^2 / 2) / x^2) = 0.
Admitted.

(* (iv) lim_{x->0} (cos x - 1 + x^2/2) / x^4 *)
Lemma lemma_15_2_iv :
  ⟦ lim 0 ⟧ (fun x => (cos x - 1 + x^2 / 2) / x^4) = 1/24.
Admitted.

(* (v) lim_{x->0} (arctan x - x + x^3/3) / x^3 *)
Lemma lemma_15_2_v :
  ⟦ lim 0 ⟧ (fun x => (arctan x - x + x^3 / 3) / x^3) = 0.
Admitted.

(* (vi) lim_{x->0} (1/x - 1/sin x) *)
Lemma lemma_15_2_vi :
  ⟦ lim 0 ⟧ (fun x => 1 / x - 1 / sin x) = 0.
Admitted.
