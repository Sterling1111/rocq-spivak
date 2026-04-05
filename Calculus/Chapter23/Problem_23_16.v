From Calculus.Chapter23 Require Import Prelude.

(* Problem 16: \int_{0}^{\infty} |\sin x / x| dx diverges. *)

Lemma problem_23_16 :
  ~ (exists L, ⟦ lim ∞ ⟧ (fun N => ∫ 0 N (fun x => if Req_dec_T x 0 then 1 else |sin x / x|)) = L).
Admitted.
