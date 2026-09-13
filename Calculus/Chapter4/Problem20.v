From Calculus.Chapter4 Require Import Prelude.

(* Sketch Thomae's function. Organize rational points by their positive
   reduced denominator (q=2, q=3, ...), rather than placing points randomly. *)
Definition problem_4_20 : Ensemble point := locus (λ x y,
  (irrational x /\ y=0) \/
  ∃ p q : ℤ, (0 < q)%Z /\ Z.gcd p q = 1%Z /\
    x = p / q /\ y = 1 / q).
