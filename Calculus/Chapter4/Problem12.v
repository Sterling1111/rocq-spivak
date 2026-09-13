From Calculus.Chapter4 Require Import Prelude.

(* Sketch the mth-root graphs for m=1,2,3,4. Even roots are
   nonnegative (including zero); odd roots allow negative arguments. *)

Definition problem_4_12_m1 : Ensemble point := locus (λ x y, y=x).

Definition problem_4_12_m2 : Ensemble point := locus (λ x y, 0 <= x /\ 0 <= y /\ y^2=x).

Definition problem_4_12_m3 : Ensemble point := locus (λ x y, y^3=x).

Definition problem_4_12_m4 : Ensemble point := locus (λ x y, 0 <= x /\ 0 <= y /\ y^4=x).
