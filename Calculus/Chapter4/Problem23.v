From Calculus.Chapter4 Require Import Prelude.

(* Figure 31 uses coordinates in axes turned counterclockwise by pi/4.
   The depicted lengths agree with these signed coordinates in the pictured
   quadrant; elsewhere actual distances are their absolute values. *)
Local Definition rotated_coordinates (x y xp yp : ℝ) : Prop :=
  pair x y = point_add (point_scale xp (pair (1/√2) (1/√2)))
                      (point_scale yp (pair (-1/√2) (1/√2))).

Lemma lemma_4_23_a :
  ∀ x y xp yp : ℝ,
    (rotated_coordinates x y xp yp <->
     xp = x/√2+y/√2 /\ yp = -x/√2+y/√2).
Abort.

Lemma lemma_4_23_b :
  ∀ x y xp yp : ℝ, rotated_coordinates x y xp yp ->
    ((xp/√2)^2-(yp/√2)^2=1 <-> x*y=1).
Abort.
