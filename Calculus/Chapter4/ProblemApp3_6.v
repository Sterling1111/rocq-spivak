From Calculus.Chapter4 Require Import Prelude.

(* PDF inconsistency: the printed y=a is drawn vertically and the
   asserted cosine formula is for x=a. State the diagram's version, and
   separately give the sine formula for the literal horizontal line y=a.
   Here r is a distance, hence nonnegative, and the directrix has a>0. *)
Lemma lemma_4_app3_6_distance :
  ∀ a r theta : ℝ, 0<a -> 0<=r ->
    distance (polar_point r theta) (pair 0 0)=|a-r*cos theta| ->
    distance_to_set (polar_point r theta) (line_equation 1 0 (-a))
      (a-r*cos theta).
Abort.

Lemma lemma_4_app3_6 :
  ∀ a r theta : ℝ, 0<a -> 0<=r ->
    (distance_to_set (polar_point r theta) (line_equation 1 0 (-a))
      (distance (polar_point r theta) (pair 0 0)) <-> a=r*(1+cos theta)).
Abort.

Lemma lemma_4_app3_6_printed_line :
  ∀ a r theta : ℝ, 0<a -> 0<=r ->
    (distance_to_set (polar_point r theta) (graph (λ _, a))
      (distance (polar_point r theta) (pair 0 0)) <-> a=r*(1+sin theta)).
Abort.
