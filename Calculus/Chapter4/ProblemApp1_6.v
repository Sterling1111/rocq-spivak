From Calculus.Chapter4 Require Import Prelude.

Lemma lemma_4_app1_6 :
  (∀ v w z, det v (point_add w z)=det v w+det v z) /\
    (∀ v w z, det (point_add v w) z=det v z+det w z) /\
    (∀ a v w, a*det v w=det (point_scale a v) w /\
                   a*det v w=det v (point_scale a w)).
Abort.
