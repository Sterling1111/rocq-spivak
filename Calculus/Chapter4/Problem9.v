From Calculus.Chapter4 Require Import Prelude.

Lemma lemma_4_9_a :
  ∀ x1 x2 y1 y2 : ℝ, √((x1+y1)^2+(x2+y2)^2) <= √(x1^2+x2^2)+√(y1^2+y2^2).
Abort.

Lemma lemma_4_9_b :
  ∀ p1 p2 p3 : point, distance p1 p3 <= distance p1 p2 + distance p2 p3.
Abort.

Lemma lemma_4_9_b_strict :
  ∀ p1 p2 p3 : point, (distance p1 p3 < distance p1 p2 + distance p2 p3 <-> ~ on_segment p2 p1 p3).
Abort.
