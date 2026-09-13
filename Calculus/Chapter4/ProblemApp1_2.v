From Calculus.Chapter4 Require Import Prelude.

Lemma lemma_4_app1_2_a_witness :
  ∀ v : point, ∃ w : point, w <> pair 0 0 /\ dot v w=0.
Abort.

Lemma lemma_4_app1_2_a :
  ∀ v w : point,
    (dot v w=0 <-> v=pair 0 0 \/ ∃ a : ℝ, w=point_scale a (pair (-snd v) (fst v))).
Abort.

Lemma lemma_4_app1_2_b :
  (∀ v w, dot v w=dot w v) /\
    (∀ v w z, dot v (point_add w z)=dot v w+dot v z) /\
    (∀ a v w, a*dot v w=dot (point_scale a v) w /\
                   a*dot v w=dot v (point_scale a w)).
Abort.

Lemma lemma_4_app1_2_c :
  ∀ v : point, 0 <= dot v v /\
    (dot v v=0 <-> v=pair 0 0) /\ (norm v=0 <-> v=pair 0 0) /\
    norm v=distance (pair 0 0) v.
Abort.

Lemma lemma_4_app1_2_d :
  ∀ v w : point, norm (point_add v w) <= norm v+norm w /\
    (norm (point_add v w)=norm v+norm w <->
     v=pair 0 0 \/ w=pair 0 0 \/ ∃ a : ℝ, 0<a /\ w=point_scale a v).
Abort.

Lemma lemma_4_app1_2_e :
  ∀ v w : point,
    dot v w=(norm (point_add v w)^2-norm (point_sub v w)^2)/4.
Abort.
