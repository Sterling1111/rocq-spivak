From Lib Require Export Imports Reals_util Notations Rational Sets Interval Functions
                        Trigonometry Vector.
Export SetNotations IntervalNotations FunctionNotations VectorNotations.
Open Scope R_scope.

(* Chapter 4 was empty. These are geometric adapters for Lib's sets and vectors;
   none of the exercise assertions is assumed here. *)
Definition point := (ℝ * ℝ)%type.
Definition plane_vector (p : point) : vector ℝ 2 := ⟨fst p, snd p⟩%V.
Definition point_add (p q : point) : point := (pair (fst p + fst q) (snd p + snd q)).
Definition point_scale (a : ℝ) (p : point) : point := (pair (a * fst p) (a * snd p)).
Definition point_sub (p q : point) : point := point_add p (point_scale (-1) q).
Definition dot (p q : point) : ℝ := (plane_vector p · plane_vector q)%V.
Definition norm (p : point) : ℝ := vector_norm (plane_vector p).
Definition distance (p q : point) : ℝ := norm (point_sub p q).
Definition det (p q : point) : ℝ := fst p * snd q - snd p * fst q.
Definition graph_on (D : Ensemble ℝ) (f : ℝ -> ℝ) : Ensemble point :=
  λ p, fst p ∈ D /\ snd p = f (fst p).
Definition graph (f : ℝ -> ℝ) : Ensemble point := graph_on ℝ f.
Definition locus (P : ℝ -> ℝ -> Prop) : Ensemble point := λ p, P (fst p) (snd p).
Definition line_through (p v : point) : Ensemble point :=
  λ q, ∃ t : ℝ, q = point_add p (point_scale t v).
Definition straight_line (L : Ensemble point) : Prop :=
  ∃ p v, v <> (pair (0) (0)) /\ L = line_through p v.
Definition line_equation (A B C : ℝ) : Ensemble point :=
  locus (λ x y, A*x + B*y + C = 0).
(* Parallel here means distinct, disjoint lines; coincident lines are separate. *)
Definition parallel (L M : Ensemble point) : Prop :=
  straight_line L /\ straight_line M /\ ∀ p, ~(p ∈ L /\ p ∈ M).
Definition perpendicular (L M : Ensemble point) : Prop :=
  ∃ p v w, v <> (pair (0) (0)) /\ w <> (pair (0) (0)) /\
    L = line_through p v /\ M = line_through p w /\
    distance v w ^ 2 = norm v ^ 2 + norm w ^ 2.
Definition on_segment (p a b : point) : Prop :=
  ∃ t : ℝ, 0 <= t <= 1 /\ p = point_add (point_scale (1-t) a) (point_scale t b).
Definition distance_to_set (p : point) (S : Ensemble point) (d : ℝ) : Prop :=
  (∃ q, q ∈ S /\ distance p q = d) /\
  ∀ q, q ∈ S -> d <= distance p q.
Definition polar_point (r theta : ℝ) : point := (pair (r * cos theta) (r * sin theta)).
(* Radii are signed, as explicitly allowed on PDF pp. 84-85. *)
Definition polar_locus (P : ℝ -> ℝ -> Prop) : Ensemble point :=
  λ p, ∃ r theta, P r theta /\ p = polar_point r theta.
Definition polar_graph (f : ℝ -> ℝ) : Ensemble point :=
  polar_locus (λ r theta, r = f theta).
(* Rotation is specified geometrically on every ray, not assumed linear. *)
Definition rotates (theta : ℝ) (T : point -> point) : Prop :=
  ∀ r phi, T (polar_point r phi) = polar_point r (phi + theta).
Definition angle_between (v w : point) (theta : ℝ) : Prop :=
  ∃ phi, v = polar_point (norm v) phi /\
    w = polar_point (norm w) (phi + theta).
(* Base times perpendicular height; not the determinant formula being asked for. *)
Definition parallelogram_area (v w : point) : ℝ :=
  norm v * norm (point_sub w (point_scale (dot v w / dot v v) v)).

Definition ellipse (S : Ensemble point) : Prop :=
  ∃ h k a b : ℝ, 0 < a /\ 0 < b /\
    S = locus (λ x y, (x-h)^2/a^2 + (y-k)^2/b^2 = 1).
Definition hyperbola (S : Ensemble point) : Prop :=
  ∃ h k a b : ℝ, 0 < a /\ 0 < b /\
    (S = locus (λ x y, (x-h)^2/a^2 - (y-k)^2/b^2 = 1) \/
     S = locus (λ x y, (y-k)^2/b^2 - (x-h)^2/a^2 = 1)).
Definition parabola (S : Ensemble point) : Prop :=
  ∃ h k a : ℝ, a <> 0 /\
    (S = locus (λ x y, y-k = a*(x-h)^2) \/
     S = locus (λ x y, x-h = a*(y-k)^2)).
Definition circle (S : Ensemble point) : Prop :=
  ∃ h k r : ℝ, 0 < r /\ S = locus (λ x y, (x-h)^2+(y-k)^2=r^2).
Definition degenerate_conic (S : Ensemble point) : Prop :=
  S = ∅ \/ (∃ p : point, S = ⦃p⦄) \/ straight_line S \/
  ∃ L M, straight_line L /\ straight_line M /\ L <> M /\ S = L ⋃ M.

(* Three-dimensional geometry for Appendix 2, using Lib/Vector throughout. *)
Definition space := vector ℝ 3.
Definition coord (p : space) (i : ℕ) : ℝ := nth i (vlist p) 0.
Definition distance3 (p q : space) : ℝ := vector_norm (p + (-1)*q)%V.
Definition plane3 (n : space) (d : ℝ) : Ensemble space := λ p, (n · p)%V=d.
Definition cylinder3 (radius : ℝ) : Ensemble space :=
  λ p, coord p 0 ^ 2 + coord p 1 ^ 2 = radius^2.
Definition cone3 (slope : ℝ) : Ensemble space :=
  λ p, coord p 2 ^ 2 = slope^2*(coord p 0 ^ 2 + coord p 1 ^ 2).
Definition plane_chart (o u v : space) (x y : ℝ) : space := (o+x*u+y*v)%V.
Definition plane_frame (n : space) (d : ℝ) (o u v : space) : Prop :=
  vector_norm u=1 /\ vector_norm v=1 /\ (u · v)%V=0 /\
  ∀ p, (p ∈ plane3 n d <-> ∃ x y, p=plane_chart o u v x y).
(* With unit normal n, this is the perpendicular foot from c to the plane. *)
Definition plane_foot (n : space) (d : ℝ) (c : space) : space :=
  (c + (d-(n · c)%V)*n)%V.
Definition axis_center (h : ℝ) : space := ⟨0,0,h⟩%V.
