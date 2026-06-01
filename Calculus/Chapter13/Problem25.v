From Calculus.Chapter13 Require Import Prelude.

Definition length_of_polygonal_curve {a b : ℝ} (f : ℝ -> ℝ) (P : partition a b) : ℝ :=
  let l := P.(points a b) in
  ∑ 0 (length l - 2) (λ i, √((l.[i+1] - l.[i])^2 + (f (l.[i+1]) - f (l.[i]))^2)).

Notation "'ℓ(' f ',' P ')'" := (length_of_polygonal_curve f P) (at level 10, f, P at next level).

Definition is_length (a b : ℝ) (f : ℝ -> ℝ) (L : ℝ) : Prop :=
  is_lub (fun y => exists P : partition a b, y = ℓ(f, P)) L.

Definition length_or_zero (a b : ℝ) (f : ℝ -> ℝ) (L : ℝ) : Prop :=
  is_length a b f L \/ (~ (exists L2, is_length a b f L2) /\ L = 0).

Definition length (a b : ℝ) (f : ℝ -> ℝ) : ℝ :=
  epsilon (inhabits 0) (length_or_zero a b f).
