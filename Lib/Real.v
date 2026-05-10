Require Import Imports Notations Sets.
Import SetNotations.

Open Scope Q_scope.

Record Real := {
  alpha : Ensemble ℚ;
  H1 : ∀ x y : ℚ, x ∈ alpha -> y < x -> y ∈ alpha;
  H2 : alpha ≠ ∅;
  H3 : alpha ≠ ℚ;
  H4 : ∀ x : ℚ, x ∈ alpha -> ∃ y : ℚ, y ∈ alpha /\ y > x 
}.

Declare Scope Real_scope.

Open Scope Real_scope.

Definition Rlt (α β : Real) : Prop :=
  α.(alpha) ⊆ β.(alpha) /\ α.(alpha) ≠ β.(alpha).

Definition Rle (α β : Real) : Prop := 
  α.(alpha) ⊆ β.(alpha).

Definition Rgt (α β : Real) : Prop := 
  Rlt β α.

Definition Rge (α β : Real) : Prop := 
  Rle β α.

Infix "<" := Rlt : Real_scope.
Infix "<=" := Rle : Real_scope.
Infix ">" := Rgt : Real_scope.
Infix ">=" := Rge : Real_scope.

Definition is_upper_bound (A : Ensemble Real) (ub : Real) : Prop :=
  ∀ x, x ∈ A -> x <= ub.

Definition bounded_above (A : Ensemble Real) : Prop :=
  ∃ ub, is_upper_bound A ub.

Definition least_upper_bound (A : Ensemble Real) (lub : Real) : Prop :=
  is_upper_bound A lub /\ ∀ ub, is_upper_bound A ub -> lub <= ub.

Theorem theorem_29_1 : ∀ A,
  A ≠ ∅ -> bounded_above A -> ∃ lub, least_upper_bound A lub.
Proof.
  intros A H1 H2.

Admitted.