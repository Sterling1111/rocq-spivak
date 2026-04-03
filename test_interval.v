Require Import Reals.
From Interval Require Import Tactic.
Open Scope R_scope.
Goal -0.990 < cos 3 < -0.989.
interval with (i_prec 30).
Qed.
