From Lib Require Export Imports Sets Limit Continuity Derivative Integral Notations Reals_util Inverse Functions Interval Tactics Trigonometry Polynomial Transcendental.
Export LimitNotations IntervalNotations SetNotations DerivativeNotations FunctionNotations IntegralNotations.
Open Scope R_scope.

Definition countable {A : Type} (S : Ensemble A) : Prop :=
  cardinal_le S (Full_set nat).
