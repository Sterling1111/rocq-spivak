(* Compile outside the checkout to exercise the installed full project. *)
From Lib Require Import Imports RealTactics Taylor PI_irrational WI_SI_WO QRT
  Asymptotics RowReduction Psatz.
From Calculus.Chapter18 Require Import Problem49.
From Calculus.Chapter28 Require Import Problem1.
From ATTAM Require Import Chapter35.
From Backprop Require Import Examples.

Check Lib.Taylor.Taylors_Theorem.
Check Lib.PI_irrational.theorem_16_1.
Check Lib.WI_SI_WO.WI_SI_WO.
Check Lib.QRT.quotient_remainder_theorem.
Check Lib.Asymptotics.master_theorem.
Check Lib.RowReduction.matrix_rref.
Check Calculus.Chapter18.Problem49.lemma_18_49.
Check Backprop.Examples.addition_predict.

Example installed_cut_arithmetic : (1.23 + 2.56 = 3.79)%Real.
Proof. real_lra. Qed.

Example installed_simplex : forall x y : Z, (x > y -> y > x -> False)%Z.
Proof. psatz. Qed.
