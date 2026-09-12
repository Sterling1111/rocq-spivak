From Calculus.Chapter18 Require Import Prelude.

Local Notation exp := Rtrigo_def.exp.

(* Graph the family exp(x)/x^n for positive natural n and x <> 0.
   The existing plot below illustrates n = 2 on x > 0. *)
Definition f (n : nat) x := exp x / x^n.
Definition f2 x := exp x / (x * x).

Definition p_f2 := ltac:(plot f2 (1/2) 5 with (i_size 2000 1000)).

Plot p_f2 as "Calculus/Chapter18/Problem16/f2.gp".