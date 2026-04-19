From Calculus.Chapter18 Require Import Prelude.

Local Notation exp := Rtrigo_def.exp.

Definition f2 x := exp x / (x * x).

Definition p_f2 := ltac:(plot f2 (1/2) 5 with (i_size 2000 1000)).

Plot p_f2 as "Calculus/Chapter18/Problem16/f2.gp".