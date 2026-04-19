From Calculus.Chapter18 Require Import Prelude.

Local Notation exp := Rtrigo_def.exp.

Definition sinh x := (exp x - exp (-x)) / 2.
Definition cosh x := (exp x + exp (-x)) / 2.
Definition tanh x := (exp x - exp (-x)) / (exp x + exp (-x)).

Definition p_sinh := ltac:(plot sinh (-3) 3 with (i_size 2000 1000)).
Definition p_cosh := ltac:(plot cosh (-3) 3 with (i_size 2000 1000)).
Definition p_tanh := ltac:(plot tanh (-3) 3 with (i_size 2000 1000)).

Plot p_sinh as "Calculus/Chapter18/Problem7/sinh.gp".
Plot p_cosh as "Calculus/Chapter18/Problem7/cosh.gp".
Plot p_tanh as "Calculus/Chapter18/Problem7/tanh.gp".