From Calculus.Chapter18 Require Import Prelude.

Local Notation exp := Rtrigo_def.exp.
Local Notation ln := Rpower.ln.

Definition f x := Rpower.Rpower x x.

Definition p_f := ltac:(plot f (1/10) 3 with (i_size 2000 1000)).

Plot p_f as "Calculus/Chapter18/Problem14/f.gp".