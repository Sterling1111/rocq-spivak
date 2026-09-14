# rocq-spivak

A formalization of Michael Spivak’s *Calculus* in the Rocq Prover (formerly Coq), with a reusable mathematics library and chapter-by-chapter exercise proofs.

The project develops textbook-style definitions of limits, continuity, derivatives, integrals, sequences, series, and transcendental functions on top of the standard library’s real numbers. It also includes supporting algebra, combinatorics, complex analysis, and companion exercises in `ATTAM/`.

**Work in progress:** some files contain unfinished proofs or placeholder statements. The default build covers the files listed in [`_CoqProject`](_CoqProject), which is a subset of the source tree. A successful build does not establish that every exercise is complete: Rocq accepts statements closed with `Admitted` as assumptions.

## Exercise progress

As of September 13, 2026, **624 problems have substantive formal statements**, and **323 of those have completed proofs**. The remaining **301 stated problems** have unfinished proofs or placeholder parts.

Counts cover `Calculus/Chapter*/Problem*.v`, including appendix problems, with each file counted once regardless of its number of subparts. A problem counts as stated when it contains at least one non-placeholder lemma or theorem statement, including statements followed by `Abort` or `Admitted`. Statements whose conclusion is just `True` are excluded. Of the 647 problem files, 23 contain only placeholders, imports, definitions, or plots and do not count as stated problems. The shared library and `ATTAM/` are outside these counts.

A problem counts as completed when its statements have proofs closed with `Qed` or `Defined`, with no placeholder statements, `Admitted`, `Abort`, `admit`, or local axiom/parameter declarations in the file. Comments are ignored. These are source-level counts of the parts currently present; they do not certify coverage of every textbook subpart or the absence of assumptions in imported dependencies.

| Chapter | Problems with statements | Completed problems |
| --- | ---: | ---: |
| 1 | 25 | 24 |
| 2 | 26 | 26 |
| 3 | 28 | 25 |
| 5 | 36 | 31 |
| 6 | 16 | 15 |
| 7 | 18 | 16 |
| 8 | 20 | 14 |
| 9 | 30 | 30 |
| 10 | 31 | 19 |
| 11 (including appendix) | 44 | 39 |
| 12 | 14 | 11 |
| 13 (including appendix) | 45 | 9 |
| 14 | 30 | 11 |
| 15 | 30 | 20 |
| 18 | 44 | 9 |
| 19 (including appendix) | 62 | 5 |
| 20 | 28 | 5 |
| 21 | 8 | 0 |
| 22 | 33 | 13 |
| 23 | 30 | 0 |
| 24 | 25 | 0 |
| 28 | 1 | 1 |
| **Total** | **624** | **323** |

## Explore the mathematics

| Topic | Starting points |
| --- | --- |
| Real numbers, sets, and completeness | [Real.v](Lib/Real.v), [Reals_util.v](Lib/Reals_util.v), [Sets.v](Lib/Sets.v), [Completeness.v](Lib/Completeness.v) |
| Limits and continuity | [Limit.v](Lib/Limit.v), [Continuity.v](Lib/Continuity.v) |
| Derivatives, Rolle’s theorem, and the mean value theorem | [Derivative.v](Lib/Derivative.v) |
| Partitions, integration, and the fundamental theorem of calculus | [Partition.v](Lib/Partition.v), [Integral.v](Lib/Integral.v) |
| Sequences, series, and Taylor’s theorem | [Sequence.v](Lib/Sequence.v), [Series.v](Lib/Series.v), [Taylor.v](Lib/Taylor.v) |
| Trigonometric and exponential functions | [Trigonometry.v](Lib/Trigonometry.v), [Exponential.v](Lib/Exponential.v) |
| Complex numbers and complex analysis | [Complex.v](Lib/Complex.v), [ComplexFunctions.v](Lib/ComplexFunctions.v) |
| Vectors and matrices, as lists and coordinate functions | [Guide](Lib/LinearAlgebra.md), [FunctionalVector.v](Lib/FunctionalVector.v), [FunctionalMatrix.v](Lib/FunctionalMatrix.v), [examples](Lib/VectorMatrixExamples.v) |
| Vector functions and planetary motion | [Vector calculus](Lib/VectorCalculus.v), [Chapter 4 examples](Calculus/Chapter4/VectorFunctions.v), [PlanetaryMotion.v](Calculus/Chapter17/PlanetaryMotion.v), [Chapter 17 guide](Calculus/Chapter17/README.md) |
| Exact rational REF and RREF, with correctness proofs over rationals and reals | [Guide](Lib/RowReduction.md), [RowReduction.v](Lib/RowReduction.v), [tests and examples](Lib/RowReductionTests.v) |
| Backpropagation: four fundamental equations and one training step | [Guide](Backprop/README.md), [NeuralNet](Backprop/NeuralNet.v), [proofs](Backprop/Correctness.v), [decreasing the loss](Backprop/Descent.v) |
| Exercise proofs | [Calculus/](Calculus/), [ATTAM/](ATTAM/) |

The notation follows the textbook where practical. For example, the two parts of the fundamental theorem of calculus are stated in `Lib/Integral.v` as:

```coq
Theorem FTC1 : ∀ f a b,
  a < b -> continuous_on f [a, b] ->
  ⟦ der ⟧ (λ x, ∫ a x f) [a, b] = f.

Theorem FTC2 : ∀ a b f g,
  a < b -> continuous_on f [a, b] ->
  ⟦ der ⟧ g [a, b] = f -> ∫ a b f = g b - g a.
```

Exercise files use paths such as `Calculus/Chapter10/Problem1.v`. Each chapter has a `Prelude.v` that collects its imports and notation; individual results generally use names such as `lemma_10_1_i`.

## Build

Run commands from the repository root with your opam environment active.

### Dependencies

The development environment uses the following versions:

| Package | Version |
| --- | --- |
| `rocq-core` | 9.1.1 |
| `rocq-stdlib` | 9.1.0 |
| `coq-interval` | 4.11.4 |
| `coq-coquelicot` | 3.4.4 |
| `coq-flocq` | 4.2.2 |
| `coq-mathcomp-ssreflect` / `rocq-mathcomp-ssreflect` | 2.5.0 |

On Debian or Ubuntu, install the system tools and Python dependency:

```bash
sudo apt-get update
sudo apt-get install -y opam build-essential pkg-config python3 python3-sympy gnuplot
```

SymPy supplies candidate antiderivatives for `auto_int`. Gnuplot renders the plots generated by selected exercises.

For a new opam installation, initialize it and add the Coq package repository:

```bash
opam init -y
eval "$(opam env)"
opam repo add coq-released https://coq.inria.fr/opam/released
```

Install the proof dependencies in your chosen switch:

```bash
opam install -y \
  rocq-core.9.1.1 rocq-stdlib.9.1.0 \
  coq-interval.4.11.4 coq-coquelicot.3.4.4 coq-flocq.4.2.2 \
  coq-mathcomp-ssreflect.2.5.0 rocq-mathcomp-ssreflect.2.5.0
eval "$(opam env)"
```

### Compile

```bash
rocq makefile -f _CoqProject -o Makefile
make -j2
```

Adjust the job count to suit your machine. The generated Makefile builds the Rocq sources and OCaml tactic plugins; [`Makefile.local`](Makefile.local) adds plot generation after the main build.

To rebuild a particular exercise that is listed in `_CoqProject`:

```bash
make Calculus/Chapter1/Problem1.vo
```

For a file outside that list, first build its dependencies, then compile it with the project’s logical paths:

```bash
rocq compile -R Lib Lib -R Calculus Calculus -R ATTAM ATTAM -I src \
  Calculus/Chapter19/Problem25.v
```

Use `make clean` to remove build artifacts. If you add a source file to the default build, update `_CoqProject` and regenerate the Makefile.

### Optional simplex solver

The custom `psatz` tactic in [`Lib/Psatz.v`](Lib/Psatz.v) uses a C++ helper. Build it before using that tactic:

```bash
sudo apt-get install -y libeigen3-dev libboost-all-dev
g++ -O3 $(pkg-config --cflags eigen3) src/simplex.cpp -o src/simplex_solver
```

`Lib/Psatz.v` is not currently listed in the default build. Run proofs using its helper from the repository root, where the plugin expects `src/simplex_solver`.

### Editor support

Open the repository root in a Rocq-aware editor so it can read `_CoqProject`. For VS Code with VsRocq, install the language server in the same opam switch:

```bash
opam install vsrocq-language-server
```

## Automation

[`Lib/Tactics.v`](Lib/Tactics.v) provides `auto_limit`, `auto_cont`, `auto_diff`, and `auto_int`. [`Lib/Reals_util.v`](Lib/Reals_util.v) provides `solve_R` for real arithmetic, including square roots, absolute values, and casts.

After building the library, this example illustrates the imports and notation needed for a limit proof:

```coq
From Lib Require Import Imports Tactics Limit.
Import LimitNotations.
Open Scope R_scope.

Goal ⟦ lim 3 ⟧ (λ x, (x^3 - 8) / (x - 2)) = 19.
Proof. auto_limit. Qed.
```

The calculus tactics combine proof by reflection with Ltac automation: they reify supported expressions into an `expr` syntax tree, compute over that representation, and apply proved correctness lemmas such as `derive_correct` and `cont_correct`. For example, `auto_diff` computes a symbolic derivative with `derive_expr` and uses its correctness theorem to reduce the goal to domain conditions and algebraic equalities. Rocq’s kernel checks the resulting proofs.

For vector and matrix equality, `auto_vec` / `solve_vec` and `auto_mat` / `solve_mat` handle concrete entries and symbolic algebra. Import `FunctionalMatrix` to use them with both list and functional representations. See the [linear algebra guide](Lib/LinearAlgebra.md#equality-solvers) for examples, supported rules, and the `vec_simpl` / `mat_simpl` tactics for exposing coordinate goals.

Proof search and the automation for side conditions are heuristic, so some goals may require subsequent proof steps. `solve_R` closes goals it can solve and otherwise leaves them unchanged; use `solve [solve_R]` when complete success is required.

`auto_int` asks a persistent Python/SymPy worker for an antiderivative, then checks the required continuity, derivative, and endpoint obligations in Rocq. Cached candidates still go through proof checking. The worker can be configured with:

| Variable | Purpose |
| --- | --- |
| `AUTO_INT_PYTHON` | Python executable; defaults to `python3`. It must have SymPy installed. |
| `AUTO_INT_SCRIPT` | Path to `src/auto_int.py`; otherwise the plugin searches the current directory and its parents. |
| `AUTO_INT_TIMEOUT` | Request timeout in seconds; defaults to 30. |

### Arithmetic with the Dedekind-cut `Real` type

[`Lib/RealTactics.v`](Lib/RealTactics.v) provides arithmetic automation for the
custom `Real` type from `Lib/Real.v`. Import it and open `Real_scope` to use
integer and decimal numerals, fractions, and natural-number powers:

```coq
From Lib Require Import RealTactics.
Open Scope Real_scope.

Example decimal_sum : 1.23 + 2.56 = 3.79.
Proof. real_lra. Qed.

Example linear_bound : forall x : Real, 2 * x + 3 < 7 -> x < 2.
Proof. real_lra. Qed.

Example square_nonnegative : forall x : Real, 0 <= x ^ 2.
Proof. real_nra. Qed.

Example cancel_fraction : forall x : Real, x <> 0 -> x / x = 1.
Proof. solve_real. Qed.
```

Use `real_lra` for linear arithmetic, `real_nra` for polynomial arithmetic,
`real_field` for rational identities, and `solve_real` to also try automation
for absolute values and reciprocals. These tactics translate the goal and
hypotheses through the proved `cut_value` correspondence and produce proofs
checked by Rocq. They fail without changing the goal if they cannot solve it.
Use `real_to_R` to expose the translated goal for further manual tactics.
The existing `ring` and `field` tactics also remain available.

Decimal literals are exact: `1.23` embeds the rational `123/100`, with no
floating-point rounding. Scientific notation such as `1.23e-2` is also supported.
The literals `0` and `1` still use the original `Rzero` and `Rone` definitions.
`Real_of_Q (1#2)%Q` embeds an exact rational; `(1 / 2)%Real` uses the custom
field operations. This is symbolic proof automation, not a decimal evaluator
for arbitrary cuts, whose definitions use classical choice. Nonlinear proof
search is incomplete, and division identities can require nonzero hypotheses.

## Compatibility with other libraries

- [`Lib/StdlibCompat.v`](Lib/StdlibCompat.v) connects the project’s definitions to standard-library limits, continuity, derivatives, sequences, series, and transcendental functions.
- [`Lib/CoquelicotCompat.v`](Lib/CoquelicotCompat.v) provides bridges to Coquelicot’s limits, derivatives, continuity, sequences, and series.
- [`Lib/MathCompCompat.v`](Lib/MathCompCompat.v) contains a commented-out MathComp compatibility development. Its bridge lemmas are currently inactive.

## Repository layout

```text
Lib/          Shared definitions, theorems, notation, and tactics
Calculus/     Spivak exercises organized by chapter and problem
ATTAM/        Companion exercise developments
src/          OCaml plugins, SymPy worker, and C++ simplex helper
_CoqProject   Logical paths, compiler options, and default build inputs
Makefile.local  Additional build rules for plots
```

## Contributing

Contributions are welcome: complete unfinished proofs, formalize exercises, improve the shared library, or extend the automation. Follow the surrounding chapter’s naming and import conventions, and compile each changed file with its dependencies. Include new files in `_CoqProject` when they should be part of the default build.

## License

[MIT](LICENSE).
