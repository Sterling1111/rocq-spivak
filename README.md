<div align="center">

# rocq-spivak

**Spivak’s calculus, formalized in Rocq.**

From epsilon–delta limits to automated integrals and verified backpropagation.

[Examples](#a-taste-of-the-library) · [Automation](#automation) · [Compatibility](#compatibility) · [Theorems](#theorems-worth-exploring) · [Build](#build-and-install)

</div>

---

**rocq-spivak is a calculus textbook you can explore as code.** It formalizes
Michael Spivak’s *Calculus* in [Rocq](https://rocq-prover.org/) (formerly Coq),
with definitions, theorems, and exercise proofs written in notation close to
the mathematics on the page. Rocq checks each completed proof.

The project has two parts: a reusable library of analysis and automation in
[`Lib/`](Lib/), and a growing collection of textbook exercises in
[`Calculus/`](Calculus/). Beyond calculus, the source tree explores exact linear
algebra, complex numbers, algorithmic recurrences, and neural-network gradients.

### What’s inside

| Start with… | Explore… |
| --- | --- |
| **Foundations** | [Real numbers as Dedekind cuts](Lib/Real.v), [sets](Lib/Sets.v), and [completeness](Lib/Completeness.v) |
| **Calculus** | [Limits](Lib/Limit.v), [continuity](Lib/Continuity.v), [derivatives](Lib/Derivative.v), and [integrals](Lib/Integral.v) |
| **Infinite processes** | [Sequences](Lib/Sequence.v), [series](Lib/Series.v), and [Taylor’s theorem](Lib/Taylor.v) |
| **Algebra and geometry** | [Complex numbers](Lib/Complex.v), [vectors and matrices](Lib/VectorMatrixExamples.v), and [exact row reduction](Lib/RowReduction.v) |
| **Applications** | [Asymptotic analysis](Lib/Asymptotics.v) and [backpropagation](Backprop/README.md) |

The exercise collection is a work in progress, with unfinished proofs and
placeholder statements. The opam package covers a smaller calculus library;
its [scope and assumptions audit](packaging/ASSUMPTIONS.md) explains what is
included and the classical foundations it uses.

## A taste of the library

### Limits, continuity, and derivatives

Mix transcendental functions, differentiate a sigmoid, or jump straight to a
tenth derivative. Each example closes with a single tactic; the imports and
notation setup make the block ready to copy into a `.v` file.

```coq
From Lib Require Import Imports Tactics Limit Continuity Derivative
                        Trigonometry Exponential.
Import LimitNotations DerivativeNotations.
Open Scope R_scope.

Example transcendental_limit :
  ⟦ lim 0 ⟧ (fun x => (sin x + cos x) / exp x) = 1.
Proof. auto_limit. Qed.

Example continuous_composition :
  continuous (fun x => exp (sin (x^2 + 1)) / (x^2 + 1)).
Proof. auto_cont. Qed.

Example sigmoid_gradient :
  ⟦ der ⟧ (fun x => 1 / (1 + e ^^ (-x))) =
  (fun x => (1 / (1 + e ^^ (-x))) * (1 - 1 / (1 + e ^^ (-x)))).
Proof. auto_diff. Qed.

Example tenth_derivative :
  ⟦ der ^ 10 ⟧ (fun x => e ^^ x) = (fun x => e ^^ x).
Proof. auto_diff. Qed.
```

### Definite integrals

Integration by parts, logarithms, and inverse trigonometric substitutions all
use the same interface. SymPy finds a candidate; Rocq checks the proof.

```coq
From Lib Require Import Imports Tactics Integral Trigonometry Exponential.
Import IntegralNotations.
Open Scope R_scope.

Example integration_by_parts : ∫ 0 1 (fun x => x * exp x) = 1.
Proof. auto_int. Qed.

Example logarithmic_area : ∫ 1 2 (fun x => log x) = 2 * log 2 - 1.
Proof. auto_int. Qed.

Example arcsine_area : ∫ 0 (1/2) (fun x => 1 / sqrt (1 - x^2)) = π / 6.
Proof. auto_int. Qed.

Example recover_pi : ∫ 0 1 (fun x => 1 / (x^2 + 1)) = π / 4.
Proof. auto_int. Qed.
```

The same tactic checks antiderivatives. Here the notation says that the
function on the right differentiates to the integrand:

```coq
From Lib Require Import Imports Tactics Integral Trigonometry.
Import IntegralNotations.
Open Scope R_scope.

Example reverse_chain_rule :
  ∫ (fun x => sin x ^ 5 * cos x) = (fun x => sin x ^ 6 / 6).
Proof. auto_int. Qed.
```

<details>
<summary><strong>Beyond calculus: exact row reduction</strong></summary>

The development library also computes with rational matrices. This example
reduces an augmented matrix to RREF with exact fractions:

```coq
From Lib Require Import Imports RowReduction.
Import VectorNotations MatrixNotations.
Local Open Scope Qc_scope.
Local Open Scope V_Scope.
Local Open Scope M_Scope.

Example reduce_matrix :
  matrix_rref (⟨⟨2, 1, 3⟩, ⟨0, 3, 1⟩⟩ : matrix Qc 2 3) =
  ⟨⟨1, 0, 4/3⟩, ⟨0, 1, 1/3⟩⟩.
Proof. qc_mat_compute. Qed.
```

[RowReduction.v](Lib/RowReduction.v) proves correctness of the reduction,
including preservation of row equivalence and the resulting REF/RREF shape.
See [more examples](Lib/RowReductionTests.v), including results transported to
real matrices. This module is part of the source build, outside the initial
calculus package.

</details>

## Automation

The main entry point is [`Lib/Tactics.v`](Lib/Tactics.v).

| Tactic | What it proves |
| --- | --- |
| `auto_limit` | Limits of supported expressions |
| `auto_cont` | Continuity, including compositions and interval domains |
| `auto_diff` | Derivative identities using symbolic differentiation |
| `auto_int` | Integral identities using checked antiderivatives |
| `solve_R` | Real arithmetic involving roots, absolute values, and casts |

The tactics turn expressions into syntax trees, compute with them, and apply
proved correctness lemmas. For differentiation, this connects a symbolic
derivative to its mathematical meaning. For integration, SymPy proposes an
antiderivative. `auto_int` proves the derivative, continuity, and endpoint
obligations, and Rocq’s kernel checks the resulting proof against the library’s
logical assumptions:

```mermaid
flowchart LR
    A[Integral] --> B[SymPy candidate]
    B --> C[Prove derivative and side conditions]
    C --> D[Rocq kernel check]
```

Cached candidates go through the same proof checking. Tactics can leave domain
conditions or algebraic goals for you to finish. `solve_R` leaves a goal
unchanged when it cannot solve it; `solve [solve_R]` fails instead.

<details>
<summary><strong>Configure the SymPy worker</strong></summary>

| Environment variable | Purpose |
| --- | --- |
| `AUTO_INT_PYTHON` | Python executable; defaults to `python3`. It must have SymPy installed. |
| `AUTO_INT_SCRIPT` | Optional path to `auto_int.py`. Otherwise the plugin searches for `src/auto_int.py` in the current directory and its parents, then in the installed `calculus` findlib package. |
| `AUTO_INT_TIMEOUT` | Request timeout in seconds; defaults to `30`. |

</details>

<details>
<summary><strong>Vectors, matrices, and Dedekind-cut reals</strong></summary>

The source tree includes `auto_vec` / `solve_vec` and `auto_mat` / `solve_mat`
for vector and matrix equalities. Both list and coordinate-function
representations are supported; see [the examples](Lib/VectorMatrixExamples.v).
Use `vec_simpl` / `mat_simpl` to expose coordinate goals.

[`RealTactics.v`](Lib/RealTactics.v) provides arithmetic automation for the
separate Dedekind-cut `Real` type defined in [`Real.v`](Lib/Real.v):

```coq
From Lib Require Import RealTactics.
Open Scope Real_scope.

Example exact_decimal_sum : 1.23 + 2.56 = 3.79.
Proof. real_lra. Qed.

Example square_nonnegative : forall x : Real, 0 <= x^2.
Proof. real_nra. Qed.

Example cancel_fraction : forall x : Real, x <> 0 -> x / x = 1.
Proof. solve_real. Qed.
```

Decimal literals are exact rational values. `real_lra`, `real_nra`,
`real_field`, and `solve_real` transport goals through a proved correspondence
with standard reals. Use `real_to_R` to expose that translation for a manual
proof. Nonlinear automation is incomplete, and division can require nonzero
hypotheses.

</details>

## Compatibility

The main calculus library uses Rocq’s standard real type `R`, with its own
textbook-style definitions and notation. Compatibility lemmas let you move
between those definitions and existing analysis libraries.

| Library | Available bridges |
| --- | --- |
| **Rocq Stdlib** | [Limits, continuity, derivatives, Riemann integrals, sequences, series, and transcendental functions](Lib/StdlibCompat.v) |
| **Coquelicot** | [Limits, derivatives, continuity, sequences, and series](Lib/CoquelicotCompat.v). Integral bridges are unfinished (`Abort`). |
| **MathComp** | [An exploratory compatibility file](Lib/MathCompCompat.v); its bridge development is currently commented out. |

For example, prove a standard-library continuity statement using this project’s
automation:

```coq
From Lib Require Import Imports Tactics StdlibCompat.
Open Scope R_scope.

Example stdlib_continuity : forall a : R,
  continuity_pt (fun x => x^2 + 1) a.
Proof.
  intro a. apply continuous_compat. auto_cont.
Qed.
```

`StdlibCompat` is included in the calculus package. `CoquelicotCompat`, the
linear algebra modules, `RealTactics`, Taylor’s theorem, asymptotics, and
backpropagation are available through the source build.

**Platform support:** the package was validated on Ubuntu 24.04. Its dependency
bounds match the tested Rocq and analysis-library versions. Native Windows is
currently excluded by the SymPy dependency package. See the
[validation record](packaging/VALIDATION.md) for the tested environment.

## Theorems worth exploring

Each result below pairs its informal meaning with its formal Rocq statement.
The statements are excerpts from the linked source files, with proofs omitted.

### The fundamental theorem of calculus

**Informal — [`FTC1`](Lib/Integral.v):** If $a<b$ and $f$ is continuous on
$[a,b]$, the accumulated area $F(x)=\int_a^x f(t)\,dt$ has derivative $f(x)$
on that interval, using one-sided derivatives at its endpoints.

**Formal:**

```coq
Theorem FTC1 : ∀ f a b,
  a < b -> continuous_on f [a, b] ->
  ⟦ der ⟧ (λ x, ∫ a x f) [a, b] = f.
```

**Informal — [`FTC2`](Lib/Integral.v):** If $a<b$, $f$ is continuous on
$[a,b]$, and $g'=f$ there, the definite integral is the change in $g$:

$$
\int_a^b f(x)\,dx = g(b)-g(a).
$$

**Formal:**

```coq
Theorem FTC2 : ∀ a b f g,
  a < b -> continuous_on f [a, b] ->
  ⟦ der ⟧ g [a, b] = f -> ∫ a b f = g b - g a.
```

The development includes partitions, Darboux sums, Riemann integration, and a
proof that the two integral constructions agree. [`Derivative.v`](Lib/Derivative.v)
contains Rolle’s theorem and the mean value theorem used along the way.

### Taylor’s theorem, with concrete bounds

**Informal — [`Taylors_Theorem`](Lib/Taylor.v):** If $a<x$ and $f$ is
$(n+1)$ times differentiable on an open interval extending past both $a$ and
$x$, its degree-$n$ Taylor polynomial $P_n$ about $a$ has an exact remainder
at some $t\in(a,x)$:

$$
f(x)-P_n(x)=\frac{f^{(n+1)}(t)}{(n+1)!}(x-a)^{n+1}.
$$

**Formal:** `R(n, a, f)` is the Taylor remainder, and `⟦ Der ^ k t ⟧ f`
is the value of the $k$th derivative at $t$.

```coq
Theorem Taylors_Theorem : forall n a x f,
  a < x ->
  (exists δ, δ > 0 /\ nth_differentiable_on (S n) f (a - δ, x + δ)) ->
  exists t, t ∈ (a, x) /\
    R(n, a, f) x = (⟦ Der ^ (n + 1) t ⟧ f) / ((n + 1)!) * (x - a) ^ (n + 1).
```

**Informal — [`e_bounds` and `π_bounds`](Lib/Taylor.v):** Taylor estimates
give certified decimal bounds on both constants:

$$
2.7182 < e < 2.7183
\qquad\text{and}\qquad
3.141591 < \pi < 3.141596.
$$

**Formal:** These decimal literals are exact rational numbers, so these are
inequalities over the reals.

```coq
Lemma e_bounds : 2.7182 < e < 2.7183.
Theorem π_bounds : 3.141591 < π < 3.141596.
```

### A master theorem for recurrences

**Informal — [`master_theorem`](Lib/Asymptotics.v):** Suppose $a\ge1$, $b>1$,
$f$ and $T$ are nonnegative, and $T(n)>0$ for $n\ge1$. Eventually,
$T(n)=aT(r(n))+f(n)$, where $r(n)$ rounds $n/b$ down or up. Write
$p=\log_b a$. The growth of the work $f(n)$ determines the total cost:

| Work per recursive call | Total cost $T(n)$ |
| --- | --- |
| $f(n)=O(n^{p-\varepsilon})$ for some $\varepsilon>0$ | $\Theta(n^p)$ |
| $f(n)=\Theta(n^p(\log n)^k)$, $k>-1$ | $\Theta(n^p(\log n)^{k+1})$ |
| $f(n)=\Theta(n^p/\log n)$ | $\Theta(n^p\log\log n)$ |
| $f(n)=\Theta(n^p(\log n)^k)$, $k<-1$ | $\Theta(n^p)$ |
| $f(n)=\Omega(n^{p+\varepsilon})$ for some $\varepsilon>0$, with $a f(r(n))\le c f(n)$ eventually for some $0<c<1$ | $\Theta(f(n))$ |

**Formal:** `^^` denotes real exponentiation; `Ο`, `Ω`, and `Θ` are the
library's asymptotic bounds. All five cases appear in one statement:

```coq
Theorem master_theorem : ∀ (a b : ℝ) (f T : ℕ -> ℝ) (r : ℕ -> ℕ),
  a >= 1 -> b > 1 ->
  (∀ n, f n >= 0) ->
  (∀ n, T n >= 0) ->
  (∀ n, (1 <= n)%nat -> T n > 0) ->
  (∀ n : ℕ, r n = ⌊n/b⌋ \/ r n = ⌈n/b⌉) ->
  (∃ N, N >= b /\ (∀ n : ℕ, n >= N -> T n = a * T (r n) + f n)) ->
  ((∃ ε, ε > 0 /\ f = Ο(λ n, n^^((log_ b a) - ε))) ->
    T = Θ(λ n, n^^(log_ b a))) /\
  (∀ k, k > -1 -> f = Θ(λ n, n^^(log_ b a) * (lg n)^^k) ->
    T = Θ(λ n, n^^(log_ b a) * (lg n)^^(k + 1))) /\
  (f = Θ(λ n, n^^(log_ b a) * (lg n)^^(-1)) ->
    T = Θ(λ n, n^^(log_ b a) * lg (lg n))) /\
  (∀ k, k < -1 -> f = Θ(λ n, n^^(log_ b a) * (lg n)^^k) ->
    T = Θ(λ n, n^^(log_ b a))) /\
  ((∃ ε c N, ε > 0 /\ 0 < c < 1 /\ f = Ω(λ n, n^^((log_ b a) + ε)) /\
    (∀ n : ℕ, n >= N -> a * f (r n) <= c * f n)) -> T = Θ(f)).
```

The file ends with worked asymptotic examples.

### Why a gradient step decreases the loss

**Informal — [`one_step_decreases_error`](Backprop/Descent.v):** For a sigmoid
network with squared-error loss $C$ and a fixed input and target, let
$g=\nabla C(\theta)$. If $g\ne0$, there is a threshold $\eta_0>0$ such that
every learning rate $0<\eta<\eta_0$ gives

$$
C(\theta-\eta g) < C(\theta)-\frac{\eta}{2}\lVert g\rVert^2.
$$

**Formal:** `train_once` updates the weights and biases using backpropagation;
`gradient_norm_sq` is the squared norm of that gradient.

```coq
Theorem one_step_decreases_error n (s : Architecture n) (net : NeuralNet s) a target :
  0 < gradient_norm_sq s (parameters net) a target ->
  exists eta0, 0 < eta0 /\ forall eta, 0 < eta < eta0 ->
    C s (parameters (train_once net a target eta)) a target <
    C s (parameters net) a target -
      eta * gradient_norm_sq s (parameters net) a target / 2.
```

The proof establishes the existence of a suitable learning-rate threshold;
it does not compute a numerical threshold or guarantee decrease for every rate.
The [backpropagation development](Backprop/README.md) also proves the four
standard backpropagation equations.
[Examples](Backprop/Examples.v) work through a single neuron and a network with
a hidden layer.

## Build and install

The following setup uses Debian/Ubuntu. Run the project commands from the
repository root.

### 1. Get the source and tools

```bash
sudo apt-get update
sudo apt-get install -y git opam build-essential pkg-config python3 python3-sympy

git clone https://github.com/Sterling1111/spivak-rocq.git
cd spivak-rocq
```

For a new opam setup, initialize it and create a switch:

```bash
opam init --bare -y
opam switch create rocq-spivak 4.14.1
eval "$(opam env)"
opam repo add rocq-released https://rocq-prover.org/opam/released
```

If you already have a suitable switch, activate it and add the repository if
needed. The development environment uses OCaml 4.14.1 and Rocq 9.1.1.

### 2. Choose what to build

| Build | Includes | Use it to… |
| --- | --- | --- |
| **Calculus package** | Calculus tactics, their dependencies, and Stdlib bridges | Import the library from your own Rocq projects |
| **Source build** | Development modules and exercises listed in `_CoqProject` | Explore the wider library and work on proofs |

**Install the calculus package**

```bash
opam pin add conf-python3-sympy ./packaging --kind=path -y
opam pin add rocq-spivak . --kind=path -y
```

These local pins work without waiting for upstream package publication. Opam
installs the dependencies and builds the files in
[`_CoqProject.opam`](_CoqProject.opam). The calculus examples above then work
from any directory, without source-tree flags or an `AUTO_INT_SCRIPT` override.
Exercise collections and modules outside that manifest are not installed.

**Build the development library and selected exercises**

```bash
opam install -y \
  rocq-core.9.1.1 rocq-stdlib.9.1.0 \
  coq-interval.4.11.4 coq-coquelicot.3.4.4 coq-flocq.4.2.2 \
  coq-mathcomp-ssreflect.2.5.0 rocq-mathcomp-ssreflect.2.5.0 \
  ocamlfind zarith
eval "$(opam env)"

rocq makefile -f _CoqProject -o Makefile
make -j2 BUILD_PLOTS=no
```

[`_CoqProject`](_CoqProject) selects the files for this build. Adjust `-j2` to
suit your machine. To generate exercise plots as well, install `gnuplot` and
run `make -j2` with the default plot rules in [`Makefile.local`](Makefile.local).

### 3. Try a proof

Save the [definite-integral example block](#definite-integrals), including its
imports, as `Example.v`. With the package installed:

```bash
rocq compile Example.v
```

With a source build, run this from the repository root instead:

```bash
rocq compile -R Lib Lib -I . -I src Example.v
```

<details>
<summary><strong>Build individual exercises</strong></summary>

To rebuild an exercise already in the manifest:

```bash
make Calculus/Chapter1/Problem1.vo
```

For a file outside the manifest, first build its dependencies, then compile it
with the project’s logical paths:

```bash
rocq compile -R Lib Lib -R Calculus Calculus -R ATTAM ATTAM \
  -R Backprop Backprop -I . -I src Calculus/Chapter19/Problem25.v
```

</details>

<details>
<summary><strong>SymPy on other systems</strong></summary>

Install SymPy for the `python3` found on `PATH`. If a system package is
unavailable, a virtual environment is one option:

```bash
python3 -m venv "$HOME/.venvs/rocq-spivak"
. "$HOME/.venvs/rocq-spivak/bin/activate"
python -m pip install sympy
export AUTO_INT_PYTHON="$(command -v python3)"
```

Keep the environment active when installing the conf package: its check invokes
`python3` directly. `AUTO_INT_PYTHON` selects the interpreter used by subsequent
`auto_int` sessions.

</details>

<details>
<summary><strong>Editor setup and package smoke tests</strong></summary>

For VS Code with VsRocq, install the language server in the same opam switch,
then open the repository root so the editor can read `_CoqProject`:

```bash
opam install vsrocq-language-server
```

After installing the package, check it outside the source tree:

```bash
smoke_dir=$(mktemp -d)
cp packaging/smoke.v packaging/assumptions.v "$smoke_dir/"
(cd "$smoke_dir" && rocq compile smoke.v && rocq compile assumptions.v)
```

The smoke test proves four integrals and checks that an incorrect result is
rejected. The assumptions file reports the logical foundations of selected
public results. See [the audit](packaging/ASSUMPTIONS.md), including the scope
of the pending independent OCaml plugin review.

</details>

<details>
<summary><strong>Optional C++ simplex helper</strong></summary>

The custom `psatz` tactic in [`Lib/Psatz.v`](Lib/Psatz.v) uses an additional
helper:

```bash
sudo apt-get install -y libeigen3-dev libboost-all-dev
g++ -O3 $(pkg-config --cflags eigen3) src/simplex.cpp -o src/simplex_solver
```

`Lib/Psatz.v` is outside the default build and the initial calculus package.
Run proofs that use this helper from the repository root.

</details>

## Find your way around

| Path | Start here for… |
| --- | --- |
| [`Lib/`](Lib/) | Analysis definitions, theorems, tactics, and compatibility lemmas |
| [`Calculus/`](Calculus/) | Spivak exercises, organized by chapter and problem |
| [`ATTAM/`](ATTAM/) | Companion exercise developments |
| [`Backprop/`](Backprop/) | Neural networks, gradient proofs, and worked examples |
| [`src/`](src/) | OCaml tactic plugins, the SymPy worker, and the simplex helper |
| [`packaging/`](packaging/) | Package validation, smoke tests, and the assumptions audit |

Exercise files follow paths such as `Calculus/Chapter10/Problem1.v`.
Each chapter has a `Prelude.v` collecting imports and notation; results commonly
use names such as `lemma_10_1_i`.

Contributions to unfinished exercises, the library, and automation are welcome.
Follow the surrounding conventions and compile changed files with their
dependencies. Add new files to `_CoqProject` when they belong in the default
build, then regenerate the Makefile. `make clean` removes build artifacts.

---

[MIT License](LICENSE) · [Changelog](CHANGELOG.md)
