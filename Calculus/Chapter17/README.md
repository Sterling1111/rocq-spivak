# Chapter 17 — Planetary motion

This development follows the four theorems in the supplied Chapter 17, using
Chapter 4, Appendix 1 for vectors and determinants. Vector calculus is developed
componentwise, as in the Appendix to Chapter 12 that Chapter 17 references.
All proofs in the new development are complete.

Start with [PlanetaryMotion.v](PlanetaryMotion.v): it presents `Theorem1`,
`Theorem2`, `Theorem3`, and `Theorem4` together, in textbook order, with the
orbital equations written explicitly. The supporting files contain their
calculus and geometry proofs.

## Reading order

| File | Mathematics |
| --- | --- |
| [PlanetaryMotion.v](PlanetaryMotion.v) | Main chapter: `Theorem1` through `Theorem4`, velocity, acceleration, area derivative, and conservation law |
| [VectorCalculus.v](../../Lib/VectorCalculus.v) | Vector functions, limits, derivatives, integrals, plane geometry |
| [Chapter 4 vector functions](../Chapter4/VectorFunctions.v) | Lines, graph curves, rotations, signed triangle area |
| [Prelude.v](Prelude.v) | Calculus on an open time interval; local equality and the zero-derivative theorem |
| [Polar.v](Polar.v) | The frame `e, e'`, polar velocity and acceleration, `det(c,c') = r²θ'` |
| [Area.v](Area.v) | Swept area, angular momentum, **Theorem 1** |
| [Conics.v](Conics.v) | Conserved velocity expressions, focal conics, **Theorem 2** |
| [Converse.v](Converse.v) | Differentiating the conic equation, **Theorem 4** |
| [Period.v](Period.v) | Area of an ellipse traversal, period and force coefficient, **Theorem 3** |
| [Examples.v](Examples.v) | A circular orbit through the complete calculus and period-law API |

## Vectors and notation

`fvector R n` is the existing type of real coordinate functions indexed by
`Fin.t n`. A `vector_function n` is a function `R -> fvector R n`.
`plane` abbreviates dimension two. It uses the same vector representation as
the rest of the library, with conversions to the existing list vectors.

```coq
From Calculus.Chapter4 Require Import VectorFunctions.
Open Scope vector_calculus_scope.

(* Ordered pairs, vector addition, and scalar multiplication. *)
Check (⟨1, 2⟩ ⊕ 3 • ⟨4, 5⟩).

(* A derivative assertion, rather than an unchecked derivative expression. *)
Check vector_function_components.
(* ⟦ der ⟧ (fun t => ⟨t, t * t⟩) = (fun t => ⟨1, 2 * t⟩) *)
```

| Notation | Meaning |
| --- | --- |
| `⟨x, y⟩` | A plane vector |
| `v ⊕ w` | Vector addition |
| `k • v` | Scalar multiplication |
| `vx v`, `vy v` | Coordinates |
| `v · w`, `det(v, w)`, `‖ v ‖` | Scalar product, signed determinant, Euclidean norm (`plane_scope`) |
| `v ∥ w` | Parallel vectors (`plane_scope`); with nonzero `v`, `w` is a scalar multiple of `v` |
| `⟦ lim a ⟧ f = v` | Componentwise limit (`vector_calculus_scope`) |
| `⟦ der a ⟧ f = g` | `f` has derivative `g a` at `a` |
| `⟦ der ⟧ f = g` | The derivative assertion at every real parameter |
| `⟦ der ⟧ c (l, u) = v` | The derivative assertion throughout an open time interval |
| `∫ a b f` | Componentwise definite integral |

`lim`, `der`, and `∫` use the same syntax for scalars and vectors. The scope
selects their meaning; it is not inferred from the function's return type.
`Open Scope vector_calculus_scope.` selects vector calculus, and `%vc`
selects it for an individual expression. The scalar meanings remain in
`limit_scope`, `derivative_scope`, and `integral_scope`.

```coq
From Calculus.Chapter17 Require Import PlanetaryMotion.

(* Keep scalar calculus as the default; select vectors explicitly. *)
Check (⟦ der ⟧ (fun t => t) = (fun _ => 1)).
Check (⟦ der ⟧ radial = transverse)%vc.
Check (⟦ lim 0 ⟧ (fun _ => ⟨1, 2⟩) = ⟨1, 2⟩)%vc.
Check (∫ 0 1 radial)%vc.

(* Or work in vector scope and switch back for scalar calculations. *)
Local Open Scope vector_calculus_scope.
Check (⟦ der ⟧ radial = transverse).
Local Open Scope derivative_scope.
Check (⟦ der ⟧ (fun t => t) = (fun _ => 1)).
```

Scopes are opened locally in the chapter files, so importing the chapter
does not change a caller's default calculus. Domain derivatives in vector scope
are two-sided derivatives at every point of the domain; Chapter 17 uses open
intervals, avoiding endpoint conventions.

`plane_limit_iff_norm` proves that componentwise limits are exactly Euclidean
limits. The library also proves uniqueness, limit arithmetic, differentiability
implying continuity, sum/product/chain rules, determinant and dot-product rules,
and both fundamental theorems of calculus for vector functions.

The vector notation lives in exported notation modules. Use `Open Scope
plane_scope.` for the dot product, determinant, norm, and parallelism notation.
Scalar `+`, `*`, and `^` keep their usual meaning throughout the orbital equations.

In `PlanetaryMotion.v`, local abbreviations follow the book: `c`, `c′`, `c″` for
position, velocity, and acceleration; `r`, `r′`, `r″` and `θ`, `θ′`, `θ″` for the
polar coordinates and their derivatives; `e`, `e′` for the moving frame; `A` for
swept area; and `M` for angular momentum at the reference time `t₀`. These are
notations for the checked definitions and derivative witnesses, not new assumptions.

## Main results

Import the complete theory with:

```coq
From Calculus.Chapter17 Require Import PlanetaryMotion.
Open Scope plane_scope.
Check Theorem1.
Check Theorem2.
Check Theorem3.
Check Theorem4.
```

**Theorem 1.** For a twice differentiable, nonzero position curve on an open
interval, central acceleration is equivalent to
`swept_area c v t0 t = rate * (t - t0)`. The conservation theorem also gives
`det(c(t), v(t)) = det(c(t0), v(t0))`.

Swept area means the **signed** integral of `det(c,v)/2`. Its derivative follows
from the fundamental theorem of calculus. For increasing polar angle this is
the positive area convention in the book; clockwise motion gives negative area.
The development does not introduce an independent measure-theoretic definition
of the region swept out by a possibly self-intersecting curve.

**Theorem 2.** An attractive inverse-square orbit with nonzero angular momentum
`M` satisfies

```text
r(t) * (1 + beta * cos(theta(t)) + gamma * sin(theta(t))) = M² / mu.
```

This is the focal conic equation without choosing a rotation angle. The vector
`⟨beta, gamma⟩` specifies its orientation and eccentricity. The theorem
`focal_conic_cartesian` proves the equivalent geometric equation

```text
‖ position(t) ‖ + ⟨beta, gamma⟩ · position(t) = M² / mu.
```

The proof conserves `vx(v) + mu/M * sin(theta)` and
`vy(v) - mu/M * cos(theta)`. These are the integration constants in Spivak's
velocity-as-a-function-of-angle argument. Differentiating them in time avoids
constructing an inverse angle function. The result describes the portion of a
conic occupied by an orbit; it does not assert that every orbit covers an entire
ellipse or hyperbola branch. Classification by eccentricity and geometric
construction of conics are outside this chapter's development.

**Theorem 3.** For a family of central-force elliptic revolutions, a common
inverse-square coefficient `G` is equivalent to

```text
a³ / T² = G / (4 * π²)
```

for every planet. Here `a` and `b` are explicitly **semiaxes**. An
`elliptic_revolution` supplies the focal and eccentric-anomaly coordinate
descriptions, `b² = a * ell`, positive geometric parameters, and an anomaly
increment of `2π` over a positive period. These are explicit geometric and
traversal hypotheses, not assumptions about the force coefficient.

`ellipse_area_per_revolution` proves the swept area is `π*a*b` by differentiating
`a*b/2 * (psi - e*sin(psi))`. Thus the period proof does not depend on the
unfinished ellipse-area exercise in Chapter 13. It yields
`M*T = 2*π*a*b` and `M²/ell = 4*π²*a³/T²`.

**Theorem 4.** A central-force orbit satisfying the focal conic equation with
positive semilatus rectum `ell` and nonzero angular momentum obeys the attractive
inverse-square law with coefficient `M²/ell`.

## Domains and assumptions

`polar_motion l u` records `r, theta`, their first and second derivatives, and
`r(t) > 0` for `l < t < u`. All derivative witnesses are checked using the
project's limit-based scalar derivative. No global extension of an orbit or
smoothness at interval endpoints is required.

The hypotheses `M <> 0`, `mu > 0`, and `ell > 0` appear wherever the mathematical
argument needs them. In particular, radial trajectories with zero angular
momentum are excluded from the nondegenerate conic theorems. No mass parameter
is needed: the force laws are stated as acceleration per unit mass.

Checking `Print Assumptions` for `Theorem1` through `Theorem4` reports only
the classical logic, choice, extensionality, and standard real-number foundations
already used by this project. No admitted mathematical lemma is in those four
theorems' dependency chains.

## Build

All new sources are registered in `_CoqProject`. From the repository root:

```sh
rocq makefile -f _CoqProject -o Makefile
make -j2 Calculus/Chapter17/PlanetaryMotion.vo Calculus/Chapter17/Examples.vo
```
