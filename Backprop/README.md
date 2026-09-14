# Backpropagation, one example and one step

This formalizes the four equations in Sterling Jeppson's *Proof of Backpropagation Algorithm* (February 5, 2022), supplied as `Backpropagation.pdf`. It uses the project's real-number calculus and functional matrix library.

Start with [NeuralNet.v](NeuralNet.v) for the algorithm and [Examples.v](Examples.v) for a tiny network you can follow by hand. The analytic proof helpers live in separate files.

There is one input vector, one target vector, one forward pass that saves a cache, one backward pass through that cache, and one simultaneous weight/bias update. There are no batches, epochs, random initialization, or stopping loops.

## The mathematics

As in the paper, a weight's first index is its destination neuron and its second index is its source neuron:

\[
 z^l_j=\sum_k w^l_{jk}a^{l-1}_k+b^l_j,
 \qquad a^l_j=\sigma(z^l_j),
 \qquad \sigma(x)=\frac1{1+e^{-x}}.
\]

The loss for the single example is

\[
 C=\frac12\sum_j(a^L_j-t_j)^2.
\]

`derivative_at_val_sigma` proves \(\sigma'(x)=\sigma(x)(1-\sigma(x))\) using `Lib.Exponential` and `Lib.Derivative`.

[Correctness.v](Correctness.v) contains the numbered theorems in the paper's order:

| Rocq theorem | Equation |
| --- | --- |
| `theorem_1` | \(\delta^L=\nabla_a C\odot\sigma'(z^L)\) |
| `theorem_2` | \(\delta^l=((w^{l+1})^T\delta^{l+1})\odot\sigma'(z^l)\) |
| `theorem_3` | \(\partial C/\partial b^l_j=\delta^l_j\) |
| `theorem_4` | \(\partial C/\partial w^l_{jk}=a^{l-1}_k\delta^l_j\) |

Import `BackpropNotations` for `σ`, `σ′`, `δ`, `∇aC`, `⊙`, and the derivative notation. Open `derivative_value_scope` for the scalar form:

```coq
Import BackpropNotations.
Open Scope derivative_value_scope.

(* Scalar derivative at x, equal to the real number d. *)
⟦ der x ⟧ f = d

(* Partial derivative at vector v, with respect to coordinate j. *)
⟦ ∂ v, j ⟧ F = d

(* Partial derivative at matrix w, with respect to entry (j,k). *)
⟦ ∂ w, j, k ⟧ F = d
```

The scalar notation uses your existing `derivative_at_val`, so the right-hand side is a number rather than a derivative function. Use `Open Scope derivative_scope.` for your original function-valued form, or `Open Scope derivative_value_scope.` for the number-valued form. `%derivative_value` also selects the latter explicitly. The partial notation uses the same brackets with `∂` instead of `der`. Theorems 3 and 4 use it directly for biases and weights.

These are statements about actual derivatives. `⟦ ∂ v, j ⟧ F` (defined by `partial F v j`) takes the library's derivative of the scalar function \(h\mapsto F(v+h e_j)\) at zero, holding all other coordinates fixed. `delta` is defined by that partial derivative of the downstream loss. It is **not** defined by the backward recurrence.

The proof first establishes `backprop_derivative`: along any differentiable curve of weights, biases, and inputs, the loss derivative equals the dot product with the values returned by the backward pass. The proof proceeds layer by layer, applying the library's scalar sum, product, and chain rules. `delta_correct` then connects these computed values to the independently defined partial derivatives. The numbered equations follow from that connection.

## The small Rocq network

`Vec n` and `Mat m n` are aliases for your `fvector R n` and `fmatrix R m n`. Forward multiplication and backward multiplication by the transpose use `fmatrix_mult` and `fmatrix_transpose`. Shape errors are ruled out by the types; there is no truncation or default value for an invalid index. `Fin.F1` is the first coordinate, corresponding to index 1 in the paper.

An architecture specifies the widths. For example:

```coq
Definition shape := Dense 2 3 (Dense 3 1 (Output 1)).
```

This is a 2 → 3 → 1 network. `Output 1` marks its end and adds no extra layer or activation. Parameters at each `Dense` are `((weights, biases), remaining_parameters)`; the end has `tt`. `NeuralNet shape` is a record holding those parameters.

The four main functions are:

```coq
forward_pass shape parameters input     (* cache activations and weighted inputs *)
backward_pass shape parameters cache target
step shape eta parameters gradients
train_once net input target eta        (* combines the three operations *)
```

`backward_pass` returns `(input_derivative, parameter_gradients)`. Returning the input derivative lets the preceding layer use it. All parameter gradients use the original weights. `step` changes all weights and biases together after the backward pass has finished.

`C shape parameters input target` evaluates the scalar loss. `backprop` abbreviates `backward_pass` applied to the cache from `forward_pass`; the proofs use this shorthand.

The paper's layer superscripts are represented by the location in the recursive architecture. In Theorems 2–4, `s,p` denote the remaining network after the layer being studied. For an output layer there is no remaining trainable layer, so Theorem 1 uses `Output n`. For an interior layer, the preceding activation is held fixed and the entire remaining network is included in the differentiated loss.

The correspondence with [neural_net.py](https://github.com/Sterling1111/Neural-network-from-scratch-in-python/blob/master/neural_net.py) is its `forward_propagate`, `backward_propagate`, and `gradient_descent` methods. The batching and averaging in `learn` are outside this development. The Python derivative helper takes an already computed activation; here `sigma' z` expresses the same quantity as \(\sigma(z)(1-\sigma(z))\).

The operations are logical functions over `R`, as requested. They are not an extracted numerical implementation: the real numbers and the library's exponential use classical mathematics.

## Why one step decreases the loss

Let \(g\) be the full vector of weight and bias gradients, \(G=\|g\|^2\), and \(\theta\) the original parameters. `training_direction_derivative` proves

\[
 \left.\frac{d}{d\eta}C(\theta-\eta g)\right|_{\eta=0}=-G.
\]

`learning_rate_remainder` makes the epsilon statement precise. For every \(\epsilon>0\), there exists \(\eta_0>0\) such that, whenever \(0<\eta<\eta_0\),

\[
 \big|C(\theta-\eta g)-C(\theta)+\eta G\big|<\eta\epsilon.
\]

Thus, for **any \(0<\epsilon<G\)** and sufficiently small positive learning rate, `error_decreases_epsilon` gives

\[
 C(\theta-\eta g)<C(\theta)-\eta(G-\epsilon).
\]

Taking \(\epsilon=G/2\), `one_step_decreases_error` proves directly for `train_once`:

\[
 C_{\mathrm{new}}<C_{\mathrm{old}}-\frac{\eta}{2}\|g\|^2.
\]

`nonzero_gradient_decreases_error` states strict decrease using the condition that the gradient is not the all-zero parameter vector. `stationary_step` handles the other case: if \(G=0\), the update leaves every parameter unchanged, for any learning rate.

The threshold \(\eta_0\) is existential and can depend on the network, its current parameters, the example, and epsilon. The proof does not compute a numerical safe learning rate or promise decrease at an arbitrary fixed rate. A numerical bound in terms of a Hessian or gradient Lipschitz constant would require an additional estimate. Here epsilon controls the first-order approximation error; it is not a stopping tolerance or a guarantee of reaching a specified target loss in one step.

## A worked example

`Examples.v` instantiates one sigmoid neuron with input \(x=1\), target \(t=1\), and initial \(w=b=0\). It proves:

\[
 z=0,\quad a=\tfrac12,\quad C=\tfrac18,\quad
 \delta=(\tfrac12-1)\tfrac12(1-\tfrac12)=-\tfrac18.
\]

Both parameter gradients are \(-1/8\). After one update,

\[
 w_{\mathrm{new}}=b_{\mathrm{new}}=\eta/8,\qquad G=1/32.
\]

For sufficiently small positive eta, the theorem gives
\(C_{\mathrm{new}}<1/8-\eta/64\). The file also checks the zero-gradient case with target \(1/2\) and shows how to construct a network with a hidden layer.

## Build and inspect

From the repository root:

```bash
rocq makefile -f _CoqProject -o Makefile
make -j2 Backprop/Examples.vo
```

The new modules also pass an independent kernel check. To repeat it while loading the existing library dependencies from their compiled files:

```bash
rocqchk -silent -R Lib Lib -R Backprop Backprop \
  -norec Backprop.Calculus -norec Backprop.NeuralNet \
  -norec Backprop.Correctness -norec Backprop.Descent -norec Backprop.Examples
```

The files are included in the default `_CoqProject`. Reading order:

1. `NeuralNet.v`: the data and algorithm.
2. `Examples.v`: one concrete forward/backward pass and update.
3. `Correctness.v`: the chain-rule proof and Theorems 1–4.
4. `Descent.v`: epsilon, learning rate, and strict decrease.
5. `Calculus.v`: finite sums and scalar derivative helpers, as needed.

All new proofs end in `Qed`; there are no admitted results or added axioms. `Print Assumptions` on Theorems 1–4 and the descent results reports only the project's foundational classical real, choice, and extensionality assumptions, with no unfinished library theorem in their dependency closures. This is a classical real analysis formalization, not an axiom-free construction.

To inspect that dependency report interactively:

```coq
From Backprop Require Import Descent.
Print Assumptions theorem_1.
Print Assumptions theorem_2.
Print Assumptions theorem_3.
Print Assumptions theorem_4.
Print Assumptions one_step_decreases_error.
Print Assumptions nonzero_gradient_decreases_error.
```
