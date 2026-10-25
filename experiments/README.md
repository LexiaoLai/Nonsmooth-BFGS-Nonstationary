# Reproducing Figures 1 and 2

These scripts evaluate one explicit realization of the objective in
Theorem 1.1 and run BFGS with the manuscript's strict Armijo–Wolfe line
search. They supply every function value and gradient from the objective;
no iterate or inverse-Hessian estimate is reset to the prescribed cycle.

The simulations illustrate the theorem. The exact inequalities needed for
the proof are checked separately by the [verification package](../verification/README.md)
and [Lean formalization](../docs/lean.md).

## Run

From the repository root, with Python 3.12:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r experiments/requirements.txt
.venv/bin/python experiments/numerical_example.py
.venv/bin/python experiments/random_initializations.py
```

Rendering also requires a LaTeX installation with `latex`, `dvipng`, and
Computer Modern fonts available on `PATH`. On macOS the scripts additionally
look in the standard MacTeX directory `/Library/TeX/texbin`. All plot text is
rendered with LaTeX. The pinned Python packages were tested with Python 3.12.14.

The first script regenerates Figure 1 and checks values, gradients,
Hessians, interpolation joins, numerical derivatives, and the shrinking
cycle. The second script regenerates all 100 runs in Figure 2. Its high-precision
simulations take longer than the proof's finite certificate checks.

The scripts write generated files to `experiments/figures/`, which is ignored
by Git:

| Output | Content |
|---|---|
| `main_two_panel.pdf`, `main_two_panel.png` | Figure 1: objective surface and BFGS iterates |
| `simulation_results.json` | Figure 1 parameters, numerical checks, and iterates |
| `random_initializations.pdf`, `random_initializations.png` | Figure 2: initial displacements, objective values, and iterate norms |
| `random_initializations.json` | Figure 2 parameters and computed summary |
| `random_initializations.runs.json.gz` | Complete recorded runs and reference run |

No saved numerical output is used as an input. With the LaTeX rendering tools
listed above, both scripts and their Python dependencies regenerate the figures;
neither reads the manuscript source, external research files, or certificate outputs.

## Experimental parameters

| | Figure 1 | Figure 2 |
|---|---|---|
| Armijo–Wolfe parameters | `(0.01, 0.9)` | `(0.01, 0.9)` |
| Iterations per displayed run | 120 | 1000 |
| Decimal precision | 100 digits | 200 digits |
| Initialization | Constructed state `(x⁰,H⁰)` | 100 perturbations of `(x⁰,H⁰)` |
| Perturbation distribution | — | Uniform five-dimensional Euclidean ball of radius `1e-9` |
| Random seed | — | `20261025` |

The state coordinates are `(x₁,x₂,H₁₁,H₁₂,H₂₂)`. Figure 2 samples a standard
normal direction and an independent radius `1e-9 * U**(1/5)`, where `U` is
uniform on `[0,1]`. The symmetric perturbation changes both off-diagonal
matrix entries together. Positive definiteness is checked for every initial
matrix, and every draw is retained, including any numerical error.

The blue/orange classification uses the finite criterion `‖x¹⁰⁰⁰‖ < 1e-9`.
It does not certify convergence of an individual numerical run. The local
sample fraction is not an estimate of the failure probability under the
Gaussian/Wishart initialization law. The existence of an open basin and
positive probability follows from the proof, independently of this
experimental radius.

The random-initialization script also accepts `--samples`, `--radius`,
`--steps`, `--precision`, and `--seed`. For a quick rendering check:

```sh
.venv/bin/python experiments/random_initializations.py --samples 2 --steps 20
```

This overwrites the generated Figure 2 outputs. Run the default command
again to recover the manuscript experiment.

## Explicit objective

`cycle_data()` in [numerical_example.py](numerical_example.py) approximates
the unique quartic root in `(0.9178, 0.9179)` by Decimal bisection. It then
evaluates all cycle positions, gradients, matrices, and interpolation data
from that same root. The Hessian coefficients are `(1.9, 1.6, -4.1, 0.2)`,
as selected in Section 2.3.

The interpolation in Lemma 2.6 is obtained analytically from the cited
existence theorem. The experiments instead use the explicit polynomial
interpolant formalized in
[PolynomialBridge.lean](../BFGS/Analysis/PolynomialBridge.lean) and
[CanonicalProfile.lean](../BFGS/Analysis/CanonicalProfile.lean). It matches
the same prescribed values and first two derivatives, so it gives a
realization of Lemma 2.10 with the same cycle and stability certificate.

For consecutive data `(a,A,d_a,k_a)` and `(c,B,d_c,k_c)`, let
`ell=c-a`, `mu=0.01*ell`, `p=ell*d_a`, `q=ell*d_c`,
`P=ell**2*k_a`, `Q=ell**2*k_c`, and `Delta=B-A`. The `Segment` class
computes the least integer `n >= 0` for which

```text
L = P + (n+2)*(p-mu) >= 0,
R = Q - (n+2)*(q-mu) <= 0,
I = mu + 2*(p+q-2*mu)/(n+4) + (P-Q)/((n+3)*(n+4)) < Delta.
```

For `0 <= s <= 1`, it evaluates

```text
psi(s) = mu + (1-s)**(n+2)*(p-mu+L*s)
            + s**(n+2)*(q-mu+R*(s-1))
            + 30*(Delta-I)*s**2*(1-s)**2,
h(a+ell*s) = A + integral(psi(u), u=0..s).
```

The pieces match the prescribed values and first two derivatives, and
`h' >= 0.01`. Adding the anchors at `-1` and `6`, the outer points at
`-2` and `7`, and identity tails gives the two functions used in Section 2.2.
The code evaluates factored powers and integrates from the nearer endpoint
to avoid expanding high-degree polynomials.

The homogeneous part is `F(M⁻¹x)` with the manuscript's matrix `M`; the
coercive modification adds `max(0, ‖x‖²-100)`, as in Section 2.4.
Function values are defined everywhere. Gradient requests at the origin or
on the radius-ten circle raise an exception. The line search evaluates
Armijo first; a failed gradient request makes the Wolfe test fail.
