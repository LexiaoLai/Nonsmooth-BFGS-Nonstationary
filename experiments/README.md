# Reproducing Figures 1 and 2

These scripts reproduce Figures 1 and 2 in the accompanying
[manuscript](../BFGS%20can%20converge%20to%20non-Clarke-stationary%20points%20with%20positive%20probability.pdf). They evaluate one explicit objective
satisfying the interpolation conditions in Section 2.2 and run BFGS with
strict Armijo–Wolfe line search. Iterates and inverse-Hessian estimates are
never reset to the prescribed cycle.

The simulations illustrate the construction. The exact finite proof
certificates are computed separately in the
[verification package](../verification/README.md). See the
[formalization overview](../docs/lean.md) for the Lean proof and its scope.

## Reproduce the figures

From the repository root, with Python 3.12:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r experiments/requirements.txt
.venv/bin/python experiments/numerical_example.py
.venv/bin/python experiments/random_initializations.py
```

Rendering requires LaTeX, `dvipng`, and Computer Modern fonts. The `latex`
and `dvipng` executables must be available on `PATH`. Plot text is rendered
with LaTeX. Neither script reads the manuscript source or saved certificate
outputs.

Both scripts write generated outputs to `experiments/figures/`, which is
ignored by Git. The first script checks the prescribed values, gradients and Hessians,
polynomial joins, numerical derivatives, and the shrinking cycle. It then
writes `figures/main_two_panel.pdf`, its PNG preview, and
`figures/simulation_results.json`. The second command writes
`figures/random_initializations.pdf`, its PNG preview, a summary JSON file,
and the complete run records in `random_initializations.runs.json.gz`.

| Parameter | Figure 1 | Figure 2 |
|---|---|---|
| Armijo–Wolfe parameters | `(0.01, 0.9)` | `(0.01, 0.9)` |
| Iterations | 120 | 1000 per run |
| Decimal precision | 100 digits | 200 digits |
| Initialization | Constructed state | 100 random perturbations |
| Perturbation radius | — | `2e-7` |
| Random seed | — | `20261025` |

Figure 2 samples uniformly from the five-dimensional Euclidean ball in
coordinates `(x1,x2,H11,H12,H22)`, centered at the constructed state. Each
sample uses a standard normal direction and an independent radius
`2e-7 * U**(1/5)`. Positive definiteness is checked for every initial matrix,
and every draw is retained. Blue indicates that the final iterate norm is
below `1e-9`; orange indicates the other completed runs. This finite test is
not a proof of convergence for an individual run, and the local sample
fraction is not a Gaussian/Wishart failure probability.

The radius was selected after pilot runs to show both observed behaviors;
[`radius_selection.json`](radius_selection.json) records the tested radii and all pilot counts.
This selection is for illustration, not statistical inference. The default
100-run experiment completed without numerical errors: 98 final norms were
below `1e-9`, and the other two final positions were within `7.26e-12` of
`(0,-10)`, with objective values close to `-10`.

The random-initialization script also accepts `--samples`, `--radius`,
`--steps`, `--precision`, and `--seed`. A quick run overwrites the generated
Figure 2 files; rerun the default command to recover the manuscript figure.

## Explicit objective

`cycle_data()` approximates the unique quartic root in `(0.9178,0.9179)`
by Decimal bisection and evaluates all cycle data from that root. The
Hessian coefficients are `(1.9,1.6,-4.1,0.2)`.

There is one interpolant `h`, shared by both half-planes. It interpolates
all four cycle data in the order

```text
-2, -1, t^2, t^0, t^3, t^1, 6, 7.
```

The added data at `-2,-1,6,7` are `(t,h,h',h'')=(t,t,1,0)`.
On each interpolation interval, the `Segment` class uses the monotone
polynomial bridge defined and certified in notebook Section 4. It computes
the least admissible integer index from the endpoint data, evaluates the
polynomials in factored form, and integrates from the nearer endpoint to
avoid cancellation. The pieces match values and first two derivatives,
with `h' >= 0.01`; outside `[-2,7]`, set `h(t)=t`.

Writing `z=M^{-1}x`, the homogeneous function is
`F(z)=abs(z1)*h(z2/abs(z1))` when `z1 != 0`, and `F(0,z2)=z2`.
The final objective is `f(x)=F(M^{-1}x)+max(0,||x||^2-100)`, as in
Section 2.4. The cycle has the same values, gradients and Hessians as those certified in the notebook.

Function values are defined everywhere. Gradient requests at the origin
or on the radius-ten circle raise an exception. The line search evaluates
Armijo first, then obtains the line derivative from the gradient at a
smooth trial point. This implementation does not cover a nonsmooth trial
whose line derivative nevertheless exists. The certified basin uses only
smooth trials.
