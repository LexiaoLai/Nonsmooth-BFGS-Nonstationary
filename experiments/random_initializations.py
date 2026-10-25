"""Reproduce the manuscript's random-initialization figure.

Sample a full five-dimensional ball in (x1,x2,H11,H12,H22).
Every draw is retained, including any numerical error or escaping run.
The sample frequency is local to this distribution, not an estimate for
the Gaussian/Wishart initialization in the Lewis--Overton challenge.
"""
from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
import gzip
import hashlib
import json
from pathlib import Path

import numpy as np

from numerical_example import C1, C2, Example, PRECISION, cycle_data

ROOT = Path(__file__).resolve().parent


def simulate(samples, radius, steps, seed, precision=200):
    rng = np.random.default_rng(seed)
    records = []
    with localcontext() as ctx:
        ctx.prec = precision
        data = cycle_data()
        example = Example(data)
        f0 = example.value([Decimal(0), Decimal(0)])
        assert f0 == 0
        reference = example.run(steps)
        assert reference['all_first_trials_accepted']
        for index in range(samples):
            direction = rng.normal(size=5)
            perturbation = radius*rng.random()**(1/5)*direction/np.linalg.norm(direction)
            delta = list(map(lambda value: Decimal(str(value)), perturbation))
            H = data['H'][0] + np.array([[delta[2], delta[3]], [delta[3], delta[4]]])
            # Check positive definiteness with the same high-precision scalars.
            assert H[0, 0] > 0 and H[0, 0]*H[1, 1]-H[0, 1]*H[1, 0] > 0
            record = {'index': index, 'perturbation': list(map(str, delta))}
            try:
                run = example.run(steps, delta)
                rows = run['rows']
                assert len(rows) == steps+1
                assert all(row['armijo_margin'] > 0 and row['wolfe_margin'] > 0
                           for row in rows[:-1])
                assert all(rows[j+1]['f'] <= rows[j]['f'] for j in range(steps))
                record.update(status='completed', run=run)
                record['near_origin'] = rows[-1]['norm'] < 1e-9
            except (ArithmeticError, AssertionError) as error:
                record.update(status='numerical_error', error=repr(error), near_origin=False)
            records.append(record)
            if (index+1) % 50 == 0:
                print(f'Completed {index+1}/{samples} sampled initializations', flush=True)
        complete = [item for item in records if item['status'] == 'completed']
        near = [item for item in complete if item['near_origin']]
        other = [item for item in complete if not item['near_origin']]
        summary = {
            'samples': samples, 'radius': radius, 'steps': steps, 'seed': seed,
            'precision_digits': precision, 'c1': str(C1), 'c2': str(C2), 'f_at_origin': str(f0),
            'sampling': 'Uniform five-dimensional Euclidean ball in (x1,x2,H11,H12,H22), using a normal direction and independent U**(1/5) radius',
            'base_position': list(map(str, data['x'][0])),
            'base_metric': [list(map(str, row)) for row in data['H'][0]],
            'near_origin_criterion': 'At the final iteration: norm(x)<1e-9',
            'near_origin': len(near), 'other_completed': len(other),
            'numerical_errors': len(records)-len(complete),
            'all_first_trial_runs': sum(item['run']['all_first_trials_accepted'] for item in complete),
            'near_origin_final_norm_range': [min(item['run']['rows'][-1]['norm'] for item in near),
                                             max(item['run']['rows'][-1]['norm'] for item in near)] if near else None,
            'near_origin_final_gap_range': [min(abs(item['run']['rows'][-1]['f']) for item in near),
                                            max(abs(item['run']['rows'][-1]['f']) for item in near)] if near else None,
            'other_final_norm_range': [min(item['run']['rows'][-1]['norm'] for item in other),
                                       max(item['run']['rows'][-1]['norm'] for item in other)] if other else None,
            'figure': {'panels': ['initial-position perturbations in original units',
                                  'signed objective value', 'iterate Euclidean norm'],
                       'vertical_scales': ['linear', 'linear', 'log'],
                       'legend': False, 'line_width': 1.3,
                       'text_rendering': 'LaTeX Computer Modern'},
            'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'objective_source_sha256': hashlib.sha256((ROOT/'numerical_example.py').read_bytes()).hexdigest(),
            'interpretation': 'Finite simulations of one explicit realization. The experimental radius is not a certified basin radius, and this local sample frequency is not a Gaussian/Wishart failure probability. The positive-probability theorem is established separately.'}
        return summary, records, reference


def render(summary, records, reference, output):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.ticker import LogLocator

    plt.rcParams.update({'text.usetex': True, 'font.family': 'serif',
                        'font.serif': ['Computer Modern Roman'], 'font.size': 11.5,
                        'axes.labelsize': 12.5, 'xtick.labelsize': 10.5, 'ytick.labelsize': 10.5})
    colors = {'near': '#176ca4', 'other': '#c86c25', 'error': '#777777'}
    fig, axes = plt.subplots(1, 3, figsize=(8.8, 3.1),
                             gridspec_kw={'width_ratios': [1, 1.1, 1.1]})
    fig.subplots_adjust(left=.07, right=.97, bottom=.21, top=.92, wspace=.43)
    norms = []
    for record in records:
        status = ('error' if record['status'] != 'completed' else
                  'near' if record['near_origin'] else 'other')
        delta = np.array(list(map(float, record['perturbation'])))
        axes[0].scatter(delta[0], delta[1], s=18, c=colors[status], alpha=.8,
                        marker='x' if status == 'error' else 'o', linewidths=.5)
        if record['status'] != 'completed':
            continue
        rows = record['run']['rows']
        k = [row['k'] for row in rows]
        values = np.array([row['f'] for row in rows])
        norm = np.array([row['norm'] for row in rows])
        assert np.all(np.isfinite(values)) and np.all(norm > 0)
        axes[1].plot(k, values, color=colors[status], lw=1.3, alpha=.35)
        axes[2].plot(k, norm, color=colors[status], lw=1.3, alpha=.35)
        norms.extend(norm)
    axes[0].set(xlim=(-summary['radius'], summary['radius']),
                ylim=(-summary['radius'], summary['radius']),
                xlabel=r'$\Delta x_1$', ylabel=r'$\Delta x_2$')
    axes[0].set_box_aspect(1)
    axes[0].set_xticks([-summary['radius'], 0, summary['radius']])
    axes[0].set_yticks([-summary['radius'], 0, summary['radius']])
    axes[0].ticklabel_format(axis='both', style='sci', scilimits=(0, 0), useMathText=True)
    for ax in axes[1:]:
        ax.set(xlim=(0, summary['steps']), xlabel=r'Iteration $k$')
        ax.set_xticks(np.linspace(0, summary['steps'], 3, dtype=int))
        ax.grid(axis='y', alpha=.18, lw=.6)
        ax.margins(y=.08)
    axes[1].set(yscale='linear', ylabel=r'$f(x^k)$')
    axes[1].set_yticks([-10, -5, 0])
    axes[2].set(yscale='log', ylabel=r'$\|x^k\|$',
                ylim=(min(norms)*.5, max(norms)*2))
    axes[2].yaxis.set_major_locator(LogLocator(base=10, numticks=5))
    for ax in axes:
        ax.spines[['top', 'right']].set_visible(False)
    for extension in ['pdf', 'png']:
        fig.savefig(output.with_suffix('.'+extension), dpi=240)
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--samples', type=int, default=100)
    parser.add_argument('--radius', type=float, default=1e-9)
    parser.add_argument('--steps', type=int, default=1000)
    parser.add_argument('--precision', type=int, default=200)
    parser.add_argument('--seed', type=int, default=20261025)
    args = parser.parse_args()
    assert args.samples > 0 and 0 < args.radius < .01 and args.steps > 0
    assert args.precision >= PRECISION
    summary, records, reference = simulate(args.samples, args.radius, args.steps, args.seed,
                                           args.precision)
    output = ROOT/'figures/random_initializations'
    output.parent.mkdir(exist_ok=True)
    output.with_suffix('.json').write_text(json.dumps(summary, indent=2)+'\n')
    with gzip.open(str(output)+'.runs.json.gz', 'wt') as handle:
        json.dump({'summary': summary, 'records': records, 'reference': reference}, handle)
    render(summary, records, reference, output)
    print(json.dumps(summary, indent=2))
    print('Figure:', output.with_suffix('.pdf'))


if __name__ == '__main__':
    main()
