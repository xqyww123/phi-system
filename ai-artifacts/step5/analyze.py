#!/usr/bin/env python3
"""STEP 5: read a leg's guard_decision records and summarise; compare two legs.

    analyze.py <leg dir>                 -- the leg's path distribution and timings
    analyze.py <leg dir A> <leg dir B>   -- B's hit rate over A's digests, flips A->B
"""

import statistics
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, '/home/qiyuan/Current/MLML/contrib/Performant_Isabelle_ML/tools')
from event_log import records  # noqa: E402


def load(leg_dir):
    rows = []
    for p in sorted(Path(leg_dir, 'event_log', 'guard_decision').glob('*.xml')):
        rows += [r.attrib for r in records(p)]
    return rows


def verdicts_by_digest(rows):
    """digest -> Counter of verdicts (one decision = one count)."""
    out = {}
    for r in rows:
        out.setdefault(r['digest'], Counter())[r['verdict']] += 1
    return out


def summarise(name, rows):
    print(f'== {name}: {len(rows)} decisions, {len({r["digest"] for r in rows})} digests')
    # within one leg a digest must be decided one way: PLPR is deterministic and the
    # store keeps one entry per digest -- an offender here is a defect, reported loudly
    mixed = {d: c for d, c in verdicts_by_digest(rows).items() if len(c) > 1}
    print(f'   digests with more than one verdict in this leg: {len(mixed)}'
          + (' -- DEFECT' if mixed else ''))
    for d, c in list(mixed.items())[:20]:
        print(f'     {d}: {dict(c)}')
    print('   verdict:', dict(Counter(r['verdict'] for r in rows)))
    print('   hit    :', dict(Counter(r['hit'] for r in rows)))
    print('   refuter:', dict(Counter(r['refuter'] for r in rows)))
    print('   judge  :', dict(Counter(r['judge'] for r in rows)))
    ms = [int(r['elapsed_ms']) for r in rows]
    print(f'   guard time: {sum(ms) / 1000:.1f} s total')
    for v in ('proved', 'refuted', 'unknown'):
        xs = sorted(int(r['elapsed_ms']) for r in rows if r['verdict'] == v)
        if xs:
            q = lambda p: xs[min(len(xs) - 1, int(p * len(xs)))]
            print(f'   {v:8s} n={len(xs):4d} median={statistics.median(xs):.0f}ms p90={q(0.9)}ms p99={q(0.99)}ms max={xs[-1]}ms')
    first = [int(r['elapsed_ms']) for r in rows if r['hit'] == 'none']
    hits = [int(r['elapsed_ms']) for r in rows if r['hit'] != 'none']
    if first:
        print(f'   first decisions: n={len(first)} mean={statistics.mean(first):.0f}ms')
    if hits:
        print(f'   hits           : n={len(hits)} mean={statistics.mean(hits):.0f}ms')


def compare(a, b):
    va, vb = verdicts_by_digest(a), verdicts_by_digest(b)
    common = set(va) & set(vb)
    flips = [d for d in common if set(va[d]) != set(vb[d])]
    count_diffs = [d for d in common if va[d] != vb[d] and set(va[d]) == set(vb[d])]
    print(f'== compare: {len(va)} digests in A, {len(vb)} in B, {len(common)} common, '
          f'{len(set(va) - set(vb))} only in A, {len(set(vb) - set(va))} only in B')
    print(f'   flips (a digest decided differently in A and B): {len(flips)}')
    for d in flips[:20]:
        print(f'     {d}: A={dict(va[d])} B={dict(vb[d])}')
    print(f'   same verdicts, different decision counts: {len(count_diffs)}')
    for d in count_diffs[:20]:
        print(f'     {d}: A={dict(va[d])} B={dict(vb[d])}')
    non_proved_b = [r for r in b if r['verdict'] != 'proved']
    hit_b = [r for r in non_proved_b if r['hit'] != 'none']
    print(f'   B: {len(non_proved_b)} non-proved decisions, {len(hit_b)} of them hits '
          f'({100 * len(hit_b) / len(non_proved_b) if non_proved_b else 0:.1f} %)')
    proved_hits = [r for r in b if r['verdict'] == 'proved' and r['hit'] != 'none']
    print(f'   B: {len(proved_hits)} proved decisions from an entry (Proved/Unknown hits re-proved)')


if __name__ == '__main__':
    legs = sys.argv[1:]
    data = [load(l) for l in legs]
    for l, rows in zip(legs, data):
        summarise(l, rows)
    if len(data) == 2:
        compare(*data)
