"""Exact finite checks of the construction in solution.md."""

import argparse
from itertools import combinations


def coloring(n):
    rows = []
    for s in range(n):
        for b in range(1, n + 1):
            for a in range(b):
                base = list(range(n))
                base.insert(b, a)
                rows.append([(v + s) % n for v in base])
    return rows


def verify(n):
    rows = coloring(n)
    height = len(rows)
    seen = set()
    for y, row in enumerate(rows):
        for left, right in combinations(range(n + 1), 2):
            if row[left] != row[right]:
                continue
            key = (left, right, row[left])
            if key in seen:
                raise AssertionError(('axis-aligned rectangle', n, y, key))
            seen.add(key)
    assert len(seen) == height == n * n * (n + 1) // 2

    checked = 0
    # From the bottom vertex the side vectors are (p,q),(-r,t), qt=pr.
    # Positivity gives every tilted rectangle exactly one representation.
    for p in range(1, n):
        for r in range(1, n - p + 1):
            product = p * r
            for q in range(1, product + 1):
                if product % q:
                    continue
                t = product // q
                for y in range(height - q - t):
                    for x in range(n - p - r + 1):
                        corners = ((x + r, y), (x + r + p, y + q),
                                   (x, y + t), (x + p, y + q + t))
                        checked += 1
                        colors = {rows[cy][cx] for cx, cy in corners}
                        if len(colors) == 1:
                            raise AssertionError(('tilted rectangle', n, corners))
    return height, checked


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=10)
    args = parser.parse_args()
    if args.max_n < 1:
        parser.error('--max-n must be positive')
    for n in range(1, args.max_n + 1):
        height, checked = verify(n)
        print(f'n={n}: {n + 1} x {height}, '
              f'{checked:,} tilted rectangles checked; none monochromatic')
