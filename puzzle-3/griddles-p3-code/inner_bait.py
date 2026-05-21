"""
inner_bait.py — WS strategy with inner bait mechanic, score=114.

After outer L fires (PP goes down col 0, WS closes (9,0)↔(9,1)), PP enters
interior at (1,9). Bait fires when PP reaches (8,9). Then PP traverses real corridor.

Real corridor design:
  Phase-1 HP: HP from (1,8) through rows 1-8 cols 1-8 (minus excluded corner (1,1)),
              ending at (8,1). 63 cells, 62 steps.
  Phase-2 tail: (8,1)→(9,1)→(9,2)→...→(9,8)→(9,9). 9 steps.
  Total HP cells: 72. Total HP steps: 71. PP goes (1,9)→(1,8)→HP→(9,9): 72 steps.

Bait isolation: walls (k,8)↔(k,9) for k=2..8.
  Leaves (1,8)↔(1,9) open (real corridor entry).

Score = 28 (outer L) + 7 (bait) + 7 (backtrack) + 72 (real) = 114.

Outer trap timing note: from (0,0), BFS via DOWN = 9+1+8=18 = BFS via RIGHT=18.
PP picks DOWN first (neighbor order). Outer trap fires correctly.
"""

from collections import deque

N, M = 10, 10
INF = 10**9


def build_graph(n, m):
    edges = []
    for r in range(n):
        for c in range(m):
            if c + 1 < m: edges.append(((r, c), (r, c + 1)))
            if r + 1 < n: edges.append(((r, c), (r + 1, c)))
    eidx = {}
    for i, (a, b) in enumerate(edges):
        eidx[(a, b)] = i
        eidx[(b, a)] = i
    return tuple(edges), eidx


def bfs_dist(start, goal, walls, n, m, eidx):
    if start == goal: return 0
    visited = {start}
    q = deque([(start, 0)])
    while q:
        pos, d = q.popleft()
        r, c = pos
        for dr, dc in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            nr, nc = r + dr, c + dc
            if 0 <= nr < n and 0 <= nc < m:
                i = eidx.get((pos, (nr, nc)))
                if i is not None and not (walls >> i & 1):
                    nxt = (nr, nc)
                    if nxt == goal: return d + 1
                    if nxt not in visited:
                        visited.add(nxt)
                        q.append((nxt, d + 1))
    return INF


def pp_step(pos, walls, goal, n, m, eidx):
    best, bk = None, INF
    for dr, dc in ((-1, 0), (1, 0), (0, -1), (0, 1)):
        nr, nc = pos[0] + dr, pos[1] + dc
        if 0 <= nr < n and 0 <= nc < m:
            i = eidx.get((pos, (nr, nc)))
            if i is not None and not (walls >> i & 1):
                d = bfs_dist((nr, nc), goal, walls, n, m, eidx)
                if d < bk:
                    bk, best = d, (nr, nc)
    return best


def find_hp_phase1():
    """HP from (1,8) to (8,1) through rows 1-8 cols 1-8 minus (1,1). 63 cells.

    Uses Warnsdorf's heuristic + endpoint-guard: don't visit end until last cell.
    """
    cells = set((r, c) for r in range(1, 9) for c in range(1, 9))
    cells.discard((1, 1))  # excluded BLACK cell
    start = (1, 8)
    end = (8, 1)
    assert start in cells and end in cells

    def nbrs(pos, visited):
        r, c = pos
        result = []
        for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
            nb = (r + dr, c + dc)
            if nb in cells and nb not in visited:
                result.append(nb)
        return result

    path = [start]
    visited = {start}

    def dfs():
        if len(path) == len(cells):
            return path[-1] == end
        remaining = len(cells) - len(path)
        cur = path[-1]
        candidates = []
        for nb in nbrs(cur, visited):
            if nb == end and remaining > 1:
                continue  # guard endpoint
            candidates.append(nb)
        # Warnsdorf: sort by fewest unvisited neighbors
        def wkey(nb):
            nb_visited = visited | {nb}
            cnt = 0
            for n2 in nbrs(nb, nb_visited):
                if n2 == end and remaining > 2:
                    continue
                cnt += 1
            return cnt
        candidates.sort(key=wkey)
        for nb in candidates:
            path.append(nb)
            visited.add(nb)
            if dfs():
                return True
            path.pop()
            visited.remove(nb)
        # Last resort: try endpoint if remaining==1
        if remaining == 1 and end in nbrs(cur, visited):
            path.append(end)
            return True
        return False

    if dfs():
        return path
    return None


def build_full_hp(phase1):
    """Append fixed Phase-2 tail: (8,1)→(9,1)→...→(9,8)→(9,9)."""
    assert phase1[-1] == (8, 1)
    tail = [(9, c) for c in range(1, 10)]  # (9,1),(9,2),...,(9,9)
    return phase1 + tail  # 63 + 9 = 72 cells


def build_outer_l(edges, eidx):
    mask = 0
    for i, (a, b) in enumerate(edges):
        (r1, c1), (r2, c2) = a, b
        if min(r1, r2) == 0 and max(r1, r2) == 1 and c1 == c2 and 1 <= c1 <= 8:
            mask |= (1 << i)
        if min(c1, c2) == 0 and max(c1, c2) == 1 and r1 == r2 and 1 <= r1 <= 8:
            mask |= (1 << i)
    return mask


def build_bait_isolation(edges, eidx):
    """Walls (k,8)↔(k,9) for k=2..8. Entry (1,8)↔(1,9) stays open."""
    mask = 0
    for k in range(2, 9):
        i = eidx.get(((k, 8), (k, 9)))
        if i is not None:
            mask |= (1 << i)
    return mask


def build_real_corridor_walls(hp, edges, eidx):
    """Wall edges within the HP cell set not on HP, plus edges to excluded cell (1,1)."""
    hp_edges = set()
    for k in range(len(hp) - 1):
        a, b = hp[k], hp[k + 1]
        hp_edges.add((a, b))
        hp_edges.add((b, a))
    real_cells = set(hp)
    excluded = (1, 1)
    mask = 0
    for i, (a, b) in enumerate(edges):
        # Wall non-HP edges within corridor
        if a in real_cells and b in real_cells and (a, b) not in hp_edges:
            mask |= (1 << i)
        # Wall edges connecting corridor to excluded cell
        elif (a in real_cells and b == excluded) or (b in real_cells and a == excluded):
            mask |= (1 << i)
    return mask


def simulate(edges, eidx, hp, verbose=True):
    goal = (N - 1, M - 1)
    pos = (0, 0)

    outer_l = build_outer_l(edges, eidx)
    bait_iso = build_bait_isolation(edges, eidx)
    real_walls = build_real_corridor_walls(hp, edges, eidx)
    walls = outer_l | bait_iso | real_walls

    d0 = bfs_dist(pos, goal, walls, N, M, eidx)
    assert d0 < INF, f"Initial walls disconnect PP! d={d0}"
    if verbose:
        print(f"Initial BFS (0,0)→goal: {d0}  (expect 18 via bait col 9)")

    score = 0
    outer_fired = False
    inner_fired = False

    for _ in range(600):
        if pos == goal:
            break

        if not outer_fired and pos == (N - 1, 0):
            tj = eidx[((N - 1, 0), (N - 1, 1))]
            new_walls = walls | (1 << tj)
            assert bfs_dist(pos, goal, new_walls, N, M, eidx) < INF, "Outer trap disconnects!"
            walls = new_walls
            outer_fired = True
            if verbose:
                print(f"  step {score:3d}: OUTER TRAP fired — closed (9,0)↔(9,1)")

        if not inner_fired and pos == (8, 9):
            ti = eidx[((8, 9), (9, 9))]
            new_walls = walls | (1 << ti)
            assert bfs_dist(pos, goal, new_walls, N, M, eidx) < INF, "Inner bait disconnects!"
            walls = new_walls
            inner_fired = True
            if verbose:
                print(f"  step {score:3d}: INNER BAIT fired — closed (8,9)↔(9,9)")

        nxt = pp_step(pos, walls, goal, N, M, eidx)
        if nxt is None:
            print(f"  PP stuck at {pos}!")
            break

        pos = nxt
        score += 1

    if verbose:
        print(f"\nFinal: pos={pos}, score={score}")
        print(f"  outer fired={outer_fired}, inner fired={inner_fired}")

    return score


def main():
    edges, eidx = build_graph(N, M)

    print("Finding Phase-1 HP from (1,8) to (8,1) through 63 cells...")
    phase1 = find_hp_phase1()
    if phase1 is None:
        print("No HP found!")
        return

    assert len(phase1) == 63, f"Phase-1 HP wrong length: {len(phase1)}"
    assert phase1[0] == (1, 8) and phase1[-1] == (8, 1)
    for k in range(len(phase1) - 1):
        r1, c1 = phase1[k]
        r2, c2 = phase1[k + 1]
        assert abs(r1 - r2) + abs(c1 - c2) == 1
    print(f"  HP found: {len(phase1)} cells, (1,8)→...→(8,1)")

    hp = build_full_hp(phase1)
    assert len(hp) == 72 and hp[0] == (1, 8) and hp[-1] == (9, 9)
    assert len(set(hp)) == 72, "HP has duplicate cells!"
    print(f"  Full HP: 72 cells, (1,8)→...→(8,1)→(9,1)→...→(9,9)")

    score = simulate(edges, eidx, hp, verbose=True)
    print(f"\nPredicted: 114, Actual: {score}")
    assert score == 114, f"Score mismatch: expected 114, got {score}"


if __name__ == '__main__':
    main()
