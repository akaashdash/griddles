"""
snake_vis.py — WS strategy on 10×10, proven to achieve score=108.

NOTE: All previous analyses (reactive WS, formula s=2nm-n-m, PP-exploit scripts) are wrong or
unprovable. This is the only strategy here because it is the best provable construction found.

WS strategy:
  Turn 1: Place L-corridor walls only.
    - (0,c)↔(1,c) for c=1..8  [row 0 floor — leaves (0,0)↔(0,9) corridor open, bait at (0,9)]
    - (r,0)↔(r,1) for r=1..8  [col 0 right wall — leaves (0,0)↔(9,0) corridor open, bait at (9,0)]
  PP is confined to the L-shaped perimeter. No other move exists.

  Trap A fires when PP reaches (0,9):
    WS atomically blocks (0,9)↔(1,9) + places snake A walls forcing path (9,1)→...→(9,9).
    PP must backtrack row 0, traverse col 0, enter interior at (9,0)→(9,1), follow 80-step snake.

  Trap B fires when PP reaches (9,0):
    WS atomically blocks (9,0)↔(9,1) + places snake B walls forcing path (1,9)→...→(9,9).
    PP must backtrack col 0, traverse row 0, enter interior at (0,9)→(1,9), follow 80-step snake.

  Either trap yields: 9 (to bait) + 9 (backtrack) + 9 (other corridor) + 1 (enter) + 80 (snake) = 108.
  PP MUST trigger one trap (no other exit from L-corridor exists).

  Greedy BFS PP (used here) goes down first due to neighbor ordering → trap B always fires.
  Trap A code is symmetric and activates against a PP that goes right first.
"""

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.patches as patches
import numpy as np
from collections import deque
import imageio.v3 as iio
import os

INF = 10**9
_DARK = '#0d1117'
N, M = 10, 10
OUT = os.path.join(os.path.dirname(__file__), '..', 'griddles-p3-vis')
os.makedirs(OUT, exist_ok=True)


def build_graph(n, m):
    edges = []
    for r in range(n):
        for c in range(m):
            if c+1 < m: edges.append(((r,c),(r,c+1)))
            if r+1 < n: edges.append(((r,c),(r+1,c)))
    eidx = {}
    for i,(a,b) in enumerate(edges):
        eidx[(a,b)]=i; eidx[(b,a)]=i
    return tuple(edges), eidx


def bfs_all(goal, walls, n, m, eidx):
    dist={goal:0}; q=deque([goal])
    while q:
        pos=q.popleft(); r,c=pos
        for dr,dc in ((-1,0),(1,0),(0,-1),(0,1)):
            nr,nc=r+dr,c+dc
            if 0<=nr<n and 0<=nc<m:
                i=eidx.get((pos,(nr,nc)))
                if i is not None and not (walls>>i&1):
                    nxt=(nr,nc)
                    if nxt not in dist: dist[nxt]=dist[pos]+1; q.append(nxt)
    return dist


def bfs_dist(start, goal, walls, n, m, eidx):
    if start==goal: return 0
    visited={start}; q=deque([(start,0)])
    while q:
        pos,d=q.popleft(); r,c=pos
        for dr,dc in ((-1,0),(1,0),(0,-1),(0,1)):
            nr,nc=r+dr,c+dc
            if 0<=nr<n and 0<=nc<m:
                i=eidx.get((pos,(nr,nc)))
                if i is not None and not (walls>>i&1):
                    nxt=(nr,nc)
                    if nxt==goal: return d+1
                    if nxt not in visited: visited.add(nxt); q.append((nxt,d+1))
    return INF


def build_snake_path_a():
    """
    Snake A: (9,1)→...→(9,9). Deployed when PP triggers trap at (0,9).
    PP enters interior via (9,0)→(9,1) after backtracking the full L-corridor.

    Structure: row 9 cols 1..8 → boustrophedon rows 8..2 cols 1..8 → row 1 cols 1..9 → col 9 rows 2..9
    """
    path = []
    for c in range(1, 9): path.append((9, c))
    for row in range(8, 1, -1):
        steps = 9 - row
        if steps % 2 == 1:
            path.append((row, 8))
            for c in range(7, 0, -1): path.append((row, c))
        else:
            path.append((row, 1))
            for c in range(2, 9): path.append((row, c))
    path.append((1, 1))
    for c in range(2, 10): path.append((1, c))
    for r in range(2, 10): path.append((r, 9))
    return path


def build_snake_path_b():
    """
    Snake B: (1,9)→...→(9,9). Deployed when PP triggers trap at (9,0).
    PP enters interior via (0,9)→(1,9) after backtracking the full L-corridor.

    Structure: col 9 rows 1..8 → boustrophedon cols 8..2 rows 1..8 → col 1 rows 1..9 → row 9 cols 2..9
    (Transpose-mirror of snake A.)
    """
    path = []
    for r in range(1, 9): path.append((r, 9))
    for col in range(8, 1, -1):
        steps = 9 - col
        if steps % 2 == 1:
            path.append((8, col))
            for r in range(7, 0, -1): path.append((r, col))
        else:
            path.append((1, col))
            for r in range(2, 9): path.append((r, col))
    path.append((1, 1))
    for r in range(2, 10): path.append((r, 1))
    for c in range(2, 10): path.append((9, c))
    return path


def walls_for_snake(snake_path, edges, eidx):
    """Wall every interior-to-interior edge NOT on the snake path."""
    snake_edges = set()
    for i in range(len(snake_path)-1):
        a, b = snake_path[i], snake_path[i+1]
        snake_edges.add((a,b)); snake_edges.add((b,a))
    interior = {(r,c) for r in range(1,N) for c in range(1,M)}
    mask = 0
    for i,(a,b) in enumerate(edges):
        if a in interior and b in interior and (a,b) not in snake_edges:
            mask |= (1 << i)
    return mask


def build_l_corridor(edges, eidx):
    """Row 0 floor walls + col 0 right walls. Both corridor endpoints left open."""
    mask = 0
    for i,(a,b) in enumerate(edges):
        (r1,c1),(r2,c2) = a, b
        if min(r1,r2)==0 and max(r1,r2)==1 and c1==c2 and 1<=c1<=8:
            mask |= (1 << i)
        if min(c1,c2)==0 and max(c1,c2)==1 and r1==r2 and 1<=r1<=8:
            mask |= (1 << i)
    return mask


def pp_bfs_greedy(pos, walls, goal, n, m, eidx):
    best, bk = None, INF
    for dr,dc in ((-1,0),(1,0),(0,-1),(0,1)):
        nr,nc=pos[0]+dr,pos[1]+dc
        if 0<=nr<n and 0<=nc<m:
            i=eidx.get((pos,(nr,nc)))
            if i is not None and not (walls>>i&1):
                d=bfs_dist((nr,nc),goal,walls,n,m,eidx)
                if d<bk: bk,best=d,(nr,nc)
    return best


def simulate():
    goal = (N-1, M-1)
    edges, eidx = build_graph(N, M)

    path_a = build_snake_path_a()
    path_b = build_snake_path_b()

    interior = {(r,c) for r in range(1,N) for c in range(1,M)}
    assert len(path_a)==81 and path_a[0]==(9,1) and path_a[-1]==(9,9), "snake A bounds wrong"
    assert len(path_b)==81 and path_b[0]==(1,9) and path_b[-1]==(9,9), "snake B bounds wrong"
    assert set(path_a)==interior, "snake A does not cover interior"
    assert set(path_b)==interior, "snake B does not cover interior"
    for p in (path_a, path_b):
        for k in range(len(p)-1):
            assert abs(p[k][0]-p[k+1][0])+abs(p[k][1]-p[k+1][1])==1, f"non-adjacent step in snake"

    snake_walls_a = walls_for_snake(path_a, edges, eidx)
    snake_walls_b = walls_for_snake(path_b, edges, eidx)
    l_walls = build_l_corridor(edges, eidx)

    pos = (0,0); walls = 0; score = 0
    trap_fired = None
    active_snake = None
    history = []

    dist = bfs_all(goal, walls, N, M, eidx)
    history.append({'pos':pos,'walls':walls,'dist':dist,'score':score,
        'new_walls':set(),'event':'start','bfs':dist.get(pos,INF),
        'phase':'start','snake':None})

    # WS turn 1: place L-corridor walls
    walls = l_walls
    dist = bfs_all(goal, walls, N, M, eidx)
    added1 = {i for i in range(len(edges)) if walls>>i&1}
    history.append({'pos':pos,'walls':walls,'dist':dist,'score':score,
        'new_walls':added1,'event':'ws','bfs':dist.get(pos,INF),
        'phase':'WS turn 1: L-corridor placed (both bait endpoints open)','snake':None})

    for _ in range(300):
        if pos == goal: break

        old_walls = walls

        if trap_fired is None and pos == (0, N-1):
            # Trap A fires: close (0,9)↔(1,9) and deploy snake A
            ti = eidx.get(((0,N-1),(1,N-1)))
            walls = walls | (1<<ti) | snake_walls_a
            active_snake = path_a
            trap_fired = 'A'
            assert bfs_dist(pos,goal,walls,N,M,eidx)<INF, "trap A made goal unreachable!"
            added = {i for i in range(len(edges)) if (walls>>i&1) and not (old_walls>>i&1)}
            dist = bfs_all(goal, walls, N, M, eidx)
            history.append({'pos':pos,'walls':walls,'dist':dist,'score':score,
                'new_walls':added,'event':'ws','bfs':dist.get(pos,INF),
                'phase':'TRAP A: WS closes (0,9)→(1,9) + deploys snake A',
                'snake':active_snake})

        elif trap_fired is None and pos == (N-1, 0):
            # Trap B fires: close (9,0)↔(9,1) and deploy snake B
            tj = eidx.get(((N-1,0),(N-1,1)))
            walls = walls | (1<<tj) | snake_walls_b
            active_snake = path_b
            trap_fired = 'B'
            assert bfs_dist(pos,goal,walls,N,M,eidx)<INF, "trap B made goal unreachable!"
            added = {i for i in range(len(edges)) if (walls>>i&1) and not (old_walls>>i&1)}
            dist = bfs_all(goal, walls, N, M, eidx)
            history.append({'pos':pos,'walls':walls,'dist':dist,'score':score,
                'new_walls':added,'event':'ws','bfs':dist.get(pos,INF),
                'phase':'TRAP B: WS closes (9,0)→(9,1) + deploys snake B',
                'snake':active_snake})

        if pos == goal: break

        nxt = pp_bfs_greedy(pos, walls, goal, N, M, eidx)
        if nxt is None: break

        pos = nxt; score += 1
        dist2 = bfs_all(goal, walls, N, M, eidx)

        if trap_fired is None:
            ph = f'PP in L-corridor → {pos}'
        elif trap_fired == 'A':
            if pos[1]==0: ph = f'PP down col 0 → {pos}'
            elif pos[0]==0: ph = f'PP backtrack row 0 → {pos}'
            elif pos == (9,1): ph = 'PP enters snake A at (9,1)'
            else: ph = f'snake A step {score} → {pos}'
        else:
            if pos[1]==0: ph = f'PP backtrack col 0 → {pos}'
            elif pos[0]==0: ph = f'PP right row 0 → {pos}'
            elif pos == (1,9): ph = 'PP enters snake B at (1,9)'
            else: ph = f'snake B step {score} → {pos}'

        history.append({'pos':pos,'walls':walls,'dist':dist2,'score':score,
            'new_walls':set(),'event':'pp','bfs':dist2.get(pos,INF),
            'phase':ph,'snake':active_snake})

    formula = 2*N*M - N - M
    print(f'Final score: {score} / formula={formula}')
    print(f'Trap fired: {trap_fired}')
    return history, edges, eidx, active_snake or path_a


def draw_frame(edges, eidx, frame, bfs_hist, score_hist):
    n, m = N, M
    fig = plt.figure(figsize=(15,8), facecolor=_DARK)
    ax = fig.add_axes([0.01,0.07,0.55,0.88])
    ax.set_facecolor(_DARK); ax.set_xlim(-0.1,m+0.1); ax.set_ylim(-0.1,n+0.1)
    ax.set_aspect('equal'); ax.axis('off')

    pos=frame['pos']; walls=frame['walls']; dist=frame['dist']
    score=frame['score']; event=frame['event']
    new_w=frame['new_walls']; cur_bfs=frame['bfs']; phase=frame['phase']
    snake=frame['snake']

    all_d=[v for v in dist.values() if v<INF]; max_d=max(all_d,default=1)
    for r in range(n):
        for c in range(m):
            d=dist.get((r,c),INF); frac=(d/max_d) if d<INF else 1.0
            ax.add_patch(patches.Rectangle((c,n-1-r),1,1,
                facecolor=plt.cm.YlOrRd(0.05+frac*0.90),edgecolor='none',zorder=1))

    if snake:
        for (sr,sc) in snake:
            ax.add_patch(patches.Rectangle((sc+0.1,n-1-sr+0.1),0.8,0.8,
                facecolor='none',edgecolor='#7c4dff',lw=0.7,alpha=0.5,zorder=2))

    for r in range(n+1): ax.plot([0,m],[r,r],color='#333',lw=0.5,zorder=2)
    for c in range(m+1): ax.plot([c,c],[0,n],color='#333',lw=0.5,zorder=2)

    for i,(a,b) in enumerate(edges):
        if not (walls>>i&1): continue
        (r1,c1),(r2,c2)=a,b
        color='#ff9800' if i in new_w else '#ffffff'
        lw=3.5 if i in new_w else 1.8
        if r1==r2:
            x=min(c1,c2)+1; ax.plot([x,x],[n-1-r1,n-r1],color=color,lw=lw,zorder=4)
        else:
            y=n-max(r1,r2); ax.plot([c1,c1+1],[y,y],color=color,lw=lw,zorder=4)

    pr,pc=pos
    ax.add_patch(patches.Circle((pc+0.5,n-0.5-pr),0.28,
        facecolor='#00e5ff',edgecolor='white',lw=1.5,zorder=6))

    ax.add_patch(patches.Rectangle((0.05,n-1+0.05),0.9,0.9,
        facecolor='none',edgecolor='#ff5722',lw=2,alpha=0.7,zorder=3))
    ax.add_patch(patches.Rectangle((m-1+0.1,0.1),0.8,0.8,
        facecolor='#76ff03',edgecolor='none',alpha=0.8,zorder=3))
    # Bait trap cells
    ax.add_patch(patches.Rectangle((m-1+0.1,n-1+0.1),0.8,0.8,
        facecolor='#ff1744',edgecolor='none',alpha=0.35,zorder=3))
    ax.add_patch(patches.Rectangle((0.1,0.1),0.8,0.8,
        facecolor='#ff1744',edgecolor='none',alpha=0.35,zorder=3))

    for r in range(n):
        ax.text(-0.05,n-0.5-r,str(r),color='#555',fontsize=6,ha='right',va='center')
    for c in range(m):
        ax.text(c+0.5,-0.1,str(c),color='#555',fontsize=6,ha='center',va='top')

    phase_color = '#ff9800' if event=='ws' else '#00e5ff'
    if 'TRAP' in phase: phase_color='#ff1744'
    if 'snake' in phase.lower(): phase_color='#7c4dff'
    ax.set_title(f'score={score}/108   BFS={cur_bfs}   {phase}',
        color=phase_color,fontsize=9,pad=3)

    ax_r = fig.add_axes([0.60,0.55,0.38,0.38])
    ax_r.set_facecolor('#161b22'); ax_r.spines[:].set_color('#444')
    ax_r.tick_params(colors='#aaa',labelsize=8)
    ax_r.set_xlabel('step',color='#aaa',fontsize=8)
    if bfs_hist: ax_r.plot(range(len(bfs_hist)),bfs_hist,color='#ff9800',lw=1.5)
    ax_r.set_xlim(0,max(len(bfs_hist)+1,10)); ax_r.set_ylim(0,max(bfs_hist or [1])*1.1)
    ax_r.set_title('BFS dist to goal',color='white',fontsize=9)

    ax_s = fig.add_axes([0.60,0.08,0.38,0.38])
    ax_s.set_facecolor('#161b22'); ax_s.spines[:].set_color('#444')
    ax_s.tick_params(colors='#aaa',labelsize=8)
    if score_hist: ax_s.plot(range(len(score_hist)),score_hist,color='#00e5ff',lw=1.5)
    ax_s.axhline(108,color='#76ff03',lw=1.0,ls='-',label='108 (best proven)')
    ax_s.axhline(180,color='#555',lw=0.8,ls='--',label='formula=180 (unproven)')
    ax_s.set_xlim(0,max(len(score_hist)+1,10)); ax_s.set_ylim(0,195)
    ax_s.set_title('score (best proven: 108)',color='white',fontsize=9)
    ax_s.legend(fontsize=7,facecolor='#161b22',labelcolor='white',loc='upper left')

    ax_leg = fig.add_axes([0.60,0.95,0.38,0.04])
    ax_leg.axis('off'); ax_leg.set_facecolor(_DARK)
    ax_leg.text(0.5,0.5,
        'purple = snake path  |  red cells = bait traps (0,9) & (9,0)  |  cyan = PP  |  green = goal',
        ha='center',va='center',fontsize=6.5,color='#aaa',transform=ax_leg.transAxes)

    fig.patch.set_facecolor(_DARK)
    return fig


def make_gif():
    print('  snake_vis.gif (10×10)...')
    history, edges, eidx, snake_path = simulate()

    bfs_hist, score_hist, frames_img, durations = [], [], [], []
    for frame in history:
        bfs_hist.append(frame['bfs']); score_hist.append(frame['score'])
        fig = draw_frame(edges, eidx, frame, list(bfs_hist), list(score_hist))
        fig.canvas.draw()
        buf = np.asarray(fig.canvas.buffer_rgba())
        frames_img.append(buf[:,:,:3]); plt.close(fig)

        ev=frame['event']; ph=frame['phase']
        if ev=='start': durations.append(2.0)
        elif ev=='ws' and 'L-corridor' in ph: durations.append(1.5)
        elif ev=='ws' and 'TRAP' in ph: durations.append(2.5)
        elif 'backtrack' in ph or 'L-corridor' in ph: durations.append(0.20)
        elif 'snake' in ph.lower(): durations.append(0.10)
        else: durations.append(0.18)

    out = os.path.join(OUT,'snake_vis.gif')
    iio.imwrite(out,frames_img,duration=durations,loop=0)
    size_kb = os.path.getsize(out)//1024
    print(f'    → {out}  ({len(frames_img)} frames, {size_kb} KB)')


if __name__ == '__main__':
    make_gif()
