import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch
import os

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                   '..', 'griddles-p2-writeup', 'fig_magic_square.png')

FACE = {
    'BLUE':   '#d6eaf8',
    'YELLOW': '#fef9e7',
    'RED':    '#fdedec',
    'GREEN':  '#d5f5e3',
}
EDGE = {
    'BLUE':   '#1a5276',
    'YELLOW': '#7d6608',
    'RED':    '#922b21',
    'GREEN':  '#1d6a39',
}
MYSTERY_BORDER = '#111111'  # thick black border for mystery cell

# (row, col, ordinal, year, city, continent, calendar_label, is_mystery)
cells = [
    (0, 0, 23, 1984, 'Los Angeles', 'RED',    '',               False),
    (0, 1, 28, 2004, 'Athens',      'BLUE',   '695.4',          False),
    (0, 2, 17, 1960, 'Rome',        'BLUE',   '2713',           False),
    (0, 3, 30, 2012, 'London',      'BLUE',   '',               False),
    (1, 0, 18, 1964, 'Tokyo',       'YELLOW', 'SHŌWA 39',  False),
    (1, 1, 29, 2008, 'Beijing',     'YELLOW', '4705',           False),
    (1, 2, 24, 1988, 'Seoul',       'YELLOW', '',               False),
    (1, 3, 27, 2000, 'Sydney',      'GREEN',  '',               False),
    (2, 0, 32, 2020, 'Tokyo',       'YELLOW', 'REIWA 2',        False),
    (2, 1, 19, 1968, 'Mexico City', 'RED',    '12.17.15.2.19',  False),
    (2, 2, 26, 1996, 'Atlanta',     'RED',    '',               True),
    (2, 3, 21, 1976, 'Montréal','RED',   '',               False),
    (3, 0, 25, 1992, 'Barcelona',   'BLUE',   '',               False),
    (3, 1, 22, 1980, 'Moscow',      'BLUE',   '',               False),
    (3, 2, 31, 2016, 'Rio',         'RED',    '',               False),
    (3, 3, 20, 1972, 'Munich',      'BLUE',   '',               False),
]

S = 1.0
PAD = 0.05

# Extra space: 0.6 right for row sums, 0.35 bottom for col sums, 0.5 top for title
fig, ax = plt.subplots(figsize=(7.5, 7.2))
ax.set_xlim(-0.05, 4.65)
ax.set_ylim(-0.9, 4.35)
ax.set_aspect('equal')
ax.axis('off')

for row, col, ordinal, year, city, cont, cal, mystery in cells:
    x0 = col * S
    y0 = (3 - row) * S

    face = FACE[cont]
    edge = MYSTERY_BORDER if mystery else EDGE[cont]
    lw = 4.5 if mystery else 2.0

    rect = FancyBboxPatch((x0 + PAD, y0 + PAD), S - 2*PAD, S - 2*PAD,
                          boxstyle='round,pad=0.03',
                          facecolor=face, edgecolor=edge, linewidth=lw)
    ax.add_patch(rect)

    cx = x0 + 0.5

    if mystery:
        ax.text(cx, y0 + 0.74, '?', ha='center', va='center',
                fontsize=24, fontweight='bold', color='#111111')
        ax.text(cx, y0 + 0.51, '= 26', ha='center', va='center',
                fontsize=11, fontweight='bold', color='#555555')
        ax.text(cx, y0 + 0.31, city, ha='center', va='center',
                fontsize=8, color='#444444')
        ax.text(cx, y0 + 0.14, str(year), ha='center', va='center',
                fontsize=7.5, color='#666666')
    else:
        ax.text(cx, y0 + 0.72, str(ordinal), ha='center', va='center',
                fontsize=20, fontweight='bold', color='#111111')
        ax.text(cx, y0 + 0.48, city, ha='center', va='center',
                fontsize=8, color='#333333')
        ax.text(cx, y0 + 0.30, str(year), ha='center', va='center',
                fontsize=7.5, color='#666666')
        if cal:
            ax.text(cx, y0 + 0.12, cal, ha='center', va='center',
                    fontsize=6.5, color='#7d4000', style='italic',
                    fontweight='semibold')

# Row sums (to the right of grid)
for row in range(4):
    yc = (3 - row) * S + 0.5
    ax.text(4.12, yc, '= 98', ha='left', va='center',
            fontsize=10, color='#333333', fontfamily='monospace')

# Column sums (below grid)
for col in range(4):
    xc = col * S + 0.5
    ax.text(xc, -0.18, '= 98', ha='center', va='top',
            fontsize=10, color='#333333', fontfamily='monospace')

# Outer grid border
border = plt.Rectangle((0, 0), 4*S, 4*S, fill=False,
                        edgecolor='#555555', linewidth=2)
ax.add_patch(border)

# Main diagonal (0,0)→(3,3): plot coords (0.5,3.5)→(3.5,0.5)
# Anti-diagonal (0,3)→(3,0): plot coords (3.5,3.5)→(0.5,0.5)
# zorder=5 keeps them on top of cell patches (default zorder ~1)
diag_kw = dict(color='#666666', lw=1.2, linestyle='--', zorder=5, alpha=0.7)
ax.plot([0.5, 3.5], [3.5, 0.5], **diag_kw)
ax.plot([3.5, 0.5], [3.5, 0.5], **diag_kw)

# Title
ax.set_title('Decoded $4\\times 4$ Parshvanath Pandiagonal Magic Square  ($M = 98$)',
             fontsize=11.5, fontweight='bold', pad=10)

# Legend below the column sum row
legend_items = [
    mpatches.Patch(facecolor=FACE['RED'],    edgecolor=EDGE['RED'],    label='Americas'),
    mpatches.Patch(facecolor=FACE['BLUE'],   edgecolor=EDGE['BLUE'],   label='Europe'),
    mpatches.Patch(facecolor=FACE['YELLOW'], edgecolor=EDGE['YELLOW'], label='Asia'),
    mpatches.Patch(facecolor=FACE['GREEN'],  edgecolor=EDGE['GREEN'],  label='Oceania'),
    mpatches.Patch(facecolor=FACE['RED'],    edgecolor=MYSTERY_BORDER, linewidth=3, label='Mystery cell'),
]
ax.legend(handles=legend_items, loc='lower center',
          bbox_to_anchor=(2.0, -0.88), fontsize=9,
          framealpha=0.95, ncol=5, columnspacing=0.9,
          handlelength=1.4, handletextpad=0.5,
          bbox_transform=ax.transData)

plt.savefig(OUT, bbox_inches='tight', dpi=180)
plt.close(fig)
print(f'Saved: {OUT}')
