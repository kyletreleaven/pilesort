from matplotlib import patches
import setiptah.pilesort.multiround as mr
from typing import Optional

from setiptah.pilesort.hard.words import ALIGN
from setiptah.pilesort.hard.util import powerspace

from setiptah.pilesort.draw.gridplt import *

ALIGN_WIDTH = len(ALIGN)

UNIT_GRID = Grid((0, 0), (1, 1))
IMAGE_GRID = Grid((0, 0), (1, -1))

ann_opts = dict(va="center", ha="center")

# underlay column highlights
COLMAP = {  # https://htmlcolorcodes.com/color-names/
    0: "#4682B4",  # start, blue
    1: "#DC143C",  # start-disq; crimson
    2: "#32CD32",  # actd; lime green
    3: "#FFD700",  # not-actd; orange
    5: "#FFA500",  # disq, end; gold
}


def compile(types: str):
    n = len(types)
    on_a = [
        min(k if types[k] == "Q" else (k + 1), n)
        for k in range(n)
    ]
    on_a.append(n)

    on_d = [
        min(k if types[k] == "S" else (k + 1), n)
        for k in range(n)
    ]
    on_d.append(n)

    return {"a": on_a, "d": on_d}


def plot_gadget_grid(
        word: str,
        start: int,
        n_measures: int = None,
        *,
        label_fn = None,
        color_key = None,
        ax = None,
        cmap = None,
        measures = None,
):

    if measures is None:
        measures = powerspace("QS", n_measures)

    cases = {
        trans: mr.virtual_pile_types(ALIGN, trans)
        for trans in measures
    }

    trans_ = next(iter(cases.keys()))
    n_assign_piles = len(trans_)

    n_cases = len(cases)
    radial = Circular(n_cases, (.5, .5), .2)
    # queen_grid_rel = nQueen(UNIT_GRID, n_cases)

    def grid_rect(cell: Grid, *args, **kwargs):
        tl = min(cell.left, cell.right), min(cell.top, cell.bottom)
        w, h = map(np.abs, cell.dims)
        return patches.Rectangle(tl, w, h, *args, **kwargs)

    grid = IMAGE_GRID

    for i in range(n_assign_piles):
        for k, col in COLMAP.items():
            col_grid = Grid.from_corners(
                grid.cell(ALIGN_WIDTH * i + k, 0).origin,
                grid.cell(ALIGN_WIDTH * i + k, len(word)).tr
            )
            rect = grid_rect(col_grid, color=col, alpha=.2)
            ax.add_patch(rect)

    # draw paths themselves
    if cmap is None:
        cmap = {}

    for k_case, (trans, types) in enumerate(cases.items()):
        rel_mark = radial.mark(k_case)
        # rel_mark = queen_grid_rel.queen(k_case + 1).center  # index by 1?

        machine = compile(types)

        for k_start in [start]:
            xs, ys = [], []

            cur = k_start

            x, y = grid.cell(cur, 0).to_abs(*rel_mark)
            xs.append(x)
            ys.append(y)

            for k_sym, action in enumerate(word, 1):
                cur = machine[action][cur]

                x, y = grid.cell(cur, k_sym).to_abs(*rel_mark)
                xs.append(x)
                ys.append(y)

            label = label_fn(trans)
            ckey = color_key(k_start, trans)
            opts = dict(label=label, linestyle="--", linewidth=1)
            if ckey in cmap:
                ax.plot(xs, ys, color=cmap[ckey], **opts)
            else:
                p = ax.plot(xs, ys, **opts)
                cmap[ckey] = p[0].get_color()
            ax.scatter(xs, ys, color=cmap[ckey], s=4)

    # build grid
    align_width = ALIGN_WIDTH

    for w in range(n_assign_piles * align_width + 1):
        for h in range(len(word) + 1):
            rect = grid_rect(grid.cell(w, h), fill=False)
            ax.add_patch(rect)

    # write grid header
    for i in range(n_assign_piles):  # assignment pile index
        pile_grid = Grid.from_corners(
            grid.cell(align_width * i, -2).origin,
            grid.cell(align_width * (i + 1), -1).origin
        )
        ax.add_patch(grid_rect(pile_grid, fill=False))

        measure_str = (
            "$k$" if i == 0
            else f"$k + {i}$"
        )
        ax.annotate(measure_str, pile_grid.center, **ann_opts)

        for j in range(align_width):  # alignment pile index
            align_grid = Grid.from_corners(
                grid.cell(align_width * i + j, -1).origin,
                grid.cell(align_width * i + j + 1, 0).origin,
            )
            ax.add_patch(grid_rect(align_grid, fill=False))
            ax.annotate(f"${j}\\backslash$", align_grid.center, **ann_opts)

    term_grid = Grid.from_corners(
        grid.cell(align_width * n_assign_piles, -2).origin,
        grid.cell(align_width * n_assign_piles, -1).tr
    )
    ax.add_patch(grid_rect(term_grid, fill=False))
    ax.annotate("*", term_grid.center, **ann_opts)

    # write the actions as vertical ticks
    dx, dy = grid.dims
    lbar = Grid(
        origin=grid.cell(-1, 0).origin,
        dims=(dx, len(word) * dy)
    )
    ax.add_patch(grid_rect(lbar, color="none"))  # claim the space
    for i, action in enumerate(word):
        # ch = "a" if action is Action.RIGHT else "d"
        ch = action
        action_cell = grid.cell(-1, i)
        ax.annotate(f"${{\\it {ch}}}$", (action_cell.left, action_cell.top), **ann_opts)

    ax.axis("off")


def scale_and_add_legend(ax):
    # Shrink current axis by 20%
    box = ax.get_position()
    ax.set_position([box.x0, box.y0, box.width * 0.8, box.height])

    # Put a legend to the right of the current axis
    ax.legend(loc='center left', bbox_to_anchor=(1, 0.5))
