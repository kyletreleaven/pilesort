from functools import cached_property

from setiptah.pilesort.hard.words import *
from setiptah.pilesort.util import singleton
from abc import ABC

from setiptah.pilesort.draw.hard.gadget_plots import *

import matplotlib.pyplot as plt

# https://towardsdatascience.com/making-publication-quality-figures-in-python-part-i-fig-and-axes-d86c3903ad9b
import matplotlib as mpl


FINE = ["tab:gray", "slategray", "tab:blue", "#7f7f7f"][2]
GREEN = ["tab:green", "limegreen", "#2ca02c"][0]
RED = ["tab:red", "maroon", "#d62728"][0]

FINE, GREEN, RED = ["#4e79a7", "#1a9850", "#e63946"]

class LabelFnMixin:

    def label_fn(self, trans):
        parts = [
            #"\\Phi^*" if False else "\\Phi",
            "\\ddot\\chi",
            "\\backslash",
        ]
        for sym in trans:
            parts.append(
                "{\\bf q}" if sym == "Q" else "{\\bf s}"
            )

        inside = " ".join(parts)
        return f"${inside}$"

    @cached_property
    def figsize(self):
        """

        TODO: Migrate.

        """

        cells = (6 * self.n_measures + 1, len(self.word) + 3)
        return tuple(dim * .4 for dim in cells)


@singleton
class start_clause(LabelFnMixin):
    word = START_CLAUSE
    n_measures = 1

    starts = (START_POS, CHAIN_DISQ)

    def color_key(self, start, seq):
        return NACTD if start == START_POS else CLAUSE_DISQ

    cmap = {
        ACTD: GREEN,
        NACTD: FINE,
        CLAUSE_DISQ: RED,
    }

    filepatt = "start-clause-{}"


class VarTest(LabelFnMixin, ABC):
    activated_by: str

    n_measures = 2

    starts = (ACTD, NACTD, CLAUSE_DISQ)

    def color_key(self, start, seq):
        if start == ACTD:
            return ACTD
        elif start == NACTD:
            return ACTD if seq[0] == self.activated_by else NACTD
        else:
            return CLAUSE_DISQ

    cmap = {
        ACTD: GREEN,
        NACTD: FINE,
        CLAUSE_DISQ: RED,
    }


@singleton
class pos(VarTest):
    word = POS
    activated_by = "Q"

    filepatt = "append-lit-pos-{}"

@singleton
class neg(VarTest):
    word = NEG
    activated_by = "S"

    filepatt = "append-lit-neg-{}"

@singleton
class dk(VarTest):
    word = DK
    activated_by = None

    filepatt = "append-lit-dk-{}"


class EndVarTest(LabelFnMixin, ABC):
    word: str
    activated_by: str

    n_measures = 3

    starts = (ACTD, NACTD, CLAUSE_DISQ)

    def color_key(self, start, seq):
        if start == CLAUSE_DISQ or seq[1] == "S":
            return CHAIN_DISQ

        if start == ACTD or seq[0] == self.activated_by:
            return END_POS

        return CHAIN_DISQ

    cmap = {
        END_POS: GREEN,
        CHAIN_DISQ: RED,
    }


@singleton
class endpos(EndVarTest):
    word = ENDPOS
    activated_by = "Q"

    filepatt = "end-lit-pos-{}"


@singleton
class endneg(EndVarTest):
    word = ENDNEG
    activated_by = "S"

    filepatt = "end-lit-neg-{}"

@singleton
class enddk(EndVarTest):
    word = ENDDK
    activated_by = None

    filepatt = "end-lit-dk-{}"


@singleton
class next(LabelFnMixin):
    word = NEXT
    n_measures = 2

    filepatt = "next-clause-{}"

    measures = tuple(
        f"Q{ch}" for ch in "QS"
    )

    starts = (END_POS,)

    def color_key(self, start, seq):
        return 0

    cmap = {
        0: FINE,
    }

@singleton
class forceq(LabelFnMixin):
    word = FORCEQ
    n_measures = 2

    filepatt = "no-invert-{}"

    starts = (START_POS, CHAIN_DISQ)

    def color_key(self, start, seq):
        if start == START_POS and seq[0] == "Q":
            return START_POS
        return CHAIN_DISQ

    cmap = {
        START_POS: FINE,
        CHAIN_DISQ: RED,
    }


@singleton
class pass_gadget(LabelFnMixin):
    word = PASS_CODE
    n_measures = 2

    filepatt = "pass-reg-{}"

    starts = (START_POS, CHAIN_DISQ, END_POS)

    def color_key(self, start, seq):
        return start

    cmap = {
        START_POS: FINE,
        CHAIN_DISQ: RED,
        END_POS: GREEN,
    }


"""
case = start_clause
case = pos
case = neg
case = dk
case = next
case = endpos
case = forceq
case = enddk
case = endneg
case = pass_gadget
"""

mpl.rcParams.update({
    #'figure.figsize': (6.0, 4.0),  # Width, Height in inches
    #'figure.figsize': (10, 6),  # Width, Height in inches
    'font.size': 10,               # Default font size
    # "font.weight": "bold",
    'axes.labelsize': 10,          # Axis label size
    'axes.titlesize': 10,          # Axes title size
    'xtick.labelsize': 8,
    'ytick.labelsize': 8,
    'legend.fontsize': 9,
    'figure.dpi': 300,             # High-res figures for papers
    #
    'text.usetex': True,
    'font.family': 'serif',  # or 'sans-serif'
    'figure.figsize': (3.4, 2.5),  # match column width
})

#mpl.rcParams['pdf.fonttype'] = 42
mpl.rcParams['pdf.fonttype'] = 42
mpl.rcParams['ps.fonttype'] = 42
mpl.rcParams['font.family'] = 'Arial'

SAVE_FIG = True


def handle_case(case, start):
    try:
        measures = case.measures
    except AttributeError:
        measures = None

    plt.close("all")

    plt.figure()
    try:
        plt.figure(figsize=case.figsize)
    except AttributeError:
        plt.figure()

    ax = plt.gca()
    plot_gadget_grid(
        case.word, start, case.n_measures,
        label_fn=case.label_fn,
        color_key=case.color_key,
        cmap=case.cmap,
        measures=measures,
        ax=ax,
    )
    ax.set_aspect("equal")
    scale_and_add_legend(ax)

    if SAVE_FIG:
        fn = case.filepatt.format(start) + ".pdf"
        plt.savefig(fn, bbox_inches="tight")
        print(fn)
    else:
        plt.show()

if True:

    for case in [
        pos, neg, dk,
    ]:
        for start in case.starts:
            handle_case(case, start)

    for case in [
        endpos, endneg, enddk,
    ]:
        for start in case.starts:
            handle_case(case, start)



if False:

    for case in [
        pass_gadget,
    ]:
        for start in case.starts:
            handle_case(case, start)

    pass


    for case in [
        forceq,
    ]:
        for start in case.starts:
            handle_case(case, start)


    for case in [
        next,
    ]:
        for start in case.starts:
            handle_case(case, start)

    for case in [
        start_clause,
    ]:
        for start in case.starts:
            handle_case(case, start)


