"""An algorithm for optimal sort on piles."""

from setiptah.pilesort.shuffle import QUEUE_TYPE, STACK_TYPE
from setiptah.pilesort.util import singleton
from typing import List


CHOICE_TYPE = "C"
"""Special "dealer choice" pile type. A sort algorithm may use either Q or S."""


@singleton
class CHOICES:
    """A simple iterable of arbitrarily many dealer-choice piles."""

    def __iter__(self):
        while True:
            yield CHOICE_TYPE


def minsort(positions: List[int], pile_types):
    """Obtain a minimal sort of given list using piles of given types.

    Args:
        positions: A permutation of an ordered set;
            a value ``i`` at position ``e`` in the array is
            the position where element ``e`` is found in the ordering.
        pile_types: An aligned iterable of pile types,
            (``"Q"``)ueue, (``"S"``)tack, or dealer (``"C"``)hoice.

    Returns:
        (shuffle, pile_types_out): The tuple of the output sort and pile types used.

        shuffle: An assignment of the elements to piles
            a value ``p`` at position ``e`` in the array is the pile (0-indexed) where ``e`` should be placed.
        pile_types_out: An aligned iterable of pile types used by the sort.

    Raises:
        ShuffleInfeasible: if the list cannot be sorted on the given piles.

    Dealer choice piles in the input will be replaced with fixed types unless the type remains arbitrary.
    That is generally only possible for the very last pile.

    """
    shuffle = []
    types_used = []

    piles = enumerate(pile_types)

    def next_pile():
        try:
            return next(piles)
        except StopIteration:
            raise ShuffleInfeasible()

    pile_type = None
    for i, pos in enumerate(positions):
        if i == 0 or not placement_okay(pos, positions[i - 1], pile_type):
            pile_idx, pile_type = next_pile()

            if pile_type == CHOICE_TYPE and i + 1 < len(positions):
                next_pos = positions[i + 1]
                if next_pos > pos:
                    pile_type = QUEUE_TYPE
                elif next_pos < pos:
                    pile_type = STACK_TYPE

            types_used.append(pile_type)

        shuffle.append(pile_idx)

    return shuffle, "".join(types_used)


class ShuffleInfeasible(Exception):
    """Exception raised if permutation cannot be sorted according to the given schedule."""


def placement_okay(pos, prev_pos, pile_type):
    if pile_type.upper() == QUEUE_TYPE:
        return pos >= prev_pos
    elif pile_type.upper() == STACK_TYPE:
        return pos <= prev_pos
    else:
        raise ValueError(f"Unrecognized pile type: {pile_type}")
