"""Functions used to simulate the parts of a shuffle on piles."""

from setiptah.pilesort.util import place_of, singleton
from typing import Optional, List

QUEUE_TYPE = "Q"
STACK_TYPE = "S"


@singleton
class QUEUES:
    """A simple iterable of arbitrarily many queue-like piles.

    TODO: Add these to docs.

    """

    def __iter__(self):
        while True:
            yield QUEUE_TYPE


@singleton
class STACKS:
    """A simple iterable of arbitrarily many stack-like piles."""

    def __iter__(self):
        while True:
            yield STACK_TYPE


def deal_values(values, shuffle, n_piles: int):
    """Distribute the elements of a list among piles according to a given shuffle.

    Args:
        values: A permutation of an ordered set;
            a value ``e`` at position ``i`` in the array is the element in position ``i`` in the ordering.
        shuffle: An assignment of the elements to piles;
            a value ``p`` at position ``e`` in the array is the pile (0-indexed) where value ``e`` should be placed.
        n_piles: The number of piles to use for the shuffle; used to pre-allocate the piles array.

    Returns:
        A collection of ``n_piles`` piles; list of lists.

    Elements are appended to their assigned pile in the order they are encountered.

    """
    piles = [[] for _ in range(n_piles)]
    for value in values:
        piles[shuffle[value]].append(value)
    return piles


def collect_piles(piles, pile_types: str) -> List[int]:
    """Collect piles into a single list.

    Args:
        piles: A list of lists, as returned by ``deal_values``.
        pile_types: An aligned iterable of pile types, (``"Q"``)ueue or (``"S"``)tack.

    Returns:
        A permutation of an ordered set;
            a value ``e`` at position ``i`` in the array is
            the element in position ``i`` in the permutation ordering.

    The piles are concatenated in order onto the end of a single list
    which starts emtpy.
    If the ``k``-th pile type is ``"Q"`` then the ``k``-th pile is queue-like, and
    it is concatenated as-is.
    If the pile type is ``"S"`` then the pile is stack-like, and
    the pile is reversed before it is concatenated.

    """
    return [
        value
        for pile, pile_type in zip(piles, pile_types)
        for pile_ in place_of(apply_pile_type(pile_type, pile))
        for value in pile_
    ]


def shuffle_values(values, shuffle, pile_types, n_piles: Optional[int] = None):
    """Shuffle the elements of a list using ``deal_values`` followed by ``collect_piles``.

    If ``n_piles`` is not provided, then ``len(pile_types)`` will be used.

    """
    if n_piles is None:
        n_piles = len(pile_types)
    return collect_piles(deal_values(values, shuffle, n_piles), pile_types)


def apply_pile_type(pile_type, pile):
    if pile_type.upper() == QUEUE_TYPE:
        return pile[:]
    elif pile_type.upper() == STACK_TYPE:
        return pile[::-1]
    else:
        raise ValueError(f"Unrecognized pile type: {pile_type}")
