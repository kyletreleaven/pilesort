"""Util module."""
from typing import TypeVar, Iterator

T = TypeVar("T")


def singleton(factory):
    return factory()


def place_of(x: T) -> Iterator[T]:
    """A trivial singleton generator of the input.

    Useful in comprehensions; e.g.,

    >>> [
    ...     (i, twice_i)
    ...     for i in range(5)
    ...     if i > 1
    ...     for twice_i in place_of(i * 2)
    ...     if twice_i < 7
    ... ]
    [(2, 4), (3, 6)]

    """
    yield x


def backnumerate(coll):
    """``enumerate`` a collection in reverse.

    >>> list(backnumerate("ABC"))
    [(2, 'C'), (1, 'B'), (0, 'A')]

    """
    n = len(coll)
    for k in range(n)[::-1]:
        yield k, coll[k]


def intervals(seq):
    """Iterate the adjacent pairs of a sequence.

    >>> list(intervals(range(3)))
    [(0, 1), (1, 2)]

    >>> list(intervals([0]))
    []

    """
    prev = None
    first = True
    for curr in seq:
        if first:
            first = False
        else:
            yield prev, curr
        prev = curr


def is_sorted(seq):
    """Check if the sequence is sorted.

    >>> is_sorted(range(10))
    True

    >> is_sorted([1, 3, 2])
    False

    """
    return all(i < j for i, j in intervals(seq))


def invert_perm(perm):
    """Invert a permutation.

    Every value ``e`` at index ``i`` will result in ``i`` at index ``e`` in the output.

    Examples:

    >>> invert_perm(range(5))
    [0, 1, 2, 3, 4]

    >>> invert_perm([0, 4, 2, 3, 1])
    [0, 4, 2, 3, 1]

    >>> invert_perm([1, 2, 0])
    [2, 0, 1]

    """
    perm_ = [None for _ in perm]
    for k, s in enumerate(perm):
        perm_[s] = k
    return perm_
