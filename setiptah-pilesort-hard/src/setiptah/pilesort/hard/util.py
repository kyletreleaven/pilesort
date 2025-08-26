import itertools


def powerspace(coll, n: int):
    """

    >>> sorted(powerspace(range(3), 2))
    [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

    """
    yield from itertools.product(*([coll] * n))
