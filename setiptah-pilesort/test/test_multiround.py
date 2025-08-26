from setiptah.pilesort.multiround import convert_virtual_piles, convert_real_piles
from setiptah.pilesort.multiround import minsort_multiround, sort_multiround
from setiptah.pilesort.util import invert_perm
from setiptah.pilesort.shuffle import shuffle_values
from setiptah.pilesort.minsort import ShuffleInfeasible

import numpy as np

import pytest


def random_positions(n):
    poses = list(range(n))
    import random
    random.shuffle(poses)
    return poses


def test_minsort_already_sorted():

    schedule = ["SS", "QQ"]
    poses = list(range(10))

    shuffle = minsort_multiround(poses, schedule)
    assert shuffle.shape == (0, len(poses))

    values = invert_perm(poses)
    for shuffle_, pile_types in zip(shuffle, schedule):
        raise RuntimeError("No shuffling should occur.")
    assert values == sorted(values)


def test_roundtrip_conversion():
    """

    We can demonstrate equivalence for _any_ shuffle,
    not just a sort.

    """
    schedule = ("QQS", "QQ", "QSS")

    real_piles = np.array([
        np.floor(np.random.rand(10) * len(pile_types)).astype(int)
        for pile_types in schedule
    ])

    vps = convert_real_piles(real_piles).to_virtual_piles(schedule)

    real_ = convert_virtual_piles(vps).to_real_piles(schedule)
    assert np.all(real_ == real_piles)


@pytest.mark.parametrize(
    "positions, schedule",
    [
        (list(range(4)[::-1]), ("QQ", "QQ")),
        (random_positions(20), ("QQS", "QQ", "QSS")),
    ]
)
def test_minsort_multiround(positions, schedule):
    shuffle = minsort_multiround(positions, schedule)

    values = invert_perm(positions)

    for shuffle_, pile_types in zip(shuffle, schedule):
        values = shuffle_values(values, shuffle_, pile_types)

    assert values == sorted(values)


def test_minsort_shortcircuit():
    poses = (1, 2, 4, 0, 3, 5)
    schedule = ["QQ", "S"]

    shuffle = minsort_multiround(poses, schedule)
    n_rounds, _ = shuffle.shape
    assert n_rounds == 1

    values = invert_perm(poses)
    for shuffle_, pile_types in zip(shuffle, schedule):
        values = shuffle_values(values, shuffle_, pile_types)

    assert values == sorted(values)


def test_sort_upset():
    poses = range(10)
    schedule = ["S"]

    minsort_multiround(poses, schedule)  # no problem!

    with pytest.raises(ShuffleInfeasible):
        sort_multiround(poses, schedule)  # but this version forced through the stack!


def test_sort_empty():

    sort_multiround(range(10), [])  # fine, already sorted
    with pytest.raises(ShuffleInfeasible):
        sort_multiround(range(10)[::-1], [])  # oops.
