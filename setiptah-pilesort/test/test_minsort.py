from setiptah.pilesort.minsort import minsort, ShuffleInfeasible, CHOICES
from setiptah.pilesort.shuffle import deal_values, collect_piles, shuffle_values
from setiptah.pilesort.util import invert_perm

import pytest


@pytest.mark.parametrize(
    "poses, pile_types, expected",
    [
        ([1, 6, 4, 2, 3, 0, 5, 7, 8, 9], "QSSQ", list(range(10))),
    ]
)
def test_minsort(poses, pile_types, expected):

    shuffle, _ = minsort(poses, pile_types)

    values = invert_perm(poses)
    piles = deal_values(values, shuffle, 1 + shuffle[-1])
    result = collect_piles(piles, pile_types)

    assert result == expected


def test_minsort_dealer_choice():
    poses = [1, 4, 3, 2, 0, 5, 6, 7]
    shuffle, pile_types = shuffle_with_types = minsort(poses, CHOICES)
    assert shuffle_with_types == ([0, 0, 1, 1, 1, 2, 2, 2], "QSQ")
    assert shuffle_values(invert_perm(poses), shuffle, pile_types) == sorted(poses)


def test_minsort_dealer_choice_dangle():
    poses = [0, 1, 3, 2]
    shuffle, _ = shuffle_with_types = minsort(poses, CHOICES)
    assert shuffle_with_types == ([0, 0, 0, 1], "QC")

    assert shuffle_values(invert_perm(poses), shuffle, "QQ") == sorted(poses)
    assert shuffle_values(invert_perm(poses), shuffle, "QS") == sorted(poses)


def test_sort_infeasible():
    poses = list(range(50))
    pile_types = "SSSS"

    with pytest.raises(ShuffleInfeasible):
        minsort(poses, pile_types)
