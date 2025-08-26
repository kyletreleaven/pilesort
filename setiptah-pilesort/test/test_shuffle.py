from setiptah.pilesort.shuffle import (
    deal_values, collect_piles, shuffle_values, apply_pile_type
)
import pytest


def test_deal_values():
    assert deal_values(range(5), [4, 3, 2, 2, 3], 5) == [[], [], [2, 3], [1, 4], [0]]


def test_collect_piles():
    assert (
            collect_piles([[], [], [2, 3], [1, 4], [0]], "SSQSQQQQQ")
            == [2, 3, 4, 1, 0]
    )


def test_shuffle_values():
    assert shuffle_values(range(5), [4, 3, 2, 2, 3], "SSQSQQQQQ", 5) == [2, 3, 4, 1, 0]


def test_invalid_pile_type():
    with pytest.raises(ValueError):
        apply_pile_type("X", [])
