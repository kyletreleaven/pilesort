"""Function for optimal sort in multiple rounds of pile sort."""

import functools

from setiptah.pilesort.shuffle import QUEUE_TYPE, STACK_TYPE
from setiptah.pilesort.util import backnumerate, is_sorted
from setiptah.pilesort.minsort import minsort, ShuffleInfeasible, CHOICE_TYPE
from typing import Sequence
import numpy as np
from dataclasses import dataclass


def minsort_multiround(positions, pile_types_per_round):
    """Compute a minimal sort of given list in multiple rounds of piles sort.

    Args:
        positions: A permutation of an ordered set;
            a value ``i`` at position ``e`` in the array is
            the position where element ``e`` is found in the ordering.
        pile_types_per_round: An iterable of the pile types available in each round.
            See single-round ``minsort`` for ``pile_types`` format.

    Returns:
        np.ndarray: A ``numpy`` matrix of multi-round pile assignments.

    The output has ``.shape == (n_rounds, len(positions))``.
    A value ``p`` in row ``r`` and column ``e`` is the pile to which element ``e``
    is assigned in round ``r``.

    """
    rounds = []

    if is_sorted(positions):
        return np.ones((0, len(positions)))

    virtual_types = "Q"  # "identity"

    for pile_types in pile_types_per_round:
        rounds.append(pile_types)
        virtual_types = virtual_pile_types(virtual_types, pile_types)

        try:
            shuffle, _ = minsort(positions, virtual_types)
            return convert_virtual_piles(shuffle).to_real_piles(rounds)
        except ShuffleInfeasible:
            pass

    raise ShuffleInfeasible()


def sort_multiround(positions, pile_types_per_round):
    """Compute a sort of given list in multiple rounds of piles sort.

    Args:
        positions: A permutation of an ordered set;
            a value ``i`` at position ``e`` in the array is
            the position where element ``e`` is found in the ordering.
        pile_types_per_round: An iterable of the pile types available in each round.
            See single-round ``minsort`` for ``pile_types`` format.

    Returns:
        np.ndarray: A ``numpy`` matrix of multi-round pile assignments.

    The output has ``.shape == (n_rounds, len(positions))``.
    A value ``p`` in row ``r`` and column ``e`` is the pile to which element ``e``
    is assigned in round ``r``.

    Unlike the minsort version, this function cannot quit early.

    """
    n_rounds = len(pile_types_per_round)

    if n_rounds == 0:
        if is_sorted(positions):
            return np.ones((0, len(positions)))
        else:
            raise ShuffleInfeasible()

    virtual_types = functools.reduce(virtual_pile_types, pile_types_per_round)
    shuffle, _ = minsort(positions, virtual_types)
    return convert_virtual_piles(shuffle).to_real_piles(pile_types_per_round)


def virtual_pile_types(pile_types_1: str, pile_types_2: str) -> str:
    """Obtain the pile types of a corresponding single-round virtual shuffle.

    Args:
        pile_types_1: The pile types available in the first round of shuffle.
        pile_types_2: The pile types available in the second round of shuffle.

    Returns:
        Pile types for an equivalent single-round virtual shuffle.

    >>> virtual_pile_types("QSS", "QSSQ")
    'QSSQQSQQSQSS'

    """
    return "".join(apply_pile(typ, pile_types_1) for typ in pile_types_2)


@dataclass(frozen=True)
class convert_virtual_piles:
    """Utilities to convert from virtual piles.

    Each combination of real pile assignments in a multi-round shuffle
    corresponds to a single virtual pile assignment
    in a corresponding single-round shuffle.

    """

    virtual_piles: Sequence[int]
    """A list of virtual piles."""

    def to_virtual_queues(self, n_piles_per_round):
        """Convert virtual piles to virtual queues.

        Args:
            n_piles_per_round: An iterable of the number of piles available in each round.

        Returns:
            np.ndarray(shape=(n_rounds, n), dtype=int)

        The output has ``.shape == (n_rounds, len(self.virtual_piles))``.
        A value ``p`` in row ``r`` and column ``e`` is the virtual queue to which element ``e``
        is assigned in round ``r``.

        The multi-round virtual queues and real piles coincide if and only if
        the shuffle is entirely on queues.

        """
        virtual_piles = np.array(self.virtual_piles)

        (n_values,) = virtual_piles.shape
        n_rounds = len(n_piles_per_round)

        VQs = np.zeros((n_rounds, n_values), dtype=int)

        for k, n_piles in enumerate(n_piles_per_round):
            virtual_piles, vqs = np.divmod(virtual_piles, n_piles)
            VQs[k, :] = vqs

        if not np.all(virtual_piles == 0):
            raise ValueError("at least one virtual pile out of bounds!")

        return VQs

    def to_real_piles(self, pile_types_per_round):
        """Convert virtual piles to real piles.

        Args:
            pile_types_per_round: An iterable of the pile types available in each round.
            See single-round ``minsort`` for ``pile_types`` format.

        Returns:
            np.ndarray(shape=(n_rounds, n), dtype=int)

        The output has ``.shape == (n_rounds, len(self.virtual_piles))``.
        A value ``p`` in row ``r`` and column ``e`` is the real pile to which element ``e``
        is assigned in round ``r``.

        """
        return convert_virtual_queues(
            self.to_virtual_queues(pile_types_to_piles_per_round(pile_types_per_round))
        ).to_real_piles(pile_types_per_round)


def pile_types_to_piles_per_round(pile_types_per_round):
    """Get an iterator of the number of piles per round."""
    return tuple(len(pile_types) for pile_types in pile_types_per_round)


@dataclass(frozen=True)
class convert_real_piles:
    """Utilities to convert from real piles.

    Each combination of real pile assignments in a multi-round shuffle
    corresponds to a single virtual pile assignment
    in a corresponding single-round shuffle.

    """

    real_piles: np.ndarray
    """A ``numpy`` matrix of real multi-round pile assignments.
    
    A value ``p`` in row ``r`` and column ``e`` is the real pile to which element ``e``
    is assigned in round ``r``.

    """

    def to_virtual_queues(self, pile_types_per_round):
        n_rounds, n_values = self.real_piles.shape
        if len(pile_types_per_round) < n_rounds:
            raise ValueError("Pile types not defined for enough rounds")

        # virtual queue assignments per round
        result = np.zeros((n_rounds, n_values), dtype=int)

        virtual_stack_parity = np.zeros(n_values, dtype=int)

        for round_idx, piles in backnumerate(self.real_piles):
            pile_types = pile_types_per_round[round_idx]
            m = len(pile_types)
            piles_reversed = m - 1 - piles

            vqs = (1 ^ virtual_stack_parity) * piles + (
                virtual_stack_parity * piles_reversed
            )
            result[round_idx, :] = vqs

            pile_stack_parties = stack_indicators(pile_types)
            virtual_stack_parity = virtual_stack_parity ^ pile_stack_parties[piles]

        return result

    def to_virtual_piles(self, pile_types_per_round):
        """Convert real piles to virtual piles.

        Args:
            pile_types_per_round: An iterable of the pile types available in each round.
            See single-round ``minsort`` for ``pile_types`` format.

        Returns:
            A ``numpy`` array of indices (int).

        A value ``p`` at index ``e`` in the output is the single-round virtual pile assignment
        for element ``e``.

        """
        return convert_virtual_queues(
            self.to_virtual_queues(pile_types_per_round)
        ).to_virtual_piles(pile_types_to_piles_per_round(pile_types_per_round))


@dataclass(frozen=True)
class convert_virtual_queues:
    virtual_queues: np.ndarray

    def to_virtual_piles(self, n_piles_per_round):
        VQs = self.virtual_queues
        n_rounds, n_values = VQs.shape
        result = np.zeros(n_values, dtype=int)
        for k, vqs in backnumerate(VQs):
            result = result * n_piles_per_round[k] + vqs
        return result

    def to_real_piles(self, pile_types_per_round):
        VQs = self.virtual_queues
        n_rounds, n_values = VQs.shape

        # real pile assignments per round
        result = np.zeros((n_rounds, n_values), dtype=int)

        virtual_stack_parity = np.zeros(n_values, dtype=int)

        for round_idx, pile_types in backnumerate(pile_types_per_round):
            vqs = VQs[round_idx, :]
            m = len(pile_types)
            vqs_reversed = m - 1 - vqs
            rqs = (1 ^ virtual_stack_parity) * vqs + (
                virtual_stack_parity * vqs_reversed
            )
            result[round_idx, :] = rqs

            pile_stack_parties = stack_indicators(pile_types)
            virtual_stack_parity = virtual_stack_parity ^ pile_stack_parties[rqs]

        return result


def stack_indicators(pile_types):
    return np.array([stack_indicator(typ) for typ in pile_types])


def stack_indicator(pile_type):
    if pile_type.upper() == QUEUE_TYPE:
        return 0
    elif pile_type.upper() == STACK_TYPE:
        return 1
    else:
        raise ValueError(f"Unrecognized pile type: {pile_type}")


def apply_stack(pile_types: str):
    return "".join(invert_type(typ) for typ in reversed(pile_types))


def apply_pile(pile_type, pile_types: str):
    if pile_type.upper() == QUEUE_TYPE:
        return pile_types
    elif pile_type.upper() == STACK_TYPE:
        return apply_stack(pile_types)
    elif pile_type.upper() == CHOICE_TYPE:
        raise ValueError("Multi-round optimal sort does not support choice-type piles.")
    else:
        raise ValueError(f"Unrecognized pile type: {pile_type}")


def invert_type(pile_type):
    if pile_type.upper() == QUEUE_TYPE:
        return STACK_TYPE
    elif pile_type.upper() == STACK_TYPE:
        return QUEUE_TYPE
    else:
        raise ValueError(f"Unrecognized pile type: {pile_type}")
