"""

Tests of the low-level gadgets leading to a computational complexity result for pile shuffle sort [1].

[1] Sorting by pile shuffles on queue-like and stack-like piles can be hard; https://arxiv.org/abs/2506.05518

"""
from setiptah.pilesort.hard import words, automata
from setiptah.pilesort.multiround import virtual_pile_types
from setiptah.pilesort.hard.util import powerspace

import pytest


@pytest.mark.parametrize("pile_type", "QS")
@pytest.mark.parametrize("start_pos", [words.START_POS, words.CHAIN_DISQ])
def test_start_clause(pile_type, start_pos):
    pile_types_ = virtual_pile_types(words.ALIGN, pile_type)
    machine = automata.compile(pile_types_)
    end_pos = automata.apply_word(machine, start_pos, words.START_CLAUSE)

    if start_pos == words.START_POS:
        assert end_pos == words.NACTD
    else:
        assert end_pos >= words.CLAUSE_DISQ


@pytest.mark.parametrize("word", [words.POS, words.NEG, words.DK])
@pytest.mark.parametrize("start_type", "QS")
@pytest.mark.parametrize("start_pos", [words.NACTD, words.ACTD, words.CLAUSE_DISQ])
def test_activation(word, start_type, start_pos):
    n = len(words.ALIGN)

    for next_type in "QS":
        pile_types_ = virtual_pile_types(words.ALIGN, (start_type, next_type))
        machine = automata.compile(pile_types_)
        end_pos = automata.apply_word(machine, start_pos, word)

        if start_pos == words.CLAUSE_DISQ:
            assert end_pos >= words.CLAUSE_DISQ + n

        elif any([
            start_pos == words.ACTD,
            word == words.POS and start_type == "Q",  # activated by POS when type is Q
            word == words.NEG and start_type == "S",  # activated by NEG when type is S
        ]):
            assert end_pos == words.ACTD + n

        else:
            assert end_pos == words.NACTD + n


@pytest.mark.parametrize("word", [words.ENDPOS, words.ENDNEG, words.ENDDK])
@pytest.mark.parametrize("start_type", "QS")
@pytest.mark.parametrize("start_pos", [words.NACTD, words.ACTD, words.CLAUSE_DISQ])
def test_end_activation(word, start_type, start_pos):

    n = len(words.ALIGN)

    for ext in powerspace("QS", 2):
        end_type, _ = ext

        pile_types_ = virtual_pile_types(words.ALIGN, (start_type, *ext))
        machine = automata.compile(pile_types_)
        end_pos = automata.apply_word(machine, start_pos, word)

        if start_pos == words.CLAUSE_DISQ or end_type != "Q":
            assert end_pos >= words.CHAIN_DISQ + 2 * n

        elif any([
            start_pos == words.ACTD,  # already activated
            word == words.ENDPOS and start_type == "Q",
            word == words.ENDNEG and start_type == "S",
        ]):
            assert end_pos == words.END_POS + n
        else:
            assert end_pos >= words.CHAIN_DISQ + 2 * n


def test_next():

    for next_type in "QS":
        pile_types_ = virtual_pile_types(words.ALIGN, ("Q", next_type))
        machine = automata.compile(pile_types_)
        end_pos = automata.apply_word(machine, words.END_POS, words.NEXT)
        assert end_pos == words.START_POS + len(words.ALIGN)


@pytest.mark.parametrize("start_type", "QS")
@pytest.mark.parametrize("start_pos", [words.START_POS, words.CHAIN_DISQ])
def test_forceq(start_type, start_pos):

    for next_type in "QS":
        pile_types_ = virtual_pile_types(words.ALIGN, (start_type, next_type))
        machine = automata.compile(pile_types_)
        end_pos = automata.apply_word(machine, start_pos, words.FORCEQ)

    if start_pos == words.START_POS and start_type == "Q":
        assert end_pos == words.START_POS + len(words.ALIGN)
    else:
        assert end_pos >= words.CHAIN_DISQ + len(words.ALIGN)


@pytest.mark.parametrize("start_pos", [words.START_POS, words.CHAIN_DISQ])
def test_align_aligned(start_pos):
    n = len(words.ALIGN)

    SEEN = set()
    for types2 in powerspace("QS", 3):
        types2 = "".join(types2)
        pile_types_ = virtual_pile_types(words.ALIGN, types2)

        if pile_types_ in SEEN:
            continue
        SEEN.add(pile_types_)

        machine = automata.compile(pile_types_)
        end_pos = automata.apply_word(machine, start_pos, words.ALIGNMENT_CODE)

        if start_pos == words.START_POS and types2[:2] == "QS":
            assert end_pos == words.START_POS + 2 * n
        else:
            assert end_pos >= words.CHAIN_DISQ + 2 * n


def test_align_unaligned():
    n = len(words.ALIGN)

    SEEN = set()

    # ignore all aligned
    for types2 in powerspace("QS", 3):
        pile_types_ = virtual_pile_types(words.ALIGN, types2)
        if pile_types_ in SEEN:
            continue
        SEEN.add(pile_types_)

    # check everything that _cannot_ be represented as an aligned example
    for types in powerspace("QS", n + 3):
        types = "".join(types)
        align, types2 = types[:n], types[n:]
        pile_types_ = virtual_pile_types(align, types2)

        if pile_types_ in SEEN:
            continue
        SEEN.add(pile_types_)

        machine = automata.compile(pile_types_)
        for start_pos in range(n):
            end_pos = automata.apply_word(machine, start_pos, words.ALIGNMENT_CODE)
            assert end_pos >= (start_pos + 1) + 2 * n  # verify penalty of at least one (1) beat
