-- Main target: everything should eventually follow transitively from this
import PileSort.Reduction.SATToShuffle

-- Additional targets not yet reachable transitively
import PileSort.SAT
import PileSort.Reduction.SATToMatchingChain
import PileSort.Reduction.ShuffleMultiRoundToSingle

-- TODO: sunset this
import PileSort.ClauseWord
