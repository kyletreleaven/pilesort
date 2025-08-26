"""Demonstrating reverse-sort; how to shuffle identity perm into a target perm."""
from setiptah.pilesort.minsort import minsort, CHOICES
from setiptah.pilesort.shuffle import QUEUES, STACKS, shuffle_values
import numpy as np
import random

from setiptah.pilesort.util import invert_perm

ns = []
means = []
for k, n_ in enumerate(np.logspace(0, 4, 1_00, base=10)):
    continue

n = round(n_)
print(k, n)

n = 10
trials = []
for t in range(1):
    continue

perm1 = list(range(n))

# target perm; embedding
target = list(range(n))
random.shuffle(target)

target_seq = invert_perm(target)

# now, target is the perm i _want_; starting from identity
shuffle_, tape = minsort(target_seq, CHOICES)

# transform?
shuffle = [shuffle_[target[k]] for k in range(n)]

tape = tape.replace("C", "Q")  # b/c it doesn't matter!
result = shuffle_values(perm1, shuffle, tape)

result, (result == target_seq)
