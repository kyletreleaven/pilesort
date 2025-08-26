"""Empirical study of the expected number of piles (hetero.) to sort."""
from setiptah.pilesort.minsort import minsort, CHOICES
from setiptah.pilesort.shuffle import QUEUES, STACKS
import numpy as np
import random


ns = []
means = []
for k, n_ in enumerate(np.logspace(0, 4, 1_00, base=10)):
    n = round(n_)
    print(k, n)

    trials = []
    for t in range(100):
        poses = list(range(n))
        random.shuffle(poses)
        _, tape = minsort(poses, CHOICES)
        # _, tape = minsort(poses, QUEUES)
        trials.append(len(tape))

    ns.append(n)
    means.append(np.mean(trials))


import matplotlib.pyplot as plt

m, b = np.polyfit(ns, means, 1)

plt.close("all")
plt.scatter(ns, means)
# plt.plot(ns, m * np.array(ns) + b)
plt.axline(xy1=(0, b), slope=m, label=f'$y = {m:.4f}x {b:+.4f}$', linestyle="--")
plt.legend()
plt.show()
