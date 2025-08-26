import os

import matplotlib.pyplot as plt
from setiptah.pilesort.util import singleton


_DIR, _ = os.path.split(__file__)
_CARD_FILE = os.path.join(_DIR, "cards.png")


@singleton
class card_guide:
    cards = plt.imread(_CARD_FILE)

    COLS = 13
    WIDTH = 71
    HEIGHT = 96
    START_X = 1
    START_Y = 1
    STRIDE_X = WIDTH + 2
    STRIDE_Y = HEIGHT + 2

    def get_card(self, k: int):
        row, col = divmod(k, self.COLS)
        sx = self.START_X + col * self.STRIDE_X
        sy = self.START_Y + row * self.STRIDE_Y

        return self.cards[
               sy:sy + self.HEIGHT,
               sx:sx+self.WIDTH,
               :
        ]
