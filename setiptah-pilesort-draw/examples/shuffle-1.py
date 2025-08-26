import matplotlib.pyplot as plt


import random

seq = list(range(10))
random.shuffle(seq)

from setiptah.pilesort.util import invert_perm, singleton

poses = invert_perm(seq)

from setiptah.pilesort.multiround import minsort_multiround
from setiptah.pilesort.shuffle import deal_values, collect_piles


def repeat(pile_types):

    @singleton
    class iterable:
        def __iter__(self):
            while True:
                yield pile_types

    return iterable


pile_types = "QQS"
shuffle = minsort_multiround(poses, repeat(pile_types))

n_rounds, n_cards = shuffle.shape

from PIL import Image
from setiptah.pilesort.draw.cards import card_guide

plt.close("all")

deck = seq
for r, shuffle_ in enumerate(shuffle):

    # show deck..
    plt.subplot(n_rounds, 2, 2 * r + 1)
    # Create a new white background image with the same size
    image = Image.new("RGBA", (400, 350), (255,) * 4)

    for k, card_index in enumerate(deck):
        card_array = card_guide.get_card(card_index)
        card = Image.fromarray((card_array * 255).astype("uint8"), mode="RGBA")

        image.paste(
            card,
            (13 * k, 0),
        )

    plt.imshow(
        # card_guide.get_card(37)
        image
    )

    # show piles
    plt.subplot(n_rounds, 2, 2 * r + 1 + 1)
    image = Image.new("RGBA", (400, 350), (255,) * 4)

    piles = deal_values(deck, shuffle_, len(pile_types))
    deck = collect_piles(piles, pile_types)

    for p, values in enumerate(piles):
        for k, card_index in enumerate(values):
            card_array = card_guide.get_card(card_index)
            card = Image.fromarray((card_array * 255).astype("uint8"), mode="RGBA")

            image.paste(
                card,
                (13 * k, 110 * p),
            )

    plt.imshow(
        # card_guide.get_card(37)
        image
    )

plt.show()
