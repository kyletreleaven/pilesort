"""

TODOs?

- Create a table (easy?).

- Draw the deck face up in front of the dealer. Use a little card stagger.

- Until the deck is empty:

    - Move the top card through a trajectory from its starting point to the top of its assigned pile (use stagger).

    - Use non-uniform velocity; probably snappiest at the end; try different "easing" functions to see what works.

    - Control the "straightaway" velocity so it feels nice.

    - If its assignment is a queue-like pile, then "flip" the card midway:

        - For a short span around the half-way point, execute an alpha transition from face to back of card.

"""
from typing import Tuple
from functools import cached_property
from dataclasses import dataclass

import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
import numpy as np

from PIL import Image

from setiptah.pilesort.draw.cards import card_guide
from setiptah.pilesort.util import invert_perm, singleton, place_of, backnumerate

N_CARDS = 30

card_images = [
    Image.fromarray(
        (card_array * 255).astype("uint8"),
        mode="RGBA"
    )
    for k in range(N_CARDS)
    for card_array in place_of(card_guide.get_card(k))
]

WIDTH, HEIGHT = 800, 600
FPS = 30


def get_table():
    return Image.new("RGBA", (WIDTH, HEIGHT), (255,) * 4)

from setiptah.pilesort.draw.util import frame_times

seq = list(range(N_CARDS))
import random
random.shuffle(seq)

poses = invert_perm(seq)

from setiptah.pilesort.multiround import minsort_multiround
from setiptah.pilesort.shuffle import shuffle_values


def repeat(pile_types):

    @singleton
    class iterable:
        def __iter__(self):
            while True:
                yield pile_types

    return iterable


pile_types = "QSQS"
# pile_types = "QQQ"
shuffle = minsort_multiround(poses, repeat(pile_types))

n_rounds, n_cards = shuffle.shape

from setiptah.pilesort.draw.traj import affine

# params
PLACE_CARD_DURATION = .35
BRAKE_BY = .1
PLACE_CARD_PERIOD = .4

CARD_OFFSET = 20


from setiptah.pilesort.draw.traj import (
    deal_card,
    delay,
    step_traj,
    piecewise,
)

from typing import Sequence


@dataclass(frozen=True)
class ShuffleHelper:
    seq: Sequence[int]  # the sequence to be shuffled; position -> card index
    shuffle: Sequence[int]  # the shuffle; card index -> pile index
    pile_types: str

    @cached_property
    def index(self):  # card index -> sequence position
        return invert_perm(self.seq)

    @cached_property
    def pile_positions(self):
        result = [None] * len(self.seq)

        pile_counts = [0] * len(self.pile_types)
        for card_idx in seq:
            pile_idx = self.shuffle[card_idx]
            result[card_idx] = pile_counts[pile_idx]
            pile_counts[pile_idx] += 1

        return result

    @cached_property
    def next_seq(self):
        return shuffle_values(self.seq, self.shuffle, self.pile_types, len(self.pile_types))

    @cached_property
    def next_index(self):
        return invert_perm(self.next_seq)

    @cached_property
    @dataclass(frozen=True)
    class deal:
        helper: "ShuffleHelper"

        def card_start(self, card_id):
            helper = self.helper
            k = seq_pos = helper.index[card_id]
            return (
                WIDTH / 2 - 5 * k,
                HEIGHT - 100 - 2 * k
            )

        def card_end(self, card_id):
            helper = self.helper
            pile_idx = helper.shuffle[card_id]
            index_in_pile = helper.pile_positions[card_id]

            return (
                100 + 200 * pile_idx - CARD_OFFSET * index_in_pile,
                200 - CARD_OFFSET * index_in_pile
            )

    @cached_property
    @dataclass(frozen=True)
    class pickup:
        """

        Note: Another case where attribute type hypercube would be really handy..

        """
        helper: "ShuffleHelper"

        def card_start(self, card_id):
            return self.helper.deal.card_end(card_id)  # easy

        def card_end(self, card_id):
            return ShuffleHelper(
                self.helper.next_seq,
                # fingies crossed
                None,
                None,
            ).deal.card_start(card_id)


# create the scene
trajs = [None] * n_cards
z_trajs = [None] * n_cards

t = 0.

print(shuffle.shape)

for round_idx, shuffle_ in enumerate(shuffle):
    helper = ShuffleHelper(seq, shuffle_, pile_types)

    # first deal
    for k, card_idx in enumerate(helper.seq):
        card_pos = k
        assert helper.index[card_idx] == card_pos

        # positions and trajectory
        card_start = helper.deal.card_start(card_idx)
        card_end = helper.deal.card_end(card_idx)

        traj_fn = delay(  # timing
            deal_card(
                card_start,
                card_end,
                PLACE_CARD_DURATION,
                BRAKE_BY,
            ),
            t,
        )

        # need drawing height too, so cards can be placed on tops or bottoms of stacks
        card_pos_ = index_in_new_deck = helper.next_index[card_idx]

        z_fn = affine.thru((0, -card_pos), (1, -card_pos_))(step_traj)
        z_fn = delay(z_fn, t + .5 * PLACE_CARD_DURATION)

        if trajs[card_idx] is None:
            trajs[card_idx] = piecewise([], [traj_fn])
            z_trajs[card_idx] = piecewise([], [z_fn])

        else:
            trajs[card_idx].events.append(t)
            trajs[card_idx].trajs.append(traj_fn)

            z_trajs[card_idx].events.append(t)
            z_trajs[card_idx].trajs.append(z_fn)

        t += PLACE_CARD_PERIOD

    # then collect

    for pile_idx, _ in enumerate(helper.pile_types):
        for card_idx, pile_idx_ in enumerate(helper.shuffle):
            if pile_idx_ != pile_idx:
                continue

            pickup_traj = deal_card(
                helper.pickup.card_start(card_idx),
                helper.pickup.card_end(card_idx),
                PLACE_CARD_DURATION,
                BRAKE_BY,
            )
            traj = trajs[card_idx]
            traj.events.append(t)
            traj.trajs.append(delay(pickup_traj, t))

            z1 = -helper.pile_positions[card_idx]
            z2 = -helper.next_index[card_idx]

            pickup_z = affine.thru((0, z1), (1, z2))(step_traj)

            ztraj = z_trajs[card_idx]
            ztraj.events.append(t)
            ztraj.trajs.append(delay(pickup_z, t))

        t += PLACE_CARD_PERIOD

    seq = helper.next_seq


ts = frame_times(2 + t, FPS)

# Function to create a Cairo surface and return the image as an array
from PIL import ImageDraw, ImageFont
#font = ImageFont.truetype("sans-serif.ttf", 16)

def draw_frame(t):
    image = get_table()
    draw = ImageDraw.Draw(image)
    # font = ImageFont.truetype(<font-file>, <font-size>)

    zs = [z_traj(t) for z_traj in z_trajs]

    for z, card_idx, traj_fn in sorted(zip(zs, seq, trajs)):

        point = traj_fn(t)
        x, y = np.round(point).astype(int)
        pos = x, y

        image.paste(card_images[card_idx], pos)
        # draw.text((x - 50, y - 50), f"{z}", (0,) * 3)

    return image


plt.close("all")


# Initialize the Matplotlib figure
fig, ax = plt.subplots()
ax.set_xlim(0, WIDTH)
ax.set_ylim(0, HEIGHT)
ax.axis('off')  # Turn off axes

# create the image
frame_data = np.array(get_table())
frame_artist = ax.imshow(frame_data)


# Animation function
def update(frame_idx):
    image = draw_frame(ts[frame_idx])
    image_arr = np.array(image)
    frame_artist.set_data(image_arr[::-1, :, :])  # why is y-axis 0th dimension!?
    return frame_artist,


# Create the animation
interval_ms = 1000. / FPS
ani = FuncAnimation(fig, update, len(ts), blit=True, interval=interval_ms)

# Save the animation to a file
ani.save("pile-shuffle.mp4", writer="ffmpeg", fps=FPS)

# Show the animation (optional)
plt.show()

plt.close("all")
