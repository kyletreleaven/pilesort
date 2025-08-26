"""Creates an animation of a card waving back and forth."""
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
import numpy as np

from PIL import Image

from setiptah.pilesort.draw.cards import card_guide
from setiptah.pilesort.draw.util import frame_times

WIDTH, HEIGHT = 800, 600
FPS = 30


def get_table():
    return Image.new("RGBA", (WIDTH, HEIGHT), (255,) * 4)


def sin_between(a, b, period):

    rate = 2 * np.pi / period
    scale = .5 * (b - a)
    center = .5 * (a + b)

    def fn(t):
        return center + scale * np.sin(rate * t)

    return fn


card_array = card_guide.get_card(0)
card_image = Image.fromarray(
    (card_array * 255).astype("uint8"),
    mode="RGBA"
)
traj = sin_between(100, 450, 1)


ts = frame_times(10, FPS)


# Function to create a Cairo surface and return the image as an array
def draw_frame(t):
    image = get_table()

    card_x = round(traj(t))

    # import IPython; IPython.embed()

    image.paste(card_image, (card_x, 200))

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
    frame_artist.set_data(image_arr)
    return frame_artist,


# Create the animation
interval_ms = 1000. / FPS
ani = FuncAnimation(fig, update, len(ts), blit=True, interval=interval_ms)

# Save the animation to a file
# ani.save("card-wave.mp4", writer="ffmpeg", fps=FPS)

# Show the animation (optional)
plt.show()
