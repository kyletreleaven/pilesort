from ursina import *
from panda3d.core import (
    FrameBufferProperties, WindowProperties, GraphicsPipe,
    GraphicsOutput, Texture, PNMImage
)
import numpy as np

from contextlib import contextmanager
from multiprocessing import Process





def run_ursina_instance():
    from ursina import *
    window.visible = False
    app = Ursina()
    Entity(model='cube', color=color.random_color())
    app.step()
    window.screenshot(name='out.png')
    app.shutdown()

# Launch multiple processes
p1 = Process(target=run_ursina_instance)
p2 = Process(target=run_ursina_instance)

p1.start()
p2.start()
p1.join()
p2.join()



@contextlib.contextmanager








app = Ursina()
window.visible = False  # Don't show the window

# Set up offscreen buffer
fb_props = FrameBufferProperties()
fb_props.set_rgb_color(True)
fb_props.set_alpha_bits(1)
fb_props.set_depth_bits(1)

win_props = WindowProperties.size(512, 512)
buffer = base.graphicsEngine.make_output(
    base.pipe, "Offscreen Buffer", -2,
    fb_props, win_props,
    GraphicsPipe.BF_refuse_window,
    base.win.get_gsg(), base.win
)

# Render target texture
tex = Texture()
buffer.add_render_texture(tex, GraphicsOutput.RTM_copy_ram)
tex.set_format(Texture.F_rgb8)  # Ensure RGB format

# Set up a camera
cam = base.makeCamera(win=buffer)
cam.reparent_to(scene)

# Add something to draw
Entity(model='cube', color=color.orange)

# Render one frame
app.step()

# Force the texture to sync
base.graphicsEngine.render_frame()
base.graphicsEngine.render_frame()  # two frames to ensure full render

# Get raw image data
image = PNMImage()
tex.store(image)

# Convert to numpy array
arr = np.array(image.get_pixels())  # (rows, cols, 3), float RGB in [0, 1]
arr = (arr * 255).astype(np.uint8)  # optional: convert to 8-bit
arr = arr[::-1]  # Flip vertically (Y-axis)

print("Array shape:", arr.shape)  # Should be (512, 512, 3)

app.shutdown()