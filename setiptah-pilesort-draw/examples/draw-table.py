from ursina import *
from ursina import (
    Ursina,
    Entity,
    Text, time,
    color,
)


app = Ursina()

cube = Entity(model="cube", color=color.rgb(0, 255, 0))
txt = Text(text="Some stuff", color=color.rgb(255, 0, 255), scale=2)

def update():
    cube.rotation_y += time.dt * 100

app.run()
