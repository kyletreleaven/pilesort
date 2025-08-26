from ursina import *
app = Ursina(
    title='Ursina',
    )
button_list = ButtonList(
    {
    'widow.position = Vec2(0,0)': Func(setattr, window, 'position', Vec2(0,0)),
    'widow.size = Vec2(512,512)': Func(setattr, window, 'size', Vec2(512,512)),
    'widow.center_on_screen()': window.center_on_screen,

    'widow.borderless = True': Func(setattr, window, 'borderless', True),
    'widow.borderless = False': Func(setattr, window, 'borderless', False),

    'widow.fullscreen = True': Func(setattr, window, 'fullscreen', True),
    'widow.fullscreen = False': Func(setattr, window, 'fullscreen', False),

    'widow.vsync = True': Func(setattr, window, 'vsync', True),
    'widow.vsync = False': Func(setattr, window, 'vsync', False),


    'application.base.win.request_properties(self)': Func(application.base.win.request_properties, window),

    }, y=0
)
startup_value = Text(y=.5,x=-.5)
startup_value.text = f'''
    position: {window.position}
    size: {window.size}
    aspect_ratio: {window.aspect_ratio}
    window.main_monitor.width: {window.main_monitor.width}
    window.main_monitor.height: {window.main_monitor.height}

'''

position_text = Text(y=.5,)


def input(key):
    if key == 'space':
        window.center_on_screen()




Entity(model='cube', color=color.green, collider='box', texture='shore')
app.run()

