from setiptah.pilesort import util
from setiptah.pilesort.util import singleton


def test_backnumerate():
    coll = range(3)

    expected = list(enumerate(coll))
    expected.reverse()

    assert list(util.backnumerate(range(3))) == expected


def test_singleton():

    @singleton
    class thing:

        @property
        def x(self):
            return 42

    assert thing.x == 42
