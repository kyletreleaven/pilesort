from typing import Callable, Tuple, List
from dataclasses import dataclass
from setiptah.pilesort.util import (
    singleton, place_of, intervals
)
from functools import cached_property
import numpy as np
from setiptah.pilesort.draw.util import mask_like


def support_scalar(fn):
    """

    TODO: Probably needs some tuning.

    """
    def fn_(self_, arr):
        if not isinstance(arr, np.ndarray):
            return fn(self_, np.array(arr)).item()
        return fn(self_, arr)

    fn_.wrapped = fn

    return fn_


@dataclass(frozen=True)
class piecewise:
    events: List[float]  # better be ordered!
    trajs: List[Callable]

    def __call__(self, ts):
        if len(self.events) == 0:
            traj, = self.trajs
            return traj(ts)

        # otherwise
        def masks():
            yield ts < self.events[0]
            yield from (
                between(ts, t1, t2)
                for t1, t2 in intervals(self.events)
            )
            yield ts > self.events[-1]

        def parts():
            for traj, mask in zip(self.trajs, masks()):
                source = traj(ts)
                yield mask_like(mask, source, axis=0) * source

        return sum(parts())


@dataclass(frozen=True)
class const:
    value: float

    @support_scalar
    def __call__(self, ts):
        return self.value * np.ones_like(ts)


@singleton
class step_traj:

    def __call__(self, ts):
        return 1. * (ts >= 0.)


@dataclass(frozen=True)
class scale_traj:
    traj_fn: Callable
    scale: float

    def __call__(self, ts):
        return self.traj_fn(ts / self.scale)


@dataclass(frozen=True)
class delay:
    traj_fn: Callable
    pause: float

    def __call__(self, ts):
        return self.traj_fn(ts - self.pause)



# we want to "ease" from one point to another, decelerating at some rate to get there;
@dataclass(frozen=True)
class deal_card:
    point_1: Tuple[float, float]
    point_2: Tuple[float, float]
    duration: float
    brake_after: float

    @cached_property
    def distance(self):
        x1, y1 = self.point_1
        x2, y2 = self.point_2

        return np.linalg.norm([x2 - x1, y2 - y1], 2).item()

    def __call__(self, ts):
        traj = ease_in(self.distance, self.duration, self.brake_after)

        toward = traj(np.array(ts)) / self.distance
        away = 1. - toward

        x1, y1 = self.point_1
        x2, y2 = self.point_2

        xs = toward * x2 + away * x1
        ys = toward * y2 + away * y1

        return np.stack([xs, ys], axis=-1)


@dataclass(frozen=True)
class ease_in:
    """

    Okay that was semi-useless...

    """
    distance: float
    duration: float
    brake_after: float

    @cached_property
    def _velocity(self):
        denom = .5 * (self.duration + self.brake_after)
        return self.distance / denom

    @cached_property
    def _decel(self):
        return self._velocity / (self.duration - self.brake_after)

    @support_scalar
    def __call__(self, ts):
        # import IPython; IPython.embed()

        result = np.zeros_like(ts)

        mask = between(ts, 0, self.duration)
        result += mask * self._velocity * ts

        mask = between(ts, self.brake_after, self.duration)
        result -= mask * .5 * self._decel * np.power(ts - self.brake_after, 2)

        mask = ts >= self.duration
        result += mask * self.distance

        return result


def between(ts, a, b):
    return (ts >= a) & (ts < b)


@dataclass(frozen=True)
class affine:
    traj_fn: Callable
    m: float
    b: float

    def __call__(self, ts):
        return self.m * self.traj_fn(ts) + self.b

    @classmethod
    def thru(cls, point_1, point_2):
        x1, y1 = point_1
        x2, y2 = point_2

        m = (y2 - y1) / (x2 - x1)
        b = y1 - m * x1

        def ctor(traj_fn: Callable):
            return cls(traj_fn, m, b)

        return ctor
