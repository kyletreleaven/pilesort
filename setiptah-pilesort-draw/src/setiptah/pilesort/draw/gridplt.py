from dataclasses import dataclass
from functools import cached_property
from numbers import Number
from typing import Tuple

import numpy as np

XYCoord = Tuple[Number, Number]


def place_of(x):
    yield x


@dataclass(frozen=True)
class Grid:
    """

    There's no reason not to treat a Grid as the GridCell at (0, 0).
    To get a different cell, we just shift the origin around, right?
    We only lose ancestry, but do we need it?

    """
    origin: XYCoord
    dims: XYCoord

    @classmethod
    def from_corners(cls, origin, tr):
        x1, y1 = origin
        x2, y2 = tr
        return cls(origin, (x2 - x1, y2 - y1))

    @property
    def upright(self):
        origin = min(self.left, self.right), min(self.bottom, self.top)

    def cell(self, ix: int, iy: int) -> "Grid":
        x0, y0 = self.origin
        dx, dy = self.dims
        xy = x0 + ix * dx, y0 + iy * dy
        return Grid(xy, self.dims)

    def cover(self, wx: int, wy: int) -> "Grid":
        return Grid.from_corners(
            self.origin,
            self.cell(wx, wy).origin
        )

    def to_abs(self, *xy: XYCoord):
        """

        >>> Grid((0, 0), (2, 3)).cell(1, 0).to_abs(.5, 1) == (3, 3)
        True

        """
        x0, y0 = self.origin
        dx, dy = self.dims
        x, y = xy
        return x0 + dx * x, y0 + dy * y

    def to_rel(self, *xy: XYCoord):
        """

        >>> Grid((0, 0), (2, 3)).cell(1, 0).to_rel(3, 3) == (.5, 1)
        True

        """
        x0, y0 = self.origin
        dx, dy = self.dims
        x, y = xy
        return (x - x0) / dx, (y - y0) / dy

    @property
    def bl(self):
        return self.to_abs(0, 0)

    @property
    def tr(self):
        return self.to_abs(1, 1)

    @property
    def center(self):
        return self.to_abs(.5, .5)

    @property
    def top(self):
        _, y = self.tr
        return y

    @property
    def bottom(self):
        _, y = self.bl
        return y

    @property
    def midy(self):
        xc, yc = self.center
        return yc

    @property
    def left(self):
        x, _ = self.bl
        return x

    @property
    def right(self):
        x, _ = self.tr
        return x

    @property
    def midx(self):
        xc, yc = self.center
        return xc

    @property
    def br(self):
        return self.right, self.bottom

    @property
    def tl(self):
        return self.left, self.top


@dataclass(frozen=True)
class Circular:
    n: int
    origin: XYCoord
    radius: Number
    theta0: Number = 0.

    @property
    def dtheta(self) -> Number:
        return np.pi * 2 / self.n

    def theta(self, k) -> Number:
        return self.theta0 + k * self.dtheta

    def mark(self, k) -> XYCoord:
        x0, y0 = self.origin
        t = self.theta(k)
        x_, y_ = np.cos(t), np.sin(t)
        return x0 + self.radius * x_, y0 + self.radius * y_


@dataclass(frozen=True)
class nQueen:
    """

    https://dl.acm.org/doi/10.1145/122319.122322
    """
    grid: Grid
    n: int

    def __post_init__(self):
        assert self.n >= 4

    @cached_property
    def subgrid(self):
        dx, dy = self.grid.dims
        dims_ = dx / self.n, dy / self.n
        return Grid(self.grid.origin, dims_)

    def queen(self, j):
        i, j = queen_cell(j, self.n)
        return self.subgrid.cell(i - 1, j - 1)


def queen_cell(j: int, n: int):
    assert n >= 4
    assert 1 <= j <= n

    # C
    if is_odd(n):
        if j == n:
            return n, n
        else:
            return queen_cell(j, n - 1)

    _, r = divmod(n, 6)
    half_n = n / 2
    j_ = j if j <= half_n else (j - half_n)

    # A
    if r != 2:
        if j <= half_n:
            return j_, 2 * j_
        else:
            return half_n + j_, 2 * j_ - 1

    # B
    if r != 0:
        arg = (2 * (j_ - 1) + half_n - 1) % n
        if j <= half_n:
            return j_, 1 + arg
        else:
            return n + 1 - j_, n - arg

    assert False


def is_odd(n):
    return n % 2 == 1
