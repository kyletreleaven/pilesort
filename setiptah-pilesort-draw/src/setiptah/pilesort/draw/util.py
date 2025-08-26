import numpy as np
from dataclasses import dataclass

from setiptah.pilesort.util import singleton


def frame_times(duration, fps):
    return np.arange(0, duration, 1. / fps)


@singleton
@dataclass(frozen=True)  # Just for the conveniences
class slicer:

    def __getitem__(self, item):
        return item


def mask_like(mask, arr, *, axis):
    """

    TODO: What's the idiomatic way to do this?

    """
    if np.isscalar(mask):
        return mask

    # otherwise
    n, = mask.shape  # it better be 1d
    assert arr.shape[axis] == n

    result = np.zeros_like(arr)
    builder = [slicer[:] for _ in result.shape]

    for k, value in enumerate(mask):
        builder[axis] = k
        result[tuple(builder)] = value

    return result
