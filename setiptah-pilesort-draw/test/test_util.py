from setiptah.pilesort.draw.util import mask_like
import numpy as np


def test_mask_like():

    mask = np.random.rand(4) < .5

    model = np.zeros((3, 4, 5))

    mask_ = mask_like(mask, model, axis=1)

    assert all(
        np.all(mask_[:, k, :] == mask[k])
        for k in range(4)
    )
