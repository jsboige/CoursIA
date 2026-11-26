import numpy as np
import pytest

def test_numpy_array_sum():
    """
    Tests a basic sum operation on a NumPy array.
    """
    # Arrange
    array = np.array([1, 2, 3])
    expected_sum = 6

    # Act
    actual_sum = np.sum(array)

    # Assert
    assert actual_sum == expected_sum