import pandas as pd
import pytest

def test_pandas_dataframe_selection():
    """
    Tests a basic column selection on a Pandas DataFrame.
    """
    # Arrange
    data = {'col1': [1, 2], 'col2': [3, 4]}
    df = pd.DataFrame(data)
    expected_series = pd.Series([3, 4], name='col2')

    # Act
    actual_series = df['col2']

    # Assert
    pd.testing.assert_series_equal(actual_series, expected_series)