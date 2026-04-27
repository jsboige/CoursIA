#region imports
from AlgorithmImports import *

import tensorflow as tf
from tensorflow.keras.layers import (
    Input, Conv1D, Dense, Lambda, Flatten
)
from tensorflow.keras.layers import Concatenate as KerasConcatenate
from tensorflow.keras import Model
from tensorflow.keras.losses import CategoricalCrossentropy
from tensorflow.keras import utils
from tensorflow.keras.models import model_from_json
from tensorflow.keras.config import enable_unsafe_deserialization
from tensorflow.keras.saving import register_keras_serializable
from sklearn.preprocessing import StandardScaler
import math
from keras.utils import set_random_seed
# endregion

set_random_seed(0)
enable_unsafe_deserialization()

factor_names = ['open', 'high', 'low', 'close', 'volume']


class Direction:
    """Constants for price movement classification."""
    UP = 0
    DOWN = 1
    STATIONARY = 2


@register_keras_serializable()
def f0(x):
    return tf.split(x, num_or_size_splits=3, axis=1)[0]


@register_keras_serializable()
def f1(x):
    return tf.split(x, num_or_size_splits=3, axis=1)[1]


@register_keras_serializable()
def f2(x):
    return tf.split(x, num_or_size_splits=3, axis=1)[2]


class TemporalCNN:
    """
    Temporal Convolutional Neural Network for price direction prediction.

    Architecture:
    1. Conv1D feature extraction layer (30 filters, kernel size 4)
    2. Temporal split into 3 regions (short/mid/long term)
    3. Conv1D per temporal region
    4. Concatenate + Flatten + Dense(3) softmax output

    The model predicts 3 classes: UP, DOWN, STATIONARY based on
    the trailing OHLCV data.
    """

    def __init__(self, model_json=None, n_tsteps=15):
        self._n_tsteps = n_tsteps
        self._scaler = StandardScaler()

        if model_json:
            self._cnn = model_from_json(model_json)
        else:
            self._cnn = self._create_model()

        self._cnn.compile(
            optimizer='adam',
            loss=CategoricalCrossentropy(from_logits=True)
        )

    def _create_model(self):
        """Build the Temporal CNN architecture."""
        inputs = Input(shape=(self._n_tsteps, len(factor_names)))

        feature_extraction = Conv1D(30, 4, activation='relu')(inputs)

        long_term = Lambda(f0, output_shape=(4, 30))(feature_extraction)
        mid_term = Lambda(f1, output_shape=(4, 30))(feature_extraction)
        short_term = Lambda(f2, output_shape=(4, 30))(feature_extraction)

        long_term_conv = Conv1D(1, 1, activation='relu')(long_term)
        mid_term_conv = Conv1D(1, 1, activation='relu')(mid_term)
        short_term_conv = Conv1D(1, 1, activation='relu')(short_term)

        combined = KerasConcatenate(axis=1)(
            [long_term_conv, mid_term_conv, short_term_conv]
        )

        flattened = Flatten()(combined)
        outputs = Dense(3, activation='softmax')(flattened)

        return Model(inputs=inputs, outputs=outputs)

    def _prepare_data(
        self, data, rolling_avg_window_size=5,
        stationary_threshold=0.0001
    ):
        """Transform raw OHLCV data into model inputs and labels."""
        df = data[factor_names].copy()
        shift = -(rolling_avg_window_size - 1)

        def label_data(row):
            if row['close_avg_change_pct'] > stationary_threshold:
                return Direction.UP
            elif row['close_avg_change_pct'] < -stationary_threshold:
                return Direction.DOWN
            else:
                return Direction.STATIONARY

        df['close_avg'] = df['close'].rolling(
            window=rolling_avg_window_size
        ).mean().shift(shift)
        df['close_avg_change_pct'] = (
            (df['close_avg'] - df['close']) / df['close']
        )
        df['movement_labels'] = df.apply(label_data, axis=1)

        data_list = []
        labels = []
        for i in range(len(df) - self._n_tsteps + 1 + shift):
            label = df['movement_labels'].iloc[i + self._n_tsteps - 1]
            data_list.append(
                df[factor_names].iloc[i:i + self._n_tsteps].values
            )
            labels.append(label)

        data_arr = np.array(data_list)
        dim1, dim2, dim3 = data_arr.shape
        data_arr = data_arr.reshape(dim1 * dim2, dim3)
        data_arr = self._scaler.fit_transform(data_arr)
        data_arr = data_arr.reshape(dim1, dim2, dim3)

        return data_arr, utils.to_categorical(labels, num_classes=3)

    def train(self, data):
        """Train the model on OHLCV data. Returns serialized model JSON."""
        data_arr, labels = self._prepare_data(data)
        self._cnn.fit(data_arr, labels, epochs=20, verbose=0)
        return self._cnn.to_json()

    def predict(self, input_data):
        """Predict price direction from trailing OHLCV data."""
        input_data = self._scaler.transform(
            input_data.fillna(method='ffill').values
        )
        prediction = self._cnn.predict(
            input_data[np.newaxis, :], verbose=0
        )[0]
        direction = int(np.argmax(prediction))
        confidence = float(prediction[direction])
        return direction, confidence
