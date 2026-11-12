"""Contrats du lecteur FieldTrip sur des fixtures à en-tête désordonné."""
from pathlib import Path

import numpy as np
import pytest
from scipy.io import savemat

from ict.meg_fieldtrip import load_lsd_pair, load_sensor_window


def write_session(path: Path, *, labels=('A', 'B'), hdr_labels=('B', 'X', 'A'),
                  types=('meggrad', 'eeg', 'meggrad'), units=('T', 'V', 'T'),
                  fs=4, header_fs=4, times=None) -> None:
    if times is None:
        times = np.arange(8) / fs
    savemat(path, {'data': {
        'label': np.array(labels, dtype=object),
        'trial': np.array([[1., 2., 3., 4., 5., 6., 7., 8.],
                           [11., 12., 13., 14., 15., 16., 17., 18.]]),
        'time': times, 'fsample': fs,
        'hdr': {'label': np.array(hdr_labels, dtype=object),
                'chantype': np.array(types, dtype=object),
                'chanunit': np.array(units, dtype=object), 'Fs': header_fs},
    }})


def test_header_is_joined_by_label_and_window_copied(tmp_path: Path) -> None:
    path = tmp_path / 'session.mat'
    write_session(path)
    result = load_sensor_window(path, ('B', 'A'), 2, 3)
    np.testing.assert_array_equal(result.values, [[13, 14, 15], [3, 4, 5]])
    assert result.values.flags.owndata
    assert result.sample_rate == 4


@pytest.mark.parametrize('overrides', [
    {'labels': ('A', 'A')},
    {'hdr_labels': ('B', 'B', 'A')},
    {'hdr_labels': ('B', 'X', 'C')},
    {'types': ('meggrad', 'eeg', 'eeg')},
    {'units': ('T', 'V', 'V')},
    {'header_fs': 5},
    {'times': np.arange(8) / 5},
    {'times': np.arange(8).reshape(2, 4) / 4},
    {'times': np.arange(8) / 4 + 1j},
])
def test_rejects_ambiguous_or_incompatible_metadata(tmp_path: Path, overrides: dict) -> None:
    path = tmp_path / 'session.mat'
    write_session(path, **overrides)
    with pytest.raises(ValueError):
        load_sensor_window(path, ('A', 'B'), 0, 4)


def test_pair_requires_identity_and_matching_full_axes(tmp_path: Path) -> None:
    lsd = tmp_path / 'LSD_LSD_010514_1.mat'
    placebo = tmp_path / 'LSD_PLA_010514_1.mat'
    wrong = tmp_path / 'LSD_PLA_010514_2.mat'
    write_session(lsd)
    write_session(placebo)
    left, right = load_lsd_pair(lsd, placebo, ('A',), 0, 4)
    np.testing.assert_array_equal(left.values, right.values)
    with pytest.raises(ValueError, match='Noms de paire'):
        load_lsd_pair(lsd, wrong, ('A',), 0, 4)
    write_session(placebo, labels=('B', 'A'))
    load_lsd_pair(lsd, placebo, ('A',), 0, 4)  # La sélection suit les noms.
    write_session(placebo, labels=('A', 'C'), hdr_labels=('C', 'X', 'A'))
    with pytest.raises(ValueError, match='Axes de capteurs'):
        load_lsd_pair(lsd, placebo, ('A',), 0, 4)


def test_window_bounds_reject_invalid_data(tmp_path: Path) -> None:
    path = tmp_path / 'session.mat'
    write_session(path)
    for start, count in ((-1, 2), (7, 2), (0, 0), (0, 41)):
        with pytest.raises(ValueError):
            load_sensor_window(path, ('A',), start, count)


def test_rejects_non_real_or_non_finite_values(tmp_path: Path) -> None:
    from scipy.io import loadmat

    path = tmp_path / 'session.mat'
    write_session(path)
    for bad in (np.complex128(1 + 2j), np.nan):
        data = loadmat(path, simplify_cells=True)['data']
        data['trial'] = data['trial'].astype(complex if np.iscomplexobj(bad) else float)
        data['trial'][0, 0] = bad
        savemat(path, {'data': data})
        with pytest.raises(ValueError, match='non numérique ou non fini'):
            load_sensor_window(path, ('A',), 0, 4)
        write_session(path)
