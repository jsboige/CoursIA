"""Lecture bornée des sessions FieldTrip de PharmacoMEG 1/f.

Les tableaux complets MATLAB sont décompressés par scipy en mémoire : pour le
jeu public, prévoir au moins 1 Go. Une fenêtre copiée est seule conservée par
session. Les contrôles de métadonnées ne détectent ni artefacts ni traitements
antérieurs ; ils ne valident pas une interprétation physiologique.

Par exemple, après avoir nommé les fichiers comme dans la notice Dataverse :

    import antropy
    from ict.meg_fieldtrip import load_lsd_pair

    lsd, placebo = load_lsd_pair("LSD_LSD_010514_1.mat", "LSD_PLA_010514_1.mat",
                                 ("MLC11",), 0, 2400)
    hfd = antropy.higuchi_fd(lsd.values[0], kmax=18)
    lzc = antropy.lziv_complexity(lsd.values[0] > lsd.values[0].mean(),
                                   normalize=True)

Ces valeurs par fenêtre ne suffisent pas à établir un effet pharmacologique.

"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re

import numpy as np
from scipy.io import loadmat


@dataclass(frozen=True)
class SensorWindow:
    """Fenêtre de signaux en teslas, et provenance de son axe de capteurs."""

    labels: tuple[str, ...]
    sample_rate: float
    start: int
    all_labels: tuple[str, ...]
    total_samples: int
    time_origin: float
    values: np.ndarray


def _unique_labels(values: object, name: str) -> tuple[str, ...]:
    labels = tuple(np.asarray(values).reshape(-1).tolist())
    if not labels or any(not isinstance(x, str) or not x for x in labels):
        raise ValueError(f"Étiquettes {name} invalides")
    if len(set(labels)) != len(labels):
        raise ValueError(f"Étiquettes {name} dupliquées")
    return labels


def load_sensor_window(path: str | Path, labels: tuple[str, ...], start: int,
                       count: int) -> SensorWindow:
    """Lit jusqu'à 16 capteurs et 10 secondes, sans conserver le tableau entier.

    ``start`` et ``count`` sont exprimés en indices d'échantillons. Les canaux
    sont joints à l'en-tête par étiquette, jamais par position. Les métadonnées
    doivent annoncer uniquement des gradiomètres en T pour les canaux demandés ;
    cela ne démontre pas que leur calibration ou leur traitement soient corrects.
    """
    if not labels or len(labels) > 16 or len(set(labels)) != len(labels):
        raise ValueError("Choisir entre 1 et 16 étiquettes distinctes")
    if not isinstance(start, int) or not isinstance(count, int) or start < 0 or count <= 0:
        raise ValueError("Fenêtre invalide")
    try:
        data = loadmat(path, variable_names=['data'], struct_as_record=False,
                       squeeze_me=True)['data']
        trial = np.asarray(data.trial)
        trial_labels = _unique_labels(data.label, 'trial')
        hdr_labels = _unique_labels(data.hdr.label, 'hdr')
        types = np.asarray(data.hdr.chantype).reshape(-1)
        units = np.asarray(data.hdr.chanunit).reshape(-1)
        time = np.asarray(data.time)
        fs = float(data.fsample)
        header_fs = float(data.hdr.Fs)
    except (AttributeError, KeyError, TypeError) as exc:
        raise ValueError("Structure FieldTrip incomplète") from exc
    if trial.ndim != 2 or trial.shape[0] != len(trial_labels):
        raise ValueError("Dimensions du signal incompatibles avec ses étiquettes")
    if len(types) != len(hdr_labels) or len(units) != len(hdr_labels):
        raise ValueError("Métadonnées de canaux incompatibles avec hdr.label")
    if not np.isfinite(fs) or fs <= 0 or fs != header_fs:
        raise ValueError("Fréquences d'échantillonnage incompatibles")
    if count > 10 * fs or start + count > trial.shape[1]:
        raise ValueError("Fenêtre hors limites ou supérieure à 10 secondes")
    if (time.ndim != 1 or time.size != trial.shape[1] or
            not (np.issubdtype(time.dtype, np.integer) or
                 np.issubdtype(time.dtype, np.floating)) or
            not np.all(np.isfinite(time))):
        raise ValueError("Axe de temps invalide")
    if not np.allclose(np.diff(time), 1.0 / fs, rtol=1e-7, atol=1e-10):
        raise ValueError("Axe de temps incompatible avec la fréquence")
    hdr_index = {name: i for i, name in enumerate(hdr_labels)}
    trial_index = {name: i for i, name in enumerate(trial_labels)}
    if any(name not in hdr_index for name in trial_labels):
        raise ValueError("Étiquette trial absente de hdr")
    for name in labels:
        if name not in trial_index:
            raise ValueError(f"Capteur absent : {name}")
        index = hdr_index[name]
        if types[index] != 'meggrad' or units[index] != 'T':
            raise ValueError(f"Type ou unité non pris en charge : {name}")
    values = np.array(trial[[trial_index[name] for name in labels], start:start + count], copy=True)
    if (not (np.issubdtype(values.dtype, np.integer) or
             np.issubdtype(values.dtype, np.floating)) or
            not np.all(np.isfinite(values))):
        raise ValueError("Signal non numérique ou non fini")
    return SensorWindow(tuple(labels), fs, start, trial_labels, trial.shape[1],
                        float(time[0]), values)


def load_lsd_pair(lsd_path: str | Path, placebo_path: str | Path,
                  labels: tuple[str, ...], start: int, count: int
                  ) -> tuple[SensorWindow, SensorWindow]:
    """Charge une paire dont les noms suivent le manifeste public Dataverse.

    Les noms attestent la convention d'appariement du dépôt, pas l'identité
    clinique ni la condition expérimentale au-delà de ce manifeste.
    """
    pattern = r'LSD_(LSD|PLA)_(\d{6}_\d+)\.mat'
    lsd_match = re.fullmatch(pattern, Path(lsd_path).name)
    pla_match = re.fullmatch(pattern, Path(placebo_path).name)
    if (not lsd_match or not pla_match or lsd_match.group(1) != 'LSD'
            or pla_match.group(1) != 'PLA' or lsd_match.group(2) != pla_match.group(2)):
        raise ValueError("Noms de paire LSD/placebo incompatibles")
    lsd = load_sensor_window(lsd_path, labels, start, count)
    placebo = load_sensor_window(placebo_path, labels, start, count)
    if (set(lsd.all_labels) != set(placebo.all_labels) or lsd.sample_rate != placebo.sample_rate
            or lsd.total_samples != placebo.total_samples
            or lsd.time_origin != placebo.time_origin):
        raise ValueError("Axes de capteurs ou de temps incompatibles entre sessions")
    return lsd, placebo
