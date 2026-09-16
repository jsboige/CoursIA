"""Endpoints multi-lentilles d'un MEME run (Epic #15475, #15479 acceptance 3).

L'acceptance 3 de #15479 : « Un meme run produit des endpoints SAE/J-Lens/F-Lens
et comportementaux **sans ecrasement de semantique** ».

Pourquoi une couche separee
---------------------------
:class:`ict.causal_engine.EffectChannels` porte les trois canaux
etat/readout/comportement d'UNE intervention, en dictionnaires plats :
``{nom}_before/_after/_delta``. Deux lentilles qui mesurent le meme run avec un
mesureur homonyme (deux « topk_overlap », un « recon_mse » SAE et un
« recon_mse » F-Lens) y ecraseraient leurs cles mutuellement — dernier
ecrivain gagnant, silencieusement. C'est exactement l'ecrasement de semantique
que l'acceptance interdit : le nombre survit, la provenance meurt.

Cette couche namespaced par lentille rend l'ecrasement IMPOSSIBLE plutot que
deconseille :

* **intra-lentille** : re-enregistrer un mesureur deja present pour le meme
  couple (lentille, canal) echoue avec un diagnostic qui nomme les trois
  coordonnees — un mesureur homonyme dans la MEME lentille est une erreur de
  l'appelant, pas une donnee ;
* **inter-lentilles** : le meme nom de mesureur dans deux lentilles differentes
  coexiste par construction — chaque lentille a son espace de noms propre ;
* **jamais d'agregation cross-lentilles** : cette classe n'expose VOLONTAIREMENT
  aucune methode qui somme ou moyenne a travers les lentilles. Comparer des
  endpoints SAE a des endpoints J-Lens est un jugement d'analyse (unites,
  echelles, semantiques distinctes) ; le moteur fournit la vue isolee par
  lentille (:meth:`MultiLensRun.channel_view`), la decision reste a l'appelant.

Contrat d'alignement
--------------------
Le bundle embarque l'alignement du run (sous-ensemble des ALIGNMENT_KEYS v1 de
``ict.causal_engine``, meme litteral, meme semantique sidecar) ; :func:`assert_run_alignment`
applique la regle du contrat : deux runs compares doivent partager CHACUNE des
cles presentes des deux cotes, un mismatch nomme le champ fautif. Le bundle
REFERE le run, il ne l'etend pas.

Coeur numpy-only, comme le reste du moteur : les mesureurs sont des callables
fournis par l'appelant (la lentille sait mesurer, le moteur sait enregistrer).
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Callable, Mapping

import numpy as np

from ict.causal_engine import ALIGNMENT_KEYS

__all__ = [
    "CHANNELS",
    "LensEndpoints",
    "MultiLensRun",
    "assert_run_alignment",
]

#: Les trois canaux d'effet, meme enum que EffectChannels (#15475 : jamais sommes).
CHANNELS: tuple[str, ...] = ("state", "readout", "behavior")


@dataclass
class LensEndpoints:
    """Endpoints d'UNE lentille sur un run, par canal, en slots separes."""

    lens: str
    state: dict[str, float] = field(default_factory=dict)
    readout: dict[str, float] = field(default_factory=dict)
    behavior: dict[str, float] = field(default_factory=dict)

    def record(
        self,
        channel: str,
        measurers: Mapping[str, Callable[[np.ndarray], float]],
        panel_before: np.ndarray,
        panel_after: np.ndarray,
    ) -> None:
        """Enregistre chaque mesureur sur le couple avant/apres.

        Meme forme de cles que :meth:`ict.causal_engine.EffectChannels.record`
        (``{nom}_before/_after/_delta``) : les deux couches de la famille
        doivent rester lisibles cote a cote. Un nom deja present dans CE canal
        de CETTE lentille echoue : l'ecrasement intra-lentille est une erreur,
        pas une donnee.
        """
        target = self._channel_dict(channel)
        clashes = sorted(set(measurers) & {
            name.rsplit("_", 1)[0]
            for name in target
            if name.endswith(("_before", "_after", "_delta"))
        })
        if clashes:
            raise ValueError(
                f"mesureur(s) {clashes} deja enregistre(s) pour la lentille "
                f"{self.lens!r} sur le canal {channel!r} — un re-enregistrement "
                f"ecraserait la semantique precedente (#15479 acceptance 3) ; "
                f"renomer le mesureur ou lire le bundle existant"
            )
        for name, fn in measurers.items():
            target[f"{name}_before"] = float(fn(panel_before))
            target[f"{name}_after"] = float(fn(panel_after))
            target[f"{name}_delta"] = (
                target[f"{name}_after"] - target[f"{name}_before"]
            )

    def _channel_dict(self, channel: str) -> dict[str, float]:
        if channel not in CHANNELS:
            raise ValueError(
                f"canal {channel!r} inconnu {CHANNELS} (etat/readout/comportement)"
            )
        return getattr(self, channel)

    def to_dict(self) -> dict[str, object]:
        return {
            "state": dict(self.state),
            "readout": dict(self.readout),
            "behavior": dict(self.behavior),
        }


class MultiLensRun:
    """Un meme run, N lentilles, des endpoints jamais ecrases.

    L'acceptance 3 de #15479 : un run, plusieurs familles d'endpoints (SAE,
    J-Lens, F-Lens, comportemental), chacune garde sa semantique. L'identite du
    run vit dans ``alignment`` (cles du contrat v1) ; chaque appel a
    :meth:`record` ajoute une famille sur un canal, sous l'espace de noms de sa
    lentille.
    """

    def __init__(self, alignment: Mapping[str, object]) -> None:
        self.alignment: dict[str, object] = dict(alignment)
        self._lenses: dict[str, LensEndpoints] = {}

    def lens(self, lens_id: str) -> LensEndpoints:
        """Endpoint bundle d'une lentille, cree au premier acces."""
        if lens_id not in self._lenses:
            self._lenses[lens_id] = LensEndpoints(lens=lens_id)
        return self._lenses[lens_id]

    def record(
        self,
        lens_id: str,
        channel: str,
        measurers: Mapping[str, Callable[[np.ndarray], float]],
        panel_before: np.ndarray,
        panel_after: np.ndarray,
    ) -> None:
        """Enregistre les mesureurs d'une lentille sur un canal du run.

        Les DEUX panneaux viennent du MEME run (avant/apres intervention) :
        c'est la garantie « un meme run » de l'acceptance — chaque lentille voit
        le meme couple, ses deltas sont donc mutuellement comparables dans le
        bundle.
        """
        self.lens(lens_id).record(channel, measurers, panel_before, panel_after)

    def lens_ids(self) -> tuple[str, ...]:
        """Lentilles enregistrees, ordre d'insertion (lisibilite des diffs)."""
        return tuple(self._lenses)

    def channel_view(self, channel: str) -> dict[str, dict[str, float]]:
        """Vue d'UN canal a travers toutes les lentilles (jamais agregee).

        Rend ``{lentille: {nom: valeur}}`` sur le canal demande — la structure
        qui rend l'ecrasement visible par construction : deux lentilles y
        apparaissent cote a cote, chacune avec ses cles propres.
        """
        if channel not in CHANNELS:
            raise ValueError(
                f"canal {channel!r} inconnu {CHANNELS} (etat/readout/comportement)"
            )
        return {
            lens_id: dict(getattr(endpoints, channel))
            for lens_id, endpoints in self._lenses.items()
            if getattr(endpoints, channel)
        }

    def to_dict(self) -> dict[str, object]:
        return {
            "alignment": dict(self.alignment),
            "lenses": {
                lens_id: endpoints.to_dict()
                for lens_id, endpoints in self._lenses.items()
            },
        }

    def to_json(self) -> str:
        return json.dumps(self.to_dict(), sort_keys=True, ensure_ascii=False)


def assert_run_alignment(run_a: MultiLensRun, run_b: MultiLensRun) -> None:
    """Echoue avec le champ fautif nomme si deux bundles ne s'alignent pas.

    Meme semantique que :func:`ict.causal_engine.assert_alignment` : toute cle
    d'ALIGNMENT_KEYS presente des deux cotes doit etre egale ; une cle absente
    d'un cote ne bloque pas (champs optionnels du contrat v1).
    """
    for key in ALIGNMENT_KEYS:
        a, b = run_a.alignment.get(key), run_b.alignment.get(key)
        if a is not None and b is not None and a != b:
            raise ValueError(
                f"desalignement {key!r}: {a!r} != {b!r} — les bundles "
                f"{sorted(run_a.lens_ids())} / {sorted(run_b.lens_ids())} "
                f"ne proviennent pas du meme run"
            )
