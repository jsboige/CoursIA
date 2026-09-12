"""Moteur commun d'interventions causales sur les etats internes (Epic #15475, #15479).

La causalite est une **couche transversale**, pas un cinquieme instrument : les lentilles
(SAE, J-Lens, F-Lens, S-Lens) proposent des cibles et des endpoints ; ce module execute
l'intervention, conserve sa provenance et mesure **separement** les effets d'etat, de
readout et comportementaux (EPIC #15475 : « toujours separer effet sur l'etat, effet sur
le readout et effet comportemental »).

Coeur **numpy-only** (l'EPIC confine torch/transformers a ``scripts/``) : ce module decrit,
apparie et agrege des interventions sur des *panneaux d'activation* ``ndarray`` deja
extraits. Il ne sait pas capturer un modele — il sait transformer un panneau selon un
contrat commun, generer les controles apparies obligatoires, et rendre un enregistrement
rejouable.

Taxonomie v1 des cinq operations
--------------------------------
Soit un panneau ``x`` de forme ``(T, d)`` (positions x dimensions du residual stream) et
une cible = ensemble de coordonnees ``(positions, features)`` :

* ``ablate``      : mise a zero des coordonnees cibles (retrait pur).
* ``clamp``       : ecriture absolue ``x'[i, j] = dose * direction[j]`` (le clamp SAE du
  Gate 24 de #5635 : candidates workspace vs features aleatoires vs intact).
* ``steer``       : ecriture additive ``x'[i, j] += dose * direction[j]`` sur direction
  unitaire (dose symetrique +-lambda).
* ``patch``       : ecriture d'un **vecteur donneur** ``x'[i, j] = donor[i, j]`` (valeurs
  en donnee, provenant par ex. d'un autre prompt au meme alignement).
* ``interchange`` : echange **bilateral** des coordonnees cibles entre deux panneaux
  apparies ``a``/``b`` (le contre-factuel apparie) — ``a'`` recoit les valeurs de ``b``
  et reciproquement.

``clamp`` et ``patch`` sont deux ecritures absolues distinctes : le clamp ecrit une valeur
*parametrique* (dose x direction, choisie par l'experimentateur), le patch ecrit des
valeurs *empiriques* (le donneur est un artefact reference, pas un parametre).

Controles obligatoires (#15479)
-------------------------------
Chaque intervention cible est reliee a sa famille de controles :

* **cible aleatoire appariée** en norme et en frequence (:func:`random_target_matched`)
  — l'appariement se fait par quantile de norme d'activation + bande de tolerance, avec
  rejet explicite si aucune candidate ne respecte la bande (jamais de degradation
  silencieuse de l'appariement) ;
* **sham** (:func:`sham_of`) — la meme operation, la meme voie de code, dose nulle : un
  artefact de pipeline produirait un effet sham non nul ;
* **doses symetriques** (:func:`symmetric_doses`) et courbe dose-reponse ;
* **contre-factuels apparies** — l'operation ``interchange`` est bilateral par
  construction ; les autres operations referencent leur panneau donneur/apparie via le
  champ ``paired_run`` de la spec ;
* **plusieurs seeds** — le champ ``seed`` de la spec ; l'appariement aleatoire en depend ;
* **correction des comparaisons multiples** : Holm-Bonferroni sur la famille de
  comparaisons {cible vs aleatoire, cible vs sham} (:func:`holm_adjust`) ;
* **controle de dommage general** (:func:`damage_metrics`) : la norme relative du
  deplacement des coordonnees NON cibles — un collapse global ne peut pas se faire passer
  pour de la causalite selective (acceptance #15479) ;
* **separation etat / readout / comportement** : :class:`EffectChannels` porte les trois
  canaux en slots separes, jamais sommes — l'aggregation est du ressort de l'appelant.

API independante de la methode de selection de cible
----------------------------------------------------
La spec prend la cible **en donnee** (indices + vecteurs). Qui la choisit (SAE, F-Lens,
oracle synthetique, echantillonnage aleatoire) ne regarde pas ce module : le moteur
transforme, il ne selectionne pas.

Conformite au contrat de trace
------------------------------
Le contrat v1 vit dans ``ict.trace_contract`` (PR #15525, en vol au moment de l'ecriture).
Ce module embarque les ``ALIGNMENT_KEYS`` v1 en **litteral propre** et valide la
_compatibilite d'alignement_ de deux enregistrements par :func:`assert_alignment` ; au
merge de #15525, l'import garde (:func:`trace_contract_module`) deleguera la validation au
contrat canonique sans changer l'API d'ici. Les enregistrements d'intervention sont une
**couche sidecar** : ils REFERENT un manifeste de trace (cles d'alignement embarquees),
ils ne l'etendent pas — pas de bump de version du contrat pour le moteur.
"""

from __future__ import annotations

from dataclasses import dataclass, field, asdict
from typing import Callable, Mapping, Sequence

import hashlib
import json
import numpy as np

__all__ = [
    "OPERATIONS",
    "ALIGNMENT_KEYS",
    "InterventionSpec",
    "InterventionRecord",
    "EffectChannels",
    "apply_intervention",
    "interchange_panels",
    "random_target_matched",
    "sham_of",
    "symmetric_doses",
    "dose_response_specs",
    "damage_metrics",
    "selectivity_verdict",
    "holm_adjust",
    "build_gate24_family",
    "assert_alignment",
    "artifact_sha256",
]

#: Les cinq operations v1 de l'issue #15479, en enum fermee : une operation hors
#: liste est une erreur de contrat, pas une extension silencieuse.
OPERATIONS: tuple[str, ...] = (
    "ablate",
    "clamp",
    "steer",
    "patch",
    "interchange",
)

#: Cles d'alignement v1 du contrat de trace (copie du litteral de ``trace_contract``,
#: PR #15525). Deux enregistrements compares doivent partager CHACUNE de ces cles.
ALIGNMENT_KEYS: tuple[str, ...] = (
    "contract_version",
    "instrument",
    "d_sae",
    "k",
    "layer",
    "model",
    "model_revision",
    "model_family",
    "dtype",
    "run",
    "seed",
    "prompt_set",
)


# --------------------------------------------------------------------------- #
# Specs : la description declarative d'une intervention
# --------------------------------------------------------------------------- #

@dataclass(frozen=True)
class InterventionSpec:
    """Description declarative et rejouable d'une intervention unique.

    Champs (verbatim de l'acceptance #15479 « chaque intervention porte ») :
    instrument source, cible, couche/position, espace tensoriel, dose, direction,
    controle apparie, seed. Les artefacts avant/apres vivent dans
    :class:`InterventionRecord` (produits par l'application, pas declares).
    """

    operation: str                       # dans OPERATIONS
    instrument: str                      # "sae" | "jlens" | "flens" | "slens" | "synthetic"
    layer: int
    positions: tuple[int, ...]           # indices dans [0, T)
    features: tuple[int, ...]            # indices dans [0, d)
    dose: float = 0.0                    # scalaire (steer/clamp) ; 0 pour ablate/patch
    direction: tuple[float, ...] | None = None   # vecteur de dim len(features) ou None
    donor: tuple[tuple[float, ...], ...] | None = None  # patch : lignes positions x features
    tensor_space: str = "residual"       # residual | sae_latent | jlens_topk | ...
    run: str = ""                        # identifiant de run source du panneau
    paired_run: str = ""                 # run du contre-factuel apparie (interchange/patch)
    control_ref: str = ""                # lien vers la spec de controle appariee
    seed: int = 0

    def __post_init__(self) -> None:
        if self.operation not in OPERATIONS:
            raise ValueError(
                f"operation {self.operation!r} hors contrat v1 {OPERATIONS}"
            )
        if self.operation in ("clamp", "steer") and self.features:
            # cible vide (bras intact du Gate 24) : la direction est documentaire
            if self.direction is None:
                raise ValueError(f"{self.operation} exige une direction")
            if len(self.direction) != len(self.features):
                raise ValueError(
                    f"direction de dim {len(self.direction)} != "
                    f"{len(self.features)} features cibles"
                )
            if self.operation == "steer":
                norm = float(np.linalg.norm(np.asarray(self.direction)))
                if norm <= 0:
                    raise ValueError("steer exige une direction non nulle")
        if self.operation == "patch" and self.donor is None:
            raise ValueError("patch exige un donneur (valeurs empiriques)")
        if self.operation == "interchange" and not self.paired_run:
            raise ValueError("interchange exige paired_run (contre-factuel apparie)")

    def alignment(self, **extra: str) -> dict[str, object]:
        """Sous-dictionnaire d'alignement embarque dans l'enregistrement sidecar."""
        base: dict[str, object] = {
            "contract_version": "v1.0.0",
            "instrument": self.instrument,
            "layer": self.layer,
            "run": self.run,
            "seed": self.seed,
        }
        base.update(extra)
        return base


# --------------------------------------------------------------------------- #
# Application : transformation numpy pure d'un panneau
# --------------------------------------------------------------------------- #

def _check_panel(x: np.ndarray, spec: InterventionSpec) -> None:
    if x.ndim != 2:
        raise ValueError(f"panneau attendu (T, d), recu {x.shape}")
    T, d = x.shape
    if spec.positions and max(spec.positions) >= T:
        raise ValueError(f"position {max(spec.positions)} hors panneau T={T}")
    if spec.features and max(spec.features) >= d:
        raise ValueError(f"feature {max(spec.features)} hors panneau d={d}")


def apply_intervention(panel: np.ndarray, spec: InterventionSpec) -> np.ndarray:
    """Applique ``spec`` a ``panel`` et retourne un NOUVEAU panneau.

    Toutes les operations passent par la meme voie : construction de l'index
    cible, ecriture selon la semantique de l'operation. Le panneau d'entree
    n'est jamais mute (rejouabilite : avant/apres conservables).
    """
    _check_panel(panel, spec)
    out = panel.copy()
    pos = list(spec.positions)
    feats = list(spec.features)
    if not pos or not feats:
        return out  # cible vide = identite (utile pour le bras "intact" du Gate 24)

    ix = np.ix_(pos, feats)
    if spec.operation == "ablate":
        out[ix] = 0.0
    elif spec.operation == "clamp":
        value = spec.dose * np.asarray(spec.direction, dtype=panel.dtype)
        out[ix] = value[None, :]
    elif spec.operation == "steer":
        direction = np.asarray(spec.direction, dtype=panel.dtype)
        direction = direction / np.linalg.norm(direction)
        out[ix] += spec.dose * direction[None, :]
    elif spec.operation == "patch":
        donor = np.asarray(spec.donor, dtype=panel.dtype)
        if donor.shape != (len(pos), len(feats)):
            raise ValueError(
                f"donneur {donor.shape} != cible ({len(pos)}, {len(feats)})"
            )
        out[ix] = donor
    else:  # interchange : unilateral sur UN panneau ; la paire via interchange_panels
        raise ValueError(
            "interchange est bilateral : utiliser interchange_panels(a, b, spec)"
        )
    return out


def interchange_panels(
    panel_a: np.ndarray, panel_b: np.ndarray, spec: InterventionSpec
) -> tuple[np.ndarray, np.ndarray]:
    """Echange bilateral des coordonnees cibles entre deux panneaux apparies.

    Le contre-factuel apparie de #15479 : ``a'`` recoit les valeurs de ``b`` sur
    la cible et reciproquement, les coordonnees hors cible restant intactes des
    deux cotes. Les deux panneaux doivent partager la forme (l'alignement fin
    run/prompt/token releve du champ ``paired_run`` + des ALIGNMENT_KEYS).
    """
    if panel_a.shape != panel_b.shape:
        raise ValueError(
            f"interchange exige des panneaux de meme forme, {panel_a.shape} != {panel_b.shape}"
        )
    _check_panel(panel_a, spec)
    a_out, b_out = panel_a.copy(), panel_b.copy()
    ix = np.ix_(list(spec.positions), list(spec.features))
    a_vals, b_vals = panel_a[ix].copy(), panel_b[ix].copy()
    a_out[ix], b_out[ix] = b_vals, a_vals
    return a_out, b_out


# --------------------------------------------------------------------------- #
# Controles apparies
# --------------------------------------------------------------------------- #

def random_target_matched(
    panel: np.ndarray,
    spec: InterventionSpec,
    *,
    feature_norms: np.ndarray | None = None,
    feature_freqs: np.ndarray | None = None,
    rel_tol: float = 0.25,
    rng: np.random.Generator | None = None,
) -> InterventionSpec:
    """Controle a cible aleatoire appariée en norme et frequence (#15479).

    Pour chaque feature cible, on tire une feature candidate dont la norme
    d'activation et la frequence tombent dans une bande relative ``rel_tol`` de
    la cible ; s'il n'existe AUCUNE candidate dans la bande, on echoue avec un
    diagnostic nomme — un appariement degrade silencieusement vaut zero comme
    controle (le random-control doit etre *difficile a distinguer a priori* de
    la cible, sinon il strawman lui-meme).

    ``feature_norms`` / ``feature_freqs`` : vecteurs (d,) mesurs sur le corpus
    (norme L2 du panneau par feature ; frequence d'activation). Fournis par la
    lentille ; a defaut, la norme se calcule depuis le panneau et la frequence
    est supposee uniforme (documente dans le diagnostic).
    """
    if rng is None:
        rng = np.random.default_rng(spec.seed)
    d = panel.shape[1]
    if feature_norms is None:
        feature_norms = np.linalg.norm(panel, axis=0)
    if feature_freqs is None:
        feature_freqs = np.full(d, 1.0 / d)
    targets = np.asarray(spec.features, dtype=int)
    excluded = set(int(t) for t in targets)
    chosen: list[int] = []
    diag: list[str] = []
    for t in targets:
        lo_n, hi_n = feature_norms[t] * (1 - rel_tol), feature_norms[t] * (1 + rel_tol)
        lo_f, hi_f = max(0.0, feature_freqs[t] * (1 - rel_tol)), feature_freqs[t] * (1 + rel_tol)
        candidates = [
            j
            for j in range(d)
            if j not in excluded
            and lo_n <= feature_norms[j] <= hi_n
            and lo_f <= feature_freqs[j] <= hi_f
        ]
        if not candidates:
            raise ValueError(
                f"aucune candidate appariée a la feature {t} "
                f"(norme cible {feature_norms[t]:.4g}, bande +-{rel_tol:.0%}) : "
                f"elargir rel_tol ou fournir des normes/frequences de corpus"
            )
        pick = int(candidates[rng.integers(len(candidates))])
        chosen.append(pick)
        excluded.add(pick)
        diag.append(f"{t}->{pick}")
    return InterventionSpec(
        operation=spec.operation,
        instrument=spec.instrument,
        layer=spec.layer,
        positions=spec.positions,
        features=tuple(chosen),
        dose=spec.dose,
        direction=spec.direction,
        donor=spec.donor,
        tensor_space=spec.tensor_space,
        run=spec.run,
        paired_run=spec.paired_run,
        control_ref="",
        seed=spec.seed,
    )


def sham_of(spec: InterventionSpec, panel: np.ndarray | None = None) -> InterventionSpec:
    """Controle sham : meme operation, meme voie de code, effet nul prouve.

    La definition operationnelle : le pipeline d'application tourne INTEGRALEMENT
    (meme operation, meme index cible, meme ecriture) et le resultat doit etre
    l'identite — un artefact de pipeline (index corrompu, mute du panneau
    source, normalisation cachee) produirait un effet sham non nul.

    * ``steer`` : dose 0 (ecriture additive nulle par la meme voie).
    * ``clamp`` : reecriture des VALEURS ORIGINALES de la tranche cible, via
      la voie d'ecriture absolue PARTAGEE clamp/patch (``out[ix] = ...`` dans
      :func:`apply_intervention`) avec la tranche en donneur — clamp n'a pas
      d'identite a dose 0 par construction (dose 0 = ablation), donc son sham
      est le write-back empirique, taggue ``sham-of-clamp`` ; exige ``panel``.
    * ``patch`` : donneur = tranche du panneau lui-meme ; exige ``panel``.
    * ``ablate`` : cible vide (l'ablation n'a pas de forme nulle qui passe par
      sa voie d'ecriture — son sham EST le bras intact du Gate 24, documente).
    * ``interchange`` : echange du panneau avec lui-meme (``paired_run = run``).
    """
    if spec.operation == "clamp":
        if panel is None:
            raise ValueError("sham de clamp exige le panneau (reecriture des valeurs propres)")
        original = np.asarray(panel)[np.ix_(list(spec.positions), list(spec.features))]
        donor = tuple(tuple(float(v) for v in row) for row in original)
        return _copy_spec(
            spec, operation="patch", donor=donor, dose=0.0,
            control_ref="sham-of-clamp(write-back)",
        )
    if spec.operation == "patch":
        if panel is None:
            raise ValueError("sham de patch exige le panneau (donneur = soi-meme)")
        original = np.asarray(panel)[np.ix_(list(spec.positions), list(spec.features))]
        donor = tuple(tuple(float(v) for v in row) for row in original)
        return _copy_spec(spec, donor=donor, control_ref="sham")
    if spec.operation == "steer":
        return _copy_spec(spec, dose=0.0, control_ref="sham")
    if spec.operation == "ablate":
        return _copy_spec(spec, positions=(), features=(), control_ref="sham-intact")
    return _copy_spec(spec, paired_run=spec.run, control_ref="sham-self")


def _copy_spec(spec: InterventionSpec, **overrides: object) -> InterventionSpec:
    """Copie une spec en remplaçant les champs nommes (les autres invariants)."""
    fields = {
        "operation": spec.operation,
        "instrument": spec.instrument,
        "layer": spec.layer,
        "positions": spec.positions,
        "features": spec.features,
        "dose": spec.dose,
        "direction": spec.direction,
        "donor": spec.donor,
        "tensor_space": spec.tensor_space,
        "run": spec.run,
        "paired_run": spec.paired_run,
        "control_ref": spec.control_ref,
        "seed": spec.seed,
    }
    fields.update(overrides)
    return InterventionSpec(**fields)  # type: ignore[arg-type]


def symmetric_doses(base_dose: float, n_pairs: int) -> tuple[float, ...]:
    """Echelle de doses symetriques +-lambda pour la courbe dose-reponse.

    ``n_pairs`` paires geometriques entre ``base_dose / 2**(n_pairs-1)`` et
    ``base_dose`` : la reponse doit etre symetrique en signe pour une
    intervention selective (un effet qui ne s'inverse pas avec la dose signalee
    un artefact de seuil, pas une pente causale).
    """
    if base_dose <= 0:
        raise ValueError("base_dose doit etre > 0")
    doses: list[float] = []
    for i in range(n_pairs, 0, -1):
        lam = base_dose / (2 ** (i - 1))
        doses.extend((lam, -lam))
    return tuple(doses)


def dose_response_specs(spec: InterventionSpec, doses: Sequence[float]) -> list[InterventionSpec]:
    """Famille de specs identiques sauf la dose (courbe dose-reponse)."""
    return [
        InterventionSpec(
            operation=spec.operation,
            instrument=spec.instrument,
            layer=spec.layer,
            positions=spec.positions,
            features=spec.features,
            dose=float(dose),
            direction=spec.direction,
            donor=spec.donor,
            tensor_space=spec.tensor_space,
            run=spec.run,
            paired_run=spec.paired_run,
            control_ref=spec.control_ref,
            seed=spec.seed,
        )
        for dose in doses
    ]


# --------------------------------------------------------------------------- #
# Mesure : canaux separes + dommage general + verdict de selectivite
# --------------------------------------------------------------------------- #

@dataclass
class EffectChannels:
    """Les trois canaux d'effet, en slots separes, jamais sommes (#15475).

    L'appelant fournit les mesureurs (l'engine ne sait pas ce qu'est un
    « comportement » — c'est le point de l'API independante de la cible ET de
    l'endpoint). Chaque canal garde brut + delta pour audit.
    """

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
        if channel not in ("state", "readout", "behavior"):
            raise ValueError(f"canal {channel!r} inconnu (etat/readout/comportement)")
        target = getattr(self, channel)
        for name, fn in measurers.items():
            target[f"{name}_before"] = float(fn(panel_before))
            target[f"{name}_after"] = float(fn(panel_after))
            target[f"{name}_delta"] = target[f"{name}_after"] - target[f"{name}_before"]


def damage_metrics(
    panel_before: np.ndarray,
    panel_after: np.ndarray,
    spec: InterventionSpec,
) -> dict[str, float]:
    """Controle de dommage general : le deplacement des coordonnees NON cibles.

    Un collapse global ne peut pas se faire passer pour de la causalite
    selective (acceptance #15479). On mesure la norme relative du deplacement
    hors cible : ``off_target_rel`` doit rester proche de 0 pour une
    intervention propre ; ``target_rel`` documente l'ampleur voulue. Le rapport
    ``selectivity_ratio`` alimente le verdict : c'est ``target_rel`` rapporte au
    deplacement hors cible, et il vaut ``inf`` -- jamais un grand nombre -- quand
    ce deplacement tombe sous le plancher de mesure (cf. le corps de la fonction).
    """
    if panel_before.shape != panel_after.shape:
        raise ValueError("panneaux avant/apres de formes differentes")
    diff = panel_after - panel_before
    mask = np.ones(panel_before.shape, dtype=bool)
    if spec.positions and spec.features:
        mask[np.ix_(list(spec.positions), list(spec.features))] = False
    eps = 1e-12
    base = np.linalg.norm(panel_before)
    off = float(np.linalg.norm(diff[mask]))
    on = float(np.linalg.norm(diff[~mask])) if (~mask).any() else 0.0
    off_rel = off / max(base, eps)
    on_rel = on / max(base, eps)
    # ``eps`` est deja le plancher declare de cette fonction : il borne
    # ``off_rel``. Un deplacement hors cible qui y tombe n'est donc pas
    # « petit », il est INDISTINGUABLE DE ZERO -- et le rapport n'est pas
    # grand, il est NON BORNE. Rendre ``on_rel / eps`` faisait dependre la
    # magnitude publiee d'une constante interne (462774272000.00 mesures sur le
    # banc copy_offset pour une intervention parfaitement propre) et invitait a
    # la lire comme une mesure. ``inf`` dit ce que le chiffre ne dit pas, et
    # reste compatible avec le seuil du verdict, qui teste ``>= min_selectivity``.
    # Reste le cas ou RIEN ne bouge, cible et hors cible au plancher : aucun
    # rapport n'y est mesurable, et une intervention sans effet ne doit pas
    # ressortir selective -- d'ou 0.0.
    if off_rel <= eps:
        selectivity = float("inf") if on_rel > 0.0 else 0.0
    else:
        selectivity = on_rel / off_rel
    return {
        "target_rel": on_rel,
        "off_target_rel": off_rel,
        "selectivity_ratio": selectivity,
    }


def selectivity_verdict(
    damage: Mapping[str, float],
    *,
    min_selectivity: float = 5.0,
    max_off_target: float = 0.10,
) -> str:
    """Verdict de selectivite causal a partir des metriques de dommage.

    ``selective`` exige un rapport cible/hors-cible >= ``min_selectivity`` ET
    un deplacement hors cible <= ``max_off_target`` — les DEUX conditions : un
    rapport eleve obtenu en ecrasant tout le panneau (off_target grand mais
    cible encore plus grande) reste un dommage global, pas de la selectivite.
    """
    if damage["off_target_rel"] > max_off_target:
        return "global_damage"
    if damage["selectivity_ratio"] >= min_selectivity:
        return "selective"
    return "not_selective"


def holm_adjust(pvalues: Sequence[float]) -> tuple[float, ...]:
    """Correction de Holm-Bonferroni sur la famille de comparaisons de controles.

    Familie typique : {cible vs aleatoire apparie, cible vs sham}. Renvoie les
    p-values ajustees, ordre d'entree conserve.
    """
    m = len(pvalues)
    if m == 0:
        return ()
    order = sorted(range(m), key=lambda i: pvalues[i])
    adjusted = [0.0] * m
    running = 0.0
    for rank, idx in enumerate(order):
        running = max(running, (m - rank) * pvalues[idx])
        adjusted[idx] = min(1.0, running)
    return tuple(adjusted)


# --------------------------------------------------------------------------- #
# Famille Gate 24 (#5635) : le test de format
# --------------------------------------------------------------------------- #

def build_gate24_family(
    spec: InterventionSpec,
    random_control: InterventionSpec,
) -> dict[str, InterventionSpec]:
    """Represente exactement le clamp SAE du Gate 24 de #5635.

    Le Gate 24 compare trois bras : ``target`` (candidates workspace clampees),
    ``random`` (meme NOMBRE de features aleatoires clampees) et ``intact``
    (aucune intervention). Le moteur fournit la famille de specs ; le run et le
    verdict restent trackes dans #5635 (acceptance #15479 : « sans dupliquer
    son acceptance »). Le bras intact = cible vide, dose 0 — l'identite PAR la
    meme voie de code.
    """
    intact = InterventionSpec(
        operation=spec.operation,
        instrument=spec.instrument,
        layer=spec.layer,
        positions=(),
        features=(),
        dose=0.0,
        direction=spec.direction,
        tensor_space=spec.tensor_space,
        run=spec.run,
        seed=spec.seed,
    )
    return {"target": spec, "random": random_control, "intact": intact}


# --------------------------------------------------------------------------- #
# Enregistrement sidecar : provenance + rejouabilite
# --------------------------------------------------------------------------- #

def artifact_sha256(panel: np.ndarray) -> str:
    """Empreinte sha256 des octets d'un panneau (avant/apres rejouables)."""
    return hashlib.sha256(np.ascontiguousarray(panel).tobytes()).hexdigest()


@dataclass
class InterventionRecord:
    """Enregistrement d'une intervention appliquee, conforme au contrat v1 en sidecar.

    REFERE le manifeste de trace via ``alignment`` (cles ALIGNMENT_KEYS
    embarquees) sans l'etendre : couche sidecar, pas bump du contrat. Les
    empreintes avant/apres rendent l'application auditable sans stocker les
    panneaux eux-memes (qui vivent dans le trace store NPZ/Zarr du contrat).
    """

    spec: InterventionSpec
    alignment: dict[str, object]
    sha_before: str
    sha_after: str
    damage: dict[str, float] = field(default_factory=dict)
    verdict: str = ""
    effects: EffectChannels = field(default_factory=EffectChannels)

    def to_dict(self) -> dict[str, object]:
        return {
            "spec": asdict(self.spec),
            "alignment": self.alignment,
            "sha_before": self.sha_before,
            "sha_after": self.sha_after,
            "damage": dict(self.damage),
            "verdict": self.verdict,
            "effects": {
                "state": dict(self.effects.state),
                "readout": dict(self.effects.readout),
                "behavior": dict(self.effects.behavior),
            },
        }

    def to_json(self) -> str:
        return json.dumps(self.to_dict(), sort_keys=True, ensure_ascii=False)


def assert_alignment(rec_a: InterventionRecord, rec_b: InterventionRecord) -> None:
    """Echoue avec le champ fautif nomme si deux enregistrements ne s'alignent pas.

    Semantique du contrat v1 : toute comparaison operée sur un couple
    d'enregistrements exige l'egalite de CHACUNE des ALIGNMENT_KEYS presentes ;
    un mismatch nomme le champ ET les deux valeurs observees (diagnostic
    actionnable, pas un echec muet). Les cles absentes des deux cotes ne
    bloquent pas (champs optionnels du contrat).
    """
    for key in ALIGNMENT_KEYS:
        a, b = rec_a.alignment.get(key), rec_b.alignment.get(key)
        if a is not None and b is not None and a != b:
            raise ValueError(
                f"desalignement {key!r}: {a!r} != {b!r} — les enregistrements "
                f"{rec_a.spec.operation}/{rec_b.spec.operation} ne sont pas comparables"
            )


def trace_contract_module():
    """Import garde du contrat canonique (PR #15525) : None tant qu'il n'est pas merge.

    Au merge de #15525, la validation d'alignement deleguera a
    ``trace_contract.check_alignment`` ; d'ici, :func:`assert_alignment` tient
    la semantique v1 avec le litteral ALIGNMENT_KEYS ci-dessus. Le garde rend
    la dependance EXPLICITE plutot qu'un import qui casserait main.
    """
    try:
        import ict.trace_contract as tc  # type: ignore

        return tc
    except ImportError:
        return None
