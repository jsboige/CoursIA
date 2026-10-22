#!/usr/bin/env python3
"""Protocole d'ecoute subjectif (MOS) : generation du protocole et agregateur.

Ce module est l'organe de la serie GenAI/Audio pour la partie **subjective** de
l'evaluation de la qualite audio. Il ne remplace pas l'oreille : il l'organise.

Il ne recopie rien de ce que le depot possede deja :

* la **rubrique** MOS (`04-7-TTS-Voice-Benchmark.ipynb`, section 10) est lue a
  l'execution par `load_rubric` : criteres, echelle et reference viennent du
  carnet lui-meme, pas d'une liste reecrite ici ;
* la chaine d'outils objective du meme dossier (`verify_transcript.py`,
  `verify_diarization.py`, `verify_prosody.py`) reste le **plancher** mesure
  avant l'oreille -- ce module la prolonge, il ne la contourne pas.

Fonctions exposees :

* `load_rubric` -- criteres + echelle lus depuis le carnet de reference ;
* `load_grid_items` -- essais de la seance, lus depuis la meme grille ;
* `build_trial_list` -- liste d'essais **randomisee** (graine fixee), ancres
  comprises ;
* `rating_sheet` -- fiche de notation pre-remplie au schema de la rubrique ;
* `aggregate_mos` -- MOS par item, MOS global, **IC 95 %**, rejet des auditeurs
  aberrants (regle d'ITU-R P.808) ;
* `format_report` -- rapport lisible.

References bibliographiques : ITU-T P.800 (MOS et protocole d'ecoute
subjective), ITU-R P.808 (rejet des auditeurs aberrants). Elles sont citees,
pas reproduites.
"""
from __future__ import annotations

import ast
import json
import random
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

import numpy as np
from scipy import stats

REPO_ROOT = Path(__file__).resolve().parents[2]

#: Carnet qui porte la rubrique MOS de reference (source de verite unique).
DEFAULT_RUBRIC_NOTEBOOK = (
    "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-7-TTS-Voice-Benchmark.ipynb"
)

#: Variable de code qui porte la grille dans le carnet de reference.
GRID_VARIABLE = "mos_grid"

#: Regle de rejet des auditeurs aberrants (ITU-R P.808) : l'auditeur est ecarte
#: si sa moyenne s'ecarte d'au moins `P808_SIGMA` ecarts-types de la moyenne
#: des auditeurs **et** si sa moyenne est inferieure a `P808_RATIO` x MOS.
P808_SIGMA = 2.0
P808_RATIO = 0.85


class RubricError(RuntimeError):
    """La rubrique de reference n'a pas pu etre lue dans le carnet attendu."""


@dataclass(frozen=True)
class Rubric:
    """Rubrique d'evaluation subjective lue depuis le carnet de reference."""

    criteria: tuple[str, ...]
    scale_min: int
    scale_max: int
    reference: str
    source: str

    @property
    def scale(self) -> tuple[int, int]:
        return (self.scale_min, self.scale_max)

    def to_dict(self) -> dict[str, Any]:
        return {
            "criteria": list(self.criteria),
            "scale_min": self.scale_min,
            "scale_max": self.scale_max,
            "reference": self.reference,
            "source": self.source,
        }


@dataclass
class MosReport:
    """Resultat de l'agregation d'une campagne de notation.

    `mos` est la moyenne des MOS par item (chaque MOS d'item = moyenne des
    auditeurs sur cet item) ; l'intervalle de confiance est celui de la moyenne
    des MOS d'items (loi de Student, `n-1` degres de liberte).
    """

    mos: float
    ci_low: float
    ci_high: float
    confidence: float
    n_items: int
    n_judges: int
    per_item: dict[str, float]
    per_judge: dict[str, float]
    rejected_judges: list[str]
    criteria: tuple[str, ...] = field(default_factory=tuple)

    def to_dict(self) -> dict[str, Any]:
        return {
            "mos": self.mos,
            "ci_low": self.ci_low,
            "ci_high": self.ci_high,
            "confidence": self.confidence,
            "n_items": self.n_items,
            "n_judges": self.n_judges,
            "per_item": dict(self.per_item),
            "per_judge": dict(self.per_judge),
            "rejected_judges": list(self.rejected_judges),
            "criteria": list(self.criteria),
        }


# --------------------------------------------------------------------------
# Rubrique (lue depuis le carnet de reference)
# --------------------------------------------------------------------------


def _repo_root(repo_root: Path | str | None = None) -> Path:
    if repo_root is None:
        return REPO_ROOT
    return Path(repo_root).resolve()


def _grid_variable(cell_source: str) -> ast.List:
    """Rend la liste litterale assignee a `GRID_VARIABLE` dans une cellule."""
    tree = ast.parse(cell_source)
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id == GRID_VARIABLE:
                    if isinstance(node.value, ast.List):
                        return node.value
    raise RubricError(
        f"la cellule ne contient pas l'affectation `{GRID_VARIABLE} = [...]`"
    )


def _split_grid_keys(list_node: ast.List) -> tuple[tuple[str, ...], tuple[str, ...]]:
    """Separe les colonnes de note des colonnes de metadonnees.

    Regle **basee sur les valeurs**, pas sur une liste de noms codee en dur :
    les colonnes de metadonnees portent une chaine (modele, echantillon), les
    colonnes de note portent un nombre (grille remplie) ou `None` (grille
    vierge). Les deux etats de la grille sont donc lus correctement.
    """
    if not list_node.elts:
        raise RubricError(f"`{GRID_VARIABLE}` est vide dans le carnet de reference")
    first = list_node.elts[0]
    if not isinstance(first, ast.Dict):
        raise RubricError(f"`{GRID_VARIABLE}` n'est pas une liste de dicts")
    scores: list[str] = []
    meta: list[str] = []
    for key, value in zip(first.keys, first.values):
        if not isinstance(key, ast.Constant) or not isinstance(key.value, str):
            raise RubricError(f"cle non textuelle dans `{GRID_VARIABLE}`")
        if isinstance(value, ast.Constant) and isinstance(value.value, str):
            meta.append(key.value)
        else:
            scores.append(key.value)
    if not scores:
        raise RubricError(f"aucune colonne de note trouvee dans `{GRID_VARIABLE}`")
    return tuple(scores), tuple(meta)


def _rubric_markdown(nb: Mapping[str, Any], criteria: Sequence[str]) -> tuple[str, tuple[int, int]]:
    """Rend (reference bibliographique, echelle) lues dans la cellule de rubric.

    La cellule retenue est celle qui mentionne la grille **et** au moins un
    des criteres de note -- une mention isolee du mot « MOS » ne suffit pas.
    """
    reference = ""
    scale = (1, 5)
    cells = [
        "".join(cell.get("source", []))
        for cell in nb.get("cells", [])
        if cell.get("cell_type") == "markdown"
    ]

    def _read(text: str) -> tuple[str, tuple[int, int] | None]:
        match = re.search(r"(ITU[-\s]?T\s*P\.?800|P\.800)", text, re.IGNORECASE)
        ref = match.group(1) if match else ""
        # Le lookbehind exclut un chiffre precede d'un chiffre : sans lui, le
        # lien de nav `04-9-...` serait lu comme une echelle « 4-9 ».
        found = re.search(r"(?<!\d)(\d)\s*(?:-|–|—|à|a|to)\s*(\d)", text)
        return ref, ((int(found.group(1)), int(found.group(2))) if found else None)

    # Trois niveaux de preference : la cellule qui porte la grille ET ses
    # definitions, puis la cellule de la grille, puis la premiere mention du
    # MOS qui cite un critere.
    tiers = [
        [t for t in cells if "mos" in t.lower() and "grille" in t.lower() and _read(t)[1]],
        [t for t in cells if "mos" in t.lower() and "grille" in t.lower()],
        [t for t in cells if "mos" in t.lower() and any(c in t.lower() for c in criteria)],
    ]
    for tier in tiers:
        if not tier:
            continue
        for text in tier:
            ref, found_scale = _read(text)
            if ref and found_scale:
                return ref, found_scale
        # tier sans cellule portant les deux : on prend la premiere qui en
        # porte au moins une.
        for text in tier:
            ref, found_scale = _read(text)
            if ref or found_scale:
                return ref, found_scale or scale
    return reference, scale


def _grid_cell_source(nb: Mapping[str, Any], path: Path) -> str:
    """Rend la source de la cellule de code qui porte la grille."""
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        source = "".join(cell.get("source", []))
        if GRID_VARIABLE in source:
            return source
    raise RubricError(
        f"aucune cellule `{GRID_VARIABLE}` trouvee dans {path.name} : "
        "la grille de reference a ete deplacee ou renommee"
    )


def load_grid_items(
    notebook_path: Path | str | None = None,
    repo_root: Path | str | None = None,
) -> list[dict[str, Any]]:
    """Rend les **essais de la seance**, lus depuis la grille de reference.

    Les lignes de la grille du carnet `04-7` (3 modeles x 3 registres) sont
    les essais que la seance d'ecoute doit couvrir : les lire ici evite au
    carnet consommateur de redeclarer un corpus qui peut diverger.

    Chaque element rendu porte un `id` stable (`<modele>-<echantillon>`), un
    `label` lisible et les colonnes de metadonnees de la grille.
    """
    root = _repo_root(repo_root)
    path = Path(notebook_path) if notebook_path else (root / DEFAULT_RUBRIC_NOTEBOOK)
    if not path.is_absolute():
        path = root / path
    if not path.is_file():
        raise RubricError(f"carnet de reference introuvable : {path}")
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise RubricError(f"carnet de reference illisible : {path} ({exc})") from exc

    list_node = _grid_variable(_grid_cell_source(nb, path))
    _criteria, meta = _split_grid_keys(list_node)
    try:
        rows = ast.literal_eval(list_node)
    except (ValueError, SyntaxError) as exc:
        raise RubricError(f"grille de reference illisible : {exc}") from exc

    label_keys = [k for k in meta if k in ("modele", "sample", "echantillon", "registre")]
    items: list[dict[str, Any]] = []
    for row in rows:
        parts = [str(row.get(k, "")).strip() for k in label_keys if row.get(k) is not None]
        item = {k: row.get(k) for k in label_keys}
        item["id"] = "-".join(p for p in parts if p) or f"essai-{len(items) + 1}"
        item["label"] = " / ".join(p for p in parts if p) or item["id"]
        items.append(item)
    if not items:
        raise RubricError(f"la grille `{GRID_VARIABLE}` ne contient aucun essai")
    return items


def load_rubric(
    notebook_path: Path | str | None = None,
    repo_root: Path | str | None = None,
) -> Rubric:
    """Lit la rubrique MOS depuis le carnet de reference.

    Les criteres de note et l'echelle sont extraits du carnet lui-meme : si la
    rubrique evolue dans `04-7`, le protocole suit, sans edition ici.

    Leve `RubricError` si le carnet n'est pas lisible ou si sa structure a
    change -- mieux vaut un echec franc qu'une grille silencieusement vide.
    """
    root = _repo_root(repo_root)
    path = Path(notebook_path) if notebook_path else (root / DEFAULT_RUBRIC_NOTEBOOK)
    if not path.is_absolute():
        path = root / path
    if not path.is_file():
        raise RubricError(f"carnet de reference introuvable : {path}")
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise RubricError(f"carnet de reference illisible : {path} ({exc})") from exc

    grid_cell = _grid_cell_source(nb, path)

    criteria, _meta = _split_grid_keys(_grid_variable(grid_cell))
    reference, scale = _rubric_markdown(nb, criteria)
    return Rubric(
        criteria=criteria,
        scale_min=scale[0],
        scale_max=scale[1],
        reference=reference,
        source=path.as_posix(),
    )


# --------------------------------------------------------------------------
# Protocole : liste d'essais et fiche de notation
# --------------------------------------------------------------------------


def build_trial_list(
    items: Iterable[Mapping[str, Any]],
    seed: int = 0,
    anchor_ids: Sequence[str] = (),
) -> list[dict[str, Any]]:
    """Range les essais dans un **ordre de presentation aleatoire**.

    L'ordre aleatoire n'est pas un detail : un jury qui note toujours le meme
    systeme dans le meme ordre converge vers des notes de position plutot que
    des notes de qualite. Les ancrages (`anchor_ids`) sont des essais de
    reference dont la note est connue de l'experimente : leur deviation
    signale une derive du jury au cours de la session.

    Chaque element rendu est une **copie** de l'element d'origine, augmentee
    de `presentation_order` (1-based) et de `is_anchor`.
    """
    materialised = [dict(item) for item in items]
    if not materialised:
        raise ValueError("la liste d'essais est vide")
    anchors = set(anchor_ids)
    rng = random.Random(seed)
    rng.shuffle(materialised)
    for position, item in enumerate(materialised, start=1):
        item["presentation_order"] = position
        item["is_anchor"] = str(item.get("id", "")) in anchors
    return materialised


def rating_sheet(
    trial_list: Sequence[Mapping[str, Any]],
    rubric: Rubric,
) -> list[dict[str, Any]]:
    """Fiche de notation pre-remplie au schema de la rubrique.

    Une ligne par essai, dans l'ordre de presentation, avec une colonne vide
    (`None`) par critere : c'est la forme que l'auditeur remplit, et la forme
    que `aggregate_mos` consomme apres remplissage.
    """
    sheet: list[dict[str, Any]] = []
    for item in trial_list:
        row: dict[str, Any] = {
            "presentation_order": item.get("presentation_order"),
            "item_id": item.get("id"),
            "label": item.get("label"),
            "is_anchor": bool(item.get("is_anchor", False)),
        }
        for criterion in rubric.criteria:
            row[criterion] = None
        sheet.append(row)
    return sheet


# --------------------------------------------------------------------------
# Agregation
# --------------------------------------------------------------------------


def _scores_of(record: Mapping[str, Any], criteria: Sequence[str]) -> list[float]:
    scores = record.get("scores")
    if not isinstance(scores, Mapping):
        raise ValueError(
            "chaque enregistrement doit porter un dict `scores` "
            f"(enregistrement recu : {sorted(record)})"
        )
    missing = [c for c in criteria if scores.get(c) is None]
    if missing:
        raise ValueError(
            "notes manquantes pour "
            + ", ".join(missing)
            + f" (essai {record.get('item_id')!r}, auditeur {record.get('judge_id')!r}) : "
            "la fiche de notation n'est pas completement remplie"
        )
    return [float(scores[c]) for c in criteria]


def aggregate_mos(
    records: Iterable[Mapping[str, Any]],
    rubric: Rubric | None = None,
    criteria: Sequence[str] | None = None,
    confidence: float = 0.95,
    reject_outliers: bool = True,
    p808_sigma: float = P808_SIGMA,
    p808_ratio: float = P808_RATIO,
) -> MosReport:
    """Agregate les notes d'une campagne en un MOS avec son intervalle.

    `records` est une iterable d'enregistrements :

    .. code-block:: python

        {"item_id": "A", "judge_id": "j1", "scores": {"naturalite": 4, ...}}

    Le MOS est la moyenne des MOS par item (chaque MOS d'item = moyenne des
    auditeurs sur cet item). L'intervalle de confiance est celui de la moyenne
    des MOS d'items (Student, `n-1` degres de liberte) : c'est l'incertitude
    sur le score du systeme, pas sur la stabilite d'un auditeur.

    Rejet des auditeurs aberrants (ITU-R P.808) : un auditeur est ecarte si sa
    moyenne s'ecarte d'au moins `p808_sigma` ecarts-types de la moyenne des
    auditeurs **et** si sa moyenne est inferieure a `p808_ratio` x MOS. Les
    auditeurs ecartes sont nommes dans le rapport -- un rejet muet serait
    impossible a auditer.
    """
    if criteria is None:
        if rubric is None:
            raise ValueError("fournir `rubric` ou `criteria`")
        criteria = tuple(rubric.criteria)
    criteria = tuple(criteria)
    if not criteria:
        raise ValueError("aucun critere de note")
    if not 0.0 < confidence < 1.0:
        raise ValueError(f"niveau de confiance hors bornes : {confidence}")

    materialised = list(records)
    if not materialised:
        raise ValueError("aucun enregistrement de notation")

    item_judge: dict[tuple[str, str], float] = {}
    item_ids: list[str] = []
    judge_ids: list[str] = []
    for record in materialised:
        item_id = str(record.get("item_id"))
        judge_id = str(record.get("judge_id"))
        if item_id not in item_ids:
            item_ids.append(item_id)
        if judge_id not in judge_ids:
            judge_ids.append(judge_id)
        key = (item_id, judge_id)
        if key in item_judge:
            raise ValueError(f"note dupliquee pour {key}")
        item_judge[key] = float(np.mean(_scores_of(record, criteria)))

    def _per_item(judges: Sequence[str]) -> dict[str, float]:
        out: dict[str, float] = {}
        for item_id in item_ids:
            values = [item_judge[(item_id, j)] for j in judges if (item_id, j) in item_judge]
            if values:
                out[item_id] = float(np.mean(values))
        return out

    def _per_judge(judges: Sequence[str]) -> dict[str, float]:
        out: dict[str, float] = {}
        for judge_id in judges:
            values = [item_judge[(i, judge_id)] for i in item_ids if (i, judge_id) in item_judge]
            if values:
                out[judge_id] = float(np.mean(values))
        return out

    def _mos(per_item: Mapping[str, float]) -> float:
        if not per_item:
            raise ValueError("aucun item note")
        return float(np.mean(list(per_item.values())))

    rejected: list[str] = []
    kept = list(judge_ids)
    per_item = _per_item(kept)
    per_judge = _per_judge(kept)

    if reject_outliers and len(judge_ids) > 2:
        mos0 = _mos(per_item)
        judge_means = np.array([per_judge[j] for j in judge_ids], dtype=float)
        spread = float(np.std(judge_means, ddof=1)) if len(judge_ids) > 1 else 0.0
        if spread > 0.0:
            rejected = [
                judge_id
                for judge_id in judge_ids
                if abs(per_judge[judge_id] - mos0) >= p808_sigma * spread
                and per_judge[judge_id] < p808_ratio * mos0
            ]
            if rejected:
                kept = [j for j in judge_ids if j not in rejected]
                per_item = _per_item(kept)
                per_judge = _per_judge(kept)

    mos = _mos(per_item)
    values = np.array(list(per_item.values()), dtype=float)
    n = values.size
    if n > 1:
        sem = float(stats.sem(values))
        margin = float(stats.t.ppf(0.5 + confidence / 2.0, df=n - 1)) * sem
    else:
        margin = 0.0

    return MosReport(
        mos=mos,
        ci_low=mos - margin,
        ci_high=mos + margin,
        confidence=confidence,
        n_items=len(per_item),
        n_judges=len(kept),
        per_item=per_item,
        per_judge=per_judge,
        rejected_judges=rejected,
        criteria=criteria,
    )


def format_report(report: MosReport) -> str:
    """Rend le rapport d'une campagne sous forme lisible."""
    lines = [
        f"MOS global : {report.mos:.3f}",
        (
            f"IC {report.confidence * 100:.0f} % : "
            f"[{report.ci_low:.3f}, {report.ci_high:.3f}] "
            f"(+/- {(report.ci_high - report.ci_low) / 2:.3f})"
        ),
        f"Essais : {report.n_items} | Auditeurs retenus : {report.n_judges}",
        f"Rejet P.808 : {', '.join(report.rejected_judges) if report.rejected_judges else 'aucun'}",
        "",
        "MOS par essai :",
    ]
    for item_id, value in report.per_item.items():
        lines.append(f"  - {item_id} : {value:.3f}")
    lines.append("")
    lines.append("Moyenne par auditeur :")
    for judge_id, value in report.per_judge.items():
        lines.append(f"  - {judge_id} : {value:.3f}")
    return "\n".join(lines)


def _demo() -> str:
    """Demonstration locale : rubric lue + campagne fictive agregee."""
    rubric = load_rubric()
    out = [f"Rubrique lue depuis {Path(rubric.source).name} :"]
    out.append(f"  criteres : {', '.join(rubric.criteria)}")
    out.append(f"  echelle  : {rubric.scale_min}-{rubric.scale_max}")
    out.append(f"  reference: {rubric.reference or 'non trouvee dans la cellule'}")

    items = [{"id": f"essai-{i}", "label": f"essai {i}"} for i in range(1, 5)]
    trial = build_trial_list(items, seed=7, anchor_ids=["essai-1"])
    out.append("")
    out.append("Ordre de presentation (graine 7) :")
    for item in trial:
        flag = " (ancre)" if item["is_anchor"] else ""
        out.append(f"  {item['presentation_order']}. {item['id']}{flag}")

    # Campagne FICTIVE : notation simulee pour la demonstration de l'outil.
    # Six auditeurs raisonnables + un aberrant, pour que la regle P.808 ait
    # un panel suffisant (l'ecart-type est gonfle par l'aberrant lui-meme
    # quand le jury est trop petit).
    records = []
    for judge_id, bias in (
        ("j1", 0.0),
        ("j2", 0.2),
        ("j3", -0.1),
        ("j4", 0.15),
        ("j5", -0.15),
        ("j6", 0.05),
        ("j7", -1.8),
    ):
        for index, item in enumerate(items):
            base = 3.0 + 0.4 * index + bias
            records.append(
                {
                    "item_id": item["id"],
                    "judge_id": judge_id,
                    "scores": {c: max(1.0, min(5.0, base + 0.1 * k)) for k, c in enumerate(rubric.criteria)},
                }
            )
    report = aggregate_mos(records, rubric=rubric)
    out.append("")
    out.append(format_report(report))
    return "\n".join(out)


if __name__ == "__main__":  # pragma: no cover - usage manuel
    print(_demo())
