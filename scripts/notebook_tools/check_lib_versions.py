"""Organe : versions canoniques des bibliotheques chargees par les carnets (#23073).

Motif (mandat user du 2026-10-28, a propos de #23047) : « Ca meritera un
organe pour stabiliser les versions d'API et de libs, car ce genre de
regressions sont parmis les plus terribles et incidieuses. C'est toute une
serie de notebook qui peut exploser. »

Ce que fait cet organe
----------------------

1. **Recensement** (`--census`) : il lit les epinglages de version portes par
   les cellules code des carnets (NuGet `#r "nuget: X, v"`, pip `x==v`,
   provisionnement versionne) et produit la table de dispersion : pour chaque
   bibliotheque du manifeste, la version canonique et tous les epinglages
   rencontres, avec le classement de chaque ecart (« a converger » ou
   « justifie », avec son motif). Le recensement sort toujours en **rc 0** :
   il decrit l'etat, il ne juge aucune PR.

2. **Garde de PR** (`--changed <range>`) : sur les **carnets modifies**, elle
   signale ce qu'une PR introduce :

   - `downgrade` -- la PR abaisse l'epinglage d'une bibliotheque ;
   - `unmanaged_upgrade` -- la PR pose une version superieure a la canonique ;
   - `divergence` -- la PR pose un epinglage different de la canonique ;
   - `foreign_provisioning` -- source de provisionnement hors de l'organe de
     serie (URL morte ou divergente).

   La comparaison des epinglages est un **delta base -> tete** : un epinglage
   deja present, non touche par la PR, ne rougit pas. C'est ce qui distingue
   un constat de regression d'un constat de derive historique, et c'est ce qui
   evite de faire rougir, a chaque PR, les carnets legacy d'une serie en cours
   de convergence. Le mode `--state` (sans base) compare l'etat brut : il sert
   au recensement d'un carnet donne, et aux controles.

   Le provisionnement etranger, lui, est signale **sur l'etat** : son
   dommage se produit a l'execution, pas a l'edition. C'est le cas
   declencheur de #23047 (l'archive charge `tweetyproject.org/builds/1.28/`,
   qui repond 404 depuis #12789).

   Seule exception : une entree d'allowlist du manifeste, avec son motif
   ecrit. La levee d'une reserve reste au tiers : cet organe ne pretend pas
   valider une PR, il publie un constat.

   Un avis non bloquant `repli_versionne` signale aussi, sur l'etat des
   carnets examines, un message litteral `print` de skip avec version dans
   un `except` Python. Il ne prouve pas que ce repli a ete execute ; les
   cellules non analysables et les messages calcules ne sont pas couverts.

Ce que cet organe ne fait pas
-----------------------------

- Il ne reexecute aucun carnet et ne compare pas deux notebooks.
- Il ne juge pas l'interpreteur : c'est le ressort de `check_kernel_drift.py`.
- Il ne touche ni aux lakes Lean (Mathlib, #4362) ni aux sorties videes par
  un environnement absent (#21424).

Regles de version
------------------

La comparaison est **numerique segment par segment** (`8.14.0` < `8.15.0`),
et non lexicographique : `9.11` > `9.9` est faux en lexicographie. Un
segment non numerique (`-preview`, `+build`) est compare comme texte apres
les segments numeriques.

Note de conception : le manifeste ne **recopie** pas la version d'un organe
de serie deja existant -- quand un organe fixe deja la version (`TWEETY_VERSION`
pour Tweety), le manifeste pointe vers lui et la valeur est lue a l'execution.
Deux surfaces qui recopient la meme valeur finissent par diverger ; c'est
exactement la regression que l'organe doit empecher.
"""

from __future__ import annotations

import argparse
import ast
import json
import os
import posixpath
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = Path(__file__).resolve().parent / "lib_versions_manifest.json"

# Racine des series de carnets. Une canonique **par serie** s'ecrit
# relative a ce prefixe (`RL`, `ML/DataScienceWithAgents/04-Vision`) : le
# lecteur ne repetera pas le long prefixe a chaque entree.
NOTEBOOKS_ROOT = "MyIA.AI.Notebooks"


def series_path(notebook_relative: str) -> str:
    """Chemin d'un carnet (ou d'un prefixe de serie) relatif aux series.

    Un prefixe ecrit avec la racine des series (`MyIA.AI.Notebooks/RL`) et
    un prefixe ecrit sans (`RL`) designent la meme serie : la normalisation
    les ramene au meme etat.
    """
    prefix = NOTEBOOKS_ROOT + "/"
    if notebook_relative.startswith(prefix):
        return notebook_relative[len(prefix):]
    return notebook_relative


def _series_covers(series_key: str, notebook_relative: str) -> bool:
    """Vrai si le prefixe de serie couvre le carnet, a la frontiere d'un segment.

    `RL` couvre `RL/RL-06-DQN-Policy-Gradient-Python.ipynb` et
    `RL/PostTraining/RLPT-02-GRPO-Minimal-Python.ipynb` ; il ne couvre pas
    `RLance/...` -- la frontiere est un segment, pas un prefixe de chaines.
    """
    key = series_path(notebook_relative)
    entry = series_key.strip("/")
    if not entry:
        return True
    return key == entry or key.startswith(entry + "/")

# Epinglages NuGet : `#r "nuget: IKVM, 8.15.0"`. La virgule peut suivre sans
# espace (`nuget:pythonnet,3.1.0`) : le motif l'accepte.
NUGET_PIN_RE = re.compile(
    r'#r\s*"nuget:\s*([^",\s]+)\s*(?:,\s*v?([0-9][^",\s]*))?(?:\s*,\s*[^"]*)?\s*"',
    re.IGNORECASE,
)

# Un epinglage **sans version** (`#r "nuget: IKVM"`) est un pin flottant : il
# est reconnu (le groupe version reste vide) et signale comme tel -- cf
# #23086, qui nomme le defaut ; il n'est pas jete en silence.
FLOATING_PIN_REASON = (
    "epinglage flottant : la version n'est pas fixee, donc le carnet peut "
    "charger une version differente a chaque re-execution (cf #23086)"
)

# Epinglages pip : la ligne doit etre une **COMMANDE** d'installation --
# `pip install x==1.2.3`, `%pip install ...`, `!pip install ...`.
#
# Le motif est ancre sur le debut de la ligne (`^`) : une version citee dans
# un commentaire ou dans une chaine n'est pas un epinglage. Le corpus portait
# exactement ce piege -- `pip install mealpy==3.0.2` dans un commentaire C# et
# dans un `print` Python -- et l'organe les comptait comme les declarations
# du corpus (relecture #23079, point 2). La version du groupe 2 est
# facultative : `pip install mealpy` (sans version) est un epinglage
# **flottant**, signale comme tel et non jete (cf #23086).
#
# Les QUATRE formes ecrites par un lecteur sont couvertes (#23104) : `pip`,
# `pip3`, `python -m pip` (et sa variante `python3`), `uv pip`. Le corps
# #23104 nomme l'angle mort -- l'organe ne reconnaissait que la premiere, donc
# `python -m pip install torch==2.8.0` (6 lignes du corpus) n'etait pas une
# declaration pour lui.
_PIP_INSTALL = (
    r"(?:(?:python3?(?:\.\d+)?\s+-m\s+pip)|(?:uv\s+pip)|(?:pip3?(?:\.\d+)?))"
    r"\s+install\b"
)

# Reconnaisseur de **ligne-commande**, sans capture : il sert a decider si une
# ligne d'une cellule MARKDOWN est une commande d'installation. C'est lui qui
# rend l'extension au markdown sure -- mesure du corpus : 36 lignes-commandes
# ancrees contre 114 mentions en prose (« installez avec `pip install x` »,
# commentaires, chaines). Un motif non ancre prendrait les 114 pour des
# declarations.
PIP_COMMAND_RE = re.compile(
    r"^\s*(?:[%!$]\s*)?" + _PIP_INSTALL,
    re.IGNORECASE,
)

PIP_PIN_RE = re.compile(
    r"^\s*(?:[%!$]\s*)?" + _PIP_INSTALL + r"\s+(?:--?\S+\s+)*([A-Za-z0-9._\-]+)"
    r"(?:\s*==\s*([A-Za-z0-9._\-+!]+))?",
    re.IGNORECASE,
)


def _norm_version(value: str) -> str:
    """Normalise une version : espaces retires, ponctuation terminale retiree."""
    return value.strip().strip(";,)")

# Nombre de composantes comparees : NuGet en utilise quatre (`1.0.0.0`).
# Completer a cette longueur rend la comparaison totale, donc `8.15` et
# `8.15.0` egales au lieu d'ordonnees par longueur de tuple.
_VERSION_COMPONENTS = 4


def version_key(value: str) -> tuple:
    """Cle de comparaison numerique d'une version.

    `8.14.0` -> (8, 14, 0) ; `9.11.4210` -> (9, 11, 4210). Un segment non
    numerique est compare comme texte, apres les segments numeriques. Une
    version pre-publique (`1.0.0-preview`) est **inferieure** a la version
    correspondante sans suffixe (`1.0.0`), comme le veut semver.
    """
    normalized = _norm_version(value)
    # `v8.15.0` est une ecriture de `8.15.0`, pas une version superieure :
    # sans ce retrait, `"v8.15.0" > "8.15.0"` comparait les caracteres
    # (relecture #23079 point 7).
    if normalized[:1] in ("v", "V"):
        normalized = normalized[1:]
    parts = []
    for segment in normalized.split("."):
        digits = ""
        for char in segment:
            if char.isdigit():
                digits += char
            else:
                break
        if digits and digits == segment:
            # Segment purement numerique : version publiee.
            parts.append((0, int(digits), 1, ""))
        elif digits:
            # Segment numerique suivi d'un suffixe : version pre-publique.
            parts.append((0, int(digits), 0, segment[len(digits):]))
        else:
            parts.append((1, 0, 0, segment))
    # `8.15` et `8.15.0` sont la MEME version. Sans completion, la
    # comparaison de tuples rend le plus court inferieur -- c'etait le faux
    # downgrade de `8.15` contre `8.15.0`, et le faux upgrade de `1.0.0.0`
    # contre `1.0.0` (relecture #23079 point 7). NuGet s'arrete a quatre
    # composantes : completer a quatre rend la comparaison totale.
    while len(parts) < _VERSION_COMPONENTS:
        parts.append((0, 0, 1, ""))
    return tuple(parts)


def compare_versions(left: str, right: str) -> int:
    """-1 si left < right, 0 si egales, +1 si left > right."""
    a, b = version_key(left), version_key(right)
    if a < b:
        return -1
    if a > b:
        return 1
    return 0


@dataclass
class Library:
    """Une bibliotheque du manifeste."""

    id: str
    ecosystem: str
    canonical: str | None = None
    # Source de la version canonique :
    #   - "manifest"  : la valeur est dans le manifeste ;
    #   - "organ"     : la valeur est lue dans un organe de serie, au runtime.
    canonical_source: str = "manifest"
    organ_path: str = ""
    organ_symbol: str = ""
    # Symbole de version que l'organe de serie possede : si un carnet le
    # **redeclare** localement, sa valeur doit rester celle de l'organe.
    # C'est la derive exacte de #23047 (l'archive reecrit `TWEETY_VERSION =
    # "1.28"` et repart sur une URL morte).
    local_symbol: str = ""
    # Motifs de provisionnement etranger a la serie : URL morte ou divergente.
    foreign_provisioning: list[dict] = field(default_factory=list)
    # Note libre : d'ou vient la version canonique, quand elle n'est pas
    # portee par un organe de serie. Pas un decompil, pas un nombre de
    # carnets : une source.
    note: str = ""
    # Ecarts classes : version -> {decision, reason}
    divergences: dict[str, dict] = field(default_factory=dict)
    # Canonique **PAR SERIE** : la version attendue peut differer d'une serie
    # a l'autre (une serie epingle torch==2.14.0, une autre converge vers
    # 2.13). Chaque entree porte un prefixe de chemin de serie, et la
    # **plus longue** correspondance gagne -- un prefixe long decrit une
    # sous-serie plus fine que son parent.
    canonical_by_series: list[dict] = field(default_factory=list)
    # Observer la version **reellement chargee** dans les sorties commitees.
    # C'est un opt-in : seules les bibliotheques dont la version n'est
    # portee par aucun epinglage (torch, numpy) sont relevees ainsi -- voir
    # `observed_versions_from_payload`.
    observe_outputs: bool = False

    def resolve_series_canonicals(
        self, repo_root: Path
    ) -> tuple[list[tuple[str, str | None]], list[str]]:
        """Resout les canoniques par serie : (liste (prefixe, version), erreurs).

        Chaque prefixe est resolu **une fois** : un artefact de serie est lu
        au runtime, et le relire par carnet multiplierait les lectures sans
        changer le resultat.
        """
        resolved: list[tuple[str, str | None]] = []
        errors: list[str] = []
        for entry in self.canonical_by_series:
            key = series_path(entry.get("series", "")).strip("/")
            source = entry.get("canonical_source", "manifest")
            if source == "artifact":
                value, error = self._read_artifact(repo_root, entry)
                if error:
                    errors.append(f"{self.id} [{key}] : {error}")
            else:
                value, error = entry.get("canonical"), None
            resolved.append((key, value))
        return resolved, errors

    def resolve_canonical_for(
        self, repo_root: Path, notebook_relative: str
    ) -> tuple[str | None, str | None]:
        """Canonique applicable a UN carnet : la serie prime sur le defaut.

        Une bibliotheque sans `canonical_by_series` garde le comportement
        d'avant -- la canonique unique du manifeste. Une bibliotheque qui en
        declare des series resout la **plus longue** correspondance, puis
        retombe sur la canonique unique si aucune serie ne couvre le carnet.
        """
        if not self.canonical_by_series:
            return self.resolve_canonical(repo_root)
        entries, errors = self.resolve_series_canonicals(repo_root)
        best: tuple[str, str | None] | None = None
        for key, value in entries:
            if not _series_covers(key, notebook_relative):
                continue
            if best is None or len(key) > len(best[0]):
                best = (key, value)
        if best is None:
            return self.resolve_canonical(repo_root)
        if best[1] is None:
            detail = next(
                (error for error in errors if f"[{best[0]}]" in error), ""
            )
            return None, detail or f"canonique de serie non resolue : {best[0]}"
        return best[1], None

    def _read_artifact(
        self, repo_root: Path, entry: dict
    ) -> tuple[str | None, str | None]:
        """Lit la version epinglee dans un artefact de serie (`id==version`).

        L'artefact est lu au runtime : le manifeste ne recopie pas la valeur,
        il pointe vers le fichier qui la porte -- deux surfaces qui recopient
        la meme valeur finissent par diverger, ce que l'organe existe pour
        empecher.
        """
        rel = entry.get("organ_path", "")
        artifact = repo_root / rel
        if not artifact.is_file():
            return None, f"artefact introuvable : {rel}"
        try:
            text = artifact.read_text(encoding="utf-8", errors="replace")
        except OSError as exc:
            return None, f"artefact illisible : {rel} ({exc})"
        pattern = re.compile(
            rf"^\s*{re.escape(self.id)}\s*(==|>=)\s*([0-9][^\s#;]*)",
            re.MULTILINE | re.IGNORECASE,
        )
        match = pattern.search(text)
        if not match:
            return None, (
                f"contrainte {self.id}== ou {self.id}>= introuvable dans {rel} "
                f"(serie {entry.get('series', '')})"
            )
        return match.group(2), None

    def resolve_canonical(self, repo_root: Path) -> tuple[str | None, str | None]:
        """Retourne (version canonique, erreur)."""
        if self.canonical_source == "manifest":
            return self.canonical, None
        organ = repo_root / self.organ_path
        if not organ.is_file():
            return None, f"organe introuvable : {self.organ_path}"
        try:
            text = organ.read_text(encoding="utf-8", errors="replace")
        except OSError as exc:
            return None, f"organe illisible : {self.organ_path} ({exc})"
        pattern = re.compile(
            rf"^\s*{re.escape(self.organ_symbol)}\s*=\s*[\"']([^\"']+)[\"']",
            re.MULTILINE,
        )
        match = pattern.search(text)
        if not match:
            return None, (
                f"symbole {self.organ_symbol} introuvable dans {self.organ_path}"
            )
        return match.group(1), None


@dataclass
class Manifest:
    """Le manifeste des versions canoniques."""

    libraries: dict[str, Library]
    allowlist: list[dict]
    path: Path


def load_manifest(path: Path) -> Manifest:
    """Charge le manifeste ; leve une ValueError explicite si le JSON est faux."""
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise ValueError(f"manifeste introuvable : {path}") from exc
    except json.JSONDecodeError as exc:
        raise ValueError(f"manifeste illisible ({path}) : {exc}") from exc

    libraries: dict[str, Library] = {}
    for entry in raw.get("libraries", []):
        lib_id = entry["id"]
        canonical = entry.get("canonical")
        source = entry.get("canonical_source", "manifest")
        if source == "organ":
            canonical = None
        libraries[lib_id] = Library(
            id=lib_id,
            ecosystem=entry["ecosystem"],
            canonical=canonical,
            canonical_source=source,
            organ_path=entry.get("organ_path", ""),
            organ_symbol=entry.get("organ_symbol", ""),
            local_symbol=entry.get("local_symbol", ""),
            foreign_provisioning=list(entry.get("foreign_provisioning", [])),
            note=entry.get("note", ""),
            canonical_by_series=[
                {
                    "series": item.get("series", ""),
                    "canonical": item.get("canonical"),
                    "canonical_source": item.get("canonical_source", "manifest"),
                    "organ_path": item.get("organ_path", ""),
                    "note": item.get("note", ""),
                }
                for item in entry.get("canonical_by_series", [])
            ],
            observe_outputs=bool(entry.get("observe_outputs", False)),
            divergences={
                d["version"]: {
                    "decision": d.get("decision", "to_converge"),
                    "reason": d.get("reason", ""),
                }
                for d in entry.get("divergences", [])
            },
        )
    return Manifest(
        libraries=libraries,
        allowlist=list(raw.get("allowlist", [])),
        path=path,
    )


@dataclass
class Pin:
    """Un epinglage de version releve dans une cellule."""

    library: str
    version: str
    ecosystem: str
    cell: int = -1
    line: str = ""
    line_no: int = 0
    cell_type: str = "code"


def _cell_text(cell: dict) -> str:
    source = cell.get("source", "")
    if isinstance(source, list):
        return "".join(source)
    return str(source)


_SKIP_MESSAGE = re.compile(r"\b(?:skip(?:ped|ping)?|saut(?:e|é|ée|er))\b", re.I)
_MESSAGE_VERSION = re.compile(r"(?<![\d.])\d+\.\d+(?:\.\d+)*(?![\d.])")


def versioned_fallbacks(notebook: str, payload: dict) -> list[dict]:
    """Avis borne : message litteral de skip imprime dans un `except` Python.

    Les cellules non analysables (magics, autres langages) et les messages
    calcules ne sont pas couverts. Aucun avis ne prouve que le handler a tourne.
    """
    result: list[dict] = []
    for index, cell in enumerate(payload.get("cells", []) or []):
        if cell.get("cell_type") != "code":
            continue
        try:
            tree = ast.parse(_cell_text(cell))
        except (SyntaxError, ValueError):
            continue
        class Visitor(ast.NodeVisitor):
            in_handler = False

            def visit_ExceptHandler(self, node: ast.ExceptHandler) -> None:
                previous = self.in_handler
                self.in_handler = True
                for statement in node.body:
                    self.visit(statement)
                self.in_handler = previous

            def visit_FunctionDef(self, node: ast.FunctionDef | ast.AsyncFunctionDef) -> None:
                previous = self.in_handler
                self.in_handler = False
                self.generic_visit(node)
                self.in_handler = previous

            visit_AsyncFunctionDef = visit_FunctionDef
            visit_ClassDef = visit_FunctionDef
            visit_Lambda = visit_FunctionDef

            def visit_Call(self, node: ast.Call) -> None:
                if self.in_handler and isinstance(node.func, ast.Name) and node.func.id == "print":
                    for arg in node.args:
                        if (isinstance(arg, ast.Constant) and isinstance(arg.value, str)
                                and _SKIP_MESSAGE.search(arg.value)
                                and _MESSAGE_VERSION.search(arg.value)):
                            result.append({"notebook": notebook, "cell": index,
                                           "line": node.lineno, "message": arg.value,
                                           "kind": "repli_versionne"})
                self.generic_visit(node)

        Visitor().visit(tree)
    return result


def _declaration_lines(payload: dict):
    """Yield (index de cellule, numero de ligne, ligne, type de cellule).

    Deux perimetres, deux regles (#23104) :

    - une cellule **code** est lue entierement -- une commande peut y etre
      prefixee (`!`, `%`, `$`) ou ecrite sur une ligne `python -m pip ...` ;
    - une cellule **markdown** n'est lue que sur ses **lignes-commandes**
      (`PIP_COMMAND_RE`, ancre en debut de ligne). C'est la restriction qui
      rend l'extension sure : une declaration d'installation logee en markdown
      *est* la commande que le lecteur execute, alors qu'une phrase qui la
      cite ne l'est pas.
    """
    for index, cell in enumerate(payload.get("cells", [])):
        cell_type = cell.get("cell_type") or ""
        if cell_type not in ("code", "markdown"):
            continue
        text = _cell_text(cell)
        for line_number, line in enumerate(text.splitlines(), start=1):
            if cell_type == "markdown" and not PIP_COMMAND_RE.match(line):
                continue
            yield index, line_number, line, cell_type


def pins_from_payload(payload: dict, manifest: Manifest) -> list[Pin]:
    """Relève les epinglages dans un carnet deja charge en memoire."""
    nuget_ids = {
        lib.id.lower(): lib.id
        for lib in manifest.libraries.values()
        if lib.ecosystem == "nuget"
    }
    pip_ids = {
        lib.id.lower(): lib.id
        for lib in manifest.libraries.values()
        if lib.ecosystem == "pip"
    }
    # Le provisionnement etranger est cable PAR BIBLIOTHEQUE : les motifs
    # vivent au manifeste, dans `foreign_provisioning`, quel que soit
    # l'ecosysteme de la bibliotheque. Un cable dur sur `ecosystem ==
    # "tweety"` laissait tous les autres motifs muets.
    provisioning_libs = [
        lib for lib in manifest.libraries.values() if lib.foreign_provisioning
    ]
    symbol_owners = {
        lib.local_symbol: lib for lib in manifest.libraries.values() if lib.local_symbol
    }
    pins: list[Pin] = []
    for cell_index, line_number, line, cell_type in _declaration_lines(payload):
        # Redeclaration locale d'un symbole que l'organe de serie possede.
        for symbol, lib in symbol_owners.items():
            match = re.match(
                rf"^\s*{re.escape(symbol)}\s*=\s*[\"']([^\"']+)[\"']", line
            )
            if match:
                pins.append(
                    Pin(
                        lib.id,
                        _norm_version(match.group(1)),
                        "local_const",
                        cell_index,
                        line.strip(),
                        line_no=line_number,
                    )
                )
        for match in NUGET_PIN_RE.finditer(line):
            lib_id = nuget_ids.get(match.group(1).lower())
            if lib_id is None:
                continue
            # Version absente : epinglage flottant. Il est signale, pas jete.
            version = _norm_version(match.group(2)) if match.group(2) else ""
            pins.append(
                Pin(
                    lib_id,
                    version,
                    "nuget",
                    cell_index,
                    line.strip(),
                    line_no=line_number,
                )
            )
        for match in PIP_PIN_RE.finditer(line):
            lib_id = pip_ids.get(match.group(1).lower())
            if lib_id is None:
                continue
            # Version absente : epinglage flottant (`pip install mealpy`),
            # signale comme tel -- cf #23086 et la relecture #23079.
            version = _norm_version(match.group(2) or "")
            pins.append(
                Pin(
                    lib_id,
                    version,
                    "pip",
                    cell_index,
                    line.strip(),
                    line_no=line_number,
                    cell_type=cell_type,
                )
            )
        for lib in provisioning_libs:
            for pattern in lib.foreign_provisioning:
                match = re.search(pattern["pattern"], line, re.IGNORECASE)
                if match:
                    version = match.group(1) if match.groups() else ""
                    pins.append(
                        Pin(
                            lib.id,
                            _norm_version(version),
                            "provisioning",
                            cell_index,
                            line.strip(),
                            line_no=line_number,
                        )
                    )
    return pins


def _relative_to_repo(notebook: Path, repo_root: Path) -> str:
    """Chemin relatif au depot ; le chemin absolu si le carnet est hors depot.

    Un carnet hors du depot est valide pour l'organe (verification d'un
    carnet local) : il ne doit pas faire echouer l'outil sur une
    `ValueError` de `relative_to`.
    """
    try:
        return notebook.relative_to(repo_root).as_posix()
    except ValueError:
        return notebook.as_posix()


def payload_from_file(notebook_path: Path) -> dict | None:
    """Charge un carnet sur disque ; None s'il est illisible."""
    try:
        return json.loads(notebook_path.read_text(encoding="utf-8", errors="replace"))
    except (OSError, json.JSONDecodeError):
        return None


def pins_from_file(notebook_path: Path, manifest: Manifest) -> list[Pin]:
    """Relève les epinglages d'un carnet sur disque (vide si illisible)."""
    try:
        payload = json.loads(notebook_path.read_text(encoding="utf-8", errors="replace"))
    except (OSError, json.JSONDecodeError):
        return []
    return pins_from_payload(payload, manifest)


# ---------------------------------------------------------------------------
# Binaires charges depuis un chemin (#23103)
# ---------------------------------------------------------------------------
#
# L'organe lit les epinglages (`#r "nuget: X, v"`, `pip install x==v`) et les
# motifs de provisionnement du manifeste. Il ne voyait pas le cas ou un carnet
# charge un binaire depuis un **chemin** : `#r "./libs/Tweety.jar"`,
# `#load "../scripts/setup.csx"`, `%classpath add jar`, `Add-Type -Path`,
# `clr.AddReference(".../X.dll")`, ou `pip install ./dist/x.whl`.
#
# L'artefact vit alors hors du depot -- ou dans un dossier ignore par git -- et
# la re-execution n'est pas reproductible depuis un clone. `#load` charge aussi
# des sources (`./Init.csx`) : meme defaut de reproductibilite, et l'organe les
# nomme « fichier source » plutot que « binaire ». C'est le cas
# declencheur de l'organe (#23047) : couvert jusqu'ici par un motif **declare
# au manifeste**, donc seulement pour les motifs connus.
#
# Trois classements, un seul est un defaut :
#   - **sous-module** : legitime (#23103, cas a). Le binaire se produit dans un
#     depot du cluster dont le pointeur est epingle dans le parent -- c'est le
#     cas des DLL `MetaGeneticSharp`, et le signaler serait un faux positif
#     permanent ;
#   - **versionne** : legitime (#23103, point 1, « artefact versionne dans le
#     depot »). Un fichier suivi par git est present apres un clone ;
#   - **hors depot** ou **non versionne** : la re-execution n'est pas
#     reproductible. Le constat tombe, sauf mecanisme de reproduction declare
#     dans le carnet -- une URL qui nomme l'artefact **et** une empreinte
#     (#23103, point 3).

# Formes de chargement portant un chemin. Le motif ne decide pas qu'un
# argument est un chemin : un identifiant de paquet (`nuget: IKVM, 8.15.0`) ou
# un nom d'assembly nu (`System.Text.Json`) traverse les memes formes. C'est
# `_looks_like_a_path` qui tranche.
_BINARY_LOAD_FORMS: tuple[tuple[str, re.Pattern], ...] = (
    ("#r", re.compile(r'#r\s+"(?!nuget:)([^"]+)"', re.IGNORECASE)),
    ("#load", re.compile(r'#load\s+"([^"]+)"', re.IGNORECASE)),
    (
        "%classpath",
        re.compile(r"%classpath\s+add\s+(?:jar|dll)\s+[\"']?([^\s\"';]+)", re.IGNORECASE),
    ),
    (
        "Add-Type",
        re.compile(
            r"Add-Type\s+-(?:Path|LiteralPath)\s+[\"']?([^\s\"';]+)", re.IGNORECASE
        ),
    ),
    (
        "clr.AddReference",
        re.compile(r"clr\.AddReference\s*\(\s*[\"']([^\"']+)[\"']", re.IGNORECASE),
    ),
    (
        "Assembly.Load",
        re.compile(
            r"(?:Assembly\.Load(?:File|From)|AssemblyName\.GetAssemblyName)"
            r"\s*\(\s*@?[\"']([^\"']+)[\"']",
            re.IGNORECASE,
        ),
    ),
    (
        "pip-fichier",
        re.compile(
            r"^\s*(?:[%!$]\s*)?"
            + _PIP_INSTALL
            + r"\s+(?:--?\S+\s+)*[\"']?([^\s\"']+\.(?:whl|tar\.gz|zip))\b",
            re.IGNORECASE,
        ),
    ),
)

# Extensions qui font d'un argument nu un chemin sans separateur
# (`#r "Tweety.jar"`). Un argument sans separateur ni extension est un nom
# d'assembly, pas un fichier.
_BINARY_EXTENSIONS = (".dll", ".exe", ".jar", ".so", ".dylib", ".whl", ".nupkg")

# Extensions de source. `#load` charge aussi des fichiers source (`./Init.csx`) :
# la non-reproductibilite est la meme, mais le motif ne doit pas annoncer un
# binaire la ou le lecteur execute un fichier C#.
_SOURCE_EXTENSIONS = (".cs", ".csx", ".fs", ".fsx", ".py", ".lean", ".jl")

# Chemins ancres : POSIX (`/opt/...`), Windows (`C:/...`) et UNC (`//srv/...`).
# Backslashes normalises en `/` avant le test, donc `C:\...` ne s'ecrit pas.
_ABSOLUTE_PATH_RE = re.compile(r"^(?:/|[A-Za-z]:/|//)")

# Prefixes qui designent un dossier utilisateur ou temporaire : ils ne peuvent
# pas resoudre dans le depot, et l'organe ne cherche pas a les developper.
_HOME_PREFIX_RE = re.compile(
    r"^(?:~|\$HOME|\$\{HOME\}|\$env:"
    r"|%(?:USERPROFILE|HOMEPATH|APPDATA|LOCALAPPDATA|TEMP|TMP|USERNAME)%)",
    re.IGNORECASE,
)

# Mecanisme de reproduction declare dans le carnet (#23103, point 3).
_URL_RE = re.compile(r"https?://[^\s\"'<>)\]`]+", re.IGNORECASE)
_CHECKSUM_RE = re.compile(
    r"sha-?256|sha256|Get-FileHash|hashlib\.(?:sha256|sha1|md5)|--checksum",
    re.IGNORECASE,
)
_SHA256_HEX_RE = re.compile(r"^[0-9a-fA-F]{64}$")
# Meme digest, mais cherche dans le texte libre d'une cellule (la forme
# historique #24520 le declare a cote de l'URL, pas dans un champ JSON).
_SHA256_DIGEST_RE = re.compile(r"(?<![0-9a-fA-F])[0-9a-fA-F]{64}(?![0-9a-fA-F])")
_REPRODUCTION_DIRECTIVE_RE = re.compile(
    r"<!--\s*reproduction\s*:\s*(\{.*?\})\s*-->", re.DOTALL
)
_REPRODUCTION_ARTIFACT_RE = re.compile(r"^[^\s/]+/[^\s]+$")

_SUBMODULE_CACHE: dict[str, list[str]] = {}


def _looks_like_a_path(value: str) -> bool:
    """L'argument est-il un chemin, ou un nom d'assembly ?

    `#r "System.Text.Json"` reference une assembly par son nom : ce n'est pas
    un chargement depuis un chemin, et l'organe n'a rien a en dire.
    `#r "./libs/Tweety.jar"` en est un.
    """
    text = value.strip()
    if not text:
        return False
    if "/" in text or "\\" in text:
        return True
    return text.lower().endswith(_BINARY_EXTENSIONS)


def _artifact_label(name: str) -> str:
    """Nomme l'artefact charge : « fichier source » ou « binaire ».

    `#load` charge les deux (`./Init.csx` autant que `./lib.dll`). Le constat
    reste le meme -- le chemin n'est pas reproductible -- mais annoncer « le
    binaire » pour un fichier C# serait faux dans le rapport.
    """
    return "fichier source" if name.lower().endswith(_SOURCE_EXTENSIONS) else "binaire"


def _is_under(root: Path, candidate: Path) -> bool:
    """`candidate` est-il sous `root` ?

    Comparaison de chaines normalisees : `Path.is_relative_to` compare les
    composants a la casse pres, et `D:/dev` contre `d:/dev` rendrait un faux
    « hors depot » sur Windows.
    """
    root_text = os.path.normcase(str(root)).replace("\\", "/").rstrip("/")
    candidate_text = os.path.normcase(str(candidate)).replace("\\", "/").rstrip("/")
    return candidate_text == root_text or candidate_text.startswith(root_text + "/")


def _under_child(relative: str, roots: list[str]) -> str | None:
    """Racine dont `relative` est un descendant (comparaison par segment)."""
    for root in roots:
        if relative == root or relative.startswith(root + "/"):
            return root
    return None


def submodule_paths(repo_root: Path) -> list[str]:
    """Chemins des sous-modules declares dans `.gitmodules`, caches par depot.

    Un binaire produit par un sous-module est legitime (#23103, cas a) : il se
    commite dedans, se pousse, puis le pointeur parent est bumpe. Le signaler
    rendrait un faux positif permanent sur les DLL des sous-modules.
    """
    key = str(repo_root)
    cached = _SUBMODULE_CACHE.get(key)
    if cached is not None:
        return cached
    code, out, _err = _git(
        repo_root, ["config", "-f", ".gitmodules", "--get-regexp", r"^submodule\..*\.path$"]
    )
    paths: list[str] = []
    if code == 0:
        for line in out.splitlines():
            parts = line.split(None, 1)
            if len(parts) == 2 and parts[1].strip():
                paths.append(parts[1].strip().replace("\\", "/").strip("/"))
    _SUBMODULE_CACHE[key] = paths
    return paths


def _classify_path(
    raw: str, notebook_dir: Path, repo_root: Path
) -> tuple[str, str, str]:
    """Classe un chemin : (`hors-depot` | `depot`, resolu, relatif au depot).

    Un chemin relatif se resout depuis le **dossier du carnet**, pas depuis la
    racine du depot : c'est la resolution que fait le lecteur, et un `../..`
    qui sort du depot est exactement le cas que l'organe doit voir. Les chemins
    ancres et ceux qui passent par un dossier utilisateur sont classes sans
    resolution -- ils ne peuvent pas tomber dans le depot.
    """
    text = raw.strip().strip("\"'").replace("\\", "/")
    if not text:
        return "hors-depot", "", ""
    if _HOME_PREFIX_RE.match(text):
        return "hors-depot", text, ""
    if _ABSOLUTE_PATH_RE.match(text):
        candidate = Path(text)
    else:
        candidate = notebook_dir / text
    try:
        resolved = candidate.resolve()
    except OSError:
        resolved = candidate
    if _is_under(repo_root, resolved):
        return "depot", resolved.as_posix(), resolved.relative_to(repo_root).as_posix()
    return "hors-depot", resolved.as_posix(), ""


def _tracked_paths(repo_root: Path, relatives: list[str]) -> set[str]:
    """Sous-ensemble de `relatives` suivi par git.

    Un fichier suivi est present apres un clone : c'est le cas legitime
    « artefact versionne dans le depot » (#23103, point 1). Un echec de git ne
    rend pas « rien n'est suivi » -- il rend l'ensemble vide, qui ne peut que
    produire des constats, jamais en eteindre un.
    """
    if not relatives:
        return set()
    code, out, _err = _git(repo_root, ["ls-files", "--"] + relatives)
    if code != 0:
        return set()
    return {line.strip().replace("\\", "/") for line in out.splitlines() if line.strip()}


def _declared_reproduction(payload: dict) -> dict[str, dict]:
    """Déclarations de reproduction, avec empreinte par artefact.

    Trois formes coexistent, toutes rendues par clé de nom d'artefact :

    - URL dont la queue nomme l'artefact, avec empreinte dans la même cellule
      (contrat de #24520). Cette forme historique exige désormais **les deux** :
      un marqueur de mécanisme (``sha256``, ``Get-FileHash``, ``hashlib.sha256``,
      ``--checksum``) **et** un digest de 64 hexadécimaux. Sans le digest, un
      ``SHA256 = "abc123"`` satisfaisait la forme faible et court-circuitait la
      directive ``archive``, qui exige un SHA-256 valide (#24943) ;
    - directive ``<!-- reproduction: {...} -->`` de type ``archive`` : URL,
      version, ``entry`` et SHA-256 de l'entrée extraite ;
    - directive de type ``build`` : ``command`` et ``project`` versionné.

    ``artifact`` vaut ``<classe>/<nom>`` : ``archive/QuikGraph.dll`` ou
    ``build/MyIA.AI.Shared.dll``. Cette clé explicite évite d'apparier une
    archive par la queue de son URL. Une directive mal formée ne rend jamais
    l'artefact reproductible.
    """
    declarations: dict[str, dict] = {}
    for cell in payload.get("cells", []) or []:
        if (cell.get("cell_type") or "") not in ("code", "markdown"):
            continue
        text = _cell_text(cell)
        # Forme historique (#24520) : le marqueur seul ne suffit pas, il doit
        # etre accompagne d'un digest. `SHA256 = "abc123"` declarait sinon une
        # empreinte sans en porter une, et la forme faible contournait la
        # directive `archive` qui, elle, exige 64 hexadecimaux (#24943).
        has_checksum = bool(_CHECKSUM_RE.search(text)) and bool(
            _SHA256_DIGEST_RE.search(text)
        )
        for match in _URL_RE.finditer(text):
            url = match.group(0).rstrip(".,;:")
            tail = url.rsplit("/", 1)[-1].split("?", 1)[0].split("#", 1)[0]
            if tail:
                declarations[tail] = {
                    "kind": "url",
                    "declared": True,
                    "checksum": declarations.get(tail, {}).get("checksum", False)
                    or has_checksum,
                    "reproducible": has_checksum
                    or declarations.get(tail, {}).get("reproducible", False),
                }
        for match in _REPRODUCTION_DIRECTIVE_RE.finditer(text):
            try:
                directive = json.loads(match.group(1))
            except json.JSONDecodeError:
                continue
            if not isinstance(directive, dict):
                continue
            kind = directive.get("kind")
            key = directive.get("artifact", "")
            if kind not in ("archive", "build") or not _REPRODUCTION_ARTIFACT_RE.fullmatch(key):
                continue
            declared = False
            reproducible = False
            command = ""
            project = ""
            if kind == "archive":
                url = directive.get("url", "")
                entry = directive.get("entry", "")
                checksum = directive.get("sha256", "")
                declared = bool(
                    isinstance(url, str)
                    and url.startswith(("https://", "http://"))
                    and isinstance(entry, str)
                    and entry
                    and directive.get("version")
                )
                reproducible = bool(
                    declared
                    and isinstance(checksum, str)
                    and _SHA256_HEX_RE.fullmatch(checksum)
                    and key.rsplit("/", 1)[-1] == entry.rsplit("/", 1)[-1]
                )
            else:
                command = directive.get("command", "")
                project = directive.get("project", "")
                declared = bool(command and project)
                # Le suivi par git est vérifié dans binary_findings, qui
                # connaît repo_root ; une recette hors du dépôt n'est jamais
                # une preuve de reproductibilité.
                reproducible = declared
            previous = declarations.get(key, {})
            # Une recette incomplète postérieure ne doit pas casser une preuve
            # complète déjà lue ; dans le cas inverse, la nouvelle preuve gagne.
            if not previous.get("reproducible", False) or reproducible:
                declarations[key] = {
                    "kind": kind,
                    "declared": declared or previous.get("declared", False),
                    "checksum": reproducible or previous.get("checksum", False),
                    "reproducible": reproducible
                    or previous.get("reproducible", False),
                    "project": project if kind == "build" else "",
                    "directive": directive,
                }
    return declarations


def _reproduction_matches(
    name: str, declarations: dict[str, dict], tracked: set[str]
) -> tuple[bool, bool]:
    """Retourne ``(déclaré, reproductible)`` sans confondre les classes."""
    direct = declarations.get(name)
    if direct and direct.get("reproducible", False):
        return True, True
    for prefix in ("archive", "build"):
        key = f"{prefix}/{name}"
        candidate = declarations.get(key)
        if not candidate:
            continue
        if prefix == "build":
            project = candidate.get("project", "")
            normalized = posixpath.normpath(project).strip("/")
            if normalized.startswith("../") or normalized not in tracked:
                return True, False
        return candidate.get("declared", False), candidate.get("reproducible", False)
    if direct:
        return direct.get("declared", False), False
    return False, False


@dataclass
class LoadedBinary:
    """Un chargement de binaire portant un chemin, et son classement."""

    path: str
    resolved: str
    relative: str
    form: str
    scope: str
    cell: int
    line_no: int
    line: str


def binary_loads(
    notebook: str, payload: dict, repo_root: Path
) -> list[LoadedBinary]:
    """Releve et classe les chargements de binaires d'un carnet (#23103).

    Le balayage porte sur les seules cellules **code** : une forme de
    chargement ecrite en markdown est de la prose qui la cite, pas une ligne
    que le lecteur execute -- c'est la meme restriction que pour les
    declarations d'installation (`_declaration_lines`).
    """
    candidates: list[tuple[str, str, int, int, str]] = []
    for cell_index, cell in enumerate(payload.get("cells", []) or []):
        if (cell.get("cell_type") or "") != "code":
            continue
        text = _cell_text(cell)
        for line_number, line in enumerate(text.splitlines(), start=1):
            for form, pattern in _BINARY_LOAD_FORMS:
                for match in pattern.finditer(line):
                    raw = match.group(1)
                    if not _looks_like_a_path(raw):
                        continue
                    candidates.append((raw, form, cell_index, line_number, line.strip()))
    if not candidates:
        return []

    notebook_dir = (repo_root / notebook).parent
    submodules = submodule_paths(repo_root)
    loads: list[LoadedBinary] = []
    for raw, form, cell_index, line_number, line in candidates:
        scope, resolved, relative = _classify_path(raw, notebook_dir, repo_root)
        loads.append(
            LoadedBinary(
                path=raw,
                resolved=resolved,
                relative=relative,
                form=form,
                scope=scope,
                cell=cell_index,
                line_no=line_number,
                line=line,
            )
        )

    # Un fichier dans le depot peut etre versionne (legitime) ou ignore par
    # git (absent apres un clone) : la distinction demande git, donc une seule
    # passe pour tous les chemins internes du carnet.
    in_repo = sorted({load.relative for load in loads if load.scope == "depot"})
    tracked = _tracked_paths(repo_root, in_repo)
    for load in loads:
        if load.scope != "depot":
            continue
        if _under_child(load.relative, submodules):
            load.scope = "sous-module"
        elif load.relative in tracked:
            load.scope = "versionne"
        else:
            load.scope = "non-versionne"
    return loads


def binary_findings(
    notebook: str, payload: dict, repo_root: Path
) -> list[dict]:
    """Constats sur les binaires charges depuis un chemin (#23103)."""
    loads = binary_loads(notebook, payload, repo_root)
    if not loads:
        return []
    declared_names = _declared_reproduction(payload)
    # Les recettes nomment un projet qui doit être versionné. Il n'est pas
    # nécessairement chargé par le carnet : cette liste complète donc les
    # chemins de chargement utilisés plus haut.
    projects = [
        value.get("project", "")
        for key, value in declared_names.items()
        if key.startswith("build/") and value.get("project")
    ]
    tracked_projects = _tracked_paths(repo_root, projects)
    findings: list[dict] = []
    seen: set[tuple] = set()
    for load in loads:
        if load.scope in ("sous-module", "versionne"):
            continue
        name = load.resolved.rsplit("/", 1)[-1] or load.path
        declared, reproducible = _reproduction_matches(
            name, declared_names, tracked_projects
        )
        if declared and reproducible:
            # Mecanisme de reproduction declare : rien a signaler.
            continue
        reproduction_hint = (
            "declarer une URL et l'empreinte de l'artefact, ou une directive "
            "structuree : URL + version + entree + empreinte pour une archive, "
            "commande + projet suivi par git pour un build"
        )
        incomplete_reason = (
            f"une reproduction de `{name}` est declaree, mais sa preuve est "
            "incomplete : une archive exige URL, version, entree et empreinte "
            "de cette entree ; un build exige une commande et son projet suivi "
            "par git ; l'ancienne forme exige une URL et une empreinte dans la "
            "meme cellule"
        )
        if load.scope == "hors-depot":
            kind = "binary_hors_depot" if not declared else "binary_sans_empreinte"
            reason = (
                f"chargement depuis `{load.resolved}` par `{load.form}` : hors du "
                f"depot, le {_artifact_label(name)} n'existe pas apres un clone et la "
                f"re-execution n'est pas reproductible ; aucun sous-module ne le porte, "
                f"et il faut {reproduction_hint}"
                if not declared
                else (
                    f"chargement depuis `{load.resolved}` par `{load.form}` : "
                    f"{incomplete_reason}"
                )
            )
        else:
            kind = "binary_non_versionne" if not declared else "binary_sans_empreinte"
            reason = (
                f"chargement depuis `{load.relative}` par `{load.form}` : le "
                f"{_artifact_label(name)} est dans le depot mais ignore par git, donc "
                f"absent apres un clone ; versionner l'artefact, ou {reproduction_hint}"
                if not declared
                else (
                    f"chargement depuis `{load.relative}` par `{load.form}` : "
                    f"{incomplete_reason}"
                )
            )
        key = (kind, load.resolved or load.path, load.form)
        if key in seen:
            continue
        seen.add(key)
        findings.append(
            {
                "notebook": notebook,
                "library": name,
                "kind": kind,
                "version": "",
                "canonical": "",
                "cell": load.cell,
                "line": load.line,
                "reason": reason,
                "path": load.resolved or load.path,
                "form": load.form,
            }
        )
    return findings


def delta_binary_findings(
    notebook: str, base_payload: dict | None, head_payload: dict, repo_root: Path
) -> list[dict]:
    """Constat binaire **introduit** par la PR (#23103).

    Un chemin non reproductible deja present dans la base n'est pas impute a la
    PR : c'est l'etat du carnet, il se lit au recensement (`--census`), pas au
    diff -- meme regle que `delta_mention_findings`. Seul un chargement ajoute
    (ou deplace vers un autre artefact) tombe ici, et la PR qui l'ajoute est
    bien celle qui doit le declarer.
    """
    head = binary_findings(notebook, head_payload, repo_root)
    if not head or base_payload is None:
        return head
    base_keys = {
        (item["path"], item["form"])
        for item in binary_findings(notebook, base_payload, repo_root)
    }
    return [
        item for item in head if (item["path"], item["form"]) not in base_keys
    ]


def _allowlisted(
    manifest: Manifest, lib_id: str, version: str, notebook: str
) -> str | None:
    """Retourne le motif d'allowlist si l'ecart est justifie pour ce carnet.

    Une entree sans motif non vide **n'eteint rien** : #23073 exige « une
    entree d'allowlist arbitree, avec son motif ecrit ». La validation
    `allowlist_errors` refuse le manifeste en amont (rc 2) ; le retour
    `None` ici est la seconde barriere, pour que le silence ne puisse pas
    revenir si la validation venait a etre contournee (relecture #23079
    point 1).
    """
    for entry in manifest.allowlist:
        if entry.get("library", "").lower() != lib_id.lower():
            continue
        if entry.get("version") and entry["version"] != version:
            continue
        notebooks = entry.get("notebooks") or []
        if notebooks and not any(
            notebook.endswith(n) or n.endswith(notebook) or notebook == n
            for n in notebooks
        ):
            continue
        reason = (entry.get("reason") or "").strip()
        return reason or None
    return None


def allowlist_errors(manifest: Manifest) -> list[str]:
    """Entrees d'allowlist inexploitables — le manifeste est alors refuse.

    L'allowlist est ce qui eteint un constat : une entree sans motif ecrit
    transforme l'organe en distributeur de vert. On refuse le manifeste
    (rc 2) plutot que d'ignorer l'entree en silence (#23079 point 1).
    """
    errors: list[str] = []
    for index, entry in enumerate(manifest.allowlist):
        if not (entry.get("library") or "").strip():
            errors.append(f"allowlist[{index}] : champ 'library' vide ou absent")
        if not (entry.get("reason") or "").strip():
            lib = (entry.get("library") or "?").strip() or "?"
            errors.append(
                f"allowlist[{index}] ({lib}) : motif absent ou vide "
                "-- une entree d'allowlist doit porter son motif ecrit"
            )
    return errors


def _finding(
    notebook: str,
    pin: Pin,
    canonical: str | None,
    kind: str,
    reason: str = "",
) -> dict:
    return {
        "notebook": notebook,
        "library": pin.library,
        "kind": kind,
        "version": pin.version,
        "canonical": canonical,
        "cell": pin.cell,
        "line": pin.line,
        "reason": reason,
    }


def state_findings(
    notebook: str,
    pins: list[Pin],
    manifest: Manifest,
    canonical_map: dict[str, str | None],
) -> list[dict]:
    """Constats sur l'ETAT d'un carnet : tout epinglage != canonique."""
    findings: list[dict] = []
    for pin in pins:
        lib = manifest.libraries[pin.library]
        canonical = canonical_map.get(pin.library)
        if pin.ecosystem in ("nuget", "pip") and not pin.version:
            # Epinglage flottant : la version n'est pas fixee (cf #23086).
            # Le cas pip compte aussi : le corpus installait mealpy sans
            # version (`pip install mealpy numpy matplotlib`), et l'organe
            # ne le voyait pas (relecture #23079, point 2).
            findings.append(
                _finding(notebook, pin, canonical, "pin_non_versionne",
                         FLOATING_PIN_REASON)
            )
            continue
        if pin.ecosystem == "provisioning":
            reason = ""
            for pattern in lib.foreign_provisioning:
                if re.search(pattern["pattern"], pin.line, re.IGNORECASE):
                    reason = pattern.get("reason", "")
                    break
            findings.append(_finding(notebook, pin, canonical, "foreign_provisioning", reason))
            continue
        if canonical is None:
            continue
        if compare_versions(pin.version, canonical) == 0:
            continue
        if _allowlisted(manifest, pin.library, pin.version, notebook):
            continue
        if compare_versions(pin.version, canonical) < 0:
            kind = "downgrade"
        else:
            kind = "unmanaged_upgrade"
        divergence = lib.divergences.get(pin.version)
        reason = (divergence or {}).get("reason", "")
        if divergence and divergence.get("decision") == "justified":
            kind = "divergence"
        findings.append(_finding(notebook, pin, canonical, kind, reason))
    return findings


def delta_findings(
    notebook: str,
    base_pins: list[Pin],
    head_pins: list[Pin],
    manifest: Manifest,
    canonical_map: dict[str, str | None],
) -> list[dict]:
    """Constats sur le DELTA base -> tete : ce que la PR introduit.

    Un epinglage deja present et non touche par la PR ne produit aucun
    constat : c'est une derive historique, que le recensement rapporte et que
    la convergence traite -- pas une regression introduite par la PR.
    """
    findings: list[dict] = []
    # Multiplicites, pas ensembles : un carnet peut porter DEUX versions de
    # la meme bibliotheque. Avec `previous == {pin.version}`, une base qui
    # porte `{8.14.0, 8.15.0}` ne reconnaissait aucun des deux epinglages
    # comme inchange -- la PR heritait donc d'un faux `downgrade` sur un
    # epinglage qu'elle n'avait pas touche (relecture #23079 point 5).
    base_counts: dict[str, Counter] = {}
    for pin in base_pins:
        if pin.ecosystem == "provisioning":
            continue
        base_counts.setdefault(pin.library, Counter())[pin.version] += 1
    seen: Counter = Counter()

    for pin in head_pins:
        if pin.ecosystem == "provisioning":
            # Le provisionnement etranger est signale sur l'etat : son
            # dommage se produit a l'execution, pas a l'edition.
            findings.extend(
                state_findings(notebook, [pin], manifest, canonical_map)
            )
            continue
        # Cet exemplaire existait-il deja en base, en meme nombre ? Les
        # occurrences au-dela du compte de base sont celles que la PR
        # ajoute ; les precedentes sont de la derive historique.
        key = (pin.library, pin.version)
        seen[key] += 1
        if seen[key] <= base_counts.get(pin.library, Counter())[pin.version]:
            continue
        canonical = canonical_map.get(pin.library)
        if canonical is None:
            continue
        if pin.ecosystem in ("nuget", "pip") and not pin.version:
            # Epinglage flottant : la version n'est pas fixee (cf #23086).
            # Le cas pip compte aussi : le corpus installait mealpy sans
            # version (`pip install mealpy numpy matplotlib`), et l'organe
            # ne le voyait pas (relecture #23079, point 2).
            findings.append(
                _finding(notebook, pin, canonical, "pin_non_versionne",
                         FLOATING_PIN_REASON)
            )
            continue
        if _allowlisted(manifest, pin.library, pin.version, notebook):
            continue
        if compare_versions(pin.version, canonical) == 0:
            continue
        if compare_versions(pin.version, canonical) < 0:
            kind = "downgrade"
        else:
            kind = "unmanaged_upgrade"
        divergence = manifest.libraries[pin.library].divergences.get(pin.version)
        reason = (divergence or {}).get("reason", "")
        if divergence and divergence.get("decision") == "justified":
            kind = "divergence"
        findings.append(_finding(notebook, pin, canonical, kind, reason))
    return findings


def _output_texts(cell: dict) -> list[str]:
    """Textes produits par une cellule : flux, resultats, erreurs."""
    texts: list[str] = []
    for output in cell.get("outputs", []) or []:
        kind = output.get("output_type")
        if kind == "stream":
            texts.append("".join(output.get("text", []) or []))
        elif kind in ("execute_result", "display_data"):
            data = output.get("data", {}) or {}
            texts.append("".join(data.get("text/plain", []) or []))
        elif kind == "error":
            texts.append(f"{output.get('ename', '')} {output.get('evalue', '')}")
    return texts


def _version_mentions(text: str, version: str) -> bool:
    """Vrai si `version` apparait dans `text` comme un jeton de version.

    Les gardes numeriques evitent qu'une version soit reconnue dans une autre :
    `3.0.5` ne doit pas matcher `13.0.5` ni `3.0.50`.
    """
    pattern = r"(?<![\d.])" + re.escape(version) + r"(?![\d.])"
    return re.search(pattern, text) is not None


# Version **chargee** relevee dans une sortie : au moins TROIS composantes
# numeriques. La notation scientifique (`2.22e-16`) et les metriques (`0.4014`)
# ne sont pas des versions : exiger trois composantes les ecarte, la ou un
# motif plus permissif les aurait confondues avec des versions -- cas mesure
# sur `3.2-Optimisateurs.ipynb` (`ecart max apres 1 pas NumPy vs torch =
# 2.22e-16`) et `3.3-Regularisation.ipynb` (`numpy=0.4014 | torch=0.4007`).
_OBSERVED_VERSION = r"(\d+\.\d+\.\d+(?:\.\d+)*(?:\+[0-9A-Za-z][0-9A-Za-z.+-]*)?)"


def _observed_version_re(library_id: str) -> re.Pattern:
    """Motif de releve de la version chargee d'une bibliotheque.

    Le nom peut etre suivi de `_version` (forme JSON
    `"torch_version": "2.14.0+cu126"`), d'un separateur (`torch 2.13.0`,
    `torch=2.8.0`, `torch : 2.6.0`) ou d'une fin de ligne. Le nom doit
    etre un mot entier : `torchvision` et `pytorch` ne sont pas `torch`.
    """
    return re.compile(
        r"(?<![A-Za-z0-9_])"
        + re.escape(library_id)
        + r"(?:[_-]?version)?"
        + r"[\"']?\s*(?::|=){0,2}\s*[\"']?"
        + _OBSERVED_VERSION,
        re.IGNORECASE,
    )


def _base_version(version: str) -> str:
    """Version sans le tag de construction local (`+cu126`).

    `2.14.0+cu126` est la **memere** release que `2.14.0`, pas une version
    inferieure : le comparateur de versions traite un suffixe `+` comme un
    marqueur de pre-publication, ce qui classerait `2.14.0+cu126` en dessous
    de `2.14.0` -- un faux recul.
    """
    return version.split("+", 1)[0]


def observed_versions_from_payload(
    payload: dict, manifest: Manifest
) -> dict[str, list[tuple[int, str, str]]]:
    """Versions **chargees** relevees dans les sorties commitees.

    Certaines bibliotheques n'apparaitrent dans aucune ligne d'epinglage :
    la serie RL declare `torch>=2.0` dans son `requirements.txt`, jamais dans
    une cellule, et la version reellement chargee ne se lit que dans les
    sorties commitees. L'observation est un **opt-in** (`observe_outputs`) :
    seules les bibliotheques declarees observees sont relevees.

    Les sorties seules sont balayees : une version ecrite dans la SOURCE est
    une intention, la mesure, c'est ce que le kernel a charge.

    Retourne, par bibliotheque, la liste des triplets `(cellule, ligne,
    version)` -- la ligne etant celle qui porte la version.
    """
    observed: dict[str, list[tuple[int, str, str]]] = {}
    for lib_id, lib in manifest.libraries.items():
        if not lib.observe_outputs:
            continue
        pattern = _observed_version_re(lib.id)
        occurrences: list[tuple[int, str, str]] = []
        for index, cell in enumerate(payload.get("cells", []) or []):
            for text in _output_texts(cell):
                for line in text.splitlines():
                    for match in pattern.finditer(line):
                        version = _base_version(_norm_version(match.group(1)))
                        occurrences.append((index, line.strip(), version))
        if occurrences:
            observed[lib_id] = occurrences
    return observed


def _mention_finding(
    notebook: str,
    library: str,
    version: str,
    canonical: str | None,
    cell: int,
    where: str,
    text: str,
) -> dict:
    extrait = text.strip()[:160]
    return {
        "notebook": notebook,
        "library": library,
        "kind": "mention_residuelle",
        "version": version,
        "canonical": canonical,
        "cell": cell,
        "line": extrait,
        "reason": (
            f"mention de la version perimee ({where}) : {extrait}"
        ),
    }


def mention_findings(
    notebook: str,
    payload: dict,
    manifest: Manifest,
    canonical_map: dict[str, str | None],
) -> list[dict]:
    """Constats sur les MENTIONS de version perimee hors ligne d'epinglage.

    L'organe lit la ligne d'epinglage ; il ne lit pas le reste du carnet. Un
    carnet peut donc etre « aligne sur le manifeste » tout en annonçant
    l'ancienne version dans sa prose ou dans ses sorties commitees -- c'est
    exactement ce que la premiere tranche de convergence a montre (sept carnets
    de la serie SemanticWeb, #23083) : l'epinglage etait a jour, le corpus
    mentait.

    Le perimetre est borne : une mention n'est signalee que dans un carnet qui
    **declare un epinglage** de cette bibliotheque, et **toute ligne
    d'epinglage est exclue**, quelle que soit la bibliotheque qu'elle epingle
    (elle porte la version qu'elle fixe, ce n'est pas une mention).
    Les sorties sont en revanche balayees en entier : le bandeau « Installed
    Packages » d'un kernel affiche la version reellement chargee, et c'est
    souvent la que l'ecart se lit.
    """
    findings: list[dict] = []
    pins = pins_from_payload(payload, manifest)
    declared = {pin.library for pin in pins}
    if not declared:
        return findings

    # Versions divergentes susceptibles d'apparaitre en prose.
    targets: dict[str, set[str]] = {}
    for lib_id, lib in manifest.libraries.items():
        if lib_id not in declared:
            continue
        canonical = canonical_map.get(lib_id)
        versions = {
            version
            for version in lib.divergences
            if canonical is None or compare_versions(version, canonical) != 0
        }
        if versions:
            targets[lib_id] = versions
    if not targets:
        return findings

    # Lignes d'epinglage : exclues du balayage des sources -- **toutes
    # bibliotheques confondues**. Une ligne d'epinglage porte la version
    # qu'elle epingle ; la rapporter comme une « mention » de la version
    # perimee d'une AUTRE bibliotheque est un faux positif. Cas mesure : deux
    # epinglages voisins dans la meme cellule (`#r "nuget: IKVM, 8.14.0"` et
    # `#r "nuget: IKVM.Image, 8.14.0"`) faisaient deux constats
    # `mention_residuelle` qui etaient precisement les lignes d'epinglage
    # (relecture #23079, point 1). La cle de l'exclusion est donc le couple
    # (cellule, ligne), sans le nom de la bibliotheque.
    pin_lines: set[tuple[int, int]] = set()
    for pin in pins:
        pin_lines.add((pin.cell, pin.line_no))

    for lib_id, versions in sorted(targets.items()):
        canonical = canonical_map.get(lib_id)
        for version in sorted(versions, key=version_key):
            if _allowlisted(manifest, lib_id, version, notebook):
                continue
            for index, cell in enumerate(payload.get("cells", []) or []):
                for line_number, line in enumerate(
                    _cell_text(cell).splitlines(), start=1
                ):
                    if (index, line_number) in pin_lines:
                        continue
                    if _version_mentions(line, version):
                        findings.append(
                            _mention_finding(
                                notebook, lib_id, version, canonical,
                                index, "source", line,
                            )
                        )
                for text in _output_texts(cell):
                    for line in text.splitlines():
                        if _version_mentions(line, version):
                            findings.append(
                                _mention_finding(
                                    notebook, lib_id, version, canonical,
                                    index, "sortie", line,
                                )
                            )
    return findings


def delta_mention_findings(
    notebook: str,
    base_payload: dict | None,
    head_payload: dict,
    manifest: Manifest,
    canonical_map: dict[str, str | None],
) -> list[dict]:
    """Mentions introduites par la PR : celles que la base ne portait pas.

    Meme semantique que les epinglages : une mention deja presente et non
    touchee par la PR est une derive historique -- le recensement la
    rapporte, la convergence la traite, la PR ne la porte pas.
    """
    head = mention_findings(notebook, head_payload, manifest, canonical_map)
    if base_payload is None:
        return head
    base = mention_findings(notebook, base_payload, manifest, canonical_map)
    base_keys = {
        (f["library"], f["version"], f["cell"], f["line"]) for f in base
    }
    return [
        f
        for f in head
        if (f["library"], f["version"], f["cell"], f["line"]) not in base_keys
    ]


def _git(repo_root: Path, args: list[str]) -> tuple[int, str, str]:
    proc = subprocess.run(
        ["git", "-C", str(repo_root)] + args,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    return proc.returncode, proc.stdout, proc.stderr


def _merge_base(repo_root: Path, left: str, right: str) -> str | None:
    code, out, _err = _git(repo_root, ["merge-base", left, right])
    if code != 0:
        return None
    return out.strip() or None


def _split_range(revision_range: str) -> tuple[str, str]:
    """Decoupe un intervalle git en (gauche, droite)."""
    if "..." in revision_range:
        left, right = revision_range.split("...", 1)
        return left.strip(), right.strip()
    if ".." in revision_range:
        left, right = revision_range.split("..", 1)
        return left.strip(), right.strip()
    return "", revision_range.strip()


def changed_notebooks(repo_root: Path, revision_range: str) -> tuple[list[Path], str | None]:
    """Liste les carnets modifies dans un intervalle git.

    Le point de comparaison est le **merge-base** : `git diff base...head`
    lit l'apport de la branche, et non l'ensemble des differences d'arbres
    (cf #23070 : la lecture en deux points attribue a la PR les changements
    venus de la base).
    """
    left, right = _split_range(revision_range)
    base = _merge_base(repo_root, left, right) if left else None
    start = base or left
    code, out, err = _git(
        repo_root,
        ["diff", "--name-only", "--diff-filter=ACMR", f"{start}...{right}"],
    )
    if code != 0:
        code, out, err = _git(
            repo_root,
            ["diff", "--name-only", "--diff-filter=ACMR", start, right],
        )
    if code != 0:
        raise RuntimeError(f"git diff en echec sur {revision_range} : {err.strip()}")
    paths = []
    for line in out.splitlines():
        line = line.strip()
        if line.endswith(".ipynb"):
            candidate = repo_root / line
            if candidate.is_file():
                paths.append(candidate)
    return paths, base


class BaseReadError(RuntimeError):
    """La base ne peut pas etre LUE pour ce carnet -- ce n'est pas une absence."""


def notebook_at(repo_root: Path, revision: str | None, relative: str) -> dict | None:
    """Charge le carnet tel qu'il etait a une revision ; None s'il n'existait pas.

    « Absent de la base » et « lecture en echec » sont deux choses
    differentes, et les confondre coutait cher : la premiere est un carnet
    neuf (tous ses epinglages sont nouveaux), la seconde faisait degenerer le
    delta en etat, si bien que la derive historique rougissait sans cause
    nommee. La presence est donc mesuree separement (`cat-file -e`) avant la
    lecture ; une lecture qui echoue sur un carnet present leve
    `BaseReadError`, que l'appelant traduit en rc 2 (relecture #23079 point 6).
    """
    if not revision:
        return None
    present, _out, _err = _git(repo_root, ["cat-file", "-e", f"{revision}:{relative}"])
    if present != 0:
        return None
    code, out, err = _git(repo_root, ["show", f"{revision}:{relative}"])
    if code != 0:
        raise BaseReadError(
            f"{relative} a {revision} : git show a echoue ({err.strip()})"
        )
    try:
        return json.loads(out)
    except json.JSONDecodeError as exc:
        raise BaseReadError(
            f"{relative} a {revision} : JSON invalide ({exc})"
        ) from exc


def tracked_notebooks(repo_root: Path) -> list[Path]:
    """Liste les carnets suivis par git (les sous-modules ne sont pas des fichiers)."""
    code, out, _err = _git(repo_root, ["ls-files", "*.ipynb"])
    if code != 0:
        raise RuntimeError("git ls-files en echec")
    paths = []
    for line in out.splitlines():
        line = line.strip()
        if not line:
            continue
        candidate = repo_root / line
        if candidate.is_file():
            paths.append(candidate)
    return paths


def resolve_canonicals(
    manifest: Manifest, repo_root: Path
) -> tuple[dict[str, str | None], list[str]]:
    """Resout toutes les versions canoniques ; retourne (map, erreurs)."""
    canonicals: dict[str, str | None] = {}
    errors: list[str] = []
    for lib_id, lib in manifest.libraries.items():
        value, error = lib.resolve_canonical(repo_root)
        canonicals[lib_id] = value
        if error:
            errors.append(f"{lib_id} : {error}")
    return canonicals, errors


class CanonicalResolver:
    """Resout la canonique **applicable a un carnet**.

    Une bibliotheque sans `canonical_by_series` garde sa canonique unique.
    Une bibliotheque qui en declare resout la **plus longue** correspondance
    de prefixe de serie -- un prefixe long decrit une sous-serie plus fine
    que son parent -- puis retombe sur la canonique unique si aucune serie
    ne couvre le carnet.

    Les artefacts de serie sont lus **une fois** a la construction : le
    resultat ne depend pas du carnet, et le relire par carnet serait un
    gaspillage de lectures.
    """

    def __init__(self, manifest: Manifest, repo_root: Path):
        self.manifest = manifest
        self.repo_root = repo_root
        self.flat, self.errors = resolve_canonicals(manifest, repo_root)
        self._series: dict[str, list[tuple[str, str | None]]] = {}
        for lib_id, lib in manifest.libraries.items():
            if not lib.canonical_by_series:
                continue
            entries, errors = lib.resolve_series_canonicals(repo_root)
            self._series[lib_id] = entries
            self.errors.extend(errors)

    def for_notebook(self, lib_id: str, relative: str) -> str | None:
        """Canonique applicable au carnet `relative` (chemin relatif au depot)."""
        entries = self._series.get(lib_id)
        if not entries:
            return self.flat.get(lib_id)
        key = series_path(relative)
        best: tuple[str, str | None] | None = None
        for prefix, value in entries:
            if prefix and not (key == prefix or key.startswith(prefix + "/")):
                continue
            if best is None or len(prefix) > len(best[0]):
                best = (prefix, value)
        if best is None:
            return self.flat.get(lib_id)
        return best[1]

    def series_for(self, lib_id: str, relative: str) -> str:
        """Prefixe de serie qui gouverne le carnet (vide si aucun)."""
        entries = self._series.get(lib_id)
        if not entries:
            return ""
        key = series_path(relative)
        best = ""
        for prefix, _value in entries:
            if prefix and not (key == prefix or key.startswith(prefix + "/")):
                continue
            if len(prefix) > len(best):
                best = prefix
        return best


def observed_findings(
    notebook: str,
    payload: dict,
    manifest: Manifest,
    resolver: CanonicalResolver,
) -> list[dict]:
    """Constats sur la version **reellement chargee** d'une bibliotheque.

    L'epinglage declare ce que le carnet *demande* ; la sortie commitee dit
    ce que le kernel a *charge*. Les deux peuvent diverger -- c'est exactement
    le recul que #23941 a laisse passer : le carnet RL-01c a ete re-execute
    sous torch 2.9.0 sans qu'aucune garde ne le voie, parce que torch n'etait
    pas au manifeste.

    Le constat porte sur la **sortie** ; une version ecrite dans la source
    n'est pas une mesure de ce qui a ete charge.
    """
    findings: list[dict] = []
    observed = observed_versions_from_payload(payload, manifest)
    for lib_id, occurrences in sorted(observed.items()):
        lib = manifest.libraries[lib_id]
        canonical = resolver.for_notebook(lib_id, notebook)
        if canonical is None:
            # Aucune canonique pour cette serie : l'organe constate la
            # version, il ne la juge pas.
            continue
        for cell, line, version in occurrences:
            # La canonique d'une serie **observee** est un **plancher** : la
            # serie tourne legitimement sous plusieurs versions voisines (2.13
            # et 2.14 dans la serie RL, 2.13 a 2.14.1 dans 04-Vision), et elle
            # converge vers le haut. Seul une version **inferieure** au
            # plancher est un recul ; une version superieure n'est pas un
            # defaut, c'est une serie qui avance.
            if compare_versions(version, canonical) >= 0:
                continue
            if _allowlisted(manifest, lib_id, version, notebook):
                continue
            kind = "downgrade"
            divergence = lib.divergences.get(version)
            reason = (divergence or {}).get("reason", "")
            if divergence and divergence.get("decision") == "justified":
                kind = "divergence"
            findings.append(
                {
                    "notebook": notebook,
                    "library": lib_id,
                    "kind": kind,
                    "version": version,
                    "canonical": canonical,
                    "cell": cell,
                    "line": line[:160],
                    "reason": reason
                    or (
                        f"version chargee relevee dans les sorties commitees "
                        f"({version}) differente de la canonique de la serie "
                        f"({canonical})"
                    ),
                }
            )
    return findings


def delta_observed_findings(
    notebook: str,
    base_payload: dict | None,
    head_payload: dict,
    manifest: Manifest,
    resolver: CanonicalResolver,
) -> list[dict]:
    """Versions chargees **introduites** par la PR.

    Meme semantique que les epinglages : une version deja chargee en base et
    non touchee par la PR est une derive historique -- le recensement la
    rapporte, la convergence la traite, la PR ne la porte pas. Seul compte
    le constat sur une version que la base ne portait pas.
    """
    head = observed_findings(notebook, head_payload, manifest, resolver)
    if base_payload is None:
        return head
    base_observed = observed_versions_from_payload(base_payload, manifest)
    base_versions = {
        lib_id: {version for _cell, _line, version in occurrences}
        for lib_id, occurrences in base_observed.items()
    }
    return [
        finding
        for finding in head
        if finding["version"]
        not in base_versions.get(finding["library"], set())
    ]


def run_census(repo_root: Path, manifest: Manifest) -> dict:
    """Recensement repo-wide : table de dispersion + classement des ecarts."""
    resolver = CanonicalResolver(manifest, repo_root)
    canonicals, errors = resolver.flat, resolver.errors
    dispersion: dict[str, dict[str, list[str]]] = {}
    floating: dict[str, list[str]] = {}
    observed_dispersion: dict[str, dict[str, list[str]]] = {}
    below_canonical: list[dict] = []
    unreadable: list[str] = []
    binaries: list[dict] = []
    for notebook in tracked_notebooks(repo_root):
        relative = _relative_to_repo(notebook, repo_root)
        payload = payload_from_file(notebook)
        if payload is None:
            # Carnet illisible : il est **nomme**, pas compte comme un carnet
            # sans epinglage. `pins_from_file` rendait `[]` dans les deux cas,
            # et le recensement ne pouvait donc pas distinguer « aucun
            # epinglage » de « carnet illisible » (relecture #23079, point 3).
            unreadable.append(relative)
            continue
        # Chargements de binaires depuis un chemin (#23103) : le recensement
        # est le seul endroit ou la mesure porte sur TOUT le corpus, et c'est
        # cette mesure que l'issue demande.
        binaries.extend(binary_findings(relative, payload, repo_root))
        for pin in pins_from_payload(payload, manifest):
            if pin.ecosystem == "provisioning":
                continue
            if not pin.version:
                # Epinglage flottant : compte a part (cf #23086).
                bucket_f = floating.setdefault(pin.library, [])
                if relative not in bucket_f:
                    bucket_f.append(relative)
                continue
            bucket = dispersion.setdefault(pin.library, {})
            bucket.setdefault(pin.version, [])
            if relative not in bucket[pin.version]:
                bucket[pin.version].append(relative)
        # Versions **chargees** (torch, numpy) : elles ne sont pas declarees
        # par une ligne d'epinglage, elles se lisent dans les sorties
        # commitees. Le recensement les range par version ET signale les
        # carnets **en dessous** de la canonique de leur serie.
        for lib_id, occurrences in observed_versions_from_payload(
            payload, manifest
        ).items():
            canonical = resolver.for_notebook(lib_id, relative)
            series = resolver.series_for(lib_id, relative)
            bucket_o = observed_dispersion.setdefault(lib_id, {})
            for _cell, _line, version in occurrences:
                bucket_o.setdefault(version, [])
                if relative not in bucket_o[version]:
                    bucket_o[version].append(relative)
                if canonical is None:
                    continue
                if compare_versions(version, canonical) >= 0:
                    continue
                below_canonical.append(
                    {
                        "notebook": relative,
                        "library": lib_id,
                        "version": version,
                        "canonical": canonical,
                        "series": series,
                    }
                )

    table = []
    phantoms: list[dict] = []
    for lib_id in sorted(manifest.libraries):
        lib = manifest.libraries[lib_id]
        canonical = canonicals.get(lib_id)
        versions = dispersion.get(lib_id, {})
        # Une divergence declaree pour une version que personne n'epingle est un
        # fantome : elle se lit comme un ecart reel dans la doc et dans le
        # manifeste, alors qu'aucun carnet ne la porte. Cas fondeur : « dotNetRDF
        # 3.2.0 » annonce au classement, absent du depot.
        for declared in sorted(set(lib.divergences) - set(versions), key=version_key):
            phantoms.append(
                {
                    "library": lib_id,
                    "version": declared,
                    "decision": lib.divergences[declared].get("decision", ""),
                    "reason": lib.divergences[declared].get("reason", ""),
                }
            )
        rows = []
        for version in sorted(versions, key=version_key):
            notebooks = sorted(versions[version])
            divergence = lib.divergences.get(version)
            if version == canonical:
                decision = "canonique"
                reason = ""
            elif divergence:
                decision = divergence.get("decision", "to_converge")
                reason = divergence.get("reason", "")
            else:
                decision = "a_classer"
                reason = ""
            rows.append(
                {
                    "version": version,
                    "notebooks": notebooks,
                    "count": len(notebooks),
                    "decision": decision,
                    "reason": reason,
                }
            )
        table.append(
            {
                "library": lib_id,
                "ecosystem": lib.ecosystem,
                "canonical": canonical,
                "canonical_source": lib.canonical_source,
                "versions": rows,
                "observed": [
                    {
                        "version": version,
                        "notebooks": sorted(notebooks),
                        "count": len(notebooks),
                    }
                    for version, notebooks in sorted(
                        observed_dispersion.get(lib_id, {}).items(),
                        key=lambda item: version_key(item[0]),
                    )
                ],
                "canonical_by_series": [
                    {
                        "series": series_path(
                            entry.get("series", "")
                        ).strip("/"),
                        "canonical": entry.get("canonical"),
                        "canonical_source": entry.get(
                            "canonical_source", "manifest"
                        ),
                        "organ_path": entry.get("organ_path", ""),
                        "note": entry.get("note", ""),
                    }
                    for entry in lib.canonical_by_series
                ],
                "note": lib.note,
                "multiple_versions": len(rows) > 1,
                "floating_notebooks": sorted(floating.get(lib_id, [])),
            }
        )
    return {
        "mode": "census",
        "generated_from": str(manifest.path),
        "errors": errors,
        "libraries": table,
        "phantom_divergences": phantoms,
        "unreadable_notebooks": sorted(unreadable),
        "binary_findings": binaries,
        "below_canonical": below_canonical,
    }


def render_census(report: dict) -> str:
    lines = ["# Recensement des versions de bibliotheques", ""]
    for lib in report["libraries"]:
        observed = lib.get("observed") or []
        if not lib["versions"] and not observed:
            continue
        canonical = lib["canonical"]
        source = "organe de serie" if lib["canonical_source"] == "organ" else "manifeste"
        lines.append(f"## {lib['library']} (canonique : {canonical} -- {source})")
        lines.append("")
        if lib.get("note"):
            lines.append(lib["note"])
            lines.append("")
        for entry in lib.get("canonical_by_series") or []:
            origin = entry.get("canonical_source", "manifest")
            if origin == "artifact":
                origin = f"artefact de serie ({entry.get('organ_path', '')})"
            lines.append(
                f"- canonique de la serie **{entry['series'] or '(racine)'}** : "
                f"`{entry['canonical']}` -- {origin}"
            )
            if entry.get("note"):
                lines.append(f"  - {entry['note']}")
        if lib.get("canonical_by_series"):
            lines.append("")
        if lib["versions"]:
            lines.append("| version | carnets | classement | motif |")
            lines.append("|---|---|---|---|")
            for row in lib["versions"]:
                motif = row["reason"].replace("|", "\\|")
                lines.append(
                    f"| {row['version']} | {row['count']} | {row['decision']} | {motif} |"
                )
            if lib.get("floating_notebooks"):
                lines.append(
                    f"| (non versionne) | {len(lib['floating_notebooks'])} "
                    f"| pin flottant | {FLOATING_PIN_REASON} |"
                )
            lines.append("")
            for row in lib["versions"]:
                if row["decision"] in ("canonique", "justified"):
                    continue
                lines.append(f"- **{row['version']}** : " + ", ".join(row["notebooks"]))
            lines.append("")
        if observed:
            lines.append(
                "Versions **chargeees** relevees dans les sorties commitees "
                "(aucune ligne d'epinglage ne les porte) :"
            )
            lines.append("")
            lines.append("| version | carnets |")
            lines.append("|---|---|")
            for row in observed:
                lines.append(f"| {row['version']} | {row['count']} |")
            lines.append("")
            for row in observed:
                lines.append(
                    f"- **{row['version']}** : " + ", ".join(row["notebooks"])
                )
            lines.append("")
    below = report.get("below_canonical") or []
    if below:
        lines.append("## Carnets en dessous de la canonique de leur serie")
        lines.append("")
        lines.append(
            "La version chargee, lue dans les sorties commitees, est inferieure "
            "a la canonique de la serie du carnet. Ces carnets sont a "
            "re-executer sous la version cible."
        )
        lines.append("")
        lines.append("| carnet | bibliotheque | serie | version chargee | canonique |")
        lines.append("|---|---|---|---|---|")
        for item in below:
            lines.append(
                f"| {item['notebook']} | {item['library']} "
                f"| {item['series'] or '(racine)'} | {item['version']} "
                f"| {item['canonical']} |"
            )
        lines.append("")
    if report.get("phantom_divergences"):
        lines.append("## Divergences declarees mais absentes du depot")
        lines.append("")
        lines.append(
            "Ces versions figurent dans le manifeste comme ecarts reels, mais "
            "aucun carnet ne les epingle : l'entree est a retirer, ou la "
            "divergence a revenir avec le carnet qui la porte."
        )
        lines.append("")
        lines.append("| bibliotheque | version | decision declaree |")
        lines.append("|---|---|---|")
        for phantom in report["phantom_divergences"]:
            lines.append(
                f"| {phantom['library']} | {phantom['version']} | {phantom['decision']} |"
            )
        lines.append("")
    binary_findings_list = report.get("binary_findings") or []
    if binary_findings_list:
        lines.append("## Binaires charges depuis un chemin non reproductible")
        lines.append("")
        lines.append(
            "Un chargement depuis un chemin hors du depot, ou depuis un dossier "
            "ignore par git, n'est pas reproductible depuis un clone : le "
            "binaire manque a la re-execution. Un binaire porte par un "
            "sous-module ou versionne dans le depot n'est pas signale."
        )
        lines.append("")
        lines.append("| carnet | artefact | constat | cellule |")
        lines.append("|---|---|---|---|")
        for finding in binary_findings_list:
            lines.append(
                f"| {finding['notebook']} | {finding['library']} "
                f"| {finding['kind']} | {finding['cell']} |"
            )
        lines.append("")
        for finding in binary_findings_list:
            lines.append(
                f"- `{finding['notebook']}` / {finding['library']} : "
                f"{finding['reason']}"
            )
        lines.append("")
    if report["errors"]:
        lines.append("## Erreurs de resolution")
        lines.append("")
        for error in report["errors"]:
            lines.append(f"- {error}")
        lines.append("")
    if report.get("unreadable_notebooks"):
        lines.append("## Carnets illisibles")
        lines.append("")
        lines.append(
            "Ces carnets n'ont pas pu etre lus : ils ne sont pas comptes comme "
            "des carnets sans epinglage, et la mesure est a refaire."
        )
        lines.append("")
        for notebook in report["unreadable_notebooks"]:
            lines.append(f"- {notebook}")
        lines.append("")
    return "\n".join(lines)


def render_findings(findings: list[dict]) -> str:
    lines = ["# Versions de bibliotheques -- constats", ""]
    if not findings:
        lines.append("Aucun constat : les carnets examines sont alignes sur le manifeste.")
        return "\n".join(lines)
    lines.append("| carnet | bibliotheque | ecart | version pinsee | canonique | cellule |")
    lines.append("|---|---|---|---|---|---|")
    for finding in findings:
        lines.append(
            "| {notebook} | {library} | {kind} | {version} | {canonical} | {cell} |".format(
                **finding
            )
        )
    lines.append("")
    for finding in findings:
        if finding.get("reason"):
            lines.append(
                f"- `{finding['notebook']}` / {finding['library']} : {finding['reason']}"
            )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Versions canoniques des bibliotheques chargees par les carnets "
            "(#23073) : recensement (rc 0) et garde de PR sur les carnets modifies."
        )
    )
    parser.add_argument(
        "--census",
        action="store_true",
        help="recensement repo-wide : table de dispersion, rc 0 toujours",
    )
    parser.add_argument(
        "--changed",
        metavar="RANGE",
        help="intervalle git (ex. origin/main...HEAD) : ne verifier que les carnets modifies",
    )
    parser.add_argument(
        "--state",
        action="store_true",
        help=(
            "comparer l'etat brut des carnets (tout epinglage != canonique) "
            "au lieu du delta base -> tete"
        ),
    )
    parser.add_argument(
        "--manifest",
        default=str(DEFAULT_MANIFEST),
        help="chemin du manifeste des versions canoniques",
    )
    parser.add_argument(
        "--repo-root",
        default=str(REPO_ROOT),
        help="racine du depot (defaut : racine du script)",
    )
    parser.add_argument("--json", action="store_true", help="sortie JSON")
    parser.add_argument(
        "--no-mentions",
        action="store_true",
        help=(
            "ne pas relever les mentions de version perimee dans la prose et "
            "les sorties (lecture de la seule ligne d'epinglage)"
        ),
    )
    parser.add_argument(
        "notebooks",
        nargs="*",
        help="carnets a verifier explicitement (mode etat)",
    )
    args = parser.parse_args(argv)

    repo_root = Path(args.repo_root).resolve()
    try:
        manifest = load_manifest(Path(args.manifest))
    except ValueError as exc:
        print(f"ERREUR : {exc}", file=sys.stderr)
        return 2

    if args.census:
        report = run_census(repo_root, manifest)
        if args.json:
            print(json.dumps(report, indent=2, ensure_ascii=False))
        else:
            print(render_census(report))
        return 0

    resolver = CanonicalResolver(manifest, repo_root)
    canonicals, errors = resolver.flat, list(resolver.errors)
    errors.extend(allowlist_errors(manifest))
    if errors:
        for error in errors:
            print(f"ERREUR : {error}", file=sys.stderr)
        return 2

    findings: list[dict] = []
    advisories: list[dict] = []
    checked = 0
    # Le mode « chemins explicites » est un mode d'ETAT : la sortie JSON doit
    # le dire, sinon elle annonce `"state": false` pour une lecture d'etat.
    state_mode = bool(args.state) or bool(args.notebooks and not args.changed)

    if args.notebooks and not args.changed:
        for raw_path in args.notebooks:
            notebook = Path(raw_path)
            if not notebook.is_absolute():
                notebook = repo_root / raw_path
            if not notebook.is_file():
                print(f"ERREUR : carnet introuvable : {raw_path}", file=sys.stderr)
                return 2
            if not notebook.resolve().is_relative_to(repo_root):
                # Un carnet hors du depot n'est pas un carnet de la famille.
                # La relecture demande un rc 2 **nomme** la (point 11), pas
                # une exception : on dit ce qui ne va pas, on ne leve pas.
                print(
                    f"ERREUR : carnet hors du depot : "
                    f"{notebook.resolve().as_posix()} "
                    f"(racine : {repo_root.as_posix()})",
                    file=sys.stderr,
                )
                return 2
            relative = _relative_to_repo(notebook, repo_root)
            payload = payload_from_file(notebook)
            if payload is None:
                # Un carnet illisible ne doit pas rendre du vert silencieux :
                # la famille rend rc 2 quand elle ne peut pas lire sa cible
                # (relecture coordinateur #23079, point 2).
                print(f"ERREUR : carnet illisible : {raw_path}", file=sys.stderr)
                return 2
            pins = pins_from_payload(payload, manifest)
            advisories.extend(versioned_fallbacks(relative, payload))
            findings.extend(state_findings(relative, pins, manifest, canonicals))
            # Version **chargeee** : elle ne se lit dans aucune ligne
            # d'epinglage, mais dans les sorties commitees.
            findings.extend(
                observed_findings(relative, payload, manifest, resolver)
            )
            # Le chargement hors depot est signale sur l'ETAT : son dommage se
            # produit a l'execution, pas a l'edition (meme regle que le
            # provisionnement etranger).
            findings.extend(binary_findings(relative, payload, repo_root))
            if not args.no_mentions:
                findings.extend(
                    mention_findings(relative, payload, manifest, canonicals)
                )
            checked += 1
    else:
        if not args.changed:
            print(
                "ERREUR : rien a verifier (--census, --changed RANGE ou des chemins).",
                file=sys.stderr,
            )
            return 2
        try:
            targets, base = changed_notebooks(repo_root, args.changed)
        except RuntimeError as exc:
            print(f"ERREUR : {exc}", file=sys.stderr)
            return 2
        for notebook in targets:
            relative = _relative_to_repo(notebook, repo_root)
            head_payload = payload_from_file(notebook)
            if head_payload is None:
                # Idem point 2 : une cible de `--changed` qu'on ne sait pas
                # lire est une erreur nommee, pas un carnet aligne.
                print(
                    f"ERREUR : carnet illisible a la tete : {relative}",
                    file=sys.stderr,
                )
                return 2
            head_pins = pins_from_payload(head_payload, manifest)
            advisories.extend(versioned_fallbacks(relative, head_payload))
            if args.state:
                # Relecture d'etat : le constat porte sur le carnet, pas sur un
                # delta -- un binaire absent du clone l'est deja dans la base.
                findings.extend(binary_findings(relative, head_payload, repo_root))
                findings.extend(
                    state_findings(relative, head_pins, manifest, canonicals)
                )
                findings.extend(
                    observed_findings(relative, head_payload, manifest, resolver)
                )
                if not args.no_mentions:
                    findings.extend(
                        mention_findings(
                            relative, head_payload, manifest, canonicals
                        )
                    )
            else:
                try:
                    base_payload = notebook_at(repo_root, base, relative)
                except BaseReadError as exc:
                    # Point 6 : une base qu'on ne sait pas lire n'est pas
                    # « un carnet neuf » -- c'est une lecture en echec, nommee.
                    print(f"ERREUR : {exc}", file=sys.stderr)
                    return 2
                base_pins = (
                    pins_from_payload(base_payload, manifest)
                    if base_payload is not None
                    else []
                )
                findings.extend(
                    delta_findings(
                        relative, base_pins, head_pins, manifest, canonicals
                    )
                )
                # Version **chargeee** introduite par la PR : c'est le cas
                # d'un carnet re-execute sous une version inferieure a celle
                # que la base portait (cf #23941).
                findings.extend(
                    delta_observed_findings(
                        relative, base_payload, head_payload, manifest, resolver
                    )
                )
                findings.extend(
                    delta_binary_findings(
                        relative, base_payload, head_payload, repo_root
                    )
                )
                if not args.no_mentions and head_payload is not None:
                    findings.extend(
                        delta_mention_findings(
                            relative, base_payload, head_payload,
                            manifest, canonicals,
                        )
                    )
            checked += 1

    if args.json:
        print(
            json.dumps(
                {
                    "mode": "check",
                    "state": state_mode,
                    "findings": findings,
                    "advisories": advisories,
                    "checked": checked,
                },
                indent=2,
                ensure_ascii=False,
            )
        )
    else:
        print(render_findings(findings))
        if advisories:
            print("\nAvis non bloquants : replis versionnes (source, pas execution)")
            for advisory in advisories:
                print(f"- {advisory['notebook']} cellule {advisory['cell']} "
                      f"ligne {advisory['line']} : {advisory['message']}")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
