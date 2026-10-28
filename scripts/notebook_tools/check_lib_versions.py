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
import json
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = Path(__file__).resolve().parent / "lib_versions_manifest.json"

# Epinglages NuGet : `#r "nuget: IKVM, 8.15.0"`. La virgule peut suivre sans
# espace (`nuget:pythonnet,3.1.0`) : le motif l'accepte.
NUGET_PIN_RE = re.compile(
    r'#r\s*"nuget:\s*([^",\s]+)\s*(?:,\s*([0-9][^"\s]*))?\s*"',
    re.IGNORECASE,
)

# Epinglages pip : `pip install x==1.2.3` (avec ou sans `!` devant).
PIP_PIN_RE = re.compile(
    r"pip\s+install\s+(?:--\S+\s+)*([A-Za-z0-9._\-]+)\s*==\s*([A-Za-z0-9._\-+!]+)",
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
    # Ecarts classes : version -> {decision, reason}
    divergences: dict[str, dict] = field(default_factory=dict)

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


def _cell_text(cell: dict) -> str:
    source = cell.get("source", "")
    if isinstance(source, list):
        return "".join(source)
    return str(source)


def _code_lines(payload: dict):
    """Yield (index de cellule, numero de ligne, ligne) des cellules code."""
    for index, cell in enumerate(payload.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        text = _cell_text(cell)
        for line_number, line in enumerate(text.splitlines(), start=1):
            yield index, line_number, line


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
    tweety_ids = [
        lib for lib in manifest.libraries.values() if lib.ecosystem == "tweety"
    ]
    symbol_owners = {
        lib.local_symbol: lib for lib in manifest.libraries.values() if lib.local_symbol
    }
    pins: list[Pin] = []
    for cell_index, line_number, line in _code_lines(payload):
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
            if lib_id is None or not match.group(2):
                continue
            pins.append(
                Pin(
                    lib_id,
                    _norm_version(match.group(2)),
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
            pins.append(
                Pin(
                    lib_id,
                    _norm_version(match.group(2)),
                    "pip",
                    cell_index,
                    line.strip(),
                    line_no=line_number,
                )
            )
        for lib in tweety_ids:
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
        canonical = canonical_map.get(pin.library)
        if canonical is None:
            continue
        # Cet exemplaire existait-il deja en base, en meme nombre ? Les
        # occurrences au-dela du compte de base sont celles que la PR
        # ajoute ; les precedentes sont de la derive historique.
        key = (pin.library, pin.version)
        seen[key] += 1
        if seen[key] <= base_counts.get(pin.library, Counter())[pin.version]:
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
    **declare un epinglage** de cette bibliotheque, et la ligne d'epinglage
    elle-meme est exclue (elle porte la version, ce n'est pas une mention).
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

    # Lignes d'epinglage : exclues du balayage des sources.
    pin_lines: set[tuple[str, int, int]] = set()
    for pin in pins:
        pin_lines.add((pin.library, pin.cell, pin.line_no))

    for lib_id, versions in sorted(targets.items()):
        canonical = canonical_map.get(lib_id)
        for version in sorted(versions, key=version_key):
            if _allowlisted(manifest, lib_id, version, notebook):
                continue
            for index, cell in enumerate(payload.get("cells", []) or []):
                for line_number, line in enumerate(
                    _cell_text(cell).splitlines(), start=1
                ):
                    if (lib_id, index, line_number) in pin_lines:
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


def run_census(repo_root: Path, manifest: Manifest) -> dict:
    """Recensement repo-wide : table de dispersion + classement des ecarts."""
    canonicals, errors = resolve_canonicals(manifest, repo_root)
    dispersion: dict[str, dict[str, list[str]]] = {}
    for notebook in tracked_notebooks(repo_root):
        relative = _relative_to_repo(notebook, repo_root)
        for pin in pins_from_file(notebook, manifest):
            if pin.ecosystem == "provisioning":
                continue
            bucket = dispersion.setdefault(pin.library, {})
            bucket.setdefault(pin.version, [])
            if relative not in bucket[pin.version]:
                bucket[pin.version].append(relative)

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
                "multiple_versions": len(rows) > 1,
            }
        )
    return {
        "mode": "census",
        "generated_from": str(manifest.path),
        "errors": errors,
        "libraries": table,
        "phantom_divergences": phantoms,
    }


def render_census(report: dict) -> str:
    lines = ["# Recensement des versions de bibliotheques", ""]
    for lib in report["libraries"]:
        if not lib["versions"]:
            continue
        canonical = lib["canonical"]
        source = "organe de serie" if lib["canonical_source"] == "organ" else "manifeste"
        lines.append(f"## {lib['library']} (canonique : {canonical} -- {source})")
        lines.append("")
        lines.append("| version | carnets | classement | motif |")
        lines.append("|---|---|---|---|")
        for row in lib["versions"]:
            motif = row["reason"].replace("|", "\\|")
            lines.append(
                f"| {row['version']} | {row['count']} | {row['decision']} | {motif} |"
            )
        lines.append("")
        for row in lib["versions"]:
            if row["decision"] in ("canonique", "justified"):
                continue
            lines.append(f"- **{row['version']}** : " + ", ".join(row["notebooks"]))
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
    if report["errors"]:
        lines.append("## Erreurs de resolution")
        lines.append("")
        for error in report["errors"]:
            lines.append(f"- {error}")
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

    canonicals, errors = resolve_canonicals(manifest, repo_root)
    errors.extend(allowlist_errors(manifest))
    if errors:
        for error in errors:
            print(f"ERREUR : {error}", file=sys.stderr)
        return 2

    findings: list[dict] = []
    checked = 0

    if args.notebooks and not args.changed:
        for raw_path in args.notebooks:
            notebook = Path(raw_path)
            if not notebook.is_absolute():
                notebook = repo_root / raw_path
            if not notebook.is_file():
                print(f"ERREUR : carnet introuvable : {raw_path}", file=sys.stderr)
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
            findings.extend(state_findings(relative, pins, manifest, canonicals))
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
            if args.state:
                findings.extend(
                    state_findings(relative, head_pins, manifest, canonicals)
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
                    "state": bool(args.state),
                    "findings": findings,
                    "checked": checked,
                },
                indent=2,
                ensure_ascii=False,
            )
        )
    else:
        print(render_findings(findings))
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
