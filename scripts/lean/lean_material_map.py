#!/usr/bin/env python3
"""Carte du materiel Lean du depot — page regeneree, jamais recopiee.

Issue #23097, tranche T1. Le depot porte plusieurs dizaines de lacs Lean, dont
une partie seulement est declaree au CI et une partie plus petite encore est
couverte par le gate d'axiomes. Une table ecrite a la main derive au premier
merge : ce script est le generateur proprietaire de la page
``docs/reference/lean-material-map.md``, et ``--check`` echoue quand la page et
l'arbre divergent.

La colonne « naissance » (date d'ajout du ``lakefile``) est celle qui rend
l'accretion visible sans recherche git : c'est elle qui a permis de mesurer que
``assignment_lean`` et ``asymmetric_information_lean`` sont nes apres la
cloture de #4365.

Usage :
    python scripts/lean/lean_material_map.py                 # page sur stdout
    python scripts/lean/lean_material_map.py --write         # ecrit la page
    python scripts/lean/lean_material_map.py --check         # 0 = page a jour
    python scripts/lean/lean_material_map.py --json          # sortie machine
    python scripts/lean/lean_material_map.py --with-sorry    # ajoute la dette

``--with-sorry`` est opt-in : ``count_code_sorry.py --json`` parcourt tout le
depot et depasse les deux minutes, ce qui est incompatible avec un ``--check``
de CI. La page par defaut ne porte donc pas de colonne de dette.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
PAGE = REPO_ROOT / "docs" / "reference" / "lean-material-map.md"
CI_LAKES = REPO_ROOT / "scripts" / "lean" / "ci_lakes.json"
BIRTHS = REPO_ROOT / "scripts" / "lean" / "lean_births.json"
COVERAGE = REPO_ROOT / "scripts" / "lean" / "check_axiom_gate_coverage.py"
WORKFLOWS = REPO_ROOT / ".github" / "workflows"

# Budget de l'organe de couverture. Mesure du 2026-11-07 sur ai-01 : 634 s
# puis 658 s (deux passes) -- le seuil de 300 s etait SOUS la duree reelle.
# L'echec etait alors avale en silence (cf `_coverage`) et la page rendue
# disait `hors matrice` pour les 41 lacs, alors que la couverture mesuree
# en donne 34 gated / 35 matrice / 2 sans gate. Regeneree avec une couverture
# reellement mesuree, la page est IDENTIQUE octet pour octet a la page
# commitee : la page est saine, le seuil etait le defaut.
COVERAGE_TIMEOUT = 1800

# Code de sortie conventionnel des generateurs : « je n'ai pas pu mesurer ».
# Distinct de 1 (`PERIMEE`) : la page peut etre parfaitement saine, c'est la
# machine qui n'a pas repondu a l'organe amont. Le garde des pages derivees
# (`scripts/lean/check_lean_derived_pages.py`) classifie ce code
# explicitement au lieu de le lire comme une divergence de l'arbre.
UNMEASURABLE_RC = 2

GENERATED_HEADER = (
    "<!-- fichier genere par scripts/lean/lean_material_map.py -- "
    "ne pas editer a la main ; relancer le generateur -->"
)

# T2 #23097 : la regle d'accretion d'un lac, tranchee par la mesure.
# Les verdicts sont datees : la mesure qui les fonde est citee dans la cellule.
ACCRETION_RULE = (
    "Un lac nouveau dans une serie existante est legitime si (1) sa toolchain"
    " diverge de celle du lac de la serie, (2) sa theorie est distincte au sens"
    " de la clause anti-god-lake (#4365), ou (3) a toolchain egale il est le"
    " compagnon de construction d'un arc numerote de carnets -- importe par au"
    " moins un carnet Lean de cet arc, sans import croise avec le lac de la"
    " serie, et sans lui imposer une dependance (un path dep d'un lac tiers"
    " deviendrait sinon facteur commun). A defaut, c'est un module de plus du"
    " lac de la serie."
)

ACCRETION_VERDICTS = [
    (
        "assignment_lean",
        "(3) compagnon d'arc",
        "legitime-documente",
        "Arc 16f : `GameTheory-16f-Lean-Assignment-Lean.ipynb` importe"
        " `Assignment.KuhnMunkres`. Toolchain et pin Mathlib identiques a"
        " `game_theory_lean` (v4.33.0, db584cd6), zero import croise, theorie"
        " (affectation hongroise, Kuhn-Munkres) absente des 8 branches du lac"
        " de la serie.",
    ),
    (
        "asymmetric_information_lean",
        "(3) compagnon d'arc",
        "legitime-documente",
        "Arc 17b-17e : `GameTheory-17c-Lean-Lemons-Certificat-Lean.ipynb`"
        " importe `AsymmetricInformation.Lemons`, `GameTheory-17d-Lean-"
        "Screening-Signaling-Lean.ipynb` en importe 4 modules. Path dep non"
        " negociable vers `lean_game_defs_ext` (#12848) : la fusion imposerait"
        " ce pont aux 38 modules de `game_theory_lean`. Zero import croise.",
    ),
]

# Un lakefile dont le dossier porte l'un de ces fragments est vendu, pas a nous.
VENDORED_MARKERS = (".lake/packages", "_peters/", "reference_docs/")

# `git ls-files '*.lean'` attrape aussi les fichiers qui portent l'extension sans
# etre du Lean : le Dockerfile du runner Lean s'appelle `Dockerfile.lean`. Le
# compter comme module gonflerait la carte d'un fichier qui ne se compile pas.
NOT_LEAN_NAMES = ("Dockerfile",)

# R1/R4 (doctrine des lakes, #4362) : les deux colonnes de conformite. Elles se
# mesurent sur les memes surfaces que le reste de la page -- git seulement, aucun
# build -- et coutent moins d'une seconde, ce qui les rend compatibles avec le
# `--check` qui garde la page.
NOTEBOOK_IMPORT_RE = re.compile(r"import\s+([A-Z][A-Za-z0-9_.]*)")
DECLARATION_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(?:theorem|lemma)\s+([A-Za-z0-9_'.À-ɏ]+)"
)


def _git(*args: str) -> str:
    """Rend la sortie de git, ou une chaine vide si la commande echoue."""
    try:
        r = subprocess.run(
            ["git", "-C", str(REPO_ROOT), *args],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
    except OSError:
        return ""
    if r.returncode != 0:
        return ""
    return r.stdout


def _git_paths(*patterns: str) -> list[str]:
    out = _git("ls-files", "-z", *patterns)
    return [p for p in out.split("\0") if p]


def _declared_lakes() -> dict[str, dict]:
    """Les entrees de ci_lakes.json, indexees par project-path normalise."""
    try:
        raw = json.loads(CI_LAKES.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    entries = raw.get("lakes", []) if isinstance(raw, dict) else raw
    out: dict[str, dict] = {}
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        path = entry.get("project-path")
        if not path:
            continue
        out[path.replace("\\", "/").rstrip("/")] = entry
    return out


class CoverageUnavailable(RuntimeError):
    """L'organe de couverture n'a pas repondu : la page ne peut pas etre certifiee."""


def _coverage() -> dict:
    """Le verdict du gate d'axiomes.

    Fail-closed. Un organe amont injoignable ne rend pas un « verdict neutre » :
    il rend une page **FAUSSE**. Rendre `{}` faisait dire `hors matrice` a
    tous les lacs, le `--check` qui suivait rendait alors `A JOUR` sur cette
    page fausse, et le `--write` ecracait une page correcte par une page
    fausse -- sans qu'aucune erreur ne soit levee. Mesure du 2026-11-07 : le
    seuil de 300 s etait sous la duree reelle de l'organe (634-658 s), donc
    l'echec etait **deterministe** sur cette machine, pas aleatoire.

    L'echec est donc remonte : le generateur refuse d'ecrire et refuse de
    declarer la page a jour.
    """
    try:
        r = subprocess.run(
            [sys.executable, "-I", str(COVERAGE), "--ref", "HEAD", "--json"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            cwd=str(REPO_ROOT),
            timeout=COVERAGE_TIMEOUT,
        )
    except subprocess.TimeoutExpired:
        raise CoverageUnavailable(
            "timeout de %d s sur %s" % (COVERAGE_TIMEOUT, COVERAGE.name))
    except (OSError, subprocess.SubprocessError) as exc:
        raise CoverageUnavailable(
            "appel impossible de %s : %s" % (COVERAGE.name, exc))
    if r.returncode != 0:
        raise CoverageUnavailable(
            "rc=%d sur %s" % (r.returncode, COVERAGE.name))
    try:
        return json.loads(r.stdout)
    except json.JSONDecodeError as exc:
        raise CoverageUnavailable(
            "sortie illisible de %s : %s" % (COVERAGE.name, exc))


def _sorry_by_lake() -> dict[str, int]:
    """Dette ``distinct_code_sorry`` par lac. Opt-in, couteux (cf docstring)."""
    try:
        r = subprocess.run(
            [sys.executable, "-I", str(REPO_ROOT / "scripts" / "lean" / "count_code_sorry.py"), "--json"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            cwd=str(REPO_ROOT),
            timeout=1800,
        )
        if r.returncode != 0 or not r.stdout.strip():
            return {}
        data = json.loads(r.stdout)
    except (OSError, subprocess.SubprocessError, json.JSONDecodeError):
        return {}
    # Forme mesuree de count_code_sorry.py --json :
    #   {"lakes": [{"lake": <chemin>, "files": n, "naive_sorry": n,
    #               "code_sorry": n, "distinct_code_sorry": n, "vacuous": [...]}]}
    # On accepte aussi une liste nue d'entrees, pour ne pas casser au premier
    # changement de forme de l'organe amont.
    entries = data.get("lakes") if isinstance(data, dict) else data
    out: dict[str, int] = {}
    if not isinstance(entries, list):
        return out
    for value in entries:
        if not isinstance(value, dict):
            continue
        path = value.get("lake") or value.get("project-path")
        count = value.get("distinct_code_sorry")
        if path and isinstance(count, int):
            out[str(path).replace("\\", "/").rstrip("/")] = count
    return out


def _workflow_texts() -> list[tuple[str, str]]:
    """(nom, contenu) de chaque workflow : l'autre surface de declaration du CI.

    `scripts/lean/ci_lakes.json` ne porte PAS tous les lacs : une serie de lacs a
    son propre workflow dedie (`lean-asymmetric-information.yml`,
    `lean-grothendieck.yml`, ...). Ne lire que le JSON classe « hors CI » des
    lacs que le CI construit a chaque push -- c'est un faux negatif mesure, pas
    une hypothese.
    """
    out: list[tuple[str, str]] = []
    for path in sorted(WORKFLOWS.glob("*.yml")) + sorted(WORKFLOWS.glob("*.yaml")):
        try:
            out.append((path.name, path.read_text(encoding="utf-8", errors="replace")))
        except OSError:
            continue
    return out


def _ci_surfaces(lakes: list[str]) -> dict[str, list[str]]:
    """Pour chaque lac, la liste des surfaces de CI qui le nomment."""
    out: dict[str, list[str]] = {lake: [] for lake in lakes}
    declared = _declared_lakes()
    for lake in lakes:
        if lake in declared:
            out[lake].append("ci_lakes.json")
    for name, text in _workflow_texts():
        for lake in lakes:
            if lake in text and name not in out[lake]:
                out[lake].append(name)
    return out


def _pinned_births() -> dict[str, str]:
    """Les naissances epinglees de `lean_births.json`, indexees par lac."""
    try:
        raw = json.loads(BIRTHS.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    lakes = raw.get("lakes") if isinstance(raw, dict) else None
    if not isinstance(lakes, dict):
        return {}
    return {
        str(k).replace("\\", "/").rstrip("/"): str(v)
        for k, v in lakes.items()
        if isinstance(v, str) and v
    }


def _git_birth(lakefile: str) -> str:
    """Premier ajout **visible** du lakefile ; vide si l'histoire n'en montre aucun.

    `--reverse` + premiere ligne, et non `-1` : `-1` rend le *dernier* ajout
    visible, donc un mass-add tardif -- ou une histoire tronquee (clone
    shallow, greffe) -- deplace la date. Le premier ajout, lui, ne bouge pas
    quand l'histoire s'allonge. Il reste borne par ce que le clone contient :
    c'est pourquoi `lean_births.json` prime (cf. `_birth`).
    """
    out = _git("log", "--diff-filter=A", "--format=%cs", "--reverse", "--", lakefile)
    lines = [line.strip() for line in out.splitlines() if line.strip()]
    return lines[0] if lines else ""


def _birth(lake: str, lakefile: str, pinned: dict[str, str] | None = None) -> str:
    """Date (AAAA-MM-JJ) de naissance du lac ; vide si inconnue.

    L'epingle committée prime sur git : sans elle, la colonne dependrait de
    l'histoire **visible** du clone, et deux sieges sur la meme histoire
    pouvaient rendre deux pages differentes (issue #24538). Un lac nouveau
    n'est pas epingle : il retombe sur git jusqu'a ce que son epingle soit
    ajoutee, geste explicite et visible en revue.

    ``pinned`` est injectable : ``collect()`` charge la table une fois pour
    tous les lacs (deux lectures par lac sinon, une par lakefile) ; les
    appels directs conservent le chargement implicite -- c'est aussi ce qui
    garde les tests libres de monkeypatcher ``BIRTHS`` sans cache interpose.
    """
    if pinned is None:
        pinned = _pinned_births()
    return pinned.get(lake.replace("\\", "/").rstrip("/")) or _git_birth(lakefile)


def _owner_of(path: str, lake_dirs: list[str]) -> str | None:
    """Le lac le plus profond qui contient ce chemin, ou None."""
    for lake in lake_dirs:
        if path.startswith(lake + "/"):
            return lake
    return None


def _notebook_consumers(modules_by_lake: dict[str, set[str]]) -> dict[str, set[str]]:
    """Carnets qui importent un module d'un lac -> {lac: {carnet}} (R1).

    La consommation se mesure sur le seul signal objectif disponible sans build :
    une ligne `import <Module>` d'un carnet, dont `<Module>` est un fichier
    `.lean` du lac. Les imports de paquets (`Mathlib`, `Batteries`) ne sont pas
    dans l'index et ne rattachent donc un carnet a aucun lac -- sans cette
    restriction, tout carnet Lean deviendrait consommateur de tous les lacs.
    """
    module_owner: dict[str, set[str]] = {}
    for lake, modules in modules_by_lake.items():
        for module in modules:
            module_owner.setdefault(module, set()).add(lake)

    out: dict[str, set[str]] = {}
    text = _git(
        "-c", "core.quotepath=false",
        "grep", "-n", "-I", "-E", "import[[:space:]]+[A-Z]", "--", "*.ipynb",
    )
    for line in text.splitlines():
        parts = line.split(":", 2)
        if len(parts) < 3:
            continue
        path, _lineno, source = parts
        for module in NOTEBOOK_IMPORT_RE.findall(source):
            for lake in module_owner.get(module, ()):
                out.setdefault(lake, set()).add(path)
    return out


def _docstring_above(source: list[str], lineno: int) -> str:
    """Le bloc `/-- ... -/` qui precede immediatement la declaration, ou ''."""
    i = lineno - 2
    while i >= 0 and not source[i].strip():
        i -= 1
    if i < 0 or not source[i].rstrip().endswith("-/"):
        return ""
    end = i
    while i >= 0 and "/--" not in source[i]:
        i -= 1
    return "\n".join(source[i:end + 1]) if i >= 0 else ""


def _shared_theorems(lake_dirs: list[str]) -> list[dict]:
    """Les theoremes portes par au moins deux lacs, et ce qu'ils declarent (R4).

    La mesure est par NOM : elle sous-compte par construction, et le controle
    negatif est mesure sur Arrow (deux preuves du meme resultat sous les noms
    `arrow` et `arrow_impossibility`, invisibles l'une a l'autre pour cet
    instrument). La page le dit, plutot que de laisser croire a un inventaire
    exhaustif.
    """
    occurrences: dict[str, list[tuple[str, str, int, str]]] = {}
    text = _git(
        "grep", "-n", "-I", "-E",
        "^[[:space:]]*(theorem|lemma)[[:space:]]", "--", "*.lean",
    )
    for line in text.splitlines():
        parts = line.split(":", 2)
        if len(parts) < 3:
            continue
        path, lineno, source = parts
        if any(marker in path for marker in VENDORED_MARKERS):
            continue
        lake = _owner_of(path, lake_dirs)
        if lake is None:
            continue
        match = DECLARATION_RE.match(source.strip())
        if match:
            # La tete d'enonce = ce qui suit le nom sur la meme ligne, espaces
            # normalises. Elle compare des FORMULATIONS : une tete identique
            # prouve le meme enonce, une tete differente ne prouve rien (deux
            # encodages d'un meme theoreme tombent la comme deux enonces sans
            # rapport) et se declare donc « non conclu » a la lecture.
            head = " ".join(source.strip()[match.end():].split())
            occurrences.setdefault(match.group(1), []).append(
                (lake, path, int(lineno), head)
            )

    out: list[dict] = []
    for name, entries in occurrences.items():
        lakes = sorted({entry[0] for entry in entries})
        if len(lakes) < 2:
            continue
        citations = 0
        per_lake: dict[str, list[int]] = {}
        heads = {entry[3] for entry in entries}
        if "" in heads:
            # Enonce dont la tete tient sur la ligne suivante : la comparaison
            # ne conclut pas, et le dit plutot que de trancher au hasard.
            nature = "non conclu"
        elif len(heads) == 1:
            # Formulation identique : le meme enonce, a coup sur.
            nature = "formulation identique"
        else:
            # Deux formulations differentes ne disent RIEN de l'identite
            # mathematique : deux encodages d'un meme theoreme (Sen en
            # SWF fini vs en SWF abstrait, FairBot en duel de boites vs en
            # logique modale) tombent ici comme deux enonces sans rapport.
            nature = "formulation differente"
        for lake, path, lineno, _head in entries:
            slot = per_lake.setdefault(lake, [0, 0])
            slot[0] += 1
            try:
                source = (REPO_ROOT / path).read_text(
                    encoding="utf-8", errors="replace"
                ).splitlines()
            except OSError:
                continue
            doc = _docstring_above(source, lineno)
            if not doc:
                continue
            # R4 demande un renvoi croise nommant l'autre maison. Le nom du lac
            # suffit : les freres `_en` citent le chemin de leur langue.
            if any(other.rsplit("/", 1)[-1] in doc for other in lakes if other != lake):
                slot[1] += 1
                citations += 1
        out.append({
            "name": name,
            "lakes": lakes,
            "occurrences": len(entries),
            "citations": citations,
            "per_lake": per_lake,
            "nature": nature,
        })
    out.sort(key=lambda item: item["name"])
    return out


def collect(with_sorry: bool = False) -> dict:
    """Un enregistrement par lac, plus les fichiers hors lac : le fait mesure."""
    lakefiles = _git_paths("*lakefile.lean", "*lakefile.toml")
    coverage = _coverage()
    gated = set(coverage.get("gated_lakes") or [])
    matrix = set(coverage.get("matrix_lakes") or [])
    ungated = set(coverage.get("matrix_lakes_without_gate") or [])
    sorry = _sorry_by_lake() if with_sorry else {}
    pinned = _pinned_births()  # une seule lecture pour tous les lacs

    by_lake: dict[str, dict] = {}
    for lakefile in lakefiles:
        lake = lakefile.rsplit("/", 1)[0] if "/" in lakefile else "."
        vendored = any(marker in lakefile for marker in VENDORED_MARKERS)
        entry = by_lake.setdefault(
            lake,
            {
                "lake": lake,
                "lakefile": lakefile,
                "vendored": vendored,
                "modules": 0,
                "mirrors": 0,
                "birth": "",
                "module_names": set(),
            },
        )
        # Un lac peut porter deux lakefiles (lean + toml) : la naissance est la
        # plus ancienne des deux, c'est celle du lac.
        born = _birth(lake, lakefile, pinned)
        if born and (not entry["birth"] or born < entry["birth"]):
            entry["birth"] = born

    # Un module appartient au lac le plus proche qui le CONTIENT, pas au dossier
    # qui le porte : `game_theory_lean/SocialChoice/Arrow.lean` est un module de
    # `game_theory_lean`. Attribuer par dossier immediat efface silencieusement
    # tous les modules des lacs arborescents -- la mesure serait fausse sans
    # qu'aucun temoin ne le dise.
    lake_dirs = sorted(by_lake, key=len, reverse=True)

    def owner(path: str) -> str | None:
        for lake in lake_dirs:
            if path.startswith(lake + "/"):
                return lake
        return None

    orphans: list[str] = []
    excluded = 0
    not_lean = 0
    for path in _git_paths("*.lean"):
        if any(marker in path for marker in VENDORED_MARKERS):
            excluded += 1
            continue
        if path.rsplit("/", 1)[-1].startswith(NOT_LEAN_NAMES):
            not_lean += 1
            continue
        lake = owner(path)
        if lake is None:
            orphans.append(path)
            continue
        entry = by_lake[lake]
        if path.endswith("_en.lean"):
            entry["mirrors"] += 1
        else:
            entry["modules"] += 1
        relative = path[len(lake) + 1:]
        if relative.endswith(".lean"):
            entry["module_names"].add(relative[:-5].replace("/", "."))

    consumers = _notebook_consumers(
        {lake: entry["module_names"] for lake, entry in by_lake.items()}
    )
    shared = _shared_theorems(lake_dirs)

    rows: list[dict] = []
    surfaces = _ci_surfaces([lake.replace("\\", "/").rstrip("/") for lake in by_lake])
    for lake, entry in by_lake.items():
        key = lake.replace("\\", "/").rstrip("/")
        where = surfaces.get(key, [])
        if entry["vendored"]:
            gate = "vendu"
        elif key in ungated:
            gate = "sans gate"
        elif key in gated:
            gate = "couverte"
        elif key in matrix:
            gate = "matrice"
        else:
            gate = "hors matrice"
        entry["ci"] = "declare" if where else "hors CI"
        entry["ci_surfaces"] = where
        entry["gate"] = gate
        entry["sorry"] = sorry.get(key)

        # R1 : le site du lac est le dossier qui le porte ; une consommation
        # depuis ce dossier est « a son site », depuis ailleurs elle est
        # « hors site » et c'est exactement ce que la doctrine veut rendre
        # visible avant qu'un deplacement ne soit decide.
        home = key.rsplit("/", 1)[0] if "/" in key else "."
        consumed = consumers.get(key, set())
        off_site = sorted(
            {carnet.rsplit("/", 1)[0] for carnet in consumed
             if not carnet.startswith(home + "/")}
        )
        if not consumed:
            entry["site"] = "non consomme"
        elif not off_site:
            entry["site"] = "ok (%d)" % len(consumed)
        else:
            entry["site"] = "%d hors site (%d carnets)" % (len(off_site), len(consumed))
        entry["site_off"] = off_site
        entry["consumers"] = len(consumed)

        # R4 : la colonne se lit par cote. Un lac declare son cote d'un nom
        # partage quand TOUTES ses propres occurrences portent le renvoi
        # croise ; le cote d'en face se juge chez lui, pas ici.
        mine = [item for item in shared if key in item["lakes"]]
        entry["dup_names"] = [item["name"] for item in mine]
        entry["dup_declared"] = sum(
            1 for item in mine
            if item["per_lake"][key][1] == item["per_lake"][key][0]
        )
        entry.pop("module_names", None)
        rows.append(entry)

    rows.sort(key=lambda r: (-r["modules"], r["lake"]))
    return {
        "lakes": rows,
        "orphans": sorted(orphans),
        "excluded": excluded,
        "not_lean": not_lean,
        "shared_theorems": shared,
    }


def render(
    rows: list[dict],
    orphans: list[str],
    excluded: int,
    not_lean: int,
    with_sorry: bool,
    shared: list[dict],
) -> str:
    lines: list[str] = [GENERATED_HEADER, ""]
    lines.append("# Carte du materiel Lean du depot")
    lines.append("")
    lines.append(
        "Une ligne par lac. Les colonnes sont des mesures rejouables, pas des"
        " appreciations : `Modules` compte les fichiers `.lean` propres du lac,"
        " `Miroirs` les freres `_en`, `Naissance` la date du commit qui a ajoute"
        " le `lakefile` a son chemin actuel -- un fichier re-ajoute y prend la"
        " date de son re-ajout, la colonne ne remonte pas plus loin que git."
        " La colonne `Gate axiomes` reprend le verdict de"
        " `scripts/lean/check_axiom_gate_coverage.py`. Les deux colonnes de"
        " conformite -- `Site = consommateur` (R1) et `Doublons declares` (R4)"
        " -- sont definies dans `docs/reference/lean-lakes-doctrine.md` et"
        " mesurees plus bas."
    )
    lines.append("")
    lines.append(
        "Cette page est regeneree par `scripts/lean/lean_material_map.py`. Une"
        " table recopiee a la main derive au premier merge : c'est la maladie"
        " que #23097 soigne, et `--check` est le garde-fou."
    )
    lines.append("")
    lines.append(
        "`sans gate` n'est pas un defaut : la couverture est une mesure, pas un"
        " verdict de surete (#17097 critere 3). Un lac sans gate doit seulement"
        " etre **connu** comme tel."
    )
    lines.append("")

    head = [
        "Lac",
        "Modules",
        "Miroirs",
        "CI",
        "Gate axiomes",
        "Site = consommateur",
        "Doublons declares",
        "Naissance",
    ]
    if with_sorry:
        head.append("Dette")
    lines.append("| " + " | ".join(head) + " |")
    lines.append("|" + "|".join(["---"] * len(head)) + "|")
    for row in rows:
        dup = (
            "%d / %d" % (row["dup_declared"], len(row["dup_names"]))
            if row["dup_names"]
            else "-"
        )
        cells = [
            "`%s`" % row["lake"],
            str(row["modules"]),
            str(row["mirrors"]),
            row["ci"],
            row["gate"],
            row["site"],
            dup,
            row["birth"] or "-",
        ]
        if with_sorry:
            cells.append("-" if row["sorry"] is None else str(row["sorry"]))
        lines.append("| " + " | ".join(cells) + " |")
    lines.append("")

    own = [r for r in rows if not r["vendored"]]
    lines.append("## Ce que la carte etablit")
    lines.append("")
    lines.append(
        "%d lacs propres, plus %d dossier vendu. Les lacs hors CI sont listes"
        " ci-dessous : ce sont eux qui rendent une consolidation invisible"
        " depuis la matrice de build."
        % (len(own), len(rows) - len(own))
    )
    lines.append("")
    modules = sum(r["modules"] for r in own)
    mirrors = sum(r["mirrors"] for r in own)
    lines.append("### Reconciliation")
    lines.append("")
    lines.append(
        "%d modules + %d miroirs attribues a un lac + %d fichiers hors lac"
        " + %d fichiers ecartes (dossier vendu, ou extension `.lean` portee par"
        " un fichier qui n'est pas du Lean) = %d fichiers `.lean` traces, soit"
        " la population entiere de `git ls-files '*.lean'`. Un fichier qui"
        " n'apparait dans aucune de ces quatre colonnes a ete perdu en route :"
        " c'est le defaut que cette reconciliation rend visible."
        % (
            modules,
            mirrors,
            len(orphans),
            excluded + not_lean,
            modules + mirrors + len(orphans) + excluded + not_lean,
        )
    )
    lines.append("")

    uncabled = [r for r in own if r["ci"] == "hors CI"]
    if uncabled:
        lines.append("### Lacs hors CI")
        lines.append("")
        lines.append(
            "Ces lacs existent dans l'arbre et aucun workflow ne les nomme : ni"
            " `scripts/lean/ci_lakes.json`, ni un fichier de"
            " `.github/workflows/`. Aucun build de matrice ne les couvre."
        )
        lines.append("")
        for row in uncabled:
            lines.append("- `%s` — %d modules, ne le %s" % (row["lake"], row["modules"], row["birth"] or "?"))
        lines.append("")

    ungated_rows = [r for r in own if r["gate"] == "sans gate"]
    if ungated_rows:
        lines.append("### Lacs de la matrice sans gate d'axiomes")
        lines.append("")
        lines.append(
            "Declares au CI, donc construits, mais le job `lean-axiom` ne les"
            " atteint pas : rien ne rougit si un axiome interdit y entre."
        )
        lines.append("")
        for row in ungated_rows:
            lines.append("- `%s` — %d modules" % (row["lake"], row["modules"]))
        lines.append("")

    if orphans:
        lines.append("### Fichiers `.lean` hors lac")
        lines.append("")
        lines.append(
            "Traces par git, mais dans aucun dossier portant un `lakefile` : ils"
            " ne sont construits par aucun lac, et aucune matrice ne les voit."
        )
        lines.append("")
        for path in orphans:
            lines.append("- `%s`" % path)
        lines.append("")

    lines.append("## R1 — le site suit le consommateur")
    lines.append("")
    lines.append(
        "La doctrine demande qu'un lac vive dans le dossier de la (sous-)serie"
        " dont les carnets l'importent. La consommation se mesure sur le seul"
        " signal objectif disponible sans build : une ligne `import <Module>`"
        " d'un carnet, ou `<Module>` est un fichier `.lean` du lac. Les imports"
        " de paquets (`Mathlib`, `Batteries`) ne rattachent un carnet a aucun"
        " lac -- sans cette restriction, tout carnet Lean consommerait tous les"
        " lacs. Un carnet est « au site » quand il vit sous le dossier du lac,"
        " « hors site » sinon."
    )
    lines.append("")
    off_site_rows = [r for r in own if r.get("site_off")]
    if off_site_rows:
        lines.append(
            "%d lacs sur %d sont consommes, dont %d depuis un dossier hors site."
            " Ce n'est pas un defaut en soi : c'est le fait que R1 rend"
            " arbitrable, et que la ligne nomme."
            % (sum(1 for r in own if r["consumers"]), len(own), len(off_site_rows))
        )
        lines.append("")
        for row in off_site_rows:
            lines.append(
                "- `%s` — %d carnets, hors site : %s"
                % (
                    row["lake"],
                    row["consumers"],
                    ", ".join("`%s`" % d for d in row["site_off"]),
                )
            )
        lines.append("")
    else:
        lines.append("Aucune consommation hors site mesuree.")
        lines.append("")

    lines.append("## R4 — les doublons de theoreme, et leur declaration")
    lines.append("")
    lines.append(
        "Un nom de `theorem`/`lemma` porte par deux lacs est un doublon au sens"
        " de la doctrine. Il est **declare** quand chaque occurrence porte le"
        " renvoi croise qui nomme l'autre maison dans sa docstring ; une seule"
        " occurrence muette laisse le doublon non declare. La colonne « par cote »"
        " se lit par lac : elle localise le cote qui manque au renvoi, la"
        " colonne « occurrences » restant le total des deux. Le renvoi compte"
        " quand il **nomme le lac** ; un lien conceptuel formule autrement ne"
        " compte pas — c'est une definition de la mesure, pas un jugement sur la"
        " qualite du lien."
    )
    lines.append("")
    lines.append(
        "La colonne « nature » compare la **formulation**, pas le resultat, et"
        " cet écart est deliberate : une « formulation identique » est un"
        " resultat prouve deux fois, sans ambiguite ; une « formulation"
        " differente » ne tranche rien et demande un regard de domaine, parce"
        " que deux encodages d'un meme theoreme y tombent au meme titre que deux"
        " enonces sans rapport. La tete comparee est ce qui suit le nom sur la"
        " ligne de declaration — une comparaison de premiere ligne, qui ne"
        " conclut pas quand l'enonce passe a la ligne."
    )
    lines.append("")
    if shared:
        lines.append(
            "| Theoreme | Lacs | Occurrences | Citent l'autre maison | Par cote | Nature | Verdict |"
        )
        lines.append("|---|---|---|---|---|---|---|")
        for item in shared:
            verdict = (
                "declare"
                if item["citations"] == item["occurrences"]
                else "non declare"
            )
            per_side = ", ".join(
                "%s %d/%d"
                % (lake.rsplit("/", 1)[-1], item["per_lake"][lake][1], item["per_lake"][lake][0])
                for lake in item["lakes"]
            )
            lines.append(
                "| `%s` | %s | %d | %d | %s | %s | %s |"
                % (
                    item["name"],
                    ", ".join("`%s`" % lake.rsplit("/", 1)[-1] for lake in item["lakes"]),
                    item["occurrences"],
                    item["citations"],
                    per_side,
                    item["nature"],
                    verdict,
                )
            )
        lines.append("")
    else:
        lines.append("Aucun nom de theoreme partage entre deux lacs.")
        lines.append("")
    lines.append(
        "**Cet inventaire sous-compte, et c'est mesure.** La detection est par"
        " nom : un meme resultat prouve sous deux noms differents lui echappe."
        " Le controle negatif est `Arrow`, declare des deux cotes"
        " (`game_theory_lean/SocialChoice/Arrow.lean` : `arrow` ;"
        " `lean_game_defs/SocialChoice.lean` : `arrow_impossibility`), et absent"
        " de la table ci-dessus. Un verdict « 0 doublon » ne se lit donc jamais"
        " comme « aucun resultat n'est prouve deux fois ». La table ne tranche"
        " pas davantage l'identite mathematique : elle compare des formulations,"
        " et une « formulation differente » peut etre le meme theoreme encode"
        " deux fois — le cas se rencontre dans ce depot, ou une maison abstraite"
        " et une maison specialisee prouvent le meme resultat a des generalites"
        " differentes. L'organe qui tranche est celui de #24183 (tranche T0) ;"
        " cette page en est l'inventaire, pas le juge."
    )
    lines.append("")

    lines.append("## Regle d'accretion d'un lac")
    lines.append("")
    lines.append(ACCRETION_RULE)
    lines.append("")
    lines.append("Verdicts tranches par la mesure (T2 #23097) :")
    lines.append("")
    lines.append("| Lac | Cas | Verdict | Mesure fondatrice |")
    lines.append("|---|---|---|---|")
    for name, case, verdict, why in ACCRETION_VERDICTS:
        lines.append("| `%s` | %s | %s | %s |" % (name, case, verdict, why))
    lines.append("")
    lines.append(
        "Les cas (1) toolchain divergente et (2) theorie distincte sont deja"
        " tranches : `social_choice_lean_peters` pour (1) (INTRINSIC #7081),"
        " `minimax_lean` et `conway_cgt_lean` pour (2)."
    )
    lines.append("")

    if with_sorry:
        lines.append("## Dette formelle")
        lines.append("")
        lines.append(
            "`distinct_code_sorry` par lac, mesure par"
            " `scripts/lean/count_code_sorry.py --json`. La colonne est opt-in :"
            " le comptage parcourt tout le depot et coute plusieurs minutes."
        )
        lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="sortie machine")
    parser.add_argument("--write", action="store_true", help="ecrit la page")
    parser.add_argument("--check", action="store_true", help="0 si la page est a jour")
    parser.add_argument("--with-sorry", action="store_true", help="ajoute la dette formelle")
    args = parser.parse_args(argv)

    try:
        data = collect(with_sorry=args.with_sorry)
    except CoverageUnavailable as exc:
        # Ni `--write` ni `--check` ne s'executent : la page sur disque n'est
        # pas touchee (elle peut etre saine), et le verdict ne porte pas sur
        # une page que l'on n'a pas reellement mesuree.
        print("COUVERTURE INJOIGNABLE : la page derivee ne peut pas etre certifiee.")
        print(
            "Ni --write ni --check ne sont executes : la page sur disque n'est"
            " pas modifiee."
        )
        print(
            "Ce n'est pas une divergence de l'arbre : c'est la machine qui n'a"
            " pas repondu. NE PAS regenerer ici."
        )
        # La cause est en DERNIER : le garde des pages derivees lit la derniere
        # ligne du generateur pour nommer le defaut.
        print("Cause : %s" % exc)
        return UNMEASURABLE_RC

    rows = data["lakes"]
    orphans = data["orphans"]
    if args.json:
        print(json.dumps(data, indent=1, ensure_ascii=False))
        return 0

    page = render(
        rows,
        orphans,
        data["excluded"],
        data["not_lean"],
        args.with_sorry,
        data["shared_theorems"],
    )
    if args.write:
        PAGE.parent.mkdir(parents=True, exist_ok=True)
        PAGE.write_text(page, encoding="utf-8", newline="\n")
        print("ecrit : %s (%d lacs)" % (PAGE, len(rows)))
        return 0

    if args.check:
        if not PAGE.exists():
            print("ABSENTE : %s n'existe pas -- lancer --write" % PAGE)
            return 1
        current = PAGE.read_text(encoding="utf-8")
        if current != page:
            print(
                "PERIMEE : %s diverge de l'arbre -- relancer --write"
                " (le generateur est proprietaire de la page)" % PAGE
            )
            return 1
        print("A JOUR : %s (%d lacs)" % (PAGE, len(rows)))
        return 0

    sys.stdout.write(page)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
