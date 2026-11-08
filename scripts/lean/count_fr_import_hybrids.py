#!/usr/bin/env python3
"""Recensement reproductible des hybrides FR-import des jumeaux `_en` Lean.

EPIC #4980 (i18n) -- repond au point 2 de #24019 : deux mesures du meme
defaut circulaient sans pouvoir etre reconciliees (le census de #23906
annoncait **29 fichiers / 41 aretes**, une re-mesure independante **70 / 118**
sur les memes lacs). Un chiffre non reproductible ne sert ni de preuve ni de
budget de travail : ce script le rend reproductible, et nomme le predicat.

## Le defaut mesure

Un jumeau anglais `Foo_en.lean` doit etre auto-suffisant : il declare son
propre `namespace ..._en` et `import` les jumeaux `_en` de ses dependances.
L'**hybride FR-import** est le cas ou le fichier declare bien sous namespace
suffixe mais importe encore le module **FR** d'une dependance dont le jumeau
`_en` existe. La byte-identite du corps peut etre parfaite : c'est l'en-tete
d'imports qui ment, et le premier consommateur EN croise reproduit le mismatch
de types (incident `knot_lean`).

## Le predicat, en quatre criteres (tous necessaires)

1. le fichier s'appelle `*_en.lean` ;
2. il vit dans un **lac** (`lakefile.toml` ou `lakefile.lean` a la racine du
   repertoire), et hors du perimetre vendore : `.lake/packages/`, `_peters/`,
   `reference_docs/` -- les memes exclusions que la regle i18n de
   `.claude/rules/code-style.md` -- et il est **atteignable** par les
   roots/globs declares du lakefile (#24666) : un miroir `_en` hors build
   n'est pas mesure (Lake ne le compilera jamais, son arete serait
   theorique), il est nomme dans la sortie avec les hors-lac ;
3. il declare au moins un `namespace` dont le nom finit par `_en`, **et** au
   moins une declaration propre (theorem, lemma, def, instance, structure,
   class, abbrev, inductive) ;
4. il porte au moins une **arete** : un `import` d'un module du **meme lac**
   dont le chemin ne finit pas par `_en` et dont le jumeau `Foo_en.lean`
   existe sur le disque. L'auto-import (le `_en` qui importe sa propre
   jumelle FR, `Nim_en -> Conway.Nim`) **compte** comme une arete -- c'est un
   sous-pattern nomme du census, pas une exemption.

Chaque critere est visible dans la sortie (`--list` montre, par fichier, le
nombre de declarations et les aretes). Un chiffre sans ses criteres n'est pas
une mesure, c'est une opinion datee.

## Ce que le script ne fait pas

Il **compte**, il ne juge pas la gravite : le census distinguait les aretes a
« risque nul pratique » (declarations sur types Mathlib seulement) des
« bombes latentes » (signatures portant un type du lac FR). Cette gradation
demande une lecture par fichier et ne s'automatise pas ici.

Il ne **cable pas** de porte : la proposition 1 de #23906 (verdict `FR-IMPORT`
dans `check_i18n_siblings.py`) est un choix a part, dont le rayon d'action est
le nombre de fichiers mesure ci-dessous. Ce script est l'instrument qui rend
ce choix decidable.

## Le compte est DATE, jamais une constante

Le corps de #24019 porte un releve du 2026-11-01 (71 fichiers / 119 aretes /
8 lacs). Ce chiffre **n'est pas reproductible a la lettre** et ne doit pas etre
lu comme tel : le corpus converge a chaque tranche i18n mergee, donc le compte
du jour est plus bas. C'est pourquoi la sortie nomme le **commit mesure** --
un chiffre sans son commit n'est pas falsifiable, et deux mesures d'etats
differents ne peuvent pas etre comparees.

Le census de #23906 (29 / 41), lui, etait faux au meme etat : il omettait deux
repertoires entiers (`ProgramGames`, `Search/discrepancy_lean`) et comptait
`knot_lean` a 3 alors qu'il mesure 0. Voir le corps de #24019 pour la
comparaison lac par lac.

Usage
-----
    python scripts/lean/count_fr_import_hybrids.py                  # racine par defaut
    python scripts/lean/count_fr_import_hybrids.py --root MyIA.AI.Notebooks
    python scripts/lean/count_fr_import_hybrids.py --json
    python scripts/lean/count_fr_import_hybrids.py --list            # detail par fichier
    python scripts/lean/count_fr_import_hybrids.py --self-test       # controle positif

Codes de sortie : 0 = mesure rendue ; 2 = **incident** -- racine absente,
perimetre vide (aucun lac), ou lacs trouves **sans aucun** fichier `_en.lean`
mesure. Les deux derniers cas sont traites en incident et non en « zero
propre » : un compte nul qui ne se distingue pas d'un chemin casse n'est pas
une mesure.
"""

from __future__ import annotations

import argparse
import json
from typing import Callable
import re
import subprocess
import sys
import tempfile
from pathlib import Path

RC_OK = 0
RC_INCIDENT = 2

try:
    # Organ-first (#24666) : le parseur roots/globs des lakefiles vit dans
    # l'organe i18n `check_i18n_siblings` (TOML + DSL, `exact` et prefixes
    # glob), qui a fait ses preuves en garde de build -- il n'est pas duplique.
    from check_i18n_siblings import lake_targets
except ImportError:  # chargement par spec_from_file_location (tests)
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from check_i18n_siblings import lake_targets

#: Exclusions du perimetre i18n (cf `.claude/rules/code-style.md`, EPIC #4980).
#: Les fragments portent leurs deux separateurs : sans le `/` de tete, un
#: repertoire exclu **a la racine mesuree** (`--root social_choice_lean_peters`)
#: passait au travers, et le fragment n'etait alors qu'un sous-chemin chanceux.
#: Le lake externe de la regle vit sous `GameTheory/SocialChoice/` : le
#: fragment historique `/_peters/` ne matchait AUCUN segment de ce chemin
#: (exclusion morte, point 4 de la review Hermes de #24032).
EXCLUDED_FRAGMENTS = ("/.lake/packages/", "/social_choice_lean_peters/", "/reference_docs/")

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(theorem|lemma|def|instance|structure|class|abbrev|inductive)\b",
    re.MULTILINE,
)
NS_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.'«»]+)", re.MULTILINE)
IMPORT_RE = re.compile(r"^\s*import\s+(.+)$", re.MULTILINE)
BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT_RE = re.compile(r"--[^\n]*")


def strip_comments(text: str) -> str:
    """Retire les commentaires : un motif d'en-tete cite en commentaire n'est pas un en-tete.

    Lean a deux formes : bloc `/- ... -/` (docstrings incluses) et ligne `--`.
    Sans ce retrait, un `import Foo` ou un `def` commentes comptaient -- faux
    positif structurel, invisible sur un corpus ou personne ne commente un
    import.
    """
    return LINE_COMMENT_RE.sub("", BLOCK_COMMENT_RE.sub("", text))


def in_scope(path: Path) -> bool:
    """Vrai si le chemin est dans le perimetre i18n (hors vendore)."""
    as_posix = "/" + path.as_posix().strip("/") + "/"
    return not any(fragment in as_posix for fragment in EXCLUDED_FRAGMENTS)


def find_lakes(root: Path) -> list[Path]:
    """Racines de lac sous `root`, hors dependances vendorees."""
    found = set()
    for pattern in ("lakefile.toml", "lakefile.lean"):
        for lakefile in root.rglob(pattern):
            if in_scope(lakefile):
                found.add(lakefile.parent)
    return sorted(found)


def lakefile_of(lake: Path) -> Path | None:
    """Le lakefile du lac (`.toml` prioritaire, puis `.lean`)."""
    for name in ("lakefile.toml", "lakefile.lean"):
        candidate = lake / name
        if candidate.is_file():
            return candidate
    return None


def reachable_predicate(lake: Path) -> tuple[bool, "Callable[[str], bool] | None"]:
    """(#24666) Predicat d'atteignabilite par les roots/globs du lakefile.

    Rend ``(False, None)`` quand le lakefile ne declare RIEN de lisible
    (aucune lib, aucun root/glob) : le lac est alors mesure en SUR-ENSEMBLE
    (l'ancien comportement), et compte parmi les lacs non restreints -- le
    dire, plutot que de vider silencieusement un lac mal parse.

    Un module `Foo_en` est atteignable s'il est dans `exact` (roots/globs
    nus, convention i18n : le jumeau est declare explicitement) ou sous un
    prefixe glob (`Foo` couvre `Foo`, `Foo.*`).
    """
    lakefile = lakefile_of(lake)
    if lakefile is None:
        return False, None
    exact, globs = lake_targets(lakefile)
    if not exact and not globs:
        return False, None

    def _reachable(module_path: str) -> bool:
        if module_path in exact:
            return True
        return any(
            module_path == prefix or module_path.startswith(prefix + ".")
            for prefix in globs
        )

    return True, _reachable


def read_source(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def measured_commit(root: Path) -> str | None:
    """Prefixe du commit mesure, ou None hors depot git.

    Le compte derive a chaque tranche i18n mergee : le nommer sans son commit
    le rend non falsifiable. Une mesure indisponible n'est pas une erreur --
    on le dit, on n'invente pas une valeur.
    """
    try:
        out = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "--short=9", "HEAD"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=10,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    commit = out.stdout.strip()
    return commit if out.returncode == 0 and commit else None


def _under_any(path: Path, parents: list[Path]) -> bool:
    for parent in parents:
        try:
            path.relative_to(parent)
        except ValueError:
            continue
        return True
    return False


def imports_of(text: str) -> list[str]:
    """Modules importes (les imports multiples sur une ligne sont separes)."""
    modules: list[str] = []
    for match in IMPORT_RE.finditer(text):
        for token in match.group(1).split():
            if token.startswith("«") or token.startswith('"'):
                continue
            modules.append(token)
    return modules


def hybrid_edges(lake: Path, source: Path, text: str) -> list[str]:
    """Aretes FR-import : module du meme lac, non suffixe, jumeau `_en` present."""
    edges: list[str] = []
    for module in imports_of(text):
        if module.endswith("_en"):
            continue
        target = lake / (module.replace(".", "/") + ".lean")
        if not target.exists() or not in_scope(target):
            continue
        if target.with_name(target.stem + "_en.lean").exists():
            edges.append(module)
    return edges


def scan_lake(lake: Path) -> tuple[list[dict], int, bool]:
    """Fichiers `_en.lean` du lac, avec leurs compteurs et leurs aretes.

    (#24666) Rend ``(records, n_hors_roots, restriction_active)`` : les
    fichiers non atteignables par les roots/globs du lakefile sortent du
    compte (Lake ne les build jamais, leur arete serait theorique) et sont
    NOMMES -- un lac au lakefile illisible reste mesure en sur-ensemble,
    `restriction_active` a False, pour ne pas vider un lac mal parse.
    """
    restricted, reachable = reachable_predicate(lake)
    records: list[dict] = []
    n_hors_roots = 0
    for source in sorted(lake.rglob("*_en.lean")):
        if not in_scope(source):
            continue
        if restricted:
            module_path = (
                source.relative_to(lake).as_posix()[: -len(".lean")]
                .replace("/", ".")
            )
            if not reachable(module_path):
                n_hors_roots += 1
                continue
        text = strip_comments(read_source(source))
        namespaces = [m.group(1) for m in NS_RE.finditer(text)]
        records.append(
            {
                "lake": lake.name,
                "lake_path": lake.as_posix(),
                "file": source.as_posix(),
                "relative": source.relative_to(lake).as_posix(),
                "namespace_suffixed": any(ns.endswith("_en") for ns in namespaces),
                "declarations": len(DECL_RE.findall(text)),
                "edges": hybrid_edges(lake, source, text),
            }
        )
    return records, n_hors_roots, restricted


def is_hybrid(record: dict) -> bool:
    """Les quatre criteres, en une predicate lisible."""
    return (
        record["namespace_suffixed"]
        and record["declarations"] >= 1
        and bool(record["edges"])
    )


def census(root: Path) -> dict:
    records: list[dict] = []
    n_hors_roots = 0
    lakes_unparsed: list[str] = []
    lakes = find_lakes(root)
    for lake in lakes:
        lake_records, lake_excluded, restricted = scan_lake(lake)
        records.extend(lake_records)
        n_hors_roots += lake_excluded
        if not restricted:
            lakes_unparsed.append(lake.name)

    # Fichiers `_en.lean` du perimetre qu'aucun lac ne porte : ils ne peuvent
    # pas produire d'arete (une arete est un import du **meme lac**), mais les
    # taire ferait passer un perimetre tronque pour un corpus converge.
    outside = [
        source
        for source in root.rglob("*_en.lean")
        if in_scope(source) and not _under_any(source, lakes)
    ]

    hybrids = [r for r in records if is_hybrid(r)]
    per_lake: dict[str, dict] = {}
    for record in hybrids:
        entry = per_lake.setdefault(record["lake"], {"files": 0, "edges": 0})
        entry["files"] += 1
        entry["edges"] += len(record["edges"])

    return {
        "root": root.as_posix(),
        "measured_commit": measured_commit(root),
        "lakes": [lake.name for lake in lakes],
        "n_lakes": len(lakes),
        "n_en_files": len(records),
        "n_en_outside_lakes": len(outside),
        "n_en_outside_roots": n_hors_roots,
        "lakes_measured_superset": sorted(lakes_unparsed),
        "files": len(hybrids),
        "edges": sum(len(r["edges"]) for r in hybrids),
        "per_lake": dict(sorted(per_lake.items())),
        "hybrids": [
            {
                "lake": r["lake"],
                "relative": r["relative"],
                "declarations": r["declarations"],
                "edges": r["edges"],
            }
            for r in hybrids
        ],
    }


def render(report: dict, show_list: bool) -> str:
    commit = report.get("measured_commit")
    provenance = (
        f"Mesure au commit {commit} : le compte derive quand le corpus converge, "
        "il ne se compare qu'a un etat, jamais au releve du corps de #24019."
        if commit
        else "Mesure hors depot git : le compte est date de l'instant, sans commit "
        "pour le rattacher."
    )
    lines = [
        f"Perimetre : {report['root']} ({report['n_lakes']} lacs, "
        f"{report['n_en_files']} fichiers *_en.lean analyses)",
        provenance,
    ]
    if report.get("n_en_outside_lakes"):
        lines.append(
            f"  ({report['n_en_outside_lakes']} fichiers *_en.lean hors lac, "
            "non mesures : une arete se mesure dans un lac)"
        )
    if report.get("n_en_outside_roots"):
        lines.append(
            f"  ({report['n_en_outside_roots']} fichiers *_en.lean hors "
            "roots/globs declares, non mesures : Lake ne les build jamais, "
            "leur arete serait theorique)"
        )
    if report.get("lakes_measured_superset"):
        lines.append(
            "  (lacs au lakefile sans lib lisible, mesures en sur-ensemble : "
            + ", ".join(report["lakes_measured_superset"]) + ")"
        )
    lines.extend(
        [
            "",
            f"TOTAL hybrides FR-import : {report['files']} fichiers / "
            f"{report['edges']} aretes",
            "",
            f"{'lac':32s} {'fichiers':>9s} {'aretes':>7s}",
            "-" * 52,
        ]
    )
    for lake, entry in report["per_lake"].items():
        lines.append(f"{lake:32s} {entry['files']:9d} {entry['edges']:7d}")
    if show_list:
        lines.append("")
        lines.append("Detail par fichier :")
        for item in report["hybrids"]:
            lines.append(
                f"  [{item['lake']}] {item['relative']} "
                f"(decl={item['declarations']}) -> {', '.join(item['edges'])}"
            )
    return "\n".join(lines)


def self_test() -> int:
    """Controle positif construit : un hybride connu doit remonter, un propre non.

    Le micro-lac est ecrit dans un repertoire temporaire -- aucune dependance a
    l'etat du depot, donc le test reste vrai quand les lacs convergent.
    """
    failures: list[str] = []
    with tempfile.TemporaryDirectory() as tmp:
        lake = Path(tmp) / "fixture_lean"
        (lake / "Alpha").mkdir(parents=True)
        (lake / "lakefile.toml").write_text('name = "fixture"\n', encoding="utf-8")

        # FR de base + jumeau propre : l'import du jumeau est deja suffixe.
        (lake / "Alpha" / "Base.lean").write_text(
            "namespace Alpha.Base\n\ndef base := 1\n\nend Alpha.Base\n",
            encoding="utf-8",
        )
        (lake / "Alpha" / "Base_en.lean").write_text(
            "import Alpha.Base_en\n\nnamespace Alpha.Base_en\n\ndef base := 1\n\n"
            "end Alpha.Base_en\n",
            encoding="utf-8",
        )
        # POSITIF : namespace suffixe + declaration + import FR non suffixe.
        (lake / "Alpha" / "Hybrid_en.lean").write_text(
            "import Alpha.Base\n\nnamespace Alpha.Hybrid_en\n\ndef hybrid := 2\n\n"
            "end Alpha.Hybrid_en\n",
            encoding="utf-8",
        )
        # NEGATIF : namespace suffixe mais aucune declaration propre.
        (lake / "Alpha" / "Empty_en.lean").write_text(
            "import Alpha.Base\n\nnamespace Alpha.Empty_en\n\nend Alpha.Empty_en\n",
            encoding="utf-8",
        )
        # NEGATIF : jumeau `_en` de la dependance absent -> pas d'arete.
        (lake / "Alpha" / "NoTwin.lean").write_text(
            "namespace Alpha.NoTwin\n\ndef x := 1\n\nend Alpha.NoTwin\n",
            encoding="utf-8",
        )
        (lake / "Alpha" / "Lonely_en.lean").write_text(
            "import Alpha.NoTwin\n\nnamespace Alpha.Lonely_en\n\ndef y := 1\n\n"
            "end Alpha.Lonely_en\n",
            encoding="utf-8",
        )
        # NEGATIF : hors perimetre (vendore).
        vendored = lake / ".lake" / "packages" / "vendor"
        vendored.mkdir(parents=True)
        (vendored / "lakefile.toml").write_text('name = "v"\n', encoding="utf-8")
        (vendored / "Vendored_en.lean").write_text(
            "import Alpha.Base\n\nnamespace Vendored_en\n\ndef z := 1\n\n"
            "end Vendored_en\n",
            encoding="utf-8",
        )

        report = census(lake)
        found = {item["relative"] for item in report["hybrids"]}

        if "Alpha/Hybrid_en.lean" not in found:
            failures.append("CONTROLE POSITIF manque : Alpha/Hybrid_en.lean")
        for unexpected in (
            "Alpha/Base_en.lean",
            "Alpha/Empty_en.lean",
            "Alpha/Lonely_en.lean",
        ):
            if unexpected in found:
                failures.append(f"faux positif : {unexpected}")
        if any("vendor" in item for item in found):
            failures.append("faux positif : un fichier vendore a ete mesure")
        if report["files"] != 1 or report["edges"] != 1:
            failures.append(
                f"compte attendu 1 fichier / 1 arete, obtenu "
                f"{report['files']} / {report['edges']}"
            )

    if failures:
        print("SELF-TEST ECHEC")
        for failure in failures:
            print(f"  - {failure}")
        return 1
    print("SELF-TEST OK : 1 hybride detecte, 3 faux positifs ecartes, vendore ignore")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Recensement reproductible des hybrides FR-import des "
        "jumeaux `_en` Lean (EPIC #4980, #24019).",
    )
    parser.add_argument(
        "--root",
        default="MyIA.AI.Notebooks",
        help="racine de la recherche (defaut : MyIA.AI.Notebooks)",
    )
    parser.add_argument("--json", action="store_true", help="sortie machine")
    parser.add_argument(
        "--list",
        action="store_true",
        help="detail par fichier : declarations et aretes",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="controle positif construit dans un lac temporaire",
    )
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()

    root = Path(args.root)
    if not root.is_dir():
        print(f"INCIDENT : racine introuvable : {root}", file=sys.stderr)
        return RC_INCIDENT

    report = census(root)
    if report["n_lakes"] == 0:
        print(
            "INCIDENT : aucun lac trouve -- un perimetre vide n'est pas un "
            "zero propre (mauvaise racine ?).",
            file=sys.stderr,
        )
        return RC_INCIDENT
    if report["n_en_files"] == 0:
        print(
            f"INCIDENT : {report['n_lakes']} lac(s) trouve(s) sous {root}, mais "
            "aucun fichier *_en.lean mesure -- ce zero n'est pas distinguable "
            "d'un chemin casse, donc il n'est pas rendu comme une mesure. "
            "Pointer --root sur le repertoire qui contient les lac(s) portant "
            "les jumeaux.",
            file=sys.stderr,
        )
        return RC_INCIDENT

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=1))
    else:
        print(render(report, args.list))
    return RC_OK


if __name__ == "__main__":
    sys.exit(main())
