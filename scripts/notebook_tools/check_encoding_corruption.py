#!/usr/bin/env python3
"""check_encoding_corruption.py — détecteur de double encodage UTF-8/cp1252 dans les carnets.

Point 3 de #23021. Un carnet commité peut avoir été relu en cp1252 (ou latin-1)
puis ré-encodé en UTF-8 : les caractères accentués et les tirets deviennent des
artefacts visibles (`é` → `Ã©`, `—` → `â€”`, nbsp → `Â `). La corruption est une
corruption de fichier entier : elle touche la source ET les sorties, et elle est
invisible aux organes de perte de contenu (le volume reste identique, seule la
valeur des caractères change).

Signatures détectées (bigrammes de la famille UTF-8→cp1252/latin-1) :

- `Ã` + U+0080..U+00BF  : la famille `é è à è …` (2e octet UTF-8 0x80-0xBF)
- `Â` + U+0080..U+00BF  : nbsp, `°`, `µ`, `·`, `¢`
- `Å€`                  : famille `Š/Ž` (C5 80)
- `â€`                  : famille `— – ' ' " " … „ »` (E2 80)

Ces bigrammes ne sont jamais légitimes en prose française : `â` seul l'est
(château), `â€` non ; `Ã` seul n'apparaît pas en français, `Ã©` non plus.

Usage :

  # Pleine vérification d'un carnet ou d'un répertoire (hook pré-commit, manuel) :
  python scripts/notebook_tools/check_encoding_corruption.py <chemin> [...]

  # Garde CI bloquante : artefacts sur les LIGNES AJOUTÉES des carnets changés
  # par rapport à une référence (formule du fast-lane `{base_ref}`). Un carnet
  # simplement DÉPLACÉ entre la base et la tête est un renommage pur : il
  # n'ajoute aucune ligne et n'est pas signalé (#24068) :
  python scripts/notebook_tools/check_encoding_corruption.py --base origin/main

  # Auto-test interne (fil de fumée du garde) :
  python scripts/notebook_tools/check_encoding_corruption.py --self-test

  # Sortie machine :
  ... --json

Sorties : 0 = propre, 1 = artefacts détectés, 2 = erreur d'usage/lecture.

Exemptions : le littéral `Ã©` est légitime dans la prose qui documente la classe
(docs/, .md) — le détecteur est scopingué aux `.ipynb` et ne la voit pas. Si un
carnet devait porter légitimement un bigramme (cas pathologique), il s'ajoute à
EXEMPT ci-dessous avec sa raison : c'est une décision reviewée, pas un silencing.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Shared rename probe (#24068): a notebook staged as a pure rename was only
# MOVED, so the double-encoding artifacts it carries pre-date the move -- a
# consolidation-by-move must not be reported for a corruption it did not
# introduce. Same family as #24039 (scripts/check_subprocess_encoding.py).
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
# T3-c (#25366) : probe git_index_renames reloge dans scripts/audit/.
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "audit"))
import git_index_renames  # noqa: E402
from git_index_renames import skip_pure_renames  # noqa: E402

# Bigrammes de la famille de corruption (cf. docstring).
MOJIBAKE = re.compile(
    r"Ã[\u0080-¿]"  # Ã + 2e octet (é, è, à, …)
    r"|Â[\u0080-¿]"  # Â + 2e octet (nbsp, °, µ, ·, ¢)
    r"|Å€"  # C5 80 (ŀ, U+0140) ; Š et Ž donnent Å + U+00A0/U+00BD, deja couverts
    r"|â€"  # E2 80 (—, –, quotes, guillemets, …)
)

# Carnets portant légitimement un bigramme : chemin relatif -> raison.
# Vide au départ : la mesure de référence (2026-10-28, #23021) ne recense que
# les deux carnets corrompus (RL-05, TV-03), qui ne sont pas des exemptions.
EXEMPT: dict[str, str] = {}


def count_in_text(text: str) -> int:
    """Nombre d'artefacts dans une chaîne."""
    return len(MOJIBAKE.findall(text))


def count_in_notebook(path: Path) -> int:
    """Nombre d'artefacts dans un carnet (source, sorties, metadata)."""
    raw = path.read_text(encoding="utf-8")
    return count_in_text(raw)


def iter_notebooks(paths: list[Path]) -> list[Path]:
    """Aplatit fichiers/répertoires vers la liste des .ipynb (triée, dedup)."""
    out: set[Path] = set()
    for p in paths:
        if p.is_dir():
            out.update(p.rglob("*.ipynb"))
        elif p.suffix == ".ipynb":
            out.add(p)
        else:
            # Un fichier non-.ipynb nommé explicitement est une erreur d'usage.
            print(f"ERREUR: {p} n'est pas un .ipynb", file=sys.stderr)
            sys.exit(2)
    return sorted(out)


def _is_exempt(rel: str) -> bool:
    return rel in EXEMPT or rel.replace("\\", "/") in EXEMPT


def _resolve(path: str) -> Path:
    """Résout un chemin d'entrée contre la racine du dépôt.

    Le hook pré-commit passe des chemins relatifs au dépôt ; les résoudre
    contre la racine unique du dépôt (celle de la sonde partagée) garantit
    que la lecture du fichier et la clé affichée portent sur le même objet,
    quel que soit le répertoire courant du processus.
    """
    p = Path(path)
    return p if p.is_absolute() else git_index_renames.repo_root() / p


def _rel_key(nb: Path) -> str:
    """Clé repo-relative POSIX d'un carnet (identique aux chemins de git).

    La clé sert à la fois à l'exemption et à l'affichage : elle doit donc
    être la forme que git rapporte, sinon un carnet serait compté sous deux
    noms différents selon le mode (chemin absolu au pré-commit, relatif en
    CI).
    """
    try:
        return nb.resolve().relative_to(
            git_index_renames.repo_root().resolve()).as_posix()
    except (ValueError, OSError):
        return nb.as_posix()


def check_paths(paths: list[Path]) -> dict[str, int]:
    """Pleine vérification : {chemin relatif: compte} pour les carnets sales."""
    dirty: dict[str, int] = {}
    for nb in iter_notebooks(paths):
        rel = _rel_key(nb)
        if _is_exempt(rel):
            continue
        n = count_in_notebook(nb)
        if n:
            dirty[rel] = n
    return dirty


def changed_notebooks(base: str) -> list[str]:
    """Carnets modifiés entre <base>...HEAD (chemins repo-relatifs).

    Le diff est pris **sans pathspec** : un pathspec restreint à `*.ipynb`
    ferait perdre à git la source d'un renommage (il ne verrait que la
    destination), et la carte des renommages -- qui doit connaître cette
    source -- deviendrait incomputable. Le filtrage des `.ipynb` se fait
    donc ici, en Python, sur une liste qui reste complète.
    """
    out = git_index_renames.git_out(
        "diff", "--name-only", f"{base}...HEAD")
    if out is None:
        print(f"ERREUR: git diff {base}...HEAD a échoué", file=sys.stderr)
        sys.exit(2)
    # Décodage explicite UTF-8 (fait par git_out) : text=True decoderait en
    # cp1252 sous Windows et fabriquerait la corruption même que ce
    # détecteur doit mesurer.
    return [l.strip() for l in out.splitlines()
            if l.strip().endswith(".ipynb")]


def added_lines_artifacts(repo_root: Path, nb_rel: str, base: str,
                          source_rel: str | None = None) -> int:
    """Artéfacts sur les LIGNES AJOUTÉES du carnet par rapport à <base>.

    Un carnet ajouté en entier compte toutes ses lignes ; un carnet absent de la
    base (nouveau) est lu en plein.

    ``source_rel`` est le chemin d'origine quand le carnet est un renommage :
    les DEUX chemins sont alors passés au pathspec, ce qui **restaure
    l'appariement** du renommage côté git (mesuré, #24068). Sans le chemin
    source, le pathspec ne contient que la destination, git ne peut plus
    l'apparier à son origine et présente le fichier comme neuf -- toutes ses
    lignes sont alors comptées comme ajoutées, et un carnet simplement
    déplacé ressuscite ses artefacts hérités.
    """
    nb = repo_root / nb_rel
    if not nb.exists():
        return 0
    pathspec = [nb_rel] if source_rel is None else [source_rel, nb_rel]
    out = git_index_renames.git_out(
        "diff", f"{base}...HEAD", "--", *pathspec)
    if out is None:
        print(f"ERREUR: git diff {base}...HEAD -- {nb_rel} a échoué",
              file=sys.stderr)
        sys.exit(2)
    # UTF-8 explicite (cf. changed_notebooks) : jamais text=True ici.
    lines = out.splitlines()
    added = [l[1:] for l in lines if l.startswith("+") and not l.startswith("+++")]
    if not added:
        # Pas de ligne ajoutée lisible (binaire ?) → repli sur la lecture pleine.
        return count_in_notebook(nb)
    # Un .ipynb est du JSON : ajouter un élément de liste ré-écrit la ponctuation
    # de la ligne précédente (virgule de liste), qui apparaît alors en `+` SANS
    # que son contenu ait changé. On ne compte que les lignes ajoutées dont le
    # contenu normalisé n'existe pas déjà côté `-` : la garde cible la matière
    # NOUVELLE, pas le churn de ponctuation.
    def _norm(l: str) -> str:
        return l.strip().rstrip(",").strip()

    removed = {_norm(l[1:]) for l in lines if l.startswith("-") and not l.startswith("---")}
    new_added = [l for l in added if _norm(l) not in removed]
    return count_in_text("\n".join(new_added))


def check_base(base: str) -> dict[str, int]:
    """Garde CI : artefacts sur les lignes ajoutées des carnets changés.

    Cas du renommage (#24068, mesuré) : un carnet simplement *déplacé* entre
    la base et la tête est un renommage pur (R100) -- il n'ajoute aucune
    ligne, donc il ne peut introduire aucun artefact. Le chemin de la
    destination seul dans le pathspec cassait l'appariement de git, qui
    présentait alors le carnet comme un fichier neuf : tous ses artefacts
    hérités étaient comptés comme ajoutés (rc=1 sur un simple déplacement).
    Deux corrections, mesurées sur un dépôt témoin :

    - renommage pur (R100) : le carnet est écarté de la cible ;
    - renommage AVEC retouche (R<100) : le chemin source est remis dans le
      pathspec, ce qui restaure l'appariement -- seules les lignes
      réellement ajoutées sont alors comptées.
    """
    repo_root = git_index_renames.repo_root()
    dirty: dict[str, int] = {}
    renames = git_index_renames.renames_between(base)
    skipped = 0
    for nb_rel in changed_notebooks(base):
        if _is_exempt(nb_rel):
            continue
        info = renames.get(nb_rel)
        if info is not None:
            source_rel, score = info
            if score == "100":
                skipped += 1
                continue  # pur déplacement : aucune ligne ajoutée (#24068)
            n = added_lines_artifacts(repo_root, nb_rel, base, source_rel)
        else:
            n = added_lines_artifacts(repo_root, nb_rel, base)
        if n:
            dirty[nb_rel] = n
    if skipped:
        print(f"encoding-corruption: {skipped} pure rename(s) ignored -- "
              "their artifacts pre-date the move (#24068)", file=sys.stderr)
    return dirty


def self_test() -> int:
    """Fil de fumée : le pattern attrape la famille et ignore le français sain."""
    positive = "mÃ©taheuristique â€” plateau Â "
    negative = "métaheuristique — plateau château naïve µ ° ¢   "
    ok = count_in_text(positive) == 3 and count_in_text(negative) == 0
    print("SELF-TEST " + ("OK" if ok else "ECHEC"))
    return 0 if ok else 1


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("paths", nargs="*", help="fichiers .ipynb ou répertoires")
    ap.add_argument("--base", help="référence git : vérifier les lignes ajoutées des carnets changés")
    ap.add_argument("--self-test", action="store_true", help="auto-test du pattern")
    ap.add_argument("--json", action="store_true", help="sortie JSON")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    if args.base:
        dirty = check_base(args.base)
    elif args.paths:
        # A notebook staged as a pure rename was only MOVED (#24068): the
        # double-encoding artifacts it carries pre-date the move. This
        # pre-commit half scans the WHOLE file, so it would re-report the
        # inherited artifacts and leave the lane with only SKIP=, i.e.
        # disabling the guard. (The CI half, --base, needed the same
        # treatment: measured, it re-reported them too -- see check_base.)
        kept, skipped = skip_pure_renames(args.paths)
        if skipped:
            print(f"encoding-corruption: {len(skipped)} pure rename(s) "
                  "ignored -- their artifacts pre-date the move (#24068)",
                  file=sys.stderr)
        dirty = check_paths([_resolve(p) for p in kept])
    else:
        ap.error("aucun chemin (ou --base / --self-test)")
        return 2

    if args.json:
        print(json.dumps({"dirty": dirty, "count": len(dirty)}, ensure_ascii=False, indent=1))
    else:
        for rel, n in dirty.items():
            print(f"{rel}: {n} artefact(s) de double encodage")
        if dirty:
            print(f"ENCODING CORRUPTION: {len(dirty)} carnet(s), "
                  f"{sum(dirty.values())} artefact(s)")
        else:
            print("OK: aucun artefact de double encodage")
    return 1 if dirty else 0


if __name__ == "__main__":
    sys.exit(main())
