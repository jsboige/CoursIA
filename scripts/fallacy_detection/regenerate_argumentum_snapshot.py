#!/usr/bin/env python3
"""Regeneration verbatim du snapshot Argumentum a partir des donnees sur disque.

POURQUOI CE SCRIPT EXISTE
-------------------------
Le snapshot `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/data/argumentum_snapshot.json`
est la **reference** que la garde d'integrite
(`scripts/fallacy_detection/tests/test_argumentum_snapshot_integrity.py`) utilise pour
detecter toute derive des CSV/OWL par rapport a leur version amont. Si le manifeste
est en retard sur l'amont (cas du pin `ae84c91c` ou les CSV ont ete resync par PR #14578
sans regenerer le manifeste), la garde rougit a tort.

Ce script **calcule** les SHA1 de blob, les comptes de lignes/colonnes, les familles
Virtues, et les assertions OWL a partir des fichiers sur disque, puis ecrit le manifeste
a l'identique de la structure qu'avait posee le commit `5df1769134f1e56e0db954029df22432611c8e71`
(feat(symbolicai): resync taxonomies Argumentum verbatim + garde d'integrite #13554).

**Il n'edite JAMAIS de SHA a la main.** Chaque valeur du manifeste est derivee
du contenu du disque a l'instant T ; toute la procedure tient dans la commande
suivante :

    python scripts/fallacy_detection/regenerate_argumentum_snapshot.py \\
        --upstream-commit <SHA> --synced-on <YYYY-MM-DD>

**Quand l'utiliser**
- Apres une PR de resync verbatim (#14578 etait dans ce cas : les CSV ont change,
  le manifeste est reste sur c86b71ff, et la garde a rougi 19 j en silence).
- Apres un renommage amont d'une famille Virtues.
- Apres un bump de pin Argumentum qui touche les CSV/OWL.

**Quand NE PAS l'utiliser**
- Pour modifier la STRUCTURE du manifeste (colonnes `required_columns`,
  `families`, structure JSON) -- ces champs relevent d'une PR a part entiere.
- Pour resynchroniser les donnees elles-memes -- c'est le geste de la PR de
  resync (PR #14578 / #14418), pas celui-ci.

CE QUE CHAQUE CHAMP CALCULE
---------------------------
1. `upstream_commit` / `synced_on` : arguments CLI.
2. `files[*].blob_sha1` : SHA1 de blob git (`hashlib.sha1(b"blob %d\0" % len + raw)`),
   identique a `git hash-object` mais sans dependance git.
3. `files[*].rows` / `columns` : `len(rows) - 1` lignes de donnees ; `len(header)`
   colonnes.
4. `files[*].required_columns` : liste canonique des colonnes AIF_*/crossLink_*
   consommees en aval (cf. docstring du test_integrity).
5. `files[*].families` : valeurs distinctes triees de la colonne `family_fr`
   du CSV Vertus -- l'ordre canonique est l'ordre alphabetique francais.
6. `ontologies[*].blob_sha1` : SHA1 de blob OWL.
7. `ontologies[*].object_property_assertions` / `annotation_assertions` :
   compte des balises `<ObjectPropertyAssertion` / `<AnnotationAssertion` dans l'OWL.

Hermetique : stdlib only, aucun acces reseau, aucun appel a git.
"""

import argparse
import csv
import hashlib
import io
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
# Recherche du repo root par les ancres plutot que par comptage de parents :
# le script peut vivre dans un clone (CoursIA) ou un worktree (CoursIA-<suffix>).
REPO = next(
    (p for p in HERE.parents if (p / "MyIA.AI.Notebooks").is_dir()),
    HERE.parent.parent.parent,
)
DATA = REPO / "MyIA.AI.Notebooks" / "SymbolicAI" / "Argument_Analysis" / "data"
ONTOLOGIES = REPO / "MyIA.AI.Notebooks" / "SymbolicAI" / "Argument_Analysis" / "ontologies"
MANIFEST = DATA / "argumentum_snapshot.json"

# Colonnes consommees en aval (miroir de test_argumentum_snapshot_integrity.py).
# Toute colonne ajoutee a ce set doit aussi figurer dans `required_columns`
# du manifeste precedent ; l'inverse n'est pas vrai (une colonne peut disparaitre
# si elle n'est plus consommee, mais c'est une PR dediee).
REQUIRED_COLUMNS = {
    "argumentum_fallacies_taxonomy.csv": [
        "AIF_attackType",
        "AIF_attackedNode",
        "AIF_skosDirectRef",
        "AIF_skosExceptionRef",
        "AIF_skosMappingType",
        "AIF_skosOther",
        "crossLink_Allows",
        "crossLink_Denounces",
        "crossLink_Inverts",
        "crossLink_IsRelatedTo",
        "crossLink_Leverages",
        "crossLink_Mirrors",
        "crossLink_Opposes",
        "crossLink_PredatesOn",
    ],
    "argumentum_virtues_taxonomy.csv": [
        "AIF_attackType",
        "AIF_attackedNode",
        "AIF_criticalQuestion",
        "AIF_skosDirectRef",
        "AIF_skosExceptionRef",
        "AIF_skosMappingType",
        "AIF_skosOther",
        "crossLink_Allows",
        "crossLink_Denounces",
        "crossLink_Inverts",
        "crossLink_IsRelatedTo",
        "crossLink_Leverages",
        "crossLink_Mirrors",
        "crossLink_Opposes",
        "crossLink_PredatesOn",
    ],
}


def git_blob_sha1(raw: bytes) -> str:
    """SHA-1 du blob git des octets bruts. Identique a `git hash-object`.

    Format canonical git blob : `blob <len>\0<raw>`.
    """
    return hashlib.sha1(b"blob %d\0" % len(raw) + raw).hexdigest()


def read_csv_rows(path: Path) -> list[list[str]]:
    """Lecture CSV UTF-8 avec BOM eventuel."""
    return list(csv.reader(io.StringIO(path.read_bytes().decode("utf-8-sig"))))


def csv_metadata(path: Path) -> dict:
    """Calcule les metadonnees verbatim d'un CSV de taxonomie."""
    raw = path.read_bytes()
    rows = read_csv_rows(path)
    return {
        "blob_sha1": git_blob_sha1(raw),
        "rows": len(rows) - 1,
        "columns": len(rows[0]) if rows else 0,
    }


def owl_metadata(path: Path) -> dict:
    """Calcule les metadonnees verbatim d'une OWL.

    - blob_sha1 : empreinte brute.
    - object_property_assertions : compte de `<ObjectPropertyAssertion` (forme
      reconnue par les raisonneurs OWL : HermiT, Pellet, owlrl).
    - annotation_assertions : compte de `<AnnotationAssertion` (forme lisible
      par SPARQL et par le thesaurus SKOS, mais hors semantique logique).
    """
    text = path.read_bytes().decode("utf-8", "replace")
    return {
        "blob_sha1": git_blob_sha1(path.read_bytes()),
        "object_property_assertions": text.count("<ObjectPropertyAssertion"),
        "annotation_assertions": text.count("<AnnotationAssertion"),
    }


def families_from_csv(path: Path, column: str = "family_fr") -> list[str]:
    """Valeurs distinctes triees d'une colonne (ordre alphabetique francais).

    Le tri est stable et independant de l'ordre amont, ce qui rend la valeur
    stable d'un run a l'autre tant que la liste des familles ne change pas.
    """
    rows = read_csv_rows(path)
    header = rows[0]
    if column not in header:
        raise ValueError(f"{path.name} : colonne {column!r} absente (header={header})")
    idx = header.index(column)
    families = {r[idx] for r in rows[1:] if len(r) > idx and r[idx].strip()}
    return sorted(families)


def build_manifest(upstream_commit: str, synced_on: str) -> dict:
    """Construit le manifeste complet a partir des donnees sur disque.

    Le commentaire `_comment` est preserve verbatim du format pose par #13554.
    Ne PAS le modifier ici -- il documente la convention que les auditeurs
    ulterieurs s'attendent a trouver.
    """
    return {
        "_comment": (
            "Genere par la resynchronisation verbatim. Ne pas editer a la main : "
            "relancer une resynchronisation depuis l'amont et regenerer ce fichier. "
            "Le commit amont est celui de master : une ref de branche de travail "
            "ne serait pas retrouvable pour un tiers. Les deux CSV sont inchanges "
            "entre a23e9568 et c86b71ff : le commit unique reste coherent. "
            "Les ontologies sont renommees a l'import (amont argumentum.owl -> "
            "local argumentum_fallacies.owl) ; `upstream_path` conserve la "
            "correspondance, sans quoi un tiers ne retrouve pas la source."
        ),
        "upstream_repo": "ArgumentumGames/Argumentum",
        "upstream_commit": upstream_commit,
        "upstream_branch": "master",
        "synced_on": synced_on,
        "files": {
            "argumentum_fallacies_taxonomy.csv": {
                **csv_metadata(DATA / "argumentum_fallacies_taxonomy.csv"),
                "required_columns": REQUIRED_COLUMNS["argumentum_fallacies_taxonomy.csv"],
            },
            "argumentum_virtues_taxonomy.csv": {
                **csv_metadata(DATA / "argumentum_virtues_taxonomy.csv"),
                "required_columns": REQUIRED_COLUMNS["argumentum_virtues_taxonomy.csv"],
                "families": families_from_csv(DATA / "argumentum_virtues_taxonomy.csv"),
            },
        },
        "ontologies": {
            "argumentum_fallacies.owl": {
                "upstream_path": "docs/ontology/argumentum.owl",
                **owl_metadata(ONTOLOGIES / "argumentum_fallacies.owl"),
            },
            "argumentum_virtues.owl": {
                "upstream_path": "docs/ontology/argumentum_virtues.owl",
                **owl_metadata(ONTOLOGIES / "argumentum_virtues.owl"),
            },
        },
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--upstream-commit",
        required=True,
        help="SHA de commit amont Argumentum (sortie de `git rev-parse` dans le submodule).",
    )
    parser.add_argument(
        "--synced-on",
        required=True,
        help="Date ISO du snapshot (YYYY-MM-DD), convention posee par #13554.",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Affiche le manifeste sans l'ecrire (utile pour verifier avant commit).",
    )
    args = parser.parse_args(argv)

    if not MANIFEST.parent.exists():
        print(f"ERREUR: repertoire manifeste absent: {MANIFEST.parent}", file=sys.stderr)
        return 2

    manifest = build_manifest(args.upstream_commit, args.synced_on)

    if args.check:
        # Mode dry-run : ecrire sur stdout pour diff avant/apres.
        json.dump(manifest, sys.stdout, indent=2, ensure_ascii=False)
        sys.stdout.write("\n")
        return 0

    # Ecriture : newline final obligatoire (Tell c.1424-L5 ★★).
    text = json.dumps(manifest, indent=2, ensure_ascii=False) + "\n"
    MANIFEST.write_text(text, encoding="utf-8")
    print(f"OK: manifeste ecrit -> {MANIFEST}")
    print(f"    upstream_commit = {args.upstream_commit}")
    print(f"    synced_on       = {args.synced_on}")
    for fname, fmeta in manifest["files"].items():
        print(f"    {fname}: blob_sha1={fmeta['blob_sha1']}, rows={fmeta['rows']}, columns={fmeta['columns']}")
    for oname, ometa in manifest["ontologies"].items():
        print(f"    {oname}: blob_sha1={ometa['blob_sha1']}, ObjectPropertyAssertion={ometa['object_property_assertions']}, AnnotationAssertion={ometa['annotation_assertions']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
