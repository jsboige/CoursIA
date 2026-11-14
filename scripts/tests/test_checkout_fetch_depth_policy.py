"""Garde-fou de la profondeur de checkout des workflows (issue #26383).

Un `actions/checkout` avec `fetch-depth: 0` telecharge tout l'historique du
depot -- sur un lien facture a l'octet, chaque job se paie. La forme adoptee
par le depot (cf. `always-on-guards.yml` l. 238) est

    fetch-depth: 0
    filter: blob:none

qui garde le graphe de commits (indispensable aux diffs 3-points, qui lisent
le merge-base) sans telecharger les blobs de l'historique.

Cet organe verifie l'invariant : **tout `fetch-depth: 0` porte un `filter:`**
dans son propre bloc de cles. Le cas general verifie est le defaut qui a ete
corrige le 13/11 -- le dernier site sans filtre du depot
(`.github/workflows/notebook-cell-id-ratchet.yml`).

Aucun dependance : le lecture des workflows est faite par un analyseur
textuel (indentation + regex), pas par PyYAML -- le job `Scripts Tests (CPU)`
n'installe pas PyYAML, et un test qui depend d'une bibliotheque absente
serait vert par defaut (le cas "organe qui ne voit rien").

La liste `EXCEPTIONS` porte les sites qui auraient besoin des blobs (une
justification ecrite est obligatoire pour y figurer) ; elle est vide au
13/11/2026.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

RACINE = Path(__file__).resolve().parents[2]
DOSSIER_WORKFLOWS = RACINE / ".github" / "workflows"

# Sites autorises a garder `fetch-depth: 0` SANS filtre, avec la
# justification ecrite de la raison (une exception sans motif est refusee).
EXCEPTIONS: dict[str, str] = {}

# Une cle `fetch-depth: 0`, eventuellement suivi d'un commentaire de fin de
# ligne (forme mesuree dans le depot : 4 sites).
MOTIF_FETCH_DEPTH_0 = re.compile(r"^(?P<indent>\s*)fetch-depth:\s*0\s*(?:#.*)?$")
MOTIF_CLE = re.compile(r"^(?P<indent>\s*)(?P<cle>[A-Za-z0-9_-]+):\s*(?P<valeur>.*)$")
MOTIF_FILTRE = re.compile(r"^(?P<indent>\s*)filter:\s*(?P<valeur>\S+)\s*$")


def _fichiers_workflows() -> list[Path]:
    if not DOSSIER_WORKFLOWS.is_dir():
        return []
    return sorted(
        chemin
        for chemin in DOSSIER_WORKFLOWS.rglob("*")
        if chemin.suffix in (".yml", ".yaml") and chemin.is_file()
    )


def _sites_sans_filtre(texte: str) -> list[int]:
    """Renvoie les numeros de ligne des `fetch-depth: 0` sans `filter:` voisin.

    Le `filter:` doit etre une cle du MEME bloc de cles : on parcourt les
    lignes qui suivent, et on s'arrete sur une cle de meme indentation
    (autre cle du bloc) ou de moins (fin du bloc).
    """
    lignes = texte.splitlines()
    sites: list[int] = []
    for index, ligne in enumerate(lignes):
        correspondance = MOTIF_FETCH_DEPTH_0.match(ligne)
        if not correspondance:
            continue
        indent = len(correspondance.group("indent"))
        filtre_trouve = False
        suivant = index + 1
        while suivant < len(lignes):
            courante = lignes[suivant]
            if courante.strip():
                indentation_courante = len(courante) - len(courante.lstrip())
                if indentation_courante < indent:
                    break
                if indentation_courante == indent:
                    if MOTIF_FILTRE.match(courante):
                        filtre_trouve = True
                        break
                    cle = MOTIF_CLE.match(courante)
                    if cle:
                        # autre cle du meme bloc : le filtre n'est pas la.
                        break
            suivant += 1
        if not filtre_trouve:
            sites.append(index + 1)
    return sites


def _violations() -> list[str]:
    violations: list[str] = []
    for chemin in _fichiers_workflows():
        relatif = chemin.relative_to(RACINE).as_posix()
        if relatif in EXCEPTIONS:
            continue
        texte = chemin.read_text(encoding="utf-8", errors="replace")
        for ligne in _sites_sans_filtre(texte):
            violations.append(f"{relatif}:{ligne}")
    return violations


def test_aucun_checkout_profondeur_complete_sans_filtre() -> None:
    """Invariant du depot : `fetch-depth: 0` implique un `filter:`."""
    violations = _violations()
    assert violations == [], (
        "checkout `fetch-depth: 0` sans `filter:` (le depot telecharge alors "
        "tous les blobs de l'historique) : "
        + ", ".join(violations)
        + " -- ajouter `filter: blob:none`, ou une exception motivee dans "
        "EXCEPTIONS (cf. issue #26383)."
    )


def test_la_lecture_vit_reellement_des_sites() -> None:
    """Contre-mesure : un scan qui ne voit rien ne doit pas etre vert.

    Le depot compte plus de 80 sites `fetch-depth: 0` filtres : si la
    detection ne les voit pas, le test precedent ne mesure rien.
    """
    total = 0
    for chemin in _fichiers_workflows():
        texte = chemin.read_text(encoding="utf-8", errors="replace")
        for ligne in texte.splitlines():
            if MOTIF_FETCH_DEPTH_0.match(ligne):
                total += 1
    assert total >= 80, (
        f"seulement {total} sites `fetch-depth: 0` detectes -- l'inventaire a "
        "change de forme, le garde-fou ne mesurerait plus rien"
    )


def test_le_detecteur_refuse_un_site_sans_filtre() -> None:
    """Controle negatif de l'analyseur, sur un workflow de synthèse."""
    workflow_sans_filtre = """\
jobs:
  job:
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0
"""
    assert _sites_sans_filtre(workflow_sans_filtre) == [6]


def test_le_detecteur_accepte_un_site_filtre() -> None:
    """Controle negatif inverse : le filtre voisin est reconnu."""
    workflow_avec_filtre = """\
jobs:
  job:
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0
          filter: blob:none
"""
    assert _sites_sans_filtre(workflow_avec_filtre) == []


def test_le_detecteur_accepte_un_commentaire_mentionnant_la_profondeur() -> None:
    """Une mention en prose n'est pas une regle : elle ne doit pas rougir."""
    workflow_commentaire = """\
jobs:
  job:
    steps:
      # le job clonait le depot entier (fetch-depth: 0)
      - uses: actions/checkout@v4
        with:
          fetch-depth: 1
"""
    assert _sites_sans_filtre(workflow_commentaire) == []


def test_chaque_exception_port_son_motif() -> None:
    """Une exception sans justification ecrite est refusee."""
    for chemin, motif in EXCEPTIONS.items():
        assert motif.strip(), (
            f"l'exception {chemin} ne porte aucun motif : une exception sans "
            "justification n'est pas une exception, c'est un oubli"
        )
        assert (RACINE / chemin).is_file(), (
            f"l'exception {chemin} ne correspond a aucun fichier du depot"
        )


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-q"]))
