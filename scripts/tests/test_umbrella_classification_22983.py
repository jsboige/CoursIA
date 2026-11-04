"""Classification umbrella / grain : une TRANCHE n'est pas un conteneur.

#22983 -- mesure du 27/10 (615 issues ouvertes) : 41 issues portent un
titre `EPIC...` sans le label `EPIC`. Parmi elles, 10 nomment un PARENT
(`[EPIC #10355] Phase 3`, `[Epic Origami #19742 - Pli 3]`, `Epic #21424
T3 : ...`) et sont des TRANCHES ; les 31 autres sont de vrais
CONTENEURS.

La consequence mesuree : sur une UMBRELLA, le filtre de livraison ne
cherche que le MARQUEUR DE CONTENEUR (`[INFO] candidate-delivered`), pas
le marqueur de grain (`[DELIVERED] lane ... -- motif`). Une tranche
livree et classee umbrella reste donc servable -- mesure sur #21435
(`[DELIVERED] lane myia-po-2028:CoursIA` present, issue servie quand
meme avec un `[CLAIMED]` fantome).

Les DEUX organes (le LECTEUR `check_lane_claim.py` et le TIRAGE
`pick_idle_grain.py`) doivent rendre le meme verdict : le test le
verifie sur les titres mesures.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc
import pick_idle_grain as pig

#: Les 10 titres mesures qui nomment un parent : ce sont des TRANCHES.
TITRES_TRANCHE = [
    "[EPIC #10355] Phase 2/5 : dataset par produit cartésien Scénarii × taxonomies",
    "[Epic Origami #19898 — Pli 2] Sensibilite 2026 : ajout additif au lac",
    "[EPIC #10355/#17578] Tranche C étape 3 : test externe humain du corpus",
    "[EPIC #10355] Phase 3 : baselines du gate (majoritaire, aleatoire, lexicale)",
    "[Epic Origami #18605 - Pli 3] 3D Gaussian Splatting avec gsplat",
    "Epic #21424 T5 : détecteur de prose de concession ajoutée, puis inventaire",
    "Epic #21424 T3 : inventaire classé des cellules à sortie de repli sur main",
    "[Epic Origami #19898 — Pli 6] Compter les couplages parfaits",
    "[Epic Origami #19742 - Pli 2] Programmes simples : un seul organe de l'automate",
    "[Epic Origami #19742 - Pli 3] Irreductibilite computationnelle, et Hashlife",
]

#: Les conteneurs : le titre commence par EPIC mais ne nomme AUCUN parent.
TITRES_CONTENEUR = [
    "[EPIC] Consolidation des accrétions — scan repo-wide du 24/10",
    "[Epic Origami] openai/math — distillation par plis : replier 372 familles",
    "[EPIC][QC] Ligue de stratégies Framework : protocole de mesure commun",
    "[EPIC] Quant-AI : angles morts mesurés face à awesome-quant-ai",
    "EPIC — Tour de fond, sans parent ni tranche",
]


def _lecteur(title, labels=()):
    return clc._is_umbrella_issue(
        {"title": title, "labels": [{"name": n} for n in labels]})


def test_une_tranche_n_est_pas_une_umbrella_pour_le_lecteur():
    for title in TITRES_TRANCHE:
        assert _lecteur(title) is False, f"tranche classee umbrella : {title}"


def test_une_tranche_n_est_pas_une_umbrella_pour_le_tirage():
    for title in TITRES_TRANCHE:
        assert pig.is_umbrella_classification(title, []) is False, (
            f"tranche classee umbrella par le tirage : {title}")


def test_un_conteneur_reste_une_umbrella():
    for title in TITRES_CONTENEUR:
        assert _lecteur(title) is True, f"conteneur non classe umbrella : {title}"
        assert pig.is_umbrella_classification(title, []) is True, (
            f"conteneur non classe umbrella par le tirage : {title}")


def test_le_label_reste_autoritaire():
    """Une issue explicitement labelisee `EPIC` reste une umbrella."""
    assert _lecteur("Epic #21424 T3 : une tranche", ["EPIC"]) is True
    assert pig.is_umbrella_classification(
        "Epic #21424 T3 : une tranche", ["EPIC"]) is True


def test_les_deux_organes_rendent_le_meme_verdict():
    """Parite : le LECTEUR et le TIRAGE classent de la meme facon."""
    corpus = [(t, []) for t in TITRES_TRANCHE + TITRES_CONTENEUR]
    corpus += [(t, ["EPIC"]) for t in TITRES_TRANCHE]
    corpus += [("Une issue ordinaire", []), ("[EPIC] vide", [])]
    for title, labels in corpus:
        lecteur = _lecteur(title, labels)
        tirage = pig.is_umbrella_classification(title, labels)
        assert lecteur == tirage, (
            f"divergence des organes sur {title!r} : "
            f"lecteur={lecteur} tirage={tirage}")


def test_le_cas_mesure_21435_est_ecarte_par_le_filtre_de_livraison():
    """Le cas mesure : une tranche livree ne doit plus etre servie.

    Le filtre de livraison `recent` ne s'applique qu'au GRAIN. Une fois la
    tranche classee grain, son marqueur `[DELIVERED]` l'ecarte.
    """
    body = ("[DELIVERED] lane myia-po-2028:CoursIA -- T3 livre : inventaire "
            "classe en commentaire de l'Epic #21424, aucun fichier du depot.")
    comments = [{"body": body, "createdAt": "2026-10-26T13:18:06Z",
                 "author": {"login": "jsboige"}, "url": "u1"}]
    assert pig._delivery_event_from_comments(comments)[0] is True
    assert pig._RECENT_DELIVERY_MARKER_RE.search(body)
