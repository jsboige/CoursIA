# -*- coding: utf-8 -*-
"""Organe humour du banc consolide GameTheory-18c (extraction #20316, T7').

Source de verite du corpus humour : les fichiers de donnees de ce dossier.
``humour_corpus.json`` porte les 120 instances annotees ; il est consomme par
le banc 18c (section Passage a l'echelle) et par la couche ICT
(``ict/humor_pairs.py`` delegue ici). Les autres fichiers portent la
provenance et l'annotation figee :

- ``argumentum_scenarii.csv`` : snapshot du CSV upstream Argumentum, capture
  au HEAD amont ``80dccece49`` (voir ``NOTICE-SCENARII`` : provenance,
  licence double marque, et la mesure qui montre pourquoi la copie au pin
  sous-module de FallacyDetection ne peut PAS servir ici -- 24/60 instances
  divergentes). La derivation (heuristiques d'annotation puis
  ``random.seed(42)`` + ``random.sample(labeled_arg, 60)``) sur ce snapshot
  reproduit exactement les instances ``arg-*`` du corpus -- c'est le temoin
  d'identite vivant du banc (cellule de chargement de 18c).
- ``humour_pairs_edits.json`` : les 30 edits main (setup, punchline,
  punchline_neutre, controle) des paires minimales humour/unfun.
- ``humour_typology.json`` : typologie par mecanisme comique des paires
  (pun / topical / sociale), annotation figee avant mesure (#14035).

Avant l'extraction, le corpus vivait dans les cellules 26-33 de 18c et chaque
consommateur (``ict/humor_pairs.load_corpus_dur`` puis le pilote ICT-35)
le reproduisait par execution positionnelle -- fragile a la renumerotation,
exigeait OPENROUTER_API_KEY (utilisee seulement par le detecteur LLM du banc)
et declenchait un fetch reseau (cache en chemin relatif, non commite).
L'organe supprime ces trois dependances : le chargement est local,
deterministe et sans cle.
"""
from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any

DATA_DIR = Path(__file__).resolve().parent

# Taxonomie 5-cellules du banc (effet communicationnel : rire x recadrage x
# uptake x refus). Inchangee depuis la consolidation #14032.
LABELS: tuple[str, ...] = (
    "humour_reussi",
    "rire_sans_recadrage",
    "recadrage_sans_rire",
    "offensif_compris_non_partage",
    "rien",
)

# Champs du contrat d'instance (verbe du banc, cellule 33 d'origine).
_REQUIRED_FIELDS = ("id", "texte", "features", "label", "justification", "source")

# Provenance de l'echantillon Argumentum (60 instances sur 120, seed 42).
ARGUMENTUM_SNAPSHOT = DATA_DIR / "argumentum_scenarii.csv"
# Empreinte du snapshot commite (16 premiers hex du sha256) et etat upstream
# au moment de la capture. La capture reproduit la derivation des outputs
# committes du banc (distribution 48/14/13/7/38, sources 60/30/20/10).
ARGUMENTUM_SNAPSHOT_SHA256_16 = "4b924640d7c353ab"
ARGUMENTUM_UPSTREAM_AT_CAPTURE = "80dccece49"
SAMPLE_SEED = 42
SAMPLE_K = 60
N_MANUAL_JOKES = 30
N_NEGATIVE_STATEMENTS = 20
N_EDGE_CASES = 10


def load_corpus() -> list[dict[str, Any]]:
    """Charge les 120 instances annotees ; le contrat est verifie a chaque lecture."""
    corpus = json.loads(
        (DATA_DIR / "humour_corpus.json").read_text(encoding="utf-8")
    )
    validate_corpus(corpus)
    return corpus


def validate_corpus(corpus: list[dict[str, Any]], *, min_size: int = 100) -> None:
    """Verifie le contrat du corpus : taille, champs, taxonomie, unicite des ids."""
    assert isinstance(corpus, list) and len(corpus) >= min_size, (
        f"CORPUS_DUR attendu >= {min_size} instances, recu {len(corpus)}"
    )
    ids = [inst["id"] for inst in corpus]
    assert len(set(ids)) == len(ids), "ids dupliques dans CORPUS_DUR"
    for inst in corpus:
        for field in _REQUIRED_FIELDS:
            assert field in inst, f"champ {field} manquant sur {inst.get('id')}"
        assert inst["label"] in LABELS, (
            f"label hors taxonomie : {inst['label']!r} sur {inst['id']}"
        )


def label_distribution(corpus: list[dict[str, Any]]) -> Counter:
    """Effectifs par label, pour le controle de stratification des tranches."""
    return Counter(inst["label"] for inst in corpus)


def load_pair_edits() -> dict[str, list[str]]:
    """Table des edits main : id -> [setup, punchline, punchline_neutre, controle].

    - setup + punchline = le texte COMMITTE de l'instance (source de verite :
      le corpus), re-verifie au chargement (span unique, suffixe exact).
    - punchline_neutre : continuation coherente attendue -- tue l'incongruite,
      conserve le lexique du registre, taille comparable.
    - controle : AUTRE continuation coherente non-humorale de taille
      comparable (controle de distance d'edition).
    """
    return json.loads(
        (DATA_DIR / "humour_pairs_edits.json").read_text(encoding="utf-8")
    )


def build_pairs(corpus: list[dict[str, Any]]) -> list[dict[str, str]]:
    """Construit les paires minimales humour/unfun/controle depuis la table d'edits.

    Chaque paire porte : le texte original (humour), sa version punchline
    neutralisee (unfun), et le controle de distance d'edition. La zone
    d'edition (punchline) est disjoncte du prefixe commun (setup) par
    construction.
    """
    by_id = {inst["id"]: inst["texte"] for inst in corpus}
    pairs = []
    for jid, (setup, punch, unfun, ctrl) in load_pair_edits().items():
        texte = by_id[jid]
        assert texte.count(punch) == 1, f"{jid}: punchline absente ou non unique"
        assert texte.endswith(punch) and texte.startswith(setup), (
            f"{jid}: le texte commite ne se coupe pas setup|punchline comme declare"
        )
        pairs.append({
            "id": jid,
            "setup": setup,
            "humour": texte,
            "unfun": setup + unfun,
            "ctrl_edit": setup + ctrl,
        })
    return pairs


def validate_pairs(pairs: list[dict[str, str]], *, min_pairs: int = 30) -> None:
    """Contrat des paires : nombre, unicite, prefixe commun exact."""
    assert len(pairs) >= min_pairs, f"{len(pairs)} paires < {min_pairs} requises"
    ids = [p["id"] for p in pairs]
    assert len(set(ids)) == len(ids), "ids de paires dupliques"
    for p in pairs:
        for variant in ("unfun", "ctrl_edit"):
            assert p[variant].startswith(p["setup"]), (
                f"{p['id']}/{variant}: le setup n'est pas prefixe commun exact"
            )
        assert p["unfun"] != p["humour"] and p["ctrl_edit"] != p["humour"]


def load_typology() -> dict[str, Any]:
    """Annotation figee des paires par mecanisme comique (pun/topical/sociale).

    Regle d'annotation (figee avant mesure, c. de claim 14035) : mecanisme
    comique PRINCIPAL -- la connaissance requise pour que la blague fonctionne.
    ``borderline`` liste les paires dont le classement se discute (deux
    mecanismes reels, un dominant retenu) ; ``min_per_type`` est le plancher
    declare : sous ce nombre de paires, la jambe est non concluante.
    """
    return json.loads(
        (DATA_DIR / "humour_typology.json").read_text(encoding="utf-8")
    )


# --------------------------------------------------------------------------- #
# Derivation Argumentum (provenance rejouable) -- cellules 28/29/31/33 du banc
# d'origine, portees par l'organe depuis l'extraction. Le temoin d'identite
# (18c cellule de chargement + test CI) compare cette derivation au corpus
# committé : elles doivent etre egales instance par instance.
# --------------------------------------------------------------------------- #

# Champs FR retenus au parse (cellule 29 d'origine).
_ARG_FIELDS = ("path", "catégorie", "sous-catégorie", "titre",
               "baratineur", "piocheur", "contexte", "enjeu", "suggestion")


def label_argumentum(row: dict[str, str]) -> str:
    """Annotation manuelle par catégorie + sous-catégorie Argumentum.

    Regles transparentes (hypothese du banc : un scenario avec enjeu absurde
    + suggestion inattendue = humour_reussi ; un scenario histoire = souvent
    rien ou recadrage_sans_ire) :
    - 'pop culture' → souvent humour_reussi (références décalées)
    - 'mythologie' → recadrage_sans_rire (anachronisme classique)
    - 'relation intime' → mixte, registre humoristique fréquent
    - 'histoire' → souvent rien (matériel trop sérieux)
    - 'politique' → offensif_compris_non_partage (sujet sensible)
    """
    cat = row["catégorie"]
    enjeu = row.get("enjeu", "").lower()
    suggestion = row.get("suggestion", "").lower()
    if cat == "pop culture":
        return "humour_reussi"  # par défaut pop culture = décalage
    if cat == "mythologie":
        return "recadrage_sans_rire"  # mythologie = anachronisme sec
    if cat == "politique":
        return "offensif_compris_non_partage"
    if cat == "histoire":
        return "rien"  # matériel historique = contexte trop sérieux
    if cat == "vie professionnelle":
        return "humour_reussi" if any(w in enjeu + suggestion
                                      for w in ["absurd", "ridicul", "drôle",
                                                "plaisant", "amusant"]) else "rien"
    if cat == "vie personnelle":
        return "rire_sans_recadrage"  # vie perso = souvent rire sans jeu partagé
    if cat == "relation intime":
        return "humour_reussi"  # relation intime = registre humoristique fréquent
    return "rien"


def derive_argumentum_instances() -> list[dict[str, Any]]:
    """Rejoue la derivation des 60 instances ``arg-*`` depuis le snapshot committé.

    Parse du snapshot CSV, annotation par les heuristiques transparentes,
    puis ``random.seed(42)`` + ``random.sample(..., 60)`` et construction des
    instances -- mot pour mot la cellule 33 d'origine du banc. Le corpus
    committé doit etre EGAL a cette derivation (temoin d'identite).
    """
    import csv
    import random

    with open(ARGUMENTUM_SNAPSHOT, "r", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    labeled_arg = [{**{k: r[k] for k in _ARG_FIELDS},
                    "label": label_argumentum(r)} for r in rows]

    random.seed(SAMPLE_SEED)  # reproductibilité (cellule 33 d'origine)
    arg_sample = random.sample(labeled_arg, k=SAMPLE_K)
    arg_instances = []
    for r in arg_sample:
        lab = r["label"]
        features = {
            "laugh":       lab == "humour_reussi" or lab == "rire_sans_recadrage",
            "reframe":     lab == "humour_reussi" or lab == "recadrage_sans_rire",
            "uptake":      lab == "humour_reussi",
            "refus":       lab == "offensif_compris_non_partage",
        }
        arg_instances.append({
            "id": "arg-" + r["path"],
            "texte": "[" + r["catégorie"] + "/" + r["sous-catégorie"] + "] "
                     + r["titre"] + " — baratineur: " + r["baratineur"]
                     + ", contexte: " + r["contexte"][:60] + "...",
            "features": features,
            "label": lab,
            "justification": "Annotation manuelle Argumentum : catégorie "
                             + r["catégorie"] + " → heuristique cell[30] donne " + lab,
            "source": "ArgumentumGames/Argumentum",
        })
    return arg_instances


def assert_corpus_identity() -> None:
    """Temoin d'identite : le corpus committé == la derivation rejouee.

    Compare les 60 instances ``arg-*`` du fichier a la derivation depuis le
    snapshot CSV (heuristiques + seed 42). Leve AssertionError si le fichier
    et la provenance ont derive. Les 60 instances manuelles (blagues,
    negatives, edge) sont des donnees figees : elles n'ont pas de derivation
    rejouable, leur contrat est porte par ``validate_corpus``.
    """
    corpus_arg = [inst for inst in load_corpus() if inst["id"].startswith("arg-")]
    derived = derive_argumentum_instances()
    assert len(corpus_arg) == SAMPLE_K, (
        f"{len(corpus_arg)} instances arg-* dans le corpus, {SAMPLE_K} attendues"
    )
    assert corpus_arg == derived, (
        "le corpus committé a dérivé de sa derivation Argumentum "
        "(snapshot CSV + heuristiques + seed 42) : voir humour_banc/"
    )
