"""Registre des corpus open access candidats pour les sondes ICT (#26911).

Ce module est l'artefact de la premiere tranche de l'issue #26911 (« sortir du
sous-corpus appauvri ») : un inventaire de corpus dont la **provenance**, la
**licence**, les **conditions d'utilisation** et les **droits de redistribution**
sont etablis *avant* toute copie.

Trois regles gouvernent le registre :

1. **Aucune donnee de corpus n'est copiee dans le depot.** Le registre ne
   contient que des metadonnees : chaque champ textuel est une description,
   jamais un echantillon. Un test le verifie mecaniquement.
2. **Chaque porte un droit est posee, chaque fait porte une source.** Une
   taille, une licence, une provenance : le champ ``*_source`` dit ou le fait
   a ete lu (carte de l'hebergeur, API de l'hebergeur, papier archive dans le
   gisement GDrive). Un fait sans source n'est pas un fait, c'est une
   affirmation.
3. **Un corpus dont les droits ne sont pas etablis est ecarte, pas devine.**
   Le statut ``a-verifier`` dit exactement quel point manque.

Les tailles sont mesurees via l'API ``datasets-server`` de Hugging Face
(``/size?dataset=<id>``), le 2026-11-16 ; elles sont donc reproductibles.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

#: Statuts possibles d'un corpus candidat.
Statut = Literal["retenu", "candidat", "a-verifier", "ecarte"]

#: Mode d'acces unique : le corpus se telecharge a l'execution, il n'entre
#: jamais dans l'arbre du depot.
ACCES_TELECHARGEMENT = "telechargement-a-l-execution"

#: Longueur maximale d'un champ textuel du registre. Au-dela, le champ
#: ressemblerait a un echantillon de donnees : c'est le seuil que le test
#: enforce pour interdire la copie d'un corpus dans le depot.
LONGUEUR_MAX_CHAMP = 400


@dataclass(frozen=True)
class CorpusCandidat:
    """Un corpus candidat, avec ses quatre champs de droits et leurs sources.

    Attributs :
        cle: identifiant court et stable, utilise par les carnets.
        nom: nom lisible du corpus.
        url: page du corpus chez l'hebergeur.
        licence: identifiant SPDX de la licence declaree par l'hebergeur.
        licence_source: ou le champ de licence a ete lu.
        conditions: conditions d'utilisation, en clair.
        redistribution: ce que la licence autorise pour la redistribution.
        langue: langue(s) du corpus.
        provenance: d'ou viennent les donnees.
        provenance_source: ou cette provenance a ete lue.
        taille_lignes: nombre de lignes mesure.
        taille_source: ou la taille a ete mesuree.
        statut: l'un des quatre statuts.
        motif: pourquoi ce statut, en une phrase.
        acces: mode d'acces au corpus.
        publication_archivee: chemin de la publication decrivant le corpus dans
            le gisement GDrive, ou ``None`` si elle n'y est pas encore.
    """

    cle: str
    nom: str
    url: str
    licence: str
    licence_source: str
    conditions: str
    redistribution: str
    langue: str
    provenance: str
    provenance_source: str
    taille_lignes: int
    taille_source: str
    statut: Statut
    motif: str
    acces: str = ACCES_TELECHARGEMENT
    publication_archivee: str | None = None


#: Licence declaree par la carte d'un corpus. La lecture se fait dans le
#: front-matter de la carte (``license:``), confirme par l'API de l'hebergeur
#: (``cardData.license``).
_CARTE = "https://huggingface.co/datasets/{cle}/raw/main/README.md"
_API = "https://huggingface.co/api/datasets/{cle}"
_TAILLE = "https://datasets-server.huggingface.co/size?dataset={cle}"

#: Chemin de la publication de reference dans le gisement partage.
_GISEMENT = "G:\\Mon Drive\\MyIA\\IA\\Bibliographie IA\\MachineLearning\\Computational Humor"


CANDIDATS: tuple[CorpusCandidat, ...] = (
    CorpusCandidat(
        cle="CreativeLang/ColBERT_Humor_Detection",
        nom="ColBERT Humor — 200 000 textes courts formels etiquetes",
        url="https://huggingface.co/datasets/CreativeLang/ColBERT_Humor_Detection",
        licence="cc-by-2.0",
        licence_source=(
            _CARTE.format(cle="CreativeLang/ColBERT_Humor_Detection")
            + " (front-matter `license: cc-by-2.0`), confirme par "
            + _API.format(cle="CreativeLang/ColBERT_Humor_Detection")
            + " (`cardData.license`)"
        ),
        conditions=(
            "CC BY 2.0 : attribution (auteur + source) obligatoire, partage dans "
            "les memes conditions pour les adaptations, aucune restriction "
            "supplementaire. Les sources amont (titres de presse, CSV de "
            "blagues) portent leurs propres conditions, qui ne sont pas "
            "couvertes par la declaration du miroir."
        ),
        redistribution=(
            "Autorisee avec mention d'attribution. Aucune copie dans le depot : "
            "telechargement a l'execution."
        ),
        langue="en",
        provenance=(
            "Deux sources melangees puis equilibrees : le News Category dataset "
            "(titres du Huffington Post, 2012-2018) et un jeu de 231 657 blagues "
            "Reddit compile en CSV (Kaggle) ; 200 000 textes formels au total."
        ),
        provenance_source=(
            "Copie archivee de la publication dans le gisement GDrive : "
            + _GISEMENT
            + "\\2022 - Annamoradnejad and Zoghi - ColBERT Using BERT Sentence "
            "Embedding in Parallel Neural Networks for Computational Humor "
            "(arXiv 2004.12765).pdf"
        ),
        taille_lignes=200_000,
        taille_source=(
            _TAILLE.format(cle="CreativeLang%2FColBERT_Humor_Detection")
            + " — split `train`, mesure du 2026-11-16"
        ),
        statut="retenu",
        motif=(
            "Droits etablis et lus a la source, taille mesuree, publication "
            "archivee et lue : c'est le corpus d'humour le plus large du lot et "
            "il n'est pas un sous-corpus. C'est le corpus retenu pour le "
            "rejeu d'ICT-35."
        ),
        publication_archivee=(
            _GISEMENT
            + "\\2022 - Annamoradnejad and Zoghi - ColBERT Using BERT Sentence "
            "Embedding in Parallel Neural Networks for Computational Humor "
            "(arXiv 2004.12765).pdf"
        ),
    ),
    CorpusCandidat(
        cle="ZSvedic/humor-chains",
        nom="Humor Chains — fils Reddit (une submission + une replique)",
        url="https://huggingface.co/datasets/ZSvedic/humor-chains",
        licence="cc-by-4.0",
        licence_source=(
            _CARTE.format(cle="ZSvedic/humor-chains")
            + " (front-matter `license: cc-by-4.0` et section `## License`), "
            "confirme par "
            + _API.format(cle="ZSvedic/humor-chains")
        ),
        conditions=(
            "CC BY 4.0 : attribution obligatoire. La carte rappelle que les "
            "publications viennent de dumps Reddit (2005-06 a 2023-12) dont le "
            "contenu appartient aux utilisateurs et non a Reddit ; les pseudos "
            "ont ete remplaces."
        ),
        redistribution=(
            "Autorisee avec attribution, sous reserve des conditions de la source "
            "Reddit, qui prévalent sur celles du miroir."
        ),
        langue="en",
        provenance=(
            "Dumps Reddit (academictorrents, 2005-06 a 2023-12), sous-reddit "
            "« funny », filtres de score (10 votes a la submission, 5 a la "
            "replique) et de longueur (256 caracteres)."
        ),
        provenance_source=(
            _CARTE.format(cle="ZSvedic/humor-chains") + " (section `## Dataset Creation`)"
        ),
        taille_lignes=6_494,
        taille_source=(
            _TAILLE.format(cle="ZSvedic%2Fhumor-chains")
            + " — splits `train` 5 844 et `test` 650, mesure du 2026-11-16"
        ),
        statut="candidat",
        motif=(
            "Droits du miroir etablis, mais le format est conversationnel et non "
            "une classification binaire d'humour : hors protocole ICT-35, "
            "utile comme donnee d'appoint."
        ),
    ),
    CorpusCandidat(
        cle="MichiganNLP/MUStARD",
        nom="MUStARD — sarcasme multimodal (texte + contexte video)",
        url="https://huggingface.co/datasets/MichiganNLP/MUStARD",
        licence="mit",
        licence_source=(
            _CARTE.format(cle="MichiganNLP/MUStARD")
            + " (front-matter `license: mit`) — la carte ne comporte aucune "
            "autre information de droits"
        ),
        conditions=(
            "MIT declaree par le miroir, sans mention de provenance ni de "
            "conditions ; le depot amont n'a pas ete atteint pendant la mesure, "
            "donc ses conditions ne sont pas verifiees."
        ),
        redistribution="Non etablie : la declaration du miroir ne suffit pas.",
        langue="en (non declaree par la carte)",
        provenance=(
            "Non documentee sur la carte du miroir ; l'amont (MUStARD, Amir et "
            "al.) n'a pas pu etre consulte pendant la mesure."
        ),
        provenance_source="Carte du miroir (aucune section de provenance)",
        taille_lignes=1_380,
        taille_source=(
            _TAILLE.format(cle="MichiganNLP%2FMUStARD")
            + " — split `train`, mesure du 2026-11-16"
        ),
        statut="a-verifier",
        motif=(
            "Une licence declaree par un miroir ne vaut pas licence de la "
            "source : sans verification amont, les droits de redistribution "
            "restent inconnus. A verifier avant tout usage."
        ),
    ),
    CorpusCandidat(
        cle="DFKI-SLT/SemEval2018_Task7",
        nom="SemEval 2018 Task 7 (humour) — miroir reduit",
        url="https://huggingface.co/datasets/DFKI-SLT/SemEval2018_Task7",
        licence="other",
        licence_source=(
            _CARTE.format(cle="DFKI-SLT/SemEval2018_Task7")
            + " (`license: other`) ; la section `### Licensing Information` "
            "renvoie a « More Information Needed »"
        ),
        conditions=(
            "Non etablies : la carte ne dit rien des conditions d'utilisation, "
            "et sa citation renvoie a SemEval-2018 Task 1 (extraction de "
            "relations) au lieu de Task 7 (humour)."
        ),
        redistribution="Non etablie.",
        langue="en",
        provenance=(
            "Miroir reduit de la tache SemEval-2018 Task 7 (deux configurations, "
            "350+150 et 348+150 lignes), sans provenance documentee."
        ),
        provenance_source=(
            _CARTE.format(cle="DFKI-SLT/SemEval2018_Task7")
            + " (section `### Citation Information`, qui cite la mauvaise tache)"
        ),
        taille_lignes=998,
        taille_source=(
            _TAILLE.format(cle="DFKI-SLT%2FSemEval2018_Task7")
            + " — deux configurations (`train` 350 + `test` 150 ; `train` 348 + "
            "`test` 150), mesure du 2026-11-16"
        ),
        statut="ecarte",
        motif=(
            "Deux defauts mesures sur la carte : les droits ne sont pas "
            "etablis et la provenance citee est celle d'une autre tache. "
            "Corpus ecarte, sans prejudice pour le SemEval d'origine."
        ),
    ),
    CorpusCandidat(
        cle="truthfulqa/truthful_qa",
        nom="TruthfulQA — 817 questions de verite",
        url="https://huggingface.co/datasets/truthfulqa/truthful_qa",
        licence="apache-2.0",
        licence_source=(
            _CARTE.format(cle="truthfulqa/truthful_qa")
            + " (front-matter `license: apache-2.0` et section `### Licensing "
            "Information`), confirme par "
            + _API.format(cle="truthfulqa/truthful_qa")
        ),
        conditions=(
            "Apache-2.0 : attribution et mention de la licence obligatoires, "
            "licence des modifications ; la carte indique explicitement que le "
            "dataset est sous Apache License 2.0."
        ),
        redistribution="Autorisee, avec mention de la licence et des modifications.",
        langue="en",
        provenance=(
            "Questions et reponses de reference ecrites par les auteurs du "
            "papier (Lin, Hilton, Evans), 817 items de validation, plus une "
            "configuration de generation."
        ),
        provenance_source=(
            _CARTE.format(cle="truthfulqa/truthful_qa")
            + " (sections `### Paper` et `### Licensing Information`)"
        ),
        taille_lignes=1_634,
        taille_source=(
            _TAILLE.format(cle="truthfulqa%2Ftruthful_qa")
            + " — deux configurations de 817 lignes, mesure du 2026-11-16"
        ),
        statut="candidat",
        motif=(
            "Droits nets et source lue, mais la sonde vise la veracite et non "
            "l'humour : hors protocole ICT-35, retenu pour les autres sondes ICT."
        ),
    ),
    CorpusCandidat(
        cle="pminervini/HaluEval",
        nom="HaluEval — 64 507 paires (question, reponse) hallucinees",
        url="https://huggingface.co/datasets/pminervini/HaluEval",
        licence="apache-2.0",
        licence_source=(
            _CARTE.format(cle="pminervini/HaluEval")
            + " (front-matter `license: apache-2.0`), confirme par "
            + _API.format(cle="pminervini/HaluEval")
        ),
        conditions=(
            "Apache-2.0 : attribution et mention de la licence obligatoires, "
            "licence des modifications."
        ),
        redistribution="Autorisee, avec mention de la licence et des modifications.",
        langue="en",
        provenance=(
            "Sept configurations construites pour l'evaluation d'hallucination : "
            "`qa`, `qa_samples`, `dialogue`, `dialogue_samples`, `summarization`, "
            "`summarization_samples` (10 000 lignes chacune) et `general` (4 507)."
        ),
        provenance_source=(
            _API.format(cle="pminervini/HaluEval")
            + " (`cardData.dataset_info`, une entree par configuration)"
        ),
        taille_lignes=64_507,
        taille_source=(
            _TAILLE.format(cle="pminervini%2FHaluEval")
            + " — sept configurations, mesure du 2026-11-16"
        ),
        statut="candidat",
        motif=(
            "Droits nets, taille mesuree et bien superieure au sous-corpus de "
            "reference : pertinent pour une sonde d'hallucination, pas pour "
            "ICT-35."
        ),
    ),
    CorpusCandidat(
        cle="tasksource/wice",
        nom="WiCE — entailment de affirmations Wikipedia",
        url="https://huggingface.co/datasets/tasksource/wice",
        licence="cc-by-sa-4.0",
        licence_source=(
            _CARTE.format(cle="tasksource/wice")
            + " (front-matter `license: cc-by-sa-4.0`), confirme par "
            + _API.format(cle="tasksource/wice")
        ),
        conditions=(
            "CC BY-SA 4.0 : attribution obligatoire et partage dans les memes "
            "conditions pour les adaptations."
        ),
        redistribution=(
            "Autorisee avec attribution, et les adaptations doivent rester en "
            "CC BY-SA 4.0."
        ),
        langue="en",
        provenance=(
            "Affirmations extraites de Wikipedia et alignees sur Wikidata "
            "(Kamoi et al., EMNLP 2023, https://aclanthology.org/2023.emnlp-main.470)."
        ),
        provenance_source=(
            _CARTE.format(cle="tasksource/wice") + " (citation de la publication)"
        ),
        taille_lignes=5_377,
        taille_source=(
            _TAILLE.format(cle="tasksource%2Fwice")
            + " — splits `train` 3 470, `validation` 949, `test` 958, mesure du 2026-11-16"
        ),
        statut="candidat",
        motif=(
            "Droits nets et taille mesuree ; sonde d'attribution de source, hors "
            "protocole ICT-35."
        ),
    ),
)


def par_cle(cle: str) -> CorpusCandidat:
    """Renvoie le corpus correspondant a ``cle``.

    Lève :
        KeyError: si aucune cle ne correspond.
    """
    for candidat in CANDIDATS:
        if candidat.cle == cle:
            return candidat
    raise KeyError(cle)


def retenus() -> tuple[CorpusCandidat, ...]:
    """Renvoie les corpus dont les droits sont etablis et retenus."""
    return tuple(c for c in CANDIDATS if c.statut == "retenu")


def plan_acces(cle: str) -> dict[str, str]:
    """Renvoie le plan d'acces d'un corpus : ou le prendre, et sous quelles obligations.

    Le plan est volontairement minimal : une URL, un mode d'acces, une licence
    et une obligation d'attribution. Il ne contient aucun echantillon.
    """
    candidat = par_cle(cle)
    return {
        "url": candidat.url,
        "mode": candidat.acces,
        "licence": candidat.licence,
        "obligation": candidat.redistribution,
        "taille_lignes": str(candidat.taille_lignes),
    }
