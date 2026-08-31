#!/usr/bin/env python3
"""Garde d'integrite des snapshots de taxonomie Argumentum.

POURQUOI CET ORGANE EXISTE
--------------------------
Les deux CSV de ``Argument_Analysis/data/`` sont des copies verbatim de l'amont
``ArgumentumGames/Argumentum``. Ils alimentent les notebooks Argument_Analysis,
FallacyDetection (02/03) et ``scripts/fallacy_detection/``. Ils ont pourri
**sept semaines en silence** (import du 03/07 -> constat du 30/08) et rien n'a
rougi, parce qu'un CSV perime parse parfaitement : meme nombre de lignes, meme
nombre de PK, tous les notebooks au vert. La panne etait invisible par
construction. Mesure du 30/08, avant resynchronisation :

  - ``AIF_attackType`` / ``AIF_attackedNode`` : colonnes tout simplement ABSENTES
    (145 lignes typees en amont) -- or le capstone ICT declare consommer un
    "graphe d'attaques AIF type" qui n'existait donc pas cote CoursIA ;
  - couche crosslinks a 8 cellules renseignees contre 940 en amont ;
  - 3938 cellules divergentes sur les colonnes communes ;
  - les 3 familles Virtues renommees les 6-7/08 portaient encore leurs anciens
    noms (``Langage exact``, ``Raisonnement valide``, ``Rigueur mathematique``).

Ce dernier point est le plus vicieux : chercher ``Inference maitrisee`` dans le
snapshot rendait 0 ligne, et ce zero se lit comme "rien a faire" alors qu'il
signale un instrument casse.

CE QUE CHAQUE TEST ATTRAPE
--------------------------
1. ``test_blob_sha`` -- le fichier sur disque est-il OCTET POUR OCTET celui qui a
   ete synchronise ? Attrape la corruption de fins de ligne. L'import de juillet
   (#5183) annoncait "verbatim" mais avait converti en CRLF les 139 LF nus
   internes aux cellules citees : le blob stocke differait de l'amont. La regle
   ``-text`` du ``.gitattributes`` empeche desormais la conversion ; ce test
   verifie qu'elle tient.
2. ``test_required_columns`` -- les colonnes que les notebooks consomment
   existent-elles ? Rouge sur l'etat d'avant (AIF_* absentes).
3. ``test_virtues_families`` -- les libelles de familles sont-ils ceux du
   manifeste ? Rouge sur l'etat d'avant (anciens noms).
4. ``test_legacy_copy_removed`` -- la troisieme copie historique
   ``SymbolicAI/data/`` a-t-elle ete SUPPRIMEE ? Rouge sur la reintroduction :
   distribuer une copie tierce de la taxonomie reouvre le piege documente
   en aout 2026 (derive silencieuse de sept semaines, voir #13578/#13619).
   Avant #13740, le test equivalent etait ``test_legacy_copy_unified_with_canonical``
   (rouge si divergence). La copie ayant ete retiree, la garde devient
   "n'existons pas" -- si elle reapparait, c'est deliberement et doit resynchroniser.

QUE FAIRE QUAND C'EST ROUGE
---------------------------
Resynchroniser depuis l'amont et REGENERER le manifeste. Ne jamais "reparer" en
editant l'assertion ou le manifeste a la main : le rouge dit que le snapshot a
diverge de l'amont, pas que l'attendu est faux. Un renommage amont DOIT passer
par une resynchronisation deliberee -- c'est precisement le geste que ce test
rend obligatoire au lieu de le laisser filer en silence.

LES ONTOLOGIES SONT COUVERTES PAR LES MEMES GARDES
--------------------------------------------------
``Argument_Analysis/ontologies/`` recoit les deux OWL du meme amont, avec en
plus un invariant qui leur est propre : les aretes du graphe argumentatif
doivent etre RAISONNABLES. Jusqu'au 30/08 elles etaient emises uniquement en
``AnnotationAssertion`` -- hors semantique logique d'OWL : SPARQL les voit,
aucun raisonneur (HermiT, Pellet, owlrl) ne les voit. Les OWL distribues ici
portaient donc ``ObjectPropertyAssertion = 0``, et tout delta d'inference owlrl
calcule dessus etait vide PAR CONSTRUCTION -- ce qui se serait lu comme un
verdict sur l'outillage aval alors que la panne etait en amont (critere 3 de
#13567). L'amont emet desormais les deux formes (Argumentum #1231) ; ces tests
verifient que la distribution locale les porte toujours toutes les deux.

Hermetique : stdlib only, aucun acces reseau, aucun appel a git.
"""

import csv
import hashlib
import io
import json
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent.parent
DATA = REPO / "MyIA.AI.Notebooks" / "SymbolicAI" / "Argument_Analysis" / "data"
MANIFEST = DATA / "argumentum_snapshot.json"


def _git_blob_sha1(path: Path) -> str:
    """SHA-1 du blob git des octets bruts, sans passer par git."""
    raw = path.read_bytes()
    return hashlib.sha1(b"blob %d\0" % len(raw) + raw).hexdigest()


def _manifest() -> dict:
    if not MANIFEST.exists():
        pytest.fail(
            f"Manifeste absent : {MANIFEST}. Il est la reference de la "
            "resynchronisation verbatim ; sans lui l'organe est aveugle."
        )
    return json.loads(MANIFEST.read_text(encoding="utf-8"))


def _rows(path: Path) -> list[list[str]]:
    return list(csv.reader(io.StringIO(path.read_bytes().decode("utf-8-sig"))))


FILES = ["argumentum_fallacies_taxonomy.csv", "argumentum_virtues_taxonomy.csv"]


@pytest.mark.parametrize("name", FILES)
def test_blob_sha(name):
    """Le CSV sur disque est octet pour octet celui qui a ete synchronise."""
    entry = _manifest()["files"][name]
    path = DATA / name
    assert path.exists(), f"{name} absent de {DATA}"
    actual = _git_blob_sha1(path)
    assert actual == entry["blob_sha1"], (
        f"{name} a diverge des octets synchronises.\n"
        f"  attendu {entry['blob_sha1']}\n  obtenu  {actual}\n"
        "Cause la plus frequente : conversion de fins de ligne (autocrlf). "
        "Verifier que la regle `-text` du .gitattributes couvre bien ce fichier, "
        "puis resynchroniser depuis l'amont et regenerer le manifeste."
    )


@pytest.mark.parametrize("name", FILES)
def test_required_columns(name):
    """Les colonnes AIF_*/crossLink_* consommees en aval sont presentes."""
    entry = _manifest()["files"][name]
    header = _rows(DATA / name)[0]
    missing = [c for c in entry["required_columns"] if c not in header]
    assert not missing, (
        f"{name} : colonnes absentes {missing}.\n"
        "Le snapshot vient d'un amont trop ancien (ces colonnes ont ete ajoutees "
        "par la serialisation AIF #498 et l'integration ontologique #763). "
        "Resynchroniser depuis l'amont courant."
    )


@pytest.mark.parametrize("name", FILES)
def test_row_and_column_counts(name):
    """Le volume correspond au manifeste (garde-fou sur une copie tronquee)."""
    entry = _manifest()["files"][name]
    rows = _rows(DATA / name)
    assert len(rows) - 1 == entry["rows"], (
        f"{name} : {len(rows) - 1} lignes, attendu {entry['rows']}"
    )
    assert len(rows[0]) == entry["columns"], (
        f"{name} : {len(rows[0])} colonnes, attendu {entry['columns']}"
    )


def test_virtues_families():
    """Les 8 libelles de familles Virtues sont ceux de l'amont synchronise.

    Rouge attendu apres un renommage amont : c'est le signal qu'il faut
    resynchroniser, PAS editer la liste. Trois familles ont ete renommees les
    6-7/08/2026 sans que le snapshot ne bouge, et la recherche par ancien nom
    rendait alors 0 ligne -- un zero qui se lit a tort comme "rien a faire".
    """
    name = "argumentum_virtues_taxonomy.csv"
    expected = _manifest()["files"][name]["families"]
    rows = _rows(DATA / name)
    idx = rows[0].index("family_fr")
    actual = sorted({r[idx] for r in rows[1:] if len(r) > idx and r[idx].strip()})
    assert actual == expected, (
        "Libelles de familles Virtues divergents.\n"
        f"  manifeste : {expected}\n  disque    : {actual}\n"
        "Si l'amont a renomme une famille, resynchroniser le CSV et regenerer "
        "le manifeste ; ne pas editer cette attente a la main."
    )


LEGACY_COPY = REPO / "MyIA.AI.Notebooks" / "SymbolicAI" / "data" / "argumentum_fallacies_taxonomy.csv"


def test_legacy_copy_removed():
    """La 3e copie historique SymbolicAI/data/ a ete supprimee (#13740 V1).

    Avant #13740, ce test etait ``test_legacy_copy_unified_with_canonical`` :
    il verifiait que la copie restait byte-identique a la canonique (74 -> 104
    colonnes en aout 2026, cf #13578). La copie ayant ete supprimee delibement,
    la garde devient "n'existons pas" -- distribuer une tierce copie reouvre
    le piege documente en aout 2026 (derive silencieuse de sept semaines,
    aucun consommateur n'aurait vu la divergence). Si la copie reapparait
    ulterieurement, c'est une decision explicite qui DOIT resynchroniser
    depuis la canonique dans le meme commit.
    """
    assert not LEGACY_COPY.exists(), (
        f"{LEGACY_COPY} est de retour : distribuer une 3e copie de la "
        "taxonomie reouvre le piege de derive silencieuse documente en "
        "aout 2026 (#13578). Si la reintroduction est deliberee (nouveau "
        "contexte de diffusion), resynchroniser depuis la canonique ET "
        "regenerer le manifeste dans le meme commit."
    )


ONTOLOGIES_DIR = REPO / "MyIA.AI.Notebooks" / "SymbolicAI" / "Argument_Analysis" / "ontologies"

ONTOLOGIES = ["argumentum_fallacies.owl", "argumentum_virtues.owl"]


def _owl(name: str) -> str:
    return (ONTOLOGIES_DIR / name).read_bytes().decode("utf-8", "replace")


@pytest.mark.parametrize("name", ONTOLOGIES)
def test_ontology_blob_sha(name):
    """L'OWL sur disque est octet pour octet celui de l'amont.

    Meme piege que pour les CSV, et deja materialise : argumentum.owl porte 41
    sauts de ligne ISOLES au milieu de ses 107853 CRLF, et l'amont stocke ces
    octets tels quels. Sous `core.autocrlf=true`, git normaliserait ici : le
    fichier sur disque semblerait identique, le blob stocke ne le serait pas.
    D'ou la regle `-text` du .gitattributes, dont ce test verifie qu'elle tient.
    """
    entry = _manifest()["ontologies"][name]
    path = ONTOLOGIES_DIR / name
    assert path.exists(), f"{name} absent de {ONTOLOGIES_DIR}"
    actual = _git_blob_sha1(path)
    assert actual == entry["blob_sha1"], (
        f"{name} a diverge des octets synchronises.\n"
        f"  attendu {entry['blob_sha1']}\n"
        f"  obtenu  {actual}\n"
        f"  amont   {entry['upstream_path']}\n"
        "Resynchroniser depuis l'amont et regenerer le manifeste."
    )


@pytest.mark.parametrize("name", ONTOLOGIES)
def test_ontology_carries_object_property_assertions(name):
    """Le graphe distribue est RAISONNABLE, pas seulement lisible.

    Rouge si une resynchronisation ramene un artefact ou les aretes sont a
    nouveau annotees sans etre assertees : aucun raisonneur ne les verrait, et
    le delta d'inference serait vide sans que rien ne le signale.
    """
    entry = _manifest()["ontologies"][name]
    actual = _owl(name).count("<ObjectPropertyAssertion")
    assert actual > 0, (
        f"{name} ne porte AUCUNE ObjectPropertyAssertion : les aretes du graphe "
        "argumentatif sont hors semantique logique d'OWL, donc invisibles a tout "
        "raisonneur. Resynchroniser depuis un amont posterieur a Argumentum #1231."
    )
    assert actual == entry["object_property_assertions"], (
        f"{name} : {actual} ObjectPropertyAssertion, manifeste "
        f"{entry['object_property_assertions']}. Resynchroniser et regenerer le "
        "manifeste plutot que d'ajuster l'attente."
    )


@pytest.mark.parametrize("name", ONTOLOGIES)
def test_ontology_keeps_annotations_alongside_assertions(name):
    """L'emission reste ADDITIVE : annotation ET assertion, jamais l'une pour l'autre.

    Retirer l'annotation casserait la lecture SKOS du thesaurus ; n'emettre que
    l'annotation prive l'ontologie de toute consequence inferable. Une
    "simplification" amont qui n'emettrait plus qu'une seule forme doit rougir.
    """
    entry = _manifest()["ontologies"][name]
    actual = _owl(name).count("<AnnotationAssertion")
    assert actual > 0, (
        f"{name} a perdu ses AnnotationAssertion : la lecture SKOS du thesaurus "
        "est cassee. L'emission doit rester additive."
    )
    assert actual == entry["annotation_assertions"], (
        f"{name} : {actual} AnnotationAssertion, manifeste "
        f"{entry['annotation_assertions']}."
    )
