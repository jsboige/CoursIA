"""Regression #19132 : un id de cellule Jupyter n'est pas un SHA de levee.

Le 2026-10-04 sur #18893, une levee designant une cellule par son id,
`6f32f63e` (token `nbformat` >= 4.5 : 8 hex, au moins une lettre et au
moins un chiffre), a ete refusee par `_cited_shas()` : l'id satisfait le
motif `_SHA_CITED` et, absent des commits de la PR, faisait tomber toute
la levee. L'auteur a du reecrire la phrase en prose (« la cellule
d'ouverture du Dojo ») pour passer.

Remede (modele `_HOST_QUALIFIED` de #16876) : `_cited_shas()` ignore un
token hex immediatement qualifie comme id de cellule (`cellule`, `cell`,
`cell_id`, avec deux-points et/ou encage optionnels). La protection #13639
(vrais SHAs cites detectes) est couverte par les controles positifs
ci-dessous.

`id` SEUL est exclu du remede (review ai-01 du 2026-10-05, mesuree avec cet
organe) : « commit id 1a2b3c4d », « commit-id: 1a2b3c4d » et « pushed as id
0abc1234ef » sont des citations de COMMIT courantes -- les masquer rouvrirait
#13639. Le temoin correspondant est
`test_qualifiant_id_seul_ne_masque_pas_une_citation_de_commit`.
"""
import importlib.util
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_unaddressed_nits.py"
spec = importlib.util.spec_from_file_location("check_unaddressed_nits", SCRIPT)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits"] = mod
spec.loader.exec_module(mod)

# Id de cellule de l'instance fondatrice (#18893) : 8 hex, lettres + chiffres.
CELL_ID = "6f32f63e"


def test_cellule_qualifiee_nest_pas_un_sha():
    # Phrase meme de l'instance fondatrice : la levee designe la cellule.
    body = "La reserve du Dojo est traitee dans la cellule 6f32f63e, prose comprise."
    assert CELL_ID not in mod._cited_shas(body)
    assert mod._cited_shas(body) == set()


def test_controle_positif_sha_libre_reste_cite():
    # La protection #13639 reste intacte : sans qualifiant, le token est un SHA.
    body = "la reserve est traitee en 6f32f63e"
    assert CELL_ID in mod._cited_shas(body)


def test_variantes_de_qualifiant():
    for forme in (
        "cellule 6f32f63e",
        "cellule: 6f32f63e",
        "cell 6f32f63e",
        "cell_id 6f32f63e",
        "cell_id: 6f32f63e",
        "la cellule `6f32f63e`",
    ):
        assert CELL_ID not in mod._cited_shas(f"traitee dans la {forme} ce matin"), forme


def test_qualifiant_id_seul_ne_masque_pas_une_citation_de_commit():
    # Review ai-01 du 2026-10-05 : `id` SEUL est trop large. « commit id »,
    # « commit-id: » et « pushed as id » sont des tournures courantes de
    # citation de COMMIT ; les faire sauter rouvrirait #13639 -- une levee qui
    # cite un SHA inexistant doit tomber. Le temoin est l'inverse du cas vise :
    # ici le token DOIT rester lu.
    for corps, jeton in (
        ("corrige au commit id 1a2b3c4d", "1a2b3c4d"),
        ("corrige au commit-id: 1a2b3c4d", "1a2b3c4d"),
        ("pushed as id 0abc1234ef", "0abc1234ef"),
        ("le commit id `1a2b3c4d` est absent de la PR", "1a2b3c4d"),
    ):
        assert jeton in mod._cited_shas(corps), (
            f"citation de commit masquee par le qualifiant `id` : {corps!r}"
        )


def test_qualifiant_non_immediat_ne_masque_pas():
    # `cellule` suivi d'autres mots PUIS du token : pas de qualification
    # immediate -- c'est le contournement en prose que l'issue a du ecrire.
    body = "la cellule d'ouverture du Dojo porte abc12de comme preuve"
    assert "abc12de" in mod._cited_shas(body)


def test_sha_reel_dans_meme_corps_que_cellule():
    # Les deux tokens dans le meme corps : seul le qualifie saute.
    body = ("cellule 6f32f63e corrigee -- la levee cite aussi le commit "
            "31ac6b89 qui porte le fix")
    cited = mod._cited_shas(body)
    assert CELL_ID not in cited
    assert "31ac6b89" in cited
