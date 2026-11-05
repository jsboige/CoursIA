"""Tests du gel `[FROZEN]` du tapis (#24516).

Le defaut, mesure par `myia-po-2027:CoursIA` sur **#19309** : le filtre
`has_recent_delivery_marker` ne regardait que le **dernier** commentaire
(`_last_comment`), donc n'importe quel commentaire posterieur enterrait un
gel. Sur ce fil : 43 commentaires, **un seul** `[FROZEN]` (ai-01, 07:50Z),
**37** `[RELEASED]` -- et le tapis a resservi l'EPIC a 20:48Z, soit
2 h 18 apres le gel. Quatre lanes ont brule un cycle chacune (18
`[RELEASED]` le meme jour).

La grammaire retenue (coordinateur, 2026-11-03) :

* **(A)** le gel vit dans le **body** de l'issue, sur une ligne canonique
  `[FROZEN] <motif court> -- <autorite>` ; le degel = **retirer la ligne** ;
* **(B)** les commentaires servent de **filet** pour les gels deja poses en
  commentaire : le picker doit les voir **ou qu'ils soient dans le fil**, et
  un `[UNFROZEN]` posterieur les ferme ;
* un `[RELEASED]` ne leve **aucun** gel : c'est un acquiescement de lane,
  pas la levee d'une decision du coordinateur.

Ces tests sont **synthetiques** (un faux `gh`) : ils rejouent la
grammaire, pas l'etat live d'une issue -- un test live dirait plus sur le
moment ou il s'execute que sur la regle.

Les criteres d'acceptation sont ceux de l'issue #24516 :

1. un `[FROZEN]` enterre par un `[RELEASED]` posterieur gele encore ;
2. un `[UNFROZEN]` posterieur ferme un gel pose en commentaire (controle
   negatif : sans lui, le remede serait un gel eternel) ;
3. un fil sans aucun `[FROZEN]` et dont le dernier commentaire est
   `[RELEASED]` reste SERVABLE (#21721 preserve) ;
4. le nombre de requetes par candidat est inchange.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig  # noqa: E402


class _FakeIssue:
    """Stand-in subprocess pour `gh issue view --json body,comments`.

    Reproduit le contrat : `{"body": ..., "comments": [...]}` dans l'ordre
    chronologique. Le compteur `calls` permet de verifier que le nombre de
    requetes par candidat ne bouge pas.
    """

    def __init__(self, comments, body=""):
        self._comments = comments
        self._body = body
        self.calls = 0

    def run(self, *args, **kwargs):
        self.calls += 1
        # Le contrat de la lecture historique : une seule requete porte le
        # corps ET les commentaires.
        assert "--json" in args[0] or True
        class _R:
            pass
        r = _R()
        r.stdout = json.dumps({"body": self._body,
                               "comments": self._comments})
        r.returncode = 0
        r.stderr = ""
        return r


@pytest.fixture(autouse=True)
def _pool_vide():
    """Le cache des corps du pool est vide au depart de chaque test."""
    pig._POOL_BODIES.clear()
    yield
    pig._POOL_BODIES.clear()


def _install(monkeypatch, comments, body="", issue=19309):
    """Installe le faux `gh` et le corps de l'issue dans le cache du pool.

    Le corps passe par `_POOL_BODIES` : c'est le chemin de production (le
    pool porte deja le body), et c'est ce qui permet au gel du body d'etre
    lu sans requete.
    """
    fake = _FakeIssue(comments, body)
    monkeypatch.setattr(pig.subprocess, "run", fake.run)
    pig._POOL_BODIES[issue] = body
    return fake


# --- (A) le gel vit dans le BODY -------------------------------------------

def test_un_gel_dans_le_body_gele_meme_derriere_un_RELEASED(monkeypatch):
    """Regle A : le gel du body prime sur le `[RELEASED]` du dernier
    commentaire -- c'est le defaut mesure sur #19309."""
    _install(monkeypatch,
             [{"body": "[RELEASED] lane myia-po-2024:CoursIA"}],
             body="[FROZEN] accord de coordination -- ai-01\n\nSuite au gel.")
    assert pig.has_recent_delivery_marker(19309) is True
    assert pig._issue_is_frozen("[FROZEN] accord -- ai-01", []) == "body"


def test_un_gel_dans_le_body_gele_meme_derriere_un_DELIVERED(monkeypatch):
    _install(monkeypatch,
             [{"body": "[DELIVERED] lane myia-po-2024:CoursIA"}],
             body="[FROZEN] accord de coordination -- ai-01")
    assert pig.has_recent_delivery_marker(19309) is True


def test_le_body_peut_porter_le_motif_canonique_avec_un_geant_de_markdown(
        monkeypatch):
    """La ligne canonique peut etre un titre : la decoration markdown ne
    doit pas cacher le gel."""
    _install(monkeypatch,
             [{"body": "[RELEASED] lane myia-po-2024:CoursIA"}],
             body="## [FROZEN] accord de coordination -- ai-01")
    assert pig.has_recent_delivery_marker(19309) is True


def test_un_UNFROZEN_ne_leve_pas_un_gel_du_body(monkeypatch):
    """Le degel d'un gel de body, c'est le **retrait de la ligne** : un
    commentaire `[UNFROZEN]` ne fait pas foi (grammaire du 2026-11-03)."""
    _install(monkeypatch,
             [{"body": "[UNFROZEN] gel leve -- lane myia-ai-01:CoursIA"},
              {"body": "[RELEASED] lane myia-po-2024:CoursIA"}],
             body="[FROZEN] accord de coordination -- ai-01")
    assert pig.has_recent_delivery_marker(19309) is True
    assert pig._issue_is_frozen("[FROZEN] accord -- ai-01", []) == "body"


def test_un_body_qui_PARLE_du_gel_ne_gele_pas(monkeypatch):
    """Un corps qui *parle* d'un gel n'en porte pas : la ligne canonique
    commence la ligne. Sans cette distinction, l'issue qui decrit le
    defaut (#24516) gelerait elle-meme."""
    body = ("Un `[FROZEN]` du coordinateur est un etat durable, mais le "
            "filtre du tapis le lit comme une propriete de position.\n\n"
            "1. dans `has_recent_delivery_marker`, balayer tous les "
            "commentaires ;\n"
            "2. retenir le **dernier gel non leve**.\n")
    _install(monkeypatch,
             [{"body": "[RELEASED] lane myia-po-2024:CoursIA"}],
             body=body)
    assert pig.has_recent_delivery_marker(24516) is False


def test_un_body_qui_DOCUMENTE_le_gel_dans_une_fence_ne_gele_pas(monkeypatch):
    """Le code **documente** un marqueur, il ne le **pose** pas.

    Un corps qui recopie la ligne canonique dans une fence l'illustrerait
    -- la ligne est alors en debut de ligne, et la regle A la prendrait
    pour un gel. C'est le meme defaut que le corps qui *parle* du gel, par
    un autre chemin. Mesure : revue Hermes du 2026-11-03 sur #24523
    (angle mort de documentation signale, non bloquant).
    """
    body = ("La grammaire du gel est la suivante :\n\n"
            "```\n"
            "[FROZEN] accord de coordination -- ai-01\n"
            "```\n\n"
            "Une fois la ligne posee, le degel consiste a la retirer.\n")
    _install(monkeypatch,
             [{"body": "[RELEASED] lane myia-po-2024:CoursIA"}],
             body=body)
    assert pig.has_recent_delivery_marker(24516) is False
    assert pig._issue_is_frozen(body, []) is None


def test_un_commentaire_qui_cite_le_gel_dans_une_fence_ne_gele_pas(monkeypatch):
    """Meme regle pour le filet de commentaires (regle B) : une fence qui
    recopie la ligne canonique ne gele pas l'item."""
    comment = ("Je rapelle la forme :\n\n"
               "```\n"
               "[FROZEN] accord de coordination -- ai-01\n"
               "```\n")
    _install(monkeypatch, [{"body": comment}])
    assert pig.has_recent_delivery_marker(24516) is False


def test_le_code_span_inline_ne_pose_pas_le_gel(monkeypatch):
    """Un code-span inline (`` `[FROZEN] ...` ``) non plus : meme raison."""
    body = "La forme est `[FROZEN] accord de coordination -- ai-01`."
    _install(monkeypatch,
             [{"body": "[RELEASED] lane myia-po-2024:CoursIA"}],
             body=body)
    assert pig.has_recent_delivery_marker(24516) is False


def test_un_gel_reel_pose_en_commentaire_gele_toujours_avec_des_fences_ailleurs(
        monkeypatch):
    """Controle : le tri des fences ne doit pas rendre le filtre laxiste.
    Un vrai gel (en tete de ligne, hors fence) gele toujours l'item."""
    _install(monkeypatch, [
        {"body": "Un commentaire qui montre la forme :\n\n```\n[FROZEN] x -- y\n```\n"},
        {"body": "[FROZEN] accord de coordination -- ai-01"},
    ])
    assert pig.has_recent_delivery_marker(19309) is True
    assert pig._issue_is_frozen("Corps neutre.", [
        {"body": "[FROZEN] accord de coordination -- ai-01"}]) == "comment"


# --- (B) le filet des gels poses en commentaire ----------------------------

def test_un_gel_pose_en_commentaire_enterre_par_un_RELEASED_gele_encore(
        monkeypatch):
    """Le cas mesure sur #19309 : le gel est plus haut dans le fil, un
    `[RELEASED]` est arrive apres. Le tapis resservait l'EPIC."""
    _install(monkeypatch, [
        {"body": "Un commentaire sans marqueur"},
        {"body": "[FROZEN] accord de coordination -- ai-01"},
        {"body": "[RELEASED] lane myia-po-2024:CoursIA"},
        {"body": "[RELEASED] lane myia-po-2023:CoursIA"},
    ])
    assert pig.has_recent_delivery_marker(19309) is True
    assert pig._issue_is_frozen(None, [
        {"body": "[FROZEN] accord de coordination -- ai-01"}]) == "comment"


def test_un_UNFROZEN_posterieur_ferme_un_gel_pose_en_commentaire(monkeypatch):
    """Controle NEGATIF : sans cette sortie, le filet serait un gel
    eternel (criteres d'acceptation de #24516)."""
    _install(monkeypatch, [
        {"body": "[FROZEN] accord de coordination -- ai-01"},
        {"body": "[UNFROZEN] gel leve -- lane myia-ai-01:CoursIA"},
        {"body": "[RELEASED] lane myia-po-2024:CoursIA"},
    ])
    assert pig.has_recent_delivery_marker(19309) is False


def test_un_gel_pose_en_commentaire_plus_recent_qu_un_UNFROZEN_gele(
        monkeypatch):
    """Le fil se lit dans l'ordre : le dernier etat gagne."""
    _install(monkeypatch, [
        {"body": "[FROZEN] accord de coordination -- ai-01"},
        {"body": "[UNFROZEN] gel leve -- lane myia-ai-01:CoursIA"},
        {"body": "[FROZEN] accord de coordination -- ai-01"},
    ])
    assert pig.has_recent_delivery_marker(19309) is True


def test_un_gel_du_body_prime_sur_un_UNFROZEN_du_fil(monkeypatch):
    _install(monkeypatch,
             [{"body": "[UNFROZEN] gel leve -- lane myia-ai-01:CoursIA"}],
             body="[FROZEN] accord de coordination -- ai-01")
    assert pig.has_recent_delivery_marker(19309) is True


# --- (B') l'AUTORITE du degel : la lane declaree, pas l'auteur GitHub -------

def test_un_UNFROZEN_d_une_lane_tierce_ne_leve_pas_le_gel(monkeypatch):
    """Temoin NEGATIF exige par le coordinateur (dispatch c2764, point 2).

    Le login GitHub est **partage** (`jsboige`) : l'auteur du commentaire ne
    prouve rien. L'autorite se lit dans la lane DECLAREE dans le marqueur,
    et seules deux lanes sont habilitees (coordinateur, adjoint
    titulaire). Un `[UNFROZEN]` d'une lane tierce ne leve donc rien.
    """
    _install(monkeypatch, [
        {"body": "[FROZEN] accord de coordination -- ai-01"},
        {"body": "[UNFROZEN] gel leve -- lane myia-po-2027:CoursIA"},
        {"body": "[RELEASED] lane myia-po-2024:CoursIA"},
    ])
    assert pig.has_recent_delivery_marker(19309) is True


def test_un_UNFROZEN_sans_lane_declaree_ne_leve_pas_le_gel(monkeypatch):
    """Fail-closed : sans lane declaree, personne n'est habilite."""
    _install(monkeypatch, [
        {"body": "[FROZEN] accord de coordination -- ai-01"},
        {"body": "[UNFROZEN] gel leve -- ai-01"},
    ])
    assert pig.has_recent_delivery_marker(19309) is True


@pytest.mark.parametrize("lane", sorted(pig.FROZEN_UNFROZEN_LANES))
def test_l_adjoint_titulaire_ferme_bien_un_gel_de_commentaire(monkeypatch, lane):
    """Les deux lanes habilitees ferment le gel (controle positif du filtre)."""
    _install(monkeypatch, [
        {"body": "[FROZEN] accord de coordination -- ai-01"},
        {"body": f"[UNFROZEN] gel leve -- lane {lane}"},
    ])
    assert pig.has_recent_delivery_marker(19309) is False


def test_la_lane_habilitee_est_celle_du_delivered_urn(monkeypatch):
    """Le filtre d'autorite suit le meme modele que l'urne `delivered`
    (dispatch c2764) : les deux listes portent les memes lanes."""
    assert pig.FROZEN_UNFROZEN_LANES == pig.DELIVERED_URN_LANES


# --- (C) ce qui ne change pas ----------------------------------------------

def test_un_fil_sans_gel_avec_RELEASED_en_dernier_reste_servable(monkeypatch):
    """#21721 preserve : `[RELEASED]` = une main rendue sur une barriere
    reelle, l'item redevient servable. Le gel change cette lecture, pas
    cette decision."""
    _install(monkeypatch, [
        {"body": "Une discussion sans marqueur"},
        {"body": "[RELEASED] lane myia-po-2023:CoursIA"},
    ])
    assert pig.has_recent_delivery_marker(12345) is False


def test_un_FIL_vide_ne_gele_pas(monkeypatch):
    _install(monkeypatch, [])
    assert pig.has_recent_delivery_marker(12345) is False


def test_une_lecture_en_echec_reste_fail_OPEN(monkeypatch):
    """« je n'ai pas pu lire » n'est pas « c'est conforme » : le filtre
    rend None et l'appelant enchaine (fail-OPEN)."""

    def boom(*args, **kwargs):
        raise OSError("reseau")

    monkeypatch.setattr(pig.subprocess, "run", boom)
    assert pig.has_recent_delivery_marker(12345) is None


def test_le_nombre_de_requetes_par_candidat_ne_bouge_pas(monkeypatch):
    """Criteres d'acceptation de #24516 : aucun appel reseau ajoute. Le
    corps et le fil entier sont lus DANS la meme requete."""
    fake = _install(monkeypatch, [
        {"body": "[FROZEN] accord de coordination -- ai-01"},
        {"body": "[RELEASED] lane myia-po-2024:CoursIA"},
    ], body="[FROZEN] accord de coordination -- ai-01")
    pig.has_recent_delivery_marker(19309)
    assert fake.calls == 1
    pig.has_recent_delivery_marker(19309)
    assert fake.calls == 2


def test_le_corps_du_pool_permet_de_lire_le_gel_sans_requete(monkeypatch):
    """Le pool porte deja le corps de l'issue : le gel du body est lisible
    sans lire le fil de l'issue, et la requete ne sert qu'a la confirmer."""
    fake = _install(monkeypatch,
                    [{"body": "[RELEASED] lane myia-po-2024:CoursIA"}],
                    body="[FROZEN] accord de coordination -- ai-01")
    assert pig.has_recent_delivery_marker(19309) is True
    assert fake.calls == 1


# --- (D) la BOUCLE DU TAPIS : le gel doit etre lu par le tapis --------------
#
# La grammaire ci-dessus etait deja implementee (PR #24523) etait lue par
# `has_recent_delivery_marker` -- mais ce filtre ne sert que l'urne GRAIN.
# La boucle de service (`belt_pick_with_replacements`) a ses propres
# filtres : sur une UMBRELLA elle lit le marqueur de CONTENEUR (le dernier
# commentaire), sur une CONSOLIDATION l'evenement de cloture. Aucun des
# deux ne consulte le gel -- et #19309, une umbrella, etait servie malgre
# son gel (mesure du 05/11 : 7 corroborations de lanes).
#
# Ces tests sont donc au niveau de la BOUCLE, pas de la sonde.


def _belt_item(number, klass="umbrella"):
    return {
        "number": number,
        "klass": klass,
        "age": 100,
        "idle": 10,
        "genre": "docs",
        "labels": [],
        "title": f"issue #{number}",
        "created_at": "2026-01-01T00:00:00Z",
        "last_delivery_stamp": None,
    }


def _belt_args(grains=2):
    import types
    return types.SimpleNamespace(
        grains=grains, include_delivered=False,
        lane="myia-po-2027:CoursIA-2")


#: Les commentaires vus par la boucle, DECLARES par le test.
#:
#: La boucle du tapis relit l'instantane **du disque de la machine**, qui
#: porte le fil REEL des issues -- c'est ainsi que la mesure a trouve le
#: `[FROZEN]` du vrai #19309. Un test ne doit pas dependre de cet etat :
#: la fixture `_lecture_locale_controlee` remplace la lecture par ce dict.
_COMMENTAIRES: dict = {}


def _run_belt(monkeypatch, pool, frozen_probe=None):
    """Fait tourner la boucle de service avec des sondes injectees.

    Toutes les sondes de livraison sont explicitement injectees a `False`
    : ce qui est mesure ici, c'est le filtre du GEL, pas les marqueurs de
    cloture (couverts par leurs propres suites).
    """
    claims = {it["number"]: (pig.CLAIM_CODE_FREE, "libre") for it in pool}
    return pig.belt_pick_with_replacements(
        pool, claims, _belt_args(), probe_budget=8,
        delivered_probe=lambda n, lane=None: False,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: False,
        container_marker_probe=lambda n: False,
        delivery_event_probe=lambda n: (False, False, None),
        cover_probe=lambda n: None,
        frozen_probe=(frozen_probe if frozen_probe is not None
                      else pig.issue_is_frozen_marker))


@pytest.fixture(autouse=True)
def _lecture_locale_controlee(monkeypatch):
    """La lecture locale est remplacee par un dict DECLARE par le test.

    La boucle du tapis relit l'instantane du disque de la machine, qui porte
    le fil REEL des issues : sans cette neutralisation, un test dependant du
    disque passerait sur une machine et echouerait sur une autre (et la
    mesure ci-dessus -- le `[FROZEN]` du vrai #19309 -- a ete trouvee par
    ce chemin)."""
    _COMMENTAIRES.clear()
    monkeypatch.setattr(pig, "_snapshot_comments",
                        lambda n: _COMMENTAIRES.get(n))
    monkeypatch.setattr(pig, "_PASS_SNAPSHOT", {})
    monkeypatch.setattr(pig, "_BELT_SNAPSHOT", None)
    yield
    _COMMENTAIRES.clear()


def test_le_tapis_ecarte_une_umbrella_gelee_par_le_body(monkeypatch):
    """LE CAS MESURE (#19309) : une umbrella gelee par une ligne `[FROZEN]`
    dans son body etait **servie** par le tapis, parce que le filtre de
    conteneur ne lit que le dernier commentaire."""
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: pytest.fail("lecture reseau inattendue"))
    pig._POOL_BODIES[19309] = ("[FROZEN] accord de coordination -- ai-01\n\n"
                               "Suite au gel.\n")
    pool = [_belt_item(19309), _belt_item(19001)]
    picks, withheld, state = _run_belt(monkeypatch, pool)
    assert 19309 not in [p["number"] for p in picks], (
        "une umbrella gelee ne doit pas etre servie")
    causes = {w[0]["number"]: w[1] for w in withheld}
    assert causes[19309].startswith("GEL")
    assert state["frozen_filtered"] == 1


def test_le_tapis_ecarte_une_umbrella_gelee_par_un_commentaire_enterre(
        monkeypatch):
    """Meme cas, regle B : le gel est un commentaire du FIL, enterre par un
    `[RELEASED]` posterieur. La lecture passe par l'instantane local de la
    passe -- aucune requete."""
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: pytest.fail("lecture reseau inattendue"))
    pig._POOL_BODIES[19309] = "Corps neutre, aucun gel."
    _COMMENTAIRES[19309] = [
        {"body": "Une discussion sans marqueur"},
        {"body": "[FROZEN] accord de coordination -- ai-01"},
        {"body": "[RELEASED] lane myia-po-2024:CoursIA"},
    ]
    pool = [_belt_item(19309), _belt_item(19001)]
    picks, withheld, state = _run_belt(monkeypatch, pool)
    assert 19309 not in [p["number"] for p in picks]
    causes = {w[0]["number"]: w[1] for w in withheld}
    assert causes[19309].startswith("GEL")


def test_une_umbrella_sans_gel_reste_servable(monkeypatch):
    """Controle NEGATIF : #21721 preserve. Une umbrella sans gel, dont le
    dernier commentaire est un `[RELEASED]`, reste servable -- le filtre
    du gel ne peut pas devenir un filtre de plus."""
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: pytest.fail("lecture reseau inattendue"))
    pig._POOL_BODIES[19309] = "Corps neutre, aucun gel."
    _COMMENTAIRES[19309] = [
        {"body": "Une discussion sans marqueur"},
        {"body": "[RELEASED] lane myia-po-2024:CoursIA"},
    ]
    pool = [_belt_item(19309), _belt_item(19001)]
    picks, withheld, state = _run_belt(monkeypatch, pool)
    assert [p["number"] for p in picks] == [19309, 19001]
    assert state["frozen_filtered"] == 0


def test_un_body_qui_PARLE_du_gel_ne_gele_pas_le_tapis(monkeypatch):
    """Controle NEGATIF : le corps de CETTE ISSUE (#24516) *parle* d'un gel.
    S'il etait pris pour un gel, l'issue qui decrit le defaut gelerait
    elle-meme -- et le tapis se viderait de ses grains."""
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: pytest.fail("lecture reseau inattendue"))
    pig._POOL_BODIES[24516] = (
        "Un `[FROZEN]` du coordinateur est un etat durable, mais le filtre "
        "du tapis le lit comme une propriete de position.\n\n"
        "1. dans `has_recent_delivery_marker`, balayer tous les "
        "commentaires ;\n")
    pool = [_belt_item(24516), _belt_item(19001)]
    picks, withheld, state = _run_belt(monkeypatch, pool)
    assert [p["number"] for p in picks] == [24516, 19001]
    assert state["frozen_filtered"] == 0


def test_un_UNFROZEN_posterieur_rend_l_umbrella_servable(monkeypatch):
    """Controle NEGATIF (le plus important) : sans cette sortie, le remede
    serait un gel EERNEL. Un `[UNFROZEN]` d'une lane habilitee ferme le gel
    de commentaire, et l'umbrella redevient servable."""
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: pytest.fail("lecture reseau inattendue"))
    pig._POOL_BODIES[19309] = "Corps neutre, aucun gel."
    _COMMENTAIRES[19309] = [
        {"body": "[FROZEN] accord de coordination -- ai-01"},
        {"body": "[UNFROZEN] gel leve -- lane myia-ai-01:CoursIA"},
        {"body": "[RELEASED] lane myia-po-2024:CoursIA"},
    ]
    pool = [_belt_item(19309), _belt_item(19001)]
    picks, withheld, state = _run_belt(monkeypatch, pool)
    assert [p["number"] for p in picks] == [19309, 19001]
    assert state["frozen_filtered"] == 0


def test_une_lecture_du_gel_incomplete_ne_bloque_pas_le_candidat(monkeypatch):
    """« je n'ai pas pu lire » n'est pas « c'est conforme » : le candidat
    reste servable (fail-OPEN), et l'echec est PUBLIE dans `frozen_unread`."""
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: pytest.fail("lecture reseau inattendue"))
    # Ni corps dans le cache du pool, ni instantane : l'etat du gel est
    # INCONNU.
    pool = [_belt_item(19309), _belt_item(19001)]
    picks, withheld, state = _run_belt(monkeypatch, pool)
    assert [p["number"] for p in picks] == [19309, 19001]
    assert 19309 in state["frozen_unread"]


def test_le_tapis_ecarte_un_grain_gele_autant_que_l_umbrella(monkeypatch):
    """Le filtre du gel vaut pour TOUTES les classes : un grain gele est
    ecarte lui aussi (le filtre recent le fait deja par un autre chemin,
    mais le tapis doit dire « GEL », pas « LIVRAISON »)."""
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: pytest.fail("lecture reseau inattendue"))
    pig._POOL_BODIES[19001] = "[FROZEN] accord de coordination -- ai-01"
    pool = [_belt_item(19001, klass="grain"), _belt_item(19002)]
    picks, withheld, state = _run_belt(monkeypatch, pool)
    assert 19001 not in [p["number"] for p in picks]
    causes = {w[0]["number"]: w[1] for w in withheld}
    assert causes[19001].startswith("GEL")


# --- (E) la LECTURE du gel : son tri-etat -----------------------------------

def test_la_lecture_du_gel_trouve_le_gel_dans_le_body_seul():
    """Regle A seule : le corps porte la ligne canonique, le fil n'est pas
    disponible. Le verdict reste DECISIF -- un gel lu est un gel."""
    pig._POOL_BODIES[19309] = "[FROZEN] accord de coordination -- ai-01"
    assert pig.issue_is_frozen_marker(19309) is True


def test_la_lecture_du_gel_trouve_le_gel_dans_le_fil_seul():
    """Regle B seule : le gel est un commentaire du fil, le corps est
    neutre et disponible."""
    pig._POOL_BODIES[19309] = "Corps neutre."
    _COMMENTAIRES[19309] = [
        {"body": "[FROZEN] accord de coordination -- ai-01"},
        {"body": "[RELEASED] lane myia-po-2024:CoursIA"},
    ]
    assert pig.issue_is_frozen_marker(19309) is True


def test_la_lecture_du_gel_rend_faux_si_les_deux_surfaces_sont_lues():
    """Les deux surfaces lues, aucun gel : le verdict est DEFINITIF."""
    pig._POOL_BODIES[19309] = "Corps neutre."
    _COMMENTAIRES[19309] = [{"body": "[RELEASED] lane myia-po-2024:CoursIA"}]
    assert pig.issue_is_frozen_marker(19309) is False


def test_la_lecture_du_gel_rend_inconnu_quand_une_surface_manque():
    """Une surface non lue ne vaut pas « pas gele » : le verdict est
    INCONNU (`None`), et l'appelant le fail-OPEN en le disant."""
    pig._POOL_BODIES[19309] = "Corps neutre."
    # pas de commentaires declares -> la regle B n'a pas pu etre evaluee
    assert pig.issue_is_frozen_marker(19309) is None
    pig._POOL_BODIES.clear()
    _COMMENTAIRES[19309] = [{"body": "Une discussion"}]
    # pas de corps dans le cache du pool -> la regle A n'a pas pu etre
    # evaluee
    assert pig.issue_is_frozen_marker(19309) is None


def test_la_lecture_du_gel_ne_coute_aucune_requete(monkeypatch):
    """La lecture est LOCALE : corps du pool + fil de l'instantane. Aucune
    requete `gh` n'est emise, meme quand le gel est dans le corps."""
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: pytest.fail("lecture reseau inattendue"))
    pig._POOL_BODIES[19309] = "[FROZEN] accord de coordination -- ai-01"
    assert pig.issue_is_frozen_marker(19309) is True


def test_le_rapport_du_gel_non_lu_se_dit(capsys):
    """Un gel non lu ne doit pas etre muet : le rapport nomme les numeros
    concernes (doctrine des trois autres lectures non lues)."""
    pig.print_frozen_unread_report([19309, 19309, 19001],
                                   "myia-po-2027:CoursIA-2")
    out = capsys.readouterr().out
    assert "GEL NON LU" in out
    assert "#19309" in out and "#19001" in out
    # Rien a dire quand aucun candidat n'est concerne.
    pig.print_frozen_unread_report([], None)
    assert capsys.readouterr().out == ""


def test_le_compteur_du_gel_est_dans_l_etat_de_la_boucle(monkeypatch):
    """L'etat de la boucle porte les deux compteurs du filtre : ce qui a
    ete ecarte (`frozen_filtered`) et ce qui n'a pas pu etre lu
    (`frozen_unread`)."""
    pig._POOL_BODIES[19309] = "[FROZEN] accord de coordination -- ai-01"
    pool = [_belt_item(19309), _belt_item(19001)]
    picks, withheld, state = _run_belt(monkeypatch, pool)
    assert state["frozen_filtered"] == 1
    assert state["frozen_unread"] == [19001]
    assert 19309 not in [p["number"] for p in picks]
