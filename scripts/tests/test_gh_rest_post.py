"""Tests de `scripts/coordination/gh_rest_post.py` (#26973, ligne 1).

L'organe est teste **sans reseau** : le seul appel externe (`gh api`) est
monkeypatche. Ce qui est verifie :

- le **mapping** des verbes vers leur methode et leur endpoint REST ;
- le fait que le corps vient **toujours** d'un fichier, et qu'aucune option
  de la ligne de commande n'accepte un corps en ligne (le piege
  `-f body=@fichier` n'est donc pas saisissable) ;
- les **trois predicats** de la garde post-POST (divergence entre le corps
  envoye et le corps publie, longueur -- seulement si les deux different --
  et structure PAYLOAD-TRAP), qui sont la raison d'etre de l'organe ;
- le fait que la resolution du jeton **passe par** `post_dossier.py`
  (importe, jamais reecrit) ;
- le contrat de sortie : quand une garde echoue, l'id et l'URL sont quand
  meme rendus (le correctif est un PATCH sur cet id) et le code de sortie
  distingue la publication douteuse de l'echec d'ecriture.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import pathlib
import sys

import pytest

_MODULE_PATH = (
    pathlib.Path(__file__).resolve().parents[1] / "coordination" / "gh_rest_post.py"
)


def _load_module():
    spec = importlib.util.spec_from_file_location("gh_rest_post", _MODULE_PATH)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules["gh_rest_post"] = module
    spec.loader.exec_module(module)
    return module


gh_rest_post = _load_module()


# ---------------------------------------------------------------------------
# mapping des verbes
# ---------------------------------------------------------------------------

def test_chaque_verbe_a_son_endpoint_rest():
    assert gh_rest_post.endpoint_for("comment", "o/r", 12) == (
        "POST",
        "/repos/o/r/issues/12/comments",
    )
    assert gh_rest_post.endpoint_for("pr-comment", "o/r", 12) == (
        "POST",
        "/repos/o/r/issues/12/comments",
    )
    assert gh_rest_post.endpoint_for("pr-create", "o/r", None) == (
        "POST",
        "/repos/o/r/pulls",
    )
    assert gh_rest_post.endpoint_for("edit-body", "o/r", 12) == (
        "PATCH",
        "/repos/o/r/issues/12",
    )
    assert gh_rest_post.endpoint_for("edit-pr-body", "o/r", 12) == (
        "PATCH",
        "/repos/o/r/pulls/12",
    )


def test_un_verbe_qui_exige_un_numero_le_refuse():
    with pytest.raises(ValueError):
        gh_rest_post.endpoint_for("comment", "o/r", None)


def test_un_verbe_inconnu_le_refuse():
    with pytest.raises(ValueError):
        gh_rest_post.endpoint_for("ecrire", "o/r", 1)


# ---------------------------------------------------------------------------
# le corps vient d'un fichier
# ---------------------------------------------------------------------------

def _args(**kwargs):
    base = dict(
        verb="comment",
        repo="o/r",
        number=12,
        body_file="corps.md",
        title="",
        head="",
        base="",
        draft=False,
        token_source="user",
        app_id="",
        app_key_path="",
    )
    base.update(kwargs)
    return argparse.Namespace(**base)


def test_le_payload_porte_le_corps_lu():
    payload = gh_rest_post.build_payload(_args(), "le corps")
    assert payload["body"] == "le corps"


def test_une_creation_de_pr_porte_en_plus_titre_branche_et_base():
    payload = gh_rest_post.build_payload(
        _args(verb="pr-create", title="T", head="fix/x", base="main", draft=True),
        "le corps",
    )
    assert payload["title"] == "T"
    assert payload["head"] == "fix/x"
    assert payload["base"] == "main"
    assert payload["draft"] is True
    assert payload["body"] == "le corps"


def test_aucune_option_n_accepte_un_corps_en_ligne():
    """Le piege `-f body=@fichier` n'est pas saisissable depuis le CLI."""
    options = set()
    for action in gh_rest_post.build_parser()._actions:
        options.update(action.option_strings)
    assert "--body" not in options
    assert "--body-file" in options
    assert "--input" not in options


def test_l_usage_documente_emploie_les_options_reelles():
    """La doc d'usage ne doit pas nommer une option inexistante.

    Un exemple de ligne de commande que le parseur refuse est une dette
    silencieuse : l'appelant copie l'exemple, et l'organe echoue.
    """
    source = _MODULE_PATH.read_text(encoding="utf-8")
    options = set()
    for action in gh_rest_post.build_parser()._actions:
        options.update(action.option_strings)
    for mention in ("--issue", "--pr ", "--pr\\n"):
        assert mention not in source, mention
    assert "--number" in source
    assert "--number" in options


# ---------------------------------------------------------------------------
# la garde post-POST : les deux predicats
# ---------------------------------------------------------------------------

def test_un_court_corps_publie_est_signale():
    failures = gh_rest_post.check_published_body("trop court")
    assert failures
    assert "longueur" in failures[0]


def test_un_corps_publie_en_payload_json_est_signale():
    piege = json.dumps(
        {
            "body": "le vrai corps, assez long pour que la garde de longueur "
            "soit satisfaite et que seule la structure soit en cause",
            "autre": 1,
        }
    )
    failures = gh_rest_post.check_published_body(piege)
    assert failures
    assert "PAYLOAD-TRAP" in failures[0]


def test_un_corps_normal_ne_declenche_aucune_garde():
    corps = (
        "Une premiere ligne qui explique le geste, assez longue pour que la "
        "garde de longueur soit satisfaite.\n\nUne seconde ligne de contexte.\n"
    )
    assert gh_rest_post.check_published_body(corps) == []


def test_un_corps_json_sans_cle_body_ne_declenche_pas_la_garde_structure():
    """Seule la cle `body` fait le piege : un JSON legitime passe."""
    corps = json.dumps({"title": "T", "body": "x"})
    # Il porte bien `body` : c'est un piege. Un JSON sans `body` :
    sans_body = json.dumps(
        {
            "title": "Un titre assez long pour que la garde de longueur soit "
            "satisfaite par le corps publie, et de quelques caracteres de plus."
        }
    )
    assert gh_rest_post.check_published_body(sans_body) == []


# ---------------------------------------------------------------------------
# le predicat principal : la divergence entre le corps envoye et le publie
# ---------------------------------------------------------------------------

def test_un_corps_court_publie_a_l_identique_ne_declenche_aucune_garde():
    """Un corps court **publie a l'identique** est un corps legitime.

    C'est le cas d'un `[CLAIMED]` de 60 caracteres : la garde de longueur,
    prise seule, le ferait rougir a tort. Le predicat principal est la
    **divergence** entre le corps envoye et le corps publie.
    """
    corps = "[CLAIMED] lane myia-ai-01:CoursIA-2 -- grain #26979"
    assert len(corps) < gh_rest_post.MIN_PUBLISHED_LEN
    assert gh_rest_post.check_published_body(corps, corps) == []


def test_un_corps_publie_different_du_corps_envoye_est_signale():
    """Le piege `-f body=@fichier` : le publie n'est pas l'envoye."""
    envoye = "Un corps assez long pour que la garde de longueur soit satisfaite.\n"
    publie = "@/tmp/corps.md"
    failures = gh_rest_post.check_published_body(publie, envoye)
    assert failures
    assert "divergence" in failures[0]


def test_un_corps_publie_tronque_est_signale_meme_sans_etre_court():
    """La divergence suffit : la longueur n'est qu'un symptome."""
    envoye = "Un corps assez long pour que la garde de longueur soit satisfaite.\n"
    publie = "Un corps assez long pour que la garde de longueur soit satisfaite"
    failures = gh_rest_post.check_published_body(publie, envoye)
    assert failures
    assert "divergence" in failures[0]


def test_un_post_court_publie_a_l_identique_ne_declenche_aucune_garde(monkeypatch, tmp_path):
    """Au niveau du geste : un claim de 60 caracteres ne fait pas rougir."""
    corps = tmp_path / "corps.md"
    corps.write_text(
        "[CLAIMED] lane myia-ai-01:CoursIA-2 -- grain #26979",
        encoding="utf-8",
    )
    monkeypatch.setattr(gh_rest_post, "resolve_token", lambda *a, **k: "jeton")
    monkeypatch.setattr(
        gh_rest_post,
        "_gh_api",
        lambda method, path, payload, token: {
            "id": 44,
            "html_url": "https://github.com/o/r/issues/12#issuecomment-44",
            "body": payload["body"],
        },
    )
    code, report = gh_rest_post.run(_args(body_file=str(corps)))
    assert code == gh_rest_post.EXIT_OK
    assert report["guards"] == []


def test_un_espace_final_ajoute_par_l_api_ne_compte_pas_comme_divergence():
    """La comparaison ignore les espaces de bord : l'API peut en ajouter."""
    envoye = "[CLAIMED] lane myia-ai-01:CoursIA-2 -- grain #26979\n"
    publie = envoye + "\n"
    assert gh_rest_post.check_published_body(publie, envoye) == []


def test_un_post_ou_le_corps_publie_diverge_est_rouge(monkeypatch, tmp_path):
    corps = tmp_path / "corps.md"
    corps.write_text(
        "Un corps assez long pour que la garde de longueur soit satisfaite.\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(gh_rest_post, "resolve_token", lambda *a, **k: "jeton")
    monkeypatch.setattr(
        gh_rest_post,
        "_gh_api",
        lambda method, path, payload, token: {
            "id": 45,
            "html_url": "https://github.com/o/r/issues/12#issuecomment-45",
            "body": "@/tmp/corps.md",
        },
    )
    code, report = gh_rest_post.run(_args(body_file=str(corps)))
    assert code == gh_rest_post.EXIT_GUARD
    assert report["id"] == 45
    assert any("divergence" in f for f in report["guards"])


# ---------------------------------------------------------------------------
# la resolution du jeton passe par post_dossier
# ---------------------------------------------------------------------------

def test_le_jeton_utilisateur_passe_par_post_dossier(monkeypatch):
    appels = {}

    def _resolve():
        appels["appele"] = True
        return "jeton-de-test"

    monkeypatch.setattr(gh_rest_post.post_dossier, "resolve_write_token", _resolve)
    assert gh_rest_post.resolve_token("user") == "jeton-de-test"
    assert appels.get("appele") is True


def test_le_jeton_de_l_environnement_est_lu(monkeypatch):
    monkeypatch.setenv("GH_TOKEN", "jeton-env")
    assert gh_rest_post.resolve_token("env") == "jeton-env"


def test_une_absence_de_jeton_dans_l_environnement_est_une_erreur_franche(monkeypatch):
    monkeypatch.delenv("GH_TOKEN", raising=False)
    with pytest.raises(RuntimeError):
        gh_rest_post.resolve_token("env")


def test_l_organe_ne_reecrit_pas_la_resolution_du_jeton():
    """`resolve_write_token` est importe, pas reecrit (organe d'abord)."""
    source = _MODULE_PATH.read_text(encoding="utf-8")
    assert "auth token" not in source
    assert "post_dossier.resolve_write_token" in source


# ---------------------------------------------------------------------------
# le contrat de sortie
# ---------------------------------------------------------------------------

def test_un_post_sans_anomalie_rend_l_id_et_l_url(monkeypatch, tmp_path):
    corps = tmp_path / "corps.md"
    corps.write_text(
        "Une premiere ligne qui explique le geste, assez longue pour que la "
        "garde de longueur soit satisfaite.\n\nUne seconde.\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(gh_rest_post, "resolve_token", lambda *a, **k: "jeton")
    monkeypatch.setattr(
        gh_rest_post,
        "_gh_api",
        lambda method, path, payload, token: {
            "id": 42,
            "html_url": "https://github.com/o/r/issues/12#issuecomment-42",
            "body": payload["body"],
        },
    )
    code, report = gh_rest_post.run(_args(body_file=str(corps)))
    assert code == gh_rest_post.EXIT_OK
    assert report["id"] == 42
    assert report["url"].endswith("#issuecomment-42")
    assert report["guards"] == []


def test_un_corps_piege_rend_malgre_tout_l_id_pour_le_patch(monkeypatch, tmp_path):
    corps = tmp_path / "corps.md"
    corps.write_text("Un corps assez long pour passer la garde de longueur.\n", encoding="utf-8")
    piege = json.dumps({"body": "le vrai corps echappe dans une chaine"})
    monkeypatch.setattr(gh_rest_post, "resolve_token", lambda *a, **k: "jeton")
    monkeypatch.setattr(
        gh_rest_post,
        "_gh_api",
        lambda method, path, payload, token: {
            "id": 43,
            "html_url": "https://github.com/o/r/issues/12#issuecomment-43",
            "body": piege,
        },
    )
    code, report = gh_rest_post.run(_args(body_file=str(corps)))
    assert code == gh_rest_post.EXIT_GUARD
    # L'id est rendu : le remedie est un PATCH sur ce commentaire.
    assert report["id"] == 43
    assert report["guards"]


def test_un_corps_illisible_ou_vide_est_une_erreur_d_usage(monkeypatch, tmp_path):
    vide = tmp_path / "vide.md"
    vide.write_text("   \n", encoding="utf-8")
    code, report = gh_rest_post.run(_args(body_file=str(vide)))
    assert code == gh_rest_post.EXIT_USAGE
    assert "error" in report

    code, report = gh_rest_post.run(_args(body_file=str(tmp_path / "absent.md")))
    assert code == gh_rest_post.EXIT_USAGE


def test_l_appel_rest_passe_toujours_le_payload_par_un_fichier_input(monkeypatch, tmp_path):
    """Le corps transite par `--input` : jamais en argument de ligne."""
    corps = tmp_path / "corps.md"
    corps.write_text("Un corps assez long pour passer la garde de longueur.\n", encoding="utf-8")
    vu = {}

    def _fake_run(cmd, **kwargs):
        vu["cmd"] = cmd
        path = cmd[cmd.index("--input") + 1]
        vu["payload"] = json.loads(pathlib.Path(path).read_text(encoding="utf-8"))
        return argparse.Namespace(returncode=0, stdout=json.dumps({"id": 7}), stderr="")

    monkeypatch.setattr(gh_rest_post.post_dossier, "write_env", lambda token: {})
    monkeypatch.setattr(gh_rest_post.subprocess, "run", _fake_run)
    data = gh_rest_post._gh_api(
        "POST", "/repos/o/r/issues/12/comments", {"body": "x"}, "jeton"
    )
    assert "--input" in vu["cmd"]
    assert vu["payload"] == {"body": "x"}
    assert data["id"] == 7


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(pytest.main([__file__, "-v"]))
