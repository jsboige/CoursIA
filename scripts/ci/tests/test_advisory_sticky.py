"""Tests de `scripts/ci/advisory_sticky.py` (#15511).

Contrat verifie ici :

* un PR porte **au plus un** commentaire collant (marqueur HTML) ;
* une section par organe, dans un corps **deterministe** (un run repete ne
  rechauffe pas le commentaire) ;
* le SUCCES ne parle pas : l'organe qui redevient vert **retire sa section**,
  et ne cree **rien** si le commentaire n'existe pas ;
* jamais de suppression d'historique : le commentaire reste, edite en place ;
* un commentaire **humain** qui porterait le marqueur n'est jamais edite ;
* un nom d'organe invalide est refuse.

Les appels ``gh`` sont rejoues par un faux runner : aucun reseau.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import advisory_sticky as a_s  # noqa: E402


class FakeProc:
    def __init__(self, stdout="", returncode=0, stderr=""):
        self.stdout = stdout
        self.returncode = returncode
        self.stderr = stderr


class FakeRunner:
    """Enregistre les appels `gh` et rejoue des reponses script."""

    def __init__(self, comments=None, post_id=4242):
        self.calls = []
        self.comments = list(comments or [])
        self.post_id = post_id

    def __call__(self, cmd, **kwargs):
        self.calls.append(cmd)
        method = ""
        if "--method" in cmd:
            method = cmd[cmd.index("--method") + 1]
        if method == "PATCH":
            body = cmd[cmd.index("-f") + 1].split("=", 1)[1]
            target = next(e for e in cmd if "/comments/" in e).split("/")[-1]
            for c in self.comments:
                if c["id"] == int(target):
                    c["body"] = body
            return FakeProc(json.dumps({"id": int(target)}), 0)
        if method == "POST":
            body = cmd[cmd.index("-f") + 1].split("=", 1)[1]
            self.comments.append({
                "id": self.post_id, "body": body,
                "user": {"login": "github-actions[bot]"},
            })
            return FakeProc(json.dumps({"id": self.post_id}), 0)
        # listComments : `gh api --paginate --slurp` rend une liste de pages
        return FakeProc(json.dumps([self.comments]), 0)


def bot_comment(cid, body):
    return {"id": cid, "body": body, "user": {"login": "github-actions[bot]"}}


def human_comment(cid, body):
    return {"id": cid, "body": body, "user": {"login": "jsboige"}}


# --------------------------------------------------------------------------
# Corps du commentaire
# --------------------------------------------------------------------------

def test_render_un_seul_marqueur_et_une_section_par_organe():
    body = a_s.render({"organ-b": "texte B", "organ-a": "texte A"})
    assert body.count(a_s.MARKER) == 1
    assert "<!-- organ:organ-a -->" in body
    assert "<!-- organ:organ-b -->" in body
    # ordonne par nom : le corps est deterministe
    assert body.index("organ-a") < body.index("organ-b")


def test_render_deterministe():
    a = a_s.render({"x": "meme texte"})
    b = a_s.render({"x": "meme texte"})
    assert a == b


def test_render_sans_section_annonce_l_etat_vide():
    body = a_s.render({})
    assert a_s.MARKER in body
    assert "Aucun avertissement consultatif" in body


def test_parse_sections_roundtrip():
    body = a_s.render({"organ-a": "ligne 1\nligne 2", "organ-b": "autre"})
    parsed = a_s.parse_sections(body)
    assert parsed["organ-a"] == "ligne 1\nligne 2"
    assert parsed["organ-b"] == "autre"


# --------------------------------------------------------------------------
# Upsert
# --------------------------------------------------------------------------

def test_upsert_cree_le_premier_commentaire():
    runner = FakeRunner(comments=[])
    out = a_s.upsert_section("organ-a", "un avertissement", 123, runner=runner)
    assert out["action"] == "created"
    assert out["comment_id"] == 4242
    assert len(runner.comments) == 1
    assert "un avertissement" in runner.comments[0]["body"]


def test_upsert_reecrit_en_place_sans_creer_de_second_commentaire():
    runner = FakeRunner(comments=[bot_comment(7, a_s.render({"organ-a": "vieux"}))])
    out = a_s.upsert_section("organ-a", "neuf", 123, runner=runner)
    assert out["action"] == "patched"
    assert out["comment_id"] == 7
    assert len(runner.comments) == 1
    assert "neuf" in runner.comments[0]["body"]
    assert "vieux" not in runner.comments[0]["body"]


def test_upsert_ajoute_une_section_sans_ecraser_les_autres():
    runner = FakeRunner(comments=[bot_comment(7, a_s.render({"organ-a": "A"}))])
    a_s.upsert_section("organ-b", "B", 123, runner=runner)
    body = runner.comments[0]["body"]
    assert "<!-- organ:organ-a -->" in body
    assert "<!-- organ:organ-b -->" in body


def test_upsert_identique_ne_rewrite_pas():
    body = a_s.render({"organ-a": "stable"})
    runner = FakeRunner(comments=[bot_comment(7, body)])
    out = a_s.upsert_section("organ-a", "stable", 123, runner=runner)
    assert out["action"] == "unchanged"


def test_commentaire_humain_jamais_edite():
    """Un humain qui cite le marqueur verbatim n'est pas un commentaire bot."""
    runner = FakeRunner(comments=[human_comment(9, a_s.MARKER + "\ntexte humain")])
    out = a_s.upsert_section("organ-a", "avertissement", 123, runner=runner)
    assert out["action"] == "created"  # un nouveau commentaire, pas un PATCH
    assert runner.comments[0]["body"].endswith("texte humain")
    assert runner.comments[1]["id"] == 4242


# --------------------------------------------------------------------------
# Retrait (le succes ne parle pas)
# --------------------------------------------------------------------------

def test_clear_sur_commentaire_absent_n_ecrit_rien():
    runner = FakeRunner(comments=[])
    out = a_s.clear_section("organ-a", 123, runner=runner)
    assert out["action"] == "silent"
    assert runner.comments == []
    # aucun POST : le succes ne cree rien
    assert not any("POST" in c for c in runner.calls)


def test_clear_retire_la_section_et_edite_en_place():
    runner = FakeRunner(comments=[
        bot_comment(7, a_s.render({"organ-a": "averti", "organ-b": "garde"}))])
    out = a_s.clear_section("organ-a", 123, runner=runner)
    assert out["action"] == "patched"
    body = runner.comments[0]["body"]
    assert "averti" not in body
    assert "<!-- organ:organ-b -->" in body
    assert a_s.MARKER in body  # jamais de suppression d'historique


def test_clear_derniere_section_laisse_le_commentaire_vide_mais_present():
    runner = FakeRunner(comments=[bot_comment(7, a_s.render({"organ-a": "averti"}))])
    a_s.clear_section("organ-a", 123, runner=runner)
    body = runner.comments[0]["body"]
    assert "Aucun avertissement consultatif" in body
    assert len(runner.comments) == 1


def test_clear_organe_absent_ne_rewrite_pas():
    runner = FakeRunner(comments=[bot_comment(7, a_s.render({"organ-b": "garde"}))])
    out = a_s.clear_section("organ-a", 123, runner=runner)
    assert out["action"] == "unchanged"


# --------------------------------------------------------------------------
# Garde-fous
# --------------------------------------------------------------------------

@pytest.mark.parametrize("organ", ["", "org an", "org\n", "org>", "<org"])
def test_nom_dorgane_invalide_refuse(organ):
    with pytest.raises(ValueError):
        a_s.upsert_section(organ, "x", 1, runner=FakeRunner())


def test_creation_sans_identifiant_est_refusee():
    """#22758 transpose : pas d'identifiant = ecriture non constatee."""
    class NoIdRunner(FakeRunner):
        def __call__(self, cmd, **kwargs):
            if "--method" in cmd and "POST" in cmd:
                self.calls.append(cmd)
                return FakeProc("{}", 0)
            return super().__call__(cmd, **kwargs)

    runner = NoIdRunner(comments=[])
    with pytest.raises(RuntimeError):
        a_s.upsert_section("organ-a", "x", 1, runner=runner)


def test_echec_gh_remonte():
    class FailingRunner(FakeRunner):
        def __call__(self, cmd, **kwargs):
            return FakeProc("", 1, "boom")

    with pytest.raises(RuntimeError):
        a_s.upsert_section("organ-a", "x", 1, runner=FailingRunner())
