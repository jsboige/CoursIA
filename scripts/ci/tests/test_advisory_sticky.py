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


class SharedStore:
    """Etat partage par deux runners : deux ecrivains concurrents ecrivent
    dans le meme fil de commentaires."""

    def __init__(self, comments=None):
        self.comments = list(comments or [])


class FakeRunner:
    """Enregistre les appels `gh` et rejoue des reponses script."""

    def __init__(self, comments=None, post_id=4242, store=None):
        self.calls = []
        self.store = store
        self.comments = (store.comments if store is not None
                         else list(comments or []))
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


class StaleReadRunner(FakeRunner):
    """Runner dont la PREMIERE lecture est **perimee**.

    L'autre ecrivain ecrit entre notre lecture et notre ecriture : le corps
    que nous allons PATCHer est derive d'un etat qui ne contenait pas sa
    section. C'est la fenetre de perte d'ecriture.

    C'est le **miroir** de `InterleavingRunner(clobber_section=...)` : la,
    l'autre efface notre section ; ici, c'est nous qui effacons la sienne --
    et notre verification, qui ne regarde que notre organe, ne le voit pas.
    """

    def __init__(self, other, store, other_sections=None):
        super().__init__(store=store)
        self.other = other
        self.other_sections = dict(other_sections or {})
        self._injected = False

    def __call__(self, cmd, **kwargs):
        method = ""
        if "--method" in cmd:
            method = cmd[cmd.index("--method") + 1]
        if method == "" and not self._injected:
            # Notre lecture : on rend l'etat d'aujourd'hui, puis l'autre
            # ecrivain ecrit -- AVANT notre PATCH.
            self._injected = True
            snapshot = json.dumps([self.comments])
            target = self.comments[0]["id"]
            self.other(
                ["gh", "api", "--method", "PATCH",
                 f"repos/jsboige/CoursIA/issues/comments/{target}",
                 "-f", f"body={a_s.render(self.other_sections)}"],
                capture_output=True, text=True, timeout=15)
            return FakeProc(snapshot, 0)
        return super().__call__(cmd, **kwargs)


class InterleavingRunner(FakeRunner):
    """Runner A ; le runner B (le **second ecrivain**) agit au moment de
    l'ecriture, sur le meme etat partage.

    Les six workflows ont chacun leur groupe ``concurrency`` : sur un meme
    ``synchronize`` ils tournent en parallele. Deux defauts sont simules :

    * ``concurrent_section`` : B cree son commentaire collant juste apres
      notre POST -> deux commentaires collants ;
    * ``clobber_section`` : B ecrase notre ecriture et **perd** la section
      que nous venions d'ecrire (mise a jour perdue).
    """

    def __init__(self, other, store, concurrent_section=None,
                 concurrent_body="contenu de l'autre organe",
                 clobber_section=None, clobber_always=False):
        super().__init__(store=store)
        self.other = other
        self.concurrent_section = concurrent_section
        self.concurrent_body = concurrent_body
        self.clobber_section = clobber_section
        self.clobber_always = clobber_always
        self._post_done = False
        self._patch_done = False

    def __call__(self, cmd, **kwargs):
        method = ""
        if "--method" in cmd:
            method = cmd[cmd.index("--method") + 1]
        if method == "POST" and not self._post_done and self.concurrent_section:
            self._post_done = True
            out = super().__call__(cmd, **kwargs)
            self.other(
                ["gh", "api", "--method", "POST",
                 "repos/jsboige/CoursIA/issues/123/comments",
                 "-f", f"body={a_s.render({self.concurrent_section: self.concurrent_body})}"],
                capture_output=True, text=True, timeout=15)
            return out
        if method in ("POST", "PATCH") and self.clobber_section and (
                self.clobber_always or not self._patch_done):
            self._patch_done = True
            out = super().__call__(cmd, **kwargs)
            body = cmd[cmd.index("-f") + 1].split("=", 1)[1]
            if method == "PATCH":
                target = next(e for e in cmd if "/comments/" in e).split("/")[-1]
                target_id = int(target)
            else:
                target_id = self.post_id
            sections = a_s.parse_sections(body)
            sections.pop(self.clobber_section, None)
            self.other(
                ["gh", "api", "--method", "PATCH",
                 f"repos/jsboige/CoursIA/issues/comments/{target_id}",
                 "-f", f"body={a_s.render(sections)}"],
                capture_output=True, text=True, timeout=15)
            return out
        return super().__call__(cmd, **kwargs)


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


# --------------------------------------------------------------------------
# Ecritures concurrentes (reserve ai-01, review 5752268155)
# --------------------------------------------------------------------------

def test_deux_posts_concurrents_sont_fusionnes_dans_le_canonique():
    """Deux workflows en parallele ne doivent pas laisser deux collants."""
    store = SharedStore()
    other = FakeRunner(store=store, post_id=4243)
    runner = InterleavingRunner(other, store, concurrent_section="organ-b",
                                concurrent_body="avertissement B")
    out = a_s.upsert_section("organ-a", "avertissement A", 123, runner=runner,
                              sleep=lambda _s: None)
    assert out["verified"] is True
    stickies = [c for c in runner.comments if a_s.MARKER in c["body"]]
    assert len(stickies) == 1, "le PR ne doit porter qu'un commentaire collant"
    sections = a_s.parse_sections(stickies[0]["body"])
    assert sections["organ-a"] == "avertissement A"
    assert sections["organ-b"] == "avertissement B"
    # le doublon n'est pas supprime : il devient un renvoi vers le canonique
    others = [c for c in runner.comments if c is not stickies[0]]
    assert len(others) == 1
    assert a_s.FORWARD_MARKER in others[0]["body"]
    assert a_s.MARKER not in others[0]["body"]


def test_une_section_ecraseee_par_un_patch_concurrent_est_reprise():
    """Mise a jour perdue : la verification relit et reapplique."""
    store = SharedStore()
    other = FakeRunner(store=store, post_id=4243)
    runner = InterleavingRunner(other, store, clobber_section="organ-a")
    out = a_s.upsert_section("organ-a", "avertissement A", 123, runner=runner,
                              sleep=lambda _s: None)
    assert out["verified"] is True
    sections = a_s.parse_sections(
        next(c["body"] for c in runner.comments if a_s.MARKER in c["body"])
    )
    assert sections["organ-a"] == "avertissement A"


def test_une_verification_qui_echoue_toujours_est_remontee():
    """Trois tentatives, puis l'echec est remonte : pas de succes sur une
    ecriture non constatee."""
    store = SharedStore()
    other = FakeRunner(store=store, post_id=4243)
    runner = InterleavingRunner(other, store, clobber_section="organ-a",
                                clobber_always=True)
    sleeps = []
    with pytest.raises(RuntimeError):
        a_s.upsert_section("organ-a", "avertissement A", 123, runner=runner,
                           attempts=3, sleep=sleeps.append)
    # un delai aleatoire entre deux tentatives (et pas entre la derniere)
    assert len(sleeps) == 2
    assert all(s > 0 for s in sleeps)


def test_le_retrait_concurrent_est_verifie():
    """Le succes d'un organe ne parle toujours pas, et le retrait se vérifie."""
    runner = FakeRunner(comments=[
        bot_comment(7, a_s.render({"organ-a": "averti", "organ-b": "garde"}))])
    out = a_s.clear_section("organ-a", 123, runner=runner,
                             sleep=lambda _s: None)
    assert out["action"] == "patched"
    assert out["verified"] is True
    body = runner.comments[0]["body"]
    assert "averti" not in body
    assert "<!-- organ:organ-b -->" in body


def test_la_section_d_un_autre_ecrivain_survit_a_notre_lecture_perimee():
    """Le contre-exemple manquant : **notre** ecriture effacait la section
    de l'autre ecrivain.

    Mesure (adjoint `myia-po-2025:CoursIA-2`, 2026-11-03, contre-exemple
    `sections[organ]`) : B capture le corps initial ; A ecrit `organ-a` ;
    B reprend sa lecture **perimee**, PATCH son `organ-b` et termine
    `verified: true`. Etat final : `initial + organ-b`, `organ-a` **absente**
    -- et personne ne l'a vu, parce que la verification ne regarde que la
    section qu'on a ecrite. Un seul collant, donc `merge_duplicates` ne
    rattrape rien.

    La relecture d'avant-ecriture referme la fenetre : si le corps a bouge
    depuis notre lecture, notre section est reappliquee sur le corps
    courant au lieu de l'ecraser.
    """
    store = SharedStore([
        bot_comment(7, a_s.render({"initial": "etat initial"}))])
    other = FakeRunner(store=store, post_id=4243)
    runner = StaleReadRunner(other, store, other_sections={
        "initial": "etat initial", "organ-a": "avertissement A"})
    out = a_s.upsert_section("organ-b", "avertissement B", 123, runner=runner,
                              sleep=lambda _s: None)
    assert out["verified"] is True
    sections = a_s.parse_sections(
        next(c["body"] for c in runner.comments if a_s.MARKER in c["body"]))
    assert sections.get("organ-a") == "avertissement A", (
        "la section de l'autre ecrivain ne doit pas disparaitre")
    assert sections.get("organ-b") == "avertissement B"
    assert sections.get("initial") == "etat initial"


def test_le_retrait_n_efface_pas_la_section_ajoutee_par_un_autre():
    """Meme fenetre, cote retrait : retirer notre section ne doit pas
    effacer celle qu'un autre ecrivain a ajoutee entre-temps."""
    store = SharedStore([
        bot_comment(7, a_s.render({"initial": "etat initial",
                                    "organ-a": "avertissement A"}))])
    other = FakeRunner(store=store, post_id=4243)
    runner = StaleReadRunner(other, store, other_sections={
        "initial": "etat initial", "organ-a": "avertissement A",
        "organ-b": "avertissement B"})
    out = a_s.clear_section("organ-a", 123, runner=runner,
                             sleep=lambda _s: None)
    assert out["verified"] is True
    sections = a_s.parse_sections(
        next(c["body"] for c in runner.comments if a_s.MARKER in c["body"]))
    assert "organ-a" not in sections, "notre section doit etre retiree"
    assert sections.get("organ-b") == "avertissement B", (
        "la section de l'autre ecrivain ne doit pas disparaitre")
    assert sections.get("initial") == "etat initial"
