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
    dans le meme fil de commentaires et sur le meme jeu d'etiquettes (le
    verrou d'ecriture est une etiquette du PR).

    Les etiquettes portent un **identifiant serveur** attribue par
    creation (mesure du 2026-11-04) : c'est lui qui donne l'ordre
    d'arbitrage du verrou -- aucune horloge n'entre dans la decision.
    """

    def __init__(self, comments=None, labels=None):
        self.comments = list(comments or [])
        self.labels = list(labels or [])   # definitions au niveau du depot
        self.label_ids = {}                # nom -> identifiant serveur
        self._next_label_id = 1000
        for name in self.labels:
            self.label_ids[name] = self._next_label_id
            self._next_label_id += 1

    def add_label(self, name):
        """Ajout a l'ensemble : l'identifiant est attribue par creation."""
        if name not in self.label_ids:
            self.label_ids[name] = self._next_label_id
            self._next_label_id += 1
        if name not in self.labels:
            self.labels.append(name)
        return self.label_ids[name]

    def drop_label(self, name):
        """Suppression au niveau du DEPOT : la **definition** disparait et
        le PR perd l'etiquette (mesure du 2026-11-04 : DELETE
        /repos/{repo}/labels/{nom} -> 204 + detachement)."""
        while name in self.labels:
            self.labels.remove(name)
        self.label_ids.pop(name, None)

    def label_rows(self):
        return [{"name": n, "id": self.label_ids.get(n)}
                for n in self.labels]


class FakeRunner:
    """Enregistre les appels `gh` et rejoue des reponses script."""

    def __init__(self, comments=None, post_id=4242, store=None):
        self.calls = []
        self.store = store if store is not None else SharedStore(comments)
        self.comments = self.store.comments
        self.labels = self.store.labels
        self.post_id = post_id

    def __call__(self, cmd, **kwargs):
        self.calls.append(cmd)
        method = ""
        if "--method" in cmd:
            method = cmd[cmd.index("--method") + 1]
        # --- etiquettes : le verrou d'ecriture -----------------------------
        if any("/labels" in c for c in cmd):
            if method == "POST":
                name = cmd[cmd.index("-f") + 1].split("=", 1)[1]
                self.store.add_label(name)
                # la reponse du serveur porte la liste COMPLETE des
                # etiquettes du PR (mesure du 2026-11-04)
                return FakeProc(json.dumps(self.store.label_rows()), 0)
            if method == "DELETE":
                # DELETE au niveau du DEPOT : la definition disparait ET le
                # PR perd l'etiquette (mesure du 2026-11-04).
                name = next(c for c in cmd
                            if "/labels/" in c).split("/labels/", 1)[1]
                self.store.drop_label(name)
                return FakeProc("", 0)
            # GET : `--paginate --slurp` rend une liste de pages
            return FakeProc(json.dumps([self.store.label_rows()]), 0)
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


def test_une_ecriture_concurrente_qui_atterrit_apres_notre_verification_est_reprise():
    """Le **residu** signale par l'adjoint (2026-11-04) : le second
    ecrivain ecrase notre section **apres** notre premiere verification.

    Entrelencement mesure par l'adjoint : `B.relecture < A.PATCH <
    A.verify < B.PATCH` -> les deux ecrivains se croient verifies, et la
    section de A a disparu. La relecture d'**avant** ecriture ne le voit
    pas (elle est anterieure au PATCH de B) : elle rattrape l'entre-deux
    lectures, pas l'apres-relecture.

    La **fenetre de stabilisation** le voit : apres une premiere
    verification, on relit une fois de plus. Si notre section a disparu,
    c'est qu'un ecrivain concurrent nous a ecrase -- on ne certifie pas, on
    rejoue, et le rejeu remerge les DEUX sections sur le corps courant.

    Ce que la fenetre ne ferme pas (et que le corps documente) : une
    ecriture concurrente tombee **apres** la derniere relecture. L'ecriture
    conditionnelle, qui la fermerait, est refusee par l'API (mesure du
    2026-11-04 : HTTP 400 « Conditional request headers are not allowed in
    unsafe requests unless supported by the endpoint »).
    """
    store = SharedStore()
    other = FakeRunner(store=store, post_id=4242)
    runner = FakeRunner(store=store)
    # B ecrit sa section d'abord.
    other(["gh", "api", "--method", "POST",
           "repos/jsboige/CoursIA/issues/123/comments",
           "-f", f"body={a_s.render({'organ-b': 'avertissement B'})}"])
    # ... puis, au moment de notre delai de stabilisation (donc APRES notre
    # premiere verification), B ecrase notre section : son ecriture part
    # d'un corps qui ne contient pas la notre.
    state = {"clobbered": False}

    def clobber(_seconds):
        if state["clobbered"]:
            return
        state["clobbered"] = True
        other(["gh", "api", "--method", "PATCH",
               "repos/jsboige/CoursIA/issues/123/comments/4242",
               "-f", f"body={a_s.render({'organ-b': 'avertissement B'})}"])

    out = a_s.upsert_section("organ-a", "avertissement A", 123, runner=runner,
                              sleep=clobber)
    assert state["clobbered"] is True, "le clobber concurrent doit avoir eu lieu"
    assert out["verified"] is True
    sections = a_s.parse_sections(
        next(c["body"] for c in runner.comments if a_s.MARKER in c["body"]))
    assert sections.get("organ-a") == "avertissement A", (
        "notre section doit avoir ete reecrite apres le clobber concurrent")
    assert sections.get("organ-b") == "avertissement B", (
        "la section de l'autre ecrivain ne doit pas disparaitre")


# --------------------------------------------------------------------------
# Verrou d'ecriture -- etiquette du PR (2026-11-04)
# --------------------------------------------------------------------------

class DelayedLabelRunner(FakeRunner):
    """Runner B : sa lecture des etiquettes rend l'instantane capture
    **avant** que A n'ait termine son cycle.

    C'est le scheduling de l'adjoint (`myia-po-2025:CoursIA-2`, le
    2026-11-04) : `B.relecture < A.PATCH < A.verify < B.PATCH`.
    """

    def __init__(self, other_cycle, store):
        super().__init__(store=store)
        self.other_cycle = other_cycle
        self._injected = False
        # Etat de A **au moment exact de l'injection** : sert a prouver
        # que l'injection a lieu APRES les deux verifications de A
        # (le `inject_at=2` du reproducteur de l'adjoint).
        self.a_verified_at_injection = None

    def __call__(self, cmd, **kwargs):
        method = ""
        if "--method" in cmd:
            method = cmd[cmd.index("--method") + 1]
        if (method == "" and any("/labels" in c for c in cmd)
                and not self._injected):
            self._injected = True
            # l'instantane capture AVENT le cycle de A : identifiants
            # compris (l'ordre d'arbitrage est l'identifiant serveur).
            snapshot = self.store.label_rows()
            # A termine integralement avant que B ne lise les etiquettes.
            res = self.other_cycle()
            self.a_verified_at_injection = bool(res and res.get("verified"))
            # B recoit son ancien instantane.
            return FakeProc(json.dumps([snapshot]), 0)
        if (method == "PATCH" and any("/comments/" in c for c in cmd)
                and not self._injected):
            # Repli : le mecanisme lu les commentaires et non les
            # etiquettes (verrou **dans le corps**). L'injection se fait
            # alors juste avant le PATCH de B -- c'est ce PATCH, qui porte
            # un corps perime, qui effacait la section de A.
            self._injected = True
            res = self.other_cycle()
            self.a_verified_at_injection = bool(res and res.get("verified"))
        return super().__call__(cmd, **kwargs)


def test_le_scheduling_de_l_adjoint_preserve_la_section_de_a():
    """Le scheduling exact signale par l'adjoint le 2026-11-04 : B lit,
    A execute `upsert_section` integralement (prise de verrou, ecriture,
    deux verifications, liberation), puis B prend le verrou et ecrit.

    Sur le verrou **dans le corps du commentaire**, B ecrivait un corps
    perime : la section de A disparaissait, et les deux ecrivains se
    croient `verified: true`. Sur le verrou **par etiquette du PR**, B ne
    peut ecrire qu'une fois le verrou d'A libere, et il ecrit alors sur le
    corps courant -- la section de A survit.

    **Correspondance avec le reproducteur de l'adjoint (`inject_at=2`) :
    A perd sa section APRES ses deux verifications, et le delai de
    stabilisation ne refuse pas l'etat perime.** L'assertion
    `a_verified_at_injection` etablit exactement ce point : au moment ou
    l'ecriture concurrente est injectee, A a **deja** rendu
    `verified: true`. Le delai ne sert donc a rien contre ce scheduling --
    seule l'**atomicite de l'acquisition** le ferme.
    """
    store = SharedStore([bot_comment(7, a_s.render({"initial": "etat initial"}))])
    a_runner = FakeRunner(store=store)

    def a_cycle():
        return a_s.upsert_section("organ-a", "avertissement A", 123,
                                  runner=a_runner, sleep=lambda _s: None,
                                  owner="writer-A")

    b_runner = DelayedLabelRunner(a_cycle, store)
    out_b = a_s.upsert_section("organ-b", "avertissement B", 123,
                                runner=b_runner, sleep=lambda _s: None,
                                owner="writer-B")
    assert out_b["verified"] is True
    assert b_runner.a_verified_at_injection is True, (
        "l'injection doit avoir lieu APRES les deux verifications de A "
        "(reproducteur `inject_at=2` de l'adjoint)")
    sections = a_s.parse_sections(store.comments[0]["body"])
    assert sections.get("organ-a") == "avertissement A", (
        "la section de A doit survivre a l'ecriture de B")
    assert sections.get("organ-b") == "avertissement B"
    assert sections.get("initial") == "etat initial"
    assert not store.labels, "le verrou doit etre relache"


def test_un_ecrivain_concurrent_attend_le_verrou_au_lieu_d_ecraser():
    """Un ecrivain concurrent **attend** le verrou : il n'ecrit pas pendant
    la fenetre de l'autre.

    Le verrou est une **etiquette du PR** : l'ajout est atomique cote
    serveur, l'arbitrage se lit dans l'ensemble (le plus ancien gagne).
    """
    store = SharedStore([bot_comment(7, a_s.render({"initial": "etat initial"}))])
    runner = FakeRunner(store=store)
    other = FakeRunner(store=store)
    state = {"b_done": False}

    def sleep_a(_seconds):
        """Le delai de stabilisation de A : c'est la que B arrive."""
        if state["b_done"]:
            return
        state["b_done"] = True

        def b_wait(_s):
            # B attend : l'etiquette de A est vivante, donc B n'ecrit pas.
            if "during_wait" not in state:
                body = next(c["body"] for c in runner.comments
                            if a_s.MARKER in c["body"])
                state["during_wait"] = a_s.parse_sections(body)
                state["locks_during_wait"] = list(store.labels)
                # A relache : B peut ecrire.
                for name in list(store.labels):
                    a_s._delete_label(a_s.DEFAULT_REPO, runner, 15, name)

        a_s.upsert_section(
            "organ-b", "avertissement B", 123, runner=other,
            sleep=b_wait, owner="writer-B")

    out = a_s.upsert_section("organ-a", "avertissement A", 123, runner=runner,
                              sleep=sleep_a, owner="writer-A")
    assert state["b_done"] is True, "B doit avoir tente son ecriture"
    assert "organ-b" not in state["during_wait"], (
        "B ne doit pas ecrire pendant la fenetre de A")
    assert state["locks_during_wait"], (
        "le verrou de A doit etre vivant pendant que B attend")
    assert out["verified"] is True
    sections = a_s.parse_sections(
        next(c["body"] for c in runner.comments if a_s.MARKER in c["body"]))
    assert sections.get("organ-a") == "avertissement A", (
        "notre section doit avoir survecu a l'ecriture concurrente")
    assert sections.get("organ-b") == "avertissement B", (
        "la section de l'autre ecrivain ne doit pas disparaitre")
    assert sections.get("initial") == "etat initial"


def test_un_verrou_tenu_par_un_autre_refuse_l_ecriture_au_bout_de_l_attente(
        monkeypatch):
    """Le contention n'est pas un echec silencieux : on attend, puis on
    **refuse** franchement. Le corps du commentaire n'est pas touche.

    Le TTL est neutralise ici : le verrou de l'autre ecrivain est suppose
    **vivant** pendant toute l'attente -- c'est le cas qui doit finir en
    refus franc, pas en reclamation."""
    monkeypatch.setattr(a_s, "LOCK_TTL_SECONDS", 10_000.0)
    body = a_s.render({"organ-a": "A"})
    store = SharedStore([bot_comment(7, body)],
                         labels=[a_s._lock_label("writer-A")])
    runner = FakeRunner(store=store)
    ticks = iter(range(0, 100000))
    with pytest.raises(RuntimeError):
        a_s._acquire_lock(123, a_s.DEFAULT_REPO, runner, 15, "writer-B",
                          lambda _s: None,
                          monotonic=lambda: next(ticks))
    assert store.comments[0]["body"] == body, (
        "le verrou de l'autre ecrivain ne doit pas etre vole ni ecrase")
    assert store.labels == [a_s._lock_label("writer-A")], (
        "le verrou de l'autre ecrivain doit rester en place")


def test_un_verrou_perime_est_vole():
    """Un ecrivain mort laisse son etiquette : vue vivante pendant le TTL
    sans interruption, elle est presumee **perimee** -- le suivant la
    supprime et prend la main.

    La peremption se mesure sur une **duree d'observation locale** (la
    fenetre de celui qui observe) : aucune horloge d'une autre machine
    n'entre dans la comparaison."""
    store = SharedStore([bot_comment(7, a_s.render({"organ-a": "A"}))],
                         labels=[a_s._lock_label("writer-A")])
    runner = FakeRunner(store=store)
    ticks = iter(range(0, 1000000, 10))
    token = a_s._acquire_lock(
        123, a_s.DEFAULT_REPO, runner, 15, "writer-B", lambda _s: None,
        monotonic=lambda: next(ticks))
    assert token, "le verrou doit etre pris"
    assert a_s._lock_label("writer-A") not in store.labels, (
        "le verrou perime doit etre supprime")
    assert token in store.labels


def test_l_arbitrage_du_verrou_porte_sur_l_identifiant_serveur():
    """Deux concurrents eligent le **meme** gagnant : l'ordre est
    l'identifiant serveur (attribue par creation), pas l'ordre des noms,
    ni une horloge de client.

    Le rival porte ici un nom qui, par ordre alphabetique, passerait
    **dernier** : s'il l'emporte, c'est bien son identifiant qui decide."""
    monkeypatch = pytest.MonkeyPatch()
    try:
        monkeypatch.setattr(a_s, "LOCK_TTL_SECONDS", 10_000.0)
        store = SharedStore([bot_comment(7, a_s.render({"organ-a": "A"}))],
                             labels=["coursia-advisory-lock-zulu"])
        runner = FakeRunner(store=store)
        ticks = iter(range(0, 100000))
        with pytest.raises(RuntimeError):
            # l'identifiant du rival est plus petit que le notre : il
            # tient le verrou, nous attendons puis refusons.
            a_s._acquire_lock(123, a_s.DEFAULT_REPO, runner, 15, "writer-B",
                              lambda _s: None,
                              monotonic=lambda: next(ticks))
    finally:
        monkeypatch.undo()
    assert store.labels == ["coursia-advisory-lock-zulu"], (
        "le verrou du rival (identifiant plus petit) doit rester en place")


def test_un_concurrent_qui_s_enregistre_pendant_la_stabilisation_nous_fait_attendre(
        monkeypatch):
    """Une lecture peut avoir ete servie **avant** la commit d'un
    concurrent : la relecture de confirmation, apres le delai de
    stabilisation, est celle qui tranche.

    Le rival s'enregistre pendant ce delai, avec un identifiant **plus
    petit** que le notre : nous ne devons pas ecrire."""
    monkeypatch.setattr(a_s, "LOCK_TTL_SECONDS", 10_000.0)
    store = SharedStore([bot_comment(7, a_s.render({"organ-a": "A"}))])
    runner = FakeRunner(store=store)
    state = {"injected": False}

    def sleep(_seconds):
        # le rival s'enregistre pendant notre delai de stabilisation
        if not state["injected"]:
            state["injected"] = True
            store.labels.append("coursia-advisory-lock-rival")
            store.label_ids["coursia-advisory-lock-rival"] = 1  # plus petit

    ticks = iter(range(0, 100000))
    with pytest.raises(RuntimeError):
        a_s._acquire_lock(123, a_s.DEFAULT_REPO, runner, 15, "writer-B",
                          sleep, monotonic=lambda: next(ticks))
    assert state["injected"] is True, "le rival doit s'etre enregistre"


class RacingDeleteRunner(FakeRunner):
    """Runner dont le **DELETE** peut tomber sur une etiquette deja
    absente : l'autre ecrivain l'a supprimee entre notre lecture et notre
    retrait. L'API rend alors **404** (mesure Hermes, 2026-11-04T06:43Z).

    C'est le cas nominal de deux ecrivains qui voient le meme verrou
    perime : le premier le supprime, le second prend un 404.
    """

    def __init__(self, store):
        super().__init__(store=store)
        self._injected = False

    def __call__(self, cmd, **kwargs):
        method = ""
        if "--method" in cmd:
            method = cmd[cmd.index("--method") + 1]
        if method == "" and any("/labels" in c for c in cmd) and not self._injected:
            self._injected = True
            # l'instantane montre encore le verrou perime...
            rows = self.store.label_rows()
            # ...mais l'autre ecrivain vient de le supprimer
            for name in list(self.store.labels):
                self.store.drop_label(name)
            return FakeProc(json.dumps([rows]), 0)
        if method == "DELETE":
            name = next(c for c in cmd
                        if "/labels/" in c).split("/labels/", 1)[1]
            if name not in self.store.labels:
                return FakeProc("", 1, "gh: Not Found (HTTP 404)")
        return super().__call__(cmd, **kwargs)


def test_un_404_sur_le_retrait_d_une_etiquette_absente_est_tolere():
    """DELETE d'une etiquette deja absente rend 404. La purge et la
    liberation doivent le **tolerer** : sinon deux ecrivains qui voient le
    meme verrou perime font remonter l'exception, et la publication
    echoue au lieu de degrader (mesure Hermes, 2026-11-04T06:43Z)."""
    store = SharedStore([bot_comment(7, a_s.render({"organ-a": "A"}))])
    runner = RacingDeleteRunner(store=store)
    # aucune exception : l'etiquette absente reste absente
    a_s._delete_label(a_s.DEFAULT_REPO, runner, 15,
                      a_s._lock_label("writer-A"))
    assert store.labels == []
    # et la liberation d'un verrou deja vole ne leve pas non plus
    assert a_s._release_lock(123, a_s.DEFAULT_REPO, runner, 15,
                              a_s._lock_label("writer-B")) is True


def test_deux_ecrivains_purgent_le_meme_verrou_perime_sans_rompre(monkeypatch):
    """Les deux ecrivains voient le **meme** verrou perime : le premier le
    supprime, le second prend un 404 sur le meme retrait. Il doit
    attendre et publier, pas echouer."""
    monkeypatch.setattr(a_s, "LOCK_TTL_SECONDS", 0.0)
    store = SharedStore([bot_comment(7, a_s.render({"organ-a": "A"}))],
                         labels=[a_s._lock_label("writer-A")])
    runner = RacingDeleteRunner(store=store)
    token = a_s._acquire_lock(123, a_s.DEFAULT_REPO, runner, 15, "writer-B",
                              lambda _s: None, monotonic=lambda: 0.0)
    assert token, "l'ecrivain doit prendre le verrou malgre le 404"


def test_le_verrou_est_relache_a_la_fin_de_l_ecriture():
    """Le verrou est une ligne de travail, pas un artefact : l'etiquette
    doit etre retiree, et le corps ne doit porter aucune ligne de verrou."""
    store = SharedStore([bot_comment(7, a_s.render({"organ-a": "vieux"}))])
    runner = FakeRunner(store=store)
    a_s.upsert_section("organ-a", "neuf", 123, runner=runner,
                        sleep=lambda _s: None, owner="writer-A")
    body = store.comments[0]["body"]
    assert not store.labels, "le verrou doit etre relache"
    assert "neuf" in body


def test_la_liberation_supprime_la_definition_de_l_etiquette_au_depot():
    """La liberation doit supprimer la **definition** de l'etiquette au
    depot, pas seulement le lien sur le PR : sinon une definition par
    prise de verrou deriverait au depot (fuite mesuree le 2026-11-04)."""
    store = SharedStore([bot_comment(7, a_s.render({"organ-a": "vieux"}))])
    runner = FakeRunner(store=store)
    a_s.upsert_section("organ-a", "neuf", 123, runner=runner,
                        sleep=lambda _s: None, owner="writer-A")
    assert store.labels == [], (
        "aucune definition d'etiquette ne doit rester au depot")
    deletes = [c for c in runner.calls
               if "--method" in c and "DELETE" in c and "/labels/" in " ".join(c)]
    assert deletes, "la liberation doit supprimer l'etiquette"
    for cmd in deletes:
        url = next(c for c in cmd if "/labels/" in c)
        assert "/issues/" not in url, (
            "la suppression doit viser la definition du depot "
            "(repos/{repo}/labels/{nom}), pas le seul lien sur le PR")


def test_un_run_sans_nouveaute_ne_touche_pas_le_commentaire():
    """Le succes ne parle pas, et son repeat ne **reecrit pas** : un corps
    deja dans l'etat voulu ne declenche aucune ecriture (pas de bruit
    d'edition)."""
    body = a_s.render({"organ-a": "stable"})
    runner = FakeRunner(comments=[bot_comment(7, body)])
    out = a_s.upsert_section("organ-a", "stable", 123, runner=runner,
                              sleep=lambda _s: None, owner="writer-A")
    assert out["action"] == "unchanged"
    assert out["verified"] is True
    assert runner.comments[0]["body"] == body, "le corps doit rester identique"
    assert not any("PATCH" in c for c in runner.calls), (
        "aucune ecriture ne doit partir quand rien ne change")


def test_le_verrou_ne_touche_pas_aux_sections_des_autres():
    """Le corps ecrit sous verrou porte TOUJOURS les sections des autres
    ecrivains : le verrou ne les efface pas."""
    runner = FakeRunner(comments=[
        bot_comment(7, a_s.render({"organ-a": "A", "organ-b": "B"}))])
    a_s.upsert_section("organ-c", "C", 123, runner=runner,
                        sleep=lambda _s: None, owner="writer-A")
    sections = a_s.parse_sections(runner.comments[0]["body"])
    assert sections == {"organ-a": "A", "organ-b": "B", "organ-c": "C"}
