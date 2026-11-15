#!/usr/bin/env python3
"""Plancher d'allocation d'ordinal contre les PRs OUVERTES (#22299).

Le plancher d'allocation (`_audit_floor`) lisait la **ref d'integration**
seule (`origin/main`). Mesure du 2026-11-09 (constat du coordinateur) : une
PR **ouverte** peut deja tenir l'ordinal que l'on s'apprete a proposer --
l'ordinal `0018` de `tweety-11-causal` etait tenu par #25037, et la collision
n'est visible qu'**apres** le push, quand le travail est deja fait.

Le correctif ajoute un second plancher : `_open_claim_floors(repo_root)` lit
les **revendications** des PRs ouvertes via l'organe natif
`twin_open_claims.py` (importe, pas reimplemente), et l'index alloue passe
au-dessus du plus haut ordinal revendique pour la paire.

Trois proprietes sont testees ici :

    1. **controle positif** -- avec une PR ouverte revendiquant `0018`, l'index
       alloue est `0019` : il passe au-dessus de la revendication ;
    2. **controle negatif** -- SANS le plancher des PRs ouvertes, l'allocation
       retombe sur le max local + 1 et **revendique l'ordinal deja pris**
       (le comportement historique que le correctif retire) ;
    3. **degradation** -- une lecture impossible des PRs ouvertes rend un
       plancher VIDE et un avertissement sur stderr : jamais une exception,
       jamais une ecriture refusee (le plancher est un garde, pas une mesure).

Le stub cible `collect_open_claims` (le point de contact de l'organe natif) :
on ne reecrit pas l'organe dans le test, on verifie que l'appel est fait et
que son resultat est converti en plancher.

Run:
    pytest scripts/notebook_tools/tests/test_twin_allocate_open_claims.py
"""
from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent.parent
SCRIPT = SCRIPT_DIR / "check_twin_parity.py"

PAIR_NAME = "Probas-13 Crowdsourcing"
PAIR_SLUG = "probas-13-crowdsourcing"


def _load_module():
    spec = importlib.util.spec_from_file_location("check_twin_parity", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


ctp = _load_module()


def _audit_dict() -> dict:
    return {"date": "2026-11-10", "by": "myia-ai-01:CoursIA-2",
            "python": {"blob_sha": "0" * 40},
            "csharp": {"blob_sha": "1" * 40}}


def _publish_audits(registry: Path, indexes: list[int]) -> None:
    """Ecrit des attestations sur DISQUE (le max local)."""
    d = registry / PAIR_SLUG
    d.mkdir(parents=True, exist_ok=True)
    for index in indexes:
        (d / f"{index:04d}-2026-11-01-myia-po-2025-CoursIA.yaml").write_text(
            "date: \"2026-11-01\"\nby: myia-po-2025:CoursIA\n",
            encoding="utf-8", newline="",
        )


def _stub_open_claims(monkeypatch, claims_by_pr: dict) -> list:
    """Stub de l'organe natif : rend les revendications et note les appels.

    On capture aussi le `slug` demande : un appel avec un slug vide serait
    une lecture qui ne lit rien (le parc se vide silencieusement).
    """
    calls = []

    def fake_collect(slug, *, cwd=None):
        calls.append(slug)
        return {"prs": claims_by_pr}

    monkeypatch.setattr(ctp, "repo_slug", lambda cwd=None: "jsboige/CoursIA")
    monkeypatch.setattr(ctp, "collect_open_claims", fake_collect)
    return calls


# --- 1. le plancher des PRs ouvertes ----------------------------------------

def test_le_plancher_des_prs_ouvertes_est_le_plus_haut_ordinal_revendique(
        tmp_path, monkeypatch):
    """Une PR ouverte revendiquant `0018` et une autre `0004` -> plancher 18."""
    _stub_open_claims(monkeypatch, {
        "25037": [{"pair": PAIR_SLUG, "index": "0018",
                   "path": "x/0018-2026-11-01-a.yaml"}],
        "24010": [{"pair": PAIR_SLUG, "index": "0004",
                   "path": "x/0004-2026-11-01-b.yaml"}],
    })
    floors = ctp._open_claim_floors(tmp_path)
    assert floors == {PAIR_SLUG: 18}, (
        f"plancher attendu {{'{PAIR_SLUG}': 18}}, obtenu {floors} : le "
        f"plancher doit retenir le PLUS HAUT ordinal revendique par paire, "
        f"pas le premier ni le nombre de PRs."
    )


def test_une_revendication_d_une_autre_paire_ne_contamine_pas(tmp_path, monkeypatch):
    """Les paires sont cloisonnees : le dossier est la cle du plancher."""
    _stub_open_claims(monkeypatch, {
        "25037": [{"pair": "tweety-11-causal", "index": "0018", "path": "x/a.yaml"}],
    })
    floors = ctp._open_claim_floors(tmp_path)
    assert floors == {"tweety-11-causal": 18}
    assert PAIR_SLUG not in floors


def test_le_plancher_appelle_l_organe_natif_avec_le_slug_du_depot(
        tmp_path, monkeypatch):
    """Le read passe par `twin_open_claims`, pas par une reimplementation."""
    calls = _stub_open_claims(monkeypatch, {})
    ctp._open_claim_floors(tmp_path)
    assert calls == ["jsboige/CoursIA"], (
        f"un seul appel a l'organe natif est attendu, observe {calls}."
    )


def test_une_ordinal_non_numerique_ne_devient_pas_un_plancher(
        tmp_path, monkeypatch):
    """Un nom de fichier sans index numerique ne revendique rien."""
    _stub_open_claims(monkeypatch, {
        "25037": [{"pair": PAIR_SLUG, "index": "notes", "path": "x/a.yaml"}],
    })
    assert ctp._open_claim_floors(tmp_path) == {}


# --- 2. controles positif et negatif de l'allocation ------------------------

def test_controle_positif_l_allocation_passe_au_dessus_de_la_revendication(
        tmp_path, monkeypatch):
    """Max local = 17, PR ouverte revendiquant `0018` -> l'index ecrit est 19.

    C'est le cas mesure : sans ce plancher, l'allocation retombe sur le max
    local + 1 = `0018`, l'ordinal **deja pris** par #25037.
    """
    registry = tmp_path / "twin_pairs.d"
    registry.mkdir()
    _publish_audits(registry, list(range(1, 18)))  # 1..17
    _stub_open_claims(monkeypatch, {
        "25037": [{"pair": PAIR_SLUG, "index": "0018",
                   "path": "x/0018-2026-11-01-a.yaml"}],
    })
    floor = ctp._open_claim_floors(tmp_path).get(PAIR_SLUG, 0)
    assert floor == 18, f"precondition : plancher attendu 18, obtenu {floor}"
    path = ctp._write_audit_file(registry, PAIR_NAME, _audit_dict(), floor=floor)
    assert path.name.startswith("0019-"), (
        f"index attendu 0019 (au-dessus de la revendication 0018), obtenu "
        f"{path.name} : l'allocation doit passer au-dessus de l'ordinal "
        f"revendique par la PR ouverte."
    )


def test_controle_negatif_sans_le_plancher_l_allocation_revendique_l_ordinal_pris(
        tmp_path, monkeypatch):
    """Le comportement historique que le correctif retire.

    Meme etat de depart (max local 17), mais SANS le plancher des PRs
    ouvertes : l'index ecrit est `0018` -- exactement l'ordinal que #25037
    revendique. C'est la collision que la porte d'index ne voit qu'apres le
    push ; le correctif la ferme a l'ecriture.
    """
    registry = tmp_path / "twin_pairs.d"
    registry.mkdir()
    _publish_audits(registry, list(range(1, 18)))  # 1..17
    floor = ctp._audit_floor(tmp_path, registry, PAIR_NAME, None)
    assert floor == 0, f"precondition : aucun plancher de ref attendu, obtenu {floor}"
    path = ctp._write_audit_file(registry, PAIR_NAME, _audit_dict(), floor=floor)
    assert path.name.startswith("0018-"), (
        f"index attendu 0018 (le comportement historique, en collision avec "
        f"la PR ouverte), obtenu {path.name} : si ce test echoue, le "
        f"controle positif perd sa valeur de contraste."
    )


# --- 3. degradation : un garde ne bloque jamais une ecriture ----------------

def test_une_lecture_impossible_rend_un_plancher_vide_et_un_avertissement(
        tmp_path, monkeypatch, capsys):
    """`gh` absent, reseau coupe, liste tronquee -> plancher vide + stderr.

    Le plancher est un **garde**, pas une mesure : il ne doit jamais lever,
    ni refuser une ecriture. L'ecart est dit, pour que l'absence de plancher
    ne passe pas pour une lecture complete.
    """
    def fake_collect(slug, *, cwd=None):
        raise ctp.OpenClaimsError("liste tronquee")

    monkeypatch.setattr(ctp, "repo_slug", lambda cwd=None: "jsboige/CoursIA")
    monkeypatch.setattr(ctp, "collect_open_claims", fake_collect)
    floors = ctp._open_claim_floors(tmp_path)
    assert floors == {}, f"plancher attendu vide sur lecture impossible, obtenu {floors}"
    err = capsys.readouterr().err
    assert "PRs ouvertes" in err, (
        f"un avertissement sur stderr est attendu (le garde n'a pas pu "
        f"lire), stderr observe : {err!r}"
    )


def test_une_erreur_inattendue_ne_leve_pas_non_plus(tmp_path, monkeypatch, capsys):
    """Meme un defaut inattendu degrade : jamais d'exception en cascade."""
    def fake_collect(slug, *, cwd=None):
        raise RuntimeError("boom")

    monkeypatch.setattr(ctp, "repo_slug", lambda cwd=None: "jsboige/CoursIA")
    monkeypatch.setattr(ctp, "collect_open_claims", fake_collect)
    assert ctp._open_claim_floors(tmp_path) == {}
    assert "PRs ouvertes" in capsys.readouterr().err


def test_un_depot_sans_remote_n_est_pas_une_lecture_ratee(tmp_path, monkeypatch, capsys):
    """Pas de remote GitHub -> plancher vide, et AUCUN avertissement.

    Le plancher n'est pas *applicable* dans une copie locale : ce n'est pas
    une lecture ratee, il n'y a rien a mesurer. Un avertissement ici
    polluerait la sortie d'un outil qui fonctionne -- c'est ce que
    verifiait la suite chirurgicale (`stderr` sans `AVERTISSEMENT`).
    """
    def fake_slug(cwd=None):
        raise ctp.OpenClaimsError("no git remotes found")

    def fake_collect(slug, *, cwd=None):  # pragma: no cover -- jamais appele
        raise AssertionError("l'organe ne doit pas etre appele sans remote")

    monkeypatch.setattr(ctp, "repo_slug", fake_slug)
    monkeypatch.setattr(ctp, "collect_open_claims", fake_collect)
    assert ctp._open_claim_floors(tmp_path) == {}
    assert "AVERTISSEMENT" not in capsys.readouterr().err


# --- 4. cablage CLI ---------------------------------------------------------

def test_cli_expose_le_flag_du_plancher_des_prs_ouvertes():
    """Le flag est atteignable depuis la ligne de commande.

    Test de cablage pauvre : il verifie que le desactivateur existe et est
    documente -- sans lui, le plancher ne serait pas desactivable quand une
    lecture des PRs ouvertes est pasausible (usage hors ligne).
    """
    r = subprocess.run(
        [sys.executable, str(SCRIPT), "--help"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    assert r.returncode == 0, f"--help a echoue : {r.stderr[-400:]}"
    assert "--no-open-claims-floor" in r.stdout, (
        "--no-open-claims-floor absent de --help : flag non cable"
    )
