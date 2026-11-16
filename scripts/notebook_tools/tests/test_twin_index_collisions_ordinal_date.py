"""Tests de l'inversion ordinal/date de TOUT-HAUT (#26795).

L'audit de parite (`check_twin_parity.py`) charge les attestations d'une
paire par ORDINAL croissant et `_latest_audit` renvoie le DERNIER
enregistrement : le registre lu par l'audit est donc le dernier
enregistrement du fichier d'ordinal LE PLUS HAUT.

Si l'ordinal le plus haut n'est pas le plus RECENT, l'audit compare le
carnet a une attestation perimee et rend un DRIFT que rien ne justifie --
c'est ce qu'a produit #26381 (`0044` du 13/11 renumerote au-dessus de
`0043` du 15/11).

L'invariant garde par la porte est donc : **l'attestation la plus recente de
la paire doit porter l'ordinal le plus haut**.

L'invariant plus large (« tout ordinal suit l'ordre des dates ») est viole
410 fois dans 158 paires sur `origin/main` (mesure du 15/11/2026,
`origin/main` = 75a559fd8fe56) : c'est la dette historique du
registre, pas une porte possible. Ces deux mesures sont dans le corps de la
PR -- ici, on verifie l'invariant REEL et le refus qu'il produit.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_twin_index_collisions import (  # noqa: E402
    attestation_date,
    main as collisions_main,
    ordinal_date_inversion_reasons,
    ordinal_order_inversions,
    registry_of_ref,
    top_ordinal_inversions,
)

REPO = Path(__file__).resolve().parents[3]
REGISTRY = "scripts/notebook_tools/twin_pairs.d"

# Le cas mesure sur #26381.
ATT_15_NOV = "0043-2026-11-15-myia-ai-01-CoursIA-2.yaml"
ATT_13_NOV = "0044-2026-11-13-myia-ai-01-CoursIA-2.yaml"
PAIR = "gametheory-9-backwardinduction"


def _reg(spec: dict) -> dict:
    """{paire: [(index, nom), ...]} -> {paire: {index: [noms]}}."""
    out = {}
    for pair, entries in spec.items():
        d: dict = {}
        for idx, name in entries:
            d.setdefault(idx, []).append(name)
        out[pair] = {k: sorted(v) for k, v in d.items()}
    return out


# ---------------------------------------------------------------------------
# 1. la date se lit dans le NOM
# ---------------------------------------------------------------------------

def test_la_date_se_lit_dans_le_nom():
    assert attestation_date(ATT_15_NOV) == "2026-11-15"
    assert attestation_date(ATT_13_NOV) == "2026-11-13"


def test_un_nom_sans_date_illisible_ne_rend_rien():
    assert attestation_date("pas-une-attestation.yaml") is None
    assert attestation_date("0043.yaml") is None


# ---------------------------------------------------------------------------
# 2. l'invariant : l'ordinal le plus haut est le plus recent
# ---------------------------------------------------------------------------

def test_paire_saine_sans_inversion():
    reg = _reg({PAIR: [("0042", "0042-2026-11-10-x.yaml"),
                       ("0043", ATT_15_NOV)]})
    assert top_ordinal_inversions(reg) == []


def test_inversion_de_tout_haut_detectee():
    """Le cas #26381 : le haut (0044, 13/11) est plus ancien que 0043
    (15/11). L'audit lit 0044 -> il compare a une attestation perimee."""
    reg = _reg({PAIR: [("0043", ATT_15_NOV), ("0044", ATT_13_NOV)]})
    inv = top_ordinal_inversions(reg)
    assert len(inv) == 1
    v = inv[0]
    assert v["pair"] == PAIR
    assert v["index"] == "0044"
    assert v["top_date"] == "2026-11-13"
    assert v["recent_date"] == "2026-11-15"
    assert v["recent_names"] == [ATT_15_NOV]


def test_une_inversion_interieure_ne_signale_rien():
    """Une inversion qui n'est PAS au sommet n'affecte pas l'audit : il lit
    le sommet, et le sommet est le plus recent. C'est la raison pour
    laquelle l'invariant porte sur le TOUT-HAUT et pas sur tout l'ordre."""
    reg = _reg({PAIR: [("0014", "0014-2026-10-22-x.yaml"),
                       ("0015", "0015-2026-10-14-y.yaml"),
                       ("0043", ATT_15_NOV)]})
    assert top_ordinal_inversions(reg) == []


def test_plusieurs_noms_au_meme_index_ordinal():
    """Deux lanes au meme index : la date retenue est la plus recente des
    deux noms -- si l'une des deux est la plus recente de la paire, la
    paire n'est PAS en infraction."""
    reg = _reg({PAIR: [("0044", "0044-2026-11-13-a.yaml"),
                       ("0044", "0044-2026-11-15-b.yaml")]})
    assert top_ordinal_inversions(reg) == []


def test_une_paire_sans_date_lisible_nest_jamais_signalee():
    reg = _reg({PAIR: [("0001", "0001.yaml"), ("0002", "0002.yaml")]})
    assert top_ordinal_inversions(reg) == []


# ---------------------------------------------------------------------------
# 3. le refus porte sur ce que la PR INTRODUIT
# ---------------------------------------------------------------------------

def test_une_inversion_introduite_est_refusee():
    base = _reg({PAIR: [("0043", ATT_15_NOV)]})
    head = _reg({PAIR: [("0043", ATT_15_NOV), ("0044", ATT_13_NOV)]})
    raisons = ordinal_date_inversion_reasons(base, head)
    assert len(raisons) == 1
    r = raisons[0]
    assert r["kind"] == "ordinal_date_inversion"
    assert r["pair"] == PAIR
    assert r["index"] == "0044"
    assert "check_twin_parity.py --update" in r["gist"]
    # Le geste nomme doit dire COMMENT : un garde qui dit « collision »
    # laisse le porteur deviner.
    assert "git mv" in r["gist"]


def test_une_inversion_heritee_de_la_base_ne_bloque_pas():
    """Meme contrat que les doublons d'index (#23208) : la PR qui REPAIRE
    l'inversion doit passer."""
    base = _reg({PAIR: [("0043", ATT_15_NOV), ("0044", ATT_13_NOV)]})
    head = _reg({PAIR: [("0043", ATT_15_NOV), ("0044", ATT_13_NOV),
                        ("0045", "0045-2026-11-16-x.yaml")]})
    assert ordinal_date_inversion_reasons(base, head) == []


def test_une_base_propre_et_une_tete_propre_ne_produisent_rien():
    base = _reg({PAIR: [("0043", ATT_15_NOV)]})
    head = _reg({PAIR: [("0043", ATT_15_NOV)]})
    assert ordinal_date_inversion_reasons(base, head) == []


# ---------------------------------------------------------------------------
# 3 bis. l'inventaire LARGE est reproduisible, mais jamais bloquant
# ---------------------------------------------------------------------------

def test_l_inventaire_large_rend_les_inversions_interieures():
    """L'inventaire large est ce qui rend la dette historique
    REPRODUCTIBLE avec l'organe (l'issue #26795 demande le recensement
    « avec l'organe lui-meme »). Il ne bloque jamais."""
    reg = _reg({PAIR: [("0014", "0014-2026-10-22-x.yaml"),
                       ("0015", "0015-2026-10-14-y.yaml"),
                       ("0043", ATT_15_NOV)]})
    inv = ordinal_order_inversions(reg)
    assert len(inv) == 1
    assert inv[0]["pair"] == PAIR
    assert inv[0]["index"] == "0015"
    # La paire reste SAINE pour l'invariant que la porte garde.
    assert top_ordinal_inversions(reg) == []


def test_une_paire_avec_une_inversion_interieure_passe_la_porte(tmp_path, capsys):
    """Une inversion qui n'est pas au sommet ne bloque pas : l'audit lit le
    sommet, et le sommet porte l'attestation la plus recente.

    La construction : `0002` du 10/11 et `0003` du 05/11 s'inversent entre
    eux (inversion INTERIEURE, invisible du sommet), tandis que `0043` du
    15/11 reste le sommet ET le plus recent. La porte passe, l'inventaire
    large signale l'inversion interieure.
    """
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q", "-b", "main")
    _git(repo, "config", "user.name", "T")
    _git(repo, "config", "user.email", "t@example.invalid")
    _write_attestation(repo, PAIR, ATT_15_NOV)
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "base")
    base = _git(repo, "rev-parse", "HEAD")
    _write_attestation(repo, PAIR, "0002-2026-11-10-x.yaml")
    _write_attestation(repo, PAIR, "0003-2026-11-05-y.yaml")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "interieur")

    rc = collisions_main(["--base", base, "--head", "HEAD", "--gate",
                          "--repo", str(repo)])
    assert rc == 0, capsys.readouterr().out
    # La base est saine : aucun sommet perime.
    collisions_main(["--base", base, "--census", "--repo", str(repo)])
    assert "RECENSEMENT: 0" in capsys.readouterr().out
    # L'inventaire large, lui, voit l'inversion INTERIEURE -- et il
    # l'annonce comme informatif, jamais bloquant.
    collisions_main(["--base", "HEAD", "--census", "--repo", str(repo)])
    sortie = capsys.readouterr().out
    assert "RECENSEMENT: 0" in sortie
    assert "INVENTAIRE LARGE" in sortie and ": 1 inversion(s)" in sortie


# ---------------------------------------------------------------------------
# 4. bout en bout, sur un depot git jetable
# ---------------------------------------------------------------------------

def _git(cwd, *args: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(cwd), *args],
        capture_output=True, text=True,
        encoding="utf-8", errors="replace", timeout=120,
    )
    if proc.returncode != 0:
        raise AssertionError(f"git {' '.join(args)}: {proc.stderr}")
    return proc.stdout.strip()


def _write_attestation(repo: Path, pair: str, name: str) -> None:
    d = repo / REGISTRY / pair
    d.mkdir(parents=True, exist_ok=True)
    (d / name).write_text(
        "attested_at: %s\naudits:\n  - date: '%s'\n    by: test\n"
        "    python_sha: '0' * 40\n" % (name.split("-")[1], name.split("-")[1]),
        encoding="utf-8")


@pytest.fixture()
def _depot_avec_inversion(tmp_path):
    """Base : 0043 du 15/11. Tete : + 0044 du 13/11 (l'inversion mesuree)."""
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q", "-b", "main")
    _git(repo, "config", "user.name", "T")
    _git(repo, "config", "user.email", "t@example.invalid")
    _write_attestation(repo, PAIR, ATT_15_NOV)
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "base")
    base = _git(repo, "rev-parse", "HEAD")
    _write_attestation(repo, PAIR, ATT_13_NOV)
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "inversion")
    head = _git(repo, "rev-parse", "HEAD")
    return repo, base, head


def test_le_controle_positif_est_refuse(_depot_avec_inversion, capsys):
    repo, base, head = _depot_avec_inversion
    rc = collisions_main(["--base", base, "--head", head, "--gate",
                          "--repo", str(repo)])
    assert rc == 1
    sortie = capsys.readouterr().out
    assert "ordinal_date_inversion" in sortie
    assert PAIR in sortie


def test_le_controle_negatif_passe(_depot_avec_inversion, capsys):
    """La base seule, contre elle-meme (deux NOMS distincts pour le meme
    arbre) : rien n'est introduit, la porte est verte."""
    repo, base, _head = _depot_avec_inversion
    _git(repo, "branch", "base-copy", base)
    rc = collisions_main(["--base", base, "--head", "base-copy", "--gate",
                          "--repo", str(repo)])
    assert rc == 0
    assert "PORTE VERTE" in capsys.readouterr().out


def test_le_census_de_la_base_est_vide(_depot_avec_inversion, capsys):
    repo, base, _head = _depot_avec_inversion
    rc = collisions_main(["--base", base, "--census", "--repo", str(repo)])
    assert rc == 0
    sortie = capsys.readouterr().out
    assert "RECENSEMENT: 0" in sortie


def test_le_census_voit_la_tete(_depot_avec_inversion, capsys):
    repo, _base, head = _depot_avec_inversion
    collisions_main(["--base", head, "--census", "--repo", str(repo)])
    sortie = capsys.readouterr().out
    assert "RECENSEMENT: 1" in sortie
    assert PAIR in sortie


# ---------------------------------------------------------------------------
# 5. le cas reel (#26381), quand le commit est disponible
# ---------------------------------------------------------------------------

def _commit_present(sha: str) -> bool:
    proc = subprocess.run(
        ["git", "-C", str(REPO), "cat-file", "-t", sha],
        capture_output=True, text=True, encoding="utf-8", errors="replace")
    return proc.returncode == 0


@pytest.mark.skipif(not _commit_present("31efc36272d"),
                    reason="la tete 31efc36272d de #26381 n'est pas dans ce clone")
def test_la_tete_reelle_de_26381_est_refusee(capsys):
    rc = collisions_main(["--base", "origin/main", "--head", "31efc36272d",
                          "--gate", "--repo", str(REPO)])
    assert rc == 1
    sortie = capsys.readouterr().out
    assert PAIR in sortie
    assert "2026-11-13" in sortie and "2026-11-15" in sortie


@pytest.mark.skipif(not _commit_present("31efc36272d"),
                    reason="la tete 31efc36272d de #26381 n'est pas dans ce clone")
def test_main_ne_porte_aucune_inversion_de_tout_haut(capsys):
    """Le controle negatif de l'issue : `origin/main` passe."""
    rc = collisions_main(["--base", "origin/main", "--census",
                          "--repo", str(REPO)])
    assert rc == 0
    assert "RECENSEMENT: 0" in capsys.readouterr().out


def test_registry_of_ref_et_la_meme_forme_pour_les_attestations():
    """Le registre lu par l'organe et celui lu par l'audit portent les MEMES
    noms : c'est ce qui rend la comparaison pertinente."""
    reg = registry_of_ref("origin/main", REPO, REGISTRY)
    assert PAIR in reg
    noms = [n for idx, ns in reg[PAIR].items() for n in ns]
    assert all(attestation_date(n) for n in noms)
