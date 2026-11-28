#!/usr/bin/env python3
"""L'organe de mesure du volume de checkout mesure ce qu'il annonce (#26383).

Ce que ce fichier garde
-----------------------
`scripts/ci/measure_checkout_volume.py` remplace deux tableaux qui etaient
rediges a la main sur l'issue #26383 : le tableau hote par hote (taille du
miroir, fraicheur, branchement) et le tableau avant/apres des octets recus par
job. Un organe de mesure qui ne mesure rien est pire que pas d'organe : il
produit un tableau qui a l'air verifie. Ce test rejoue donc la mesure sur un
depot synthetique dont le contenu est connu, et verifie les invariants
numeriques -- pas seulement que le script ne leve pas.

Les invariants verifies
-----------------------
- les blobs de HEAD sont comptes exactement (octet pour octet) ;
- le poids "avant" (historique complet) est superieur ou egal au poids "apres"
  (historique sans blobs), et le "delta" annonce vaut la difference des deux ;
- le regime "chemins d'outillage" est plus leger que le regime "blobs de HEAD"
  (c'est tout l'interet du levier) ;
- un blob au-dessus du seuil est signale, un blob en dessous ne l'est pas ;
- le mode miroir signale un miroir non branche (`insteadOf` absent) et un
  miroir branche -- les deux etats que le tableau hote doit distinguer.
"""

import os
import subprocess
import sys

sys.path.insert(0, os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
    "scripts", "ci"))

from measure_checkout_volume import (  # noqa: E402
    BIG_BLOB_DEFAULT_MIB,
    measure_clone,
    measure_mirror,
)

BIG_BYTES = 6 * 1024 * 1024


def _run(repo, *args):
    subprocess.run(
        ["git", "-c", "safe.directory=*", "-C", str(repo), *args],
        check=True,
        capture_output=True,
    )


def _make_repo(path):
    path.mkdir(parents=True, exist_ok=True)
    _run(path, "init", "-q", "-b", "main")
    (path / "a.txt").write_text("a" * 100, encoding="utf-8")
    (path / "scripts").mkdir()
    (path / "scripts" / "x.py").write_text("x = 1\n", encoding="utf-8")
    # Contenu incompressible : des zeros se compresseraient en quelques
    # kilo-octets et l'octet disque mesure ne vaudrait plus l'octet transfere.
    (path / "big.bin").write_bytes(os.urandom(BIG_BYTES))
    _run(path, "add", "-A")
    _run(path, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-q", "-m", "init")
    return path


def test_measure_clone_sums_blobs_exactly(tmp_path):
    repo = _make_repo(tmp_path / "repo")
    report = measure_clone(repo, big_blob_mib=BIG_BLOB_DEFAULT_MIB)

    head = report["head_blobs"]
    assert head["files"] == 3
    assert head["bytes"] == 100 + len("x = 1\n") + BIG_BYTES

    by_dir = head["by_top_dir"]
    assert by_dir["(racine)"]["bytes"] == 100 + BIG_BYTES
    assert by_dir["scripts"]["bytes"] == len("x = 1\n")


def test_before_after_is_ordered_and_consistent(tmp_path):
    repo = _make_repo(tmp_path / "repo")
    ba = measure_clone(repo)["before_after"]

    assert ba["avant_octets_par_job"] >= ba["apres_blob_none_octets"] > 0
    assert ba["apres_blob_none_octets"] > ba["apres_outillage_octets"]
    assert ba["delta_blob_none_octets"] == ba["avant_octets_par_job"] - ba["apres_blob_none_octets"]
    assert ba["delta_outillage_octets"] == ba["avant_octets_par_job"] - ba["apres_outillage_octets"]
    # L'historique sans blobs ne peut pas peser plus que l'historique complet.
    assert ba["apres_outillage_octets"] < ba["avant_octets_par_job"]


def test_big_blob_detection_uses_the_threshold(tmp_path):
    repo = _make_repo(tmp_path / "repo")

    gros = measure_clone(repo, big_blob_mib=BIG_BLOB_DEFAULT_MIB)["big_blobs"]
    assert gros["count"] == 1
    assert gros["top"][0]["path"] == "big.bin"

    lenient = measure_clone(repo, big_blob_mib=100.0)["big_blobs"]
    assert lenient["count"] == 0


def test_mirror_mode_reports_wiring_state(tmp_path):
    repo = _make_repo(tmp_path / "repo")
    mirror = tmp_path / "mirror.git"
    subprocess.run(
        ["git", "clone", "--mirror", str(repo), str(mirror)],
        check=True,
        capture_output=True,
    )

    config_sans = tmp_path / "gitconfig.sans"
    config_sans.write_text("[http]\n\tlowSpeedLimit = 1024\n", encoding="utf-8")

    report = measure_mirror(mirror, config_sans)
    assert report["wired_instead_of"] is False
    assert report["wiring_evidence"] == []
    assert report["pack_bytes"] > 0
    assert report["refs"] >= 1
    assert report["alternates"] is None

    config_avec = tmp_path / "gitconfig.avec"
    config_avec.write_text(
        '[url "/home/u/mirror.git"]\n\tinsteadOf = https://github.com/jsboige/CoursIA.git\n',
        encoding="utf-8",
    )
    branche = measure_mirror(mirror, config_avec)
    assert branche["wired_instead_of"] is True
    assert any("insteadOf" in item for item in branche["wiring_evidence"])
