#!/usr/bin/env python3
"""Tests de l'echantillonneur du test externe humain (#20222).

Toute la mecanique est testee sans reseau et sans corpus reel : un corpus
synthetique suffit, l'instrument etant corpus-agnostique par conception.
"""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import sample_external_eval as sampler  # noqa: E402


def make_corpus(tmp_path: Path, families: dict[str, int], name: str = "aligned.jsonl") -> Path:
    """Corpus synthetique : n paires par famille, noeuds de premier et second niveau."""
    path = tmp_path / name
    lines = []
    for family, count in families.items():
        for i in range(count):
            lines.append({
                "text": f"Texte {family} numero {i} : argument assez long pour porter un sophisme.",
                "node": f"{family}/ noeud-{i}",
            })
    path.write_text("\n".join(json.dumps(line, ensure_ascii=False) for line in lines) + "\n", encoding="utf-8")
    return path


def run_sampler(tmp_path: Path, corpus: Path, *extra: str, out: str = "run") -> dict:
    out_dir = tmp_path / out
    rc = sampler.main([
        "--input", str(corpus), "--out-dir", str(out_dir),
        "--n", "30", "--min-per-family", "10", "--seed", "42",
        *extra,
    ])
    assert rc == 0
    return {
        "sheet": [json.loads(l) for l in (out_dir / "sheet.jsonl").read_text(encoding="utf-8").splitlines()],
        "key": [json.loads(l) for l in (out_dir / "key.jsonl").read_text(encoding="utf-8").splitlines()],
        "manifest": json.loads((out_dir / "manifest.json").read_text(encoding="utf-8")),
        "out_dir": out_dir,
    }


def test_plancher_par_famille_tenu(tmp_path):
    """Critere 1 de #20222 : chaque famille de premier niveau >= 10 paires."""
    corpus = make_corpus(tmp_path, {"attaque": 60, "appel": 40, "flou": 30})
    result = run_sampler(tmp_path, corpus)
    counts = result["manifest"]["per_family_counts"]
    assert set(counts) == {"attaque", "appel", "flou"}
    assert all(v >= 10 for v in counts.values())
    assert sum(counts.values()) == 30
    # Le reliquat (30 - 3x10) va aux plus grandes familles (plus grand reste).
    assert counts["attaque"] >= counts["flou"]


def test_reproductible_meme_graine(tmp_path):
    """Meme graine = meme echantillon, mesure par SHA de la feuille et par identifiants."""
    corpus = make_corpus(tmp_path, {"attaque": 50, "appel": 50, "flou": 50})
    first = run_sampler(tmp_path, corpus, out="run_a")
    second = run_sampler(tmp_path, corpus, out="run_b")
    assert first["sheet"] == second["sheet"]
    assert first["manifest"]["sheet_sha256"] == second["manifest"]["sheet_sha256"]


def test_graine_differente_tirage_different(tmp_path):
    corpus = make_corpus(tmp_path, {"attaque": 50, "appel": 50, "flou": 50})
    base = run_sampler(tmp_path, corpus, "--seed", "42", out="seed42")
    other = run_sampler(tmp_path, corpus, "--seed", "7", out="seed7")
    ids_base = [item["item_id"] for item in base["sheet"]]
    ids_other = [item["item_id"] for item in other["sheet"]]
    assert ids_base != ids_other


def test_feuille_aveugle_sans_etiquette(tmp_path):
    """Propriete 2 : la feuille d'annotation ne porte jamais le noeud cible."""
    corpus = make_corpus(tmp_path, {"attaque": 30, "appel": 30, "flou": 30})
    result = run_sampler(tmp_path, corpus)
    for item in result["sheet"]:
        assert "node" not in item
        assert set(item) == {"item_id", "text", "family"}
    # La cle, elle, porte le noeud -- et fait la meme longueur que la feuille.
    assert len(result["key"]) == len(result["sheet"])
    assert all("node" in item for item in result["key"])


def test_tirage_sature_par_les_planchers(tmp_path):
    """n egale la somme des planchers : aucune famille n'a de reliquat.

    Regression mesuree : la repartition proportionnelle divisait alors par un
    reliquat total nul, et le tirage levait un ZeroDivisionError.
    """
    corpus = make_corpus(tmp_path, {"attaque": 10, "appel": 10})
    result = run_sampler(tmp_path, corpus, "--n", "20")
    assert result["manifest"]["per_family_counts"] == {"attaque": 10, "appel": 10}
    assert len(result["sheet"]) == 20


def test_identifiant_opaque_ne_revele_pas_la_graine(tmp_path):
    """L'identifiant d'item ne porte ni la graine ni le rang du tirage.

    Un identifiant qui afficherait la graine la donnerait a lire a l'evaluateur
    sur la feuille : la graine suffit a rejouer le tirage sur un corpus public,
    donc a reconstruire la cle de correction.
    """
    corpus = make_corpus(tmp_path, {"attaque": 40, "appel": 40, "flou": 40})
    result = run_sampler(tmp_path, corpus, "--seed", "42")
    ids = [item["item_id"] for item in result["sheet"]]
    assert len(set(ids)) == len(ids)
    for item_id in ids:
        assert item_id.startswith("eval-")
        # Propriete STRUCTURELLE : un suffixe hexadecimal ne peut pas porter la
        # graine en clair. Un test qui chercherait les chiffres "42" dans
        # l'empreinte passerait ou echouerait au hasard -- il ne prouverait rien.
        suffix = item_id[len("eval-"):]
        assert len(suffix) == 12
        assert set(suffix) <= set("0123456789abcdef")


def test_identifiant_independent_de_la_graine(tmp_path):
    """Corpus mono-famille de la taille du tirage : les deux graines tirent les
    MEMES items, donc les identifiants doivent coincider. Un identifiant derive
    de la graine les ferait diverger."""
    corpus = make_corpus(tmp_path, {"attaque": 10})
    ids = {}
    for seed in ("42", "7"):
        out_dir = tmp_path / f"seed{seed}"
        rc = sampler.main([
            "--input", str(corpus), "--out-dir", str(out_dir),
            "--n", "10", "--min-per-family", "10", "--seed", seed,
        ])
        assert rc == 0
        ids[seed] = {json.loads(line)["item_id"] for line in (out_dir / "sheet.jsonl").read_text(encoding="utf-8").splitlines()}
    assert len(ids["42"]) == 10
    assert ids["42"] == ids["7"]


def test_identifiant_adresse_par_le_contenu(tmp_path):
    """L'identifiant se recalcule depuis (noeud, texte) -- sans graine ni rang."""
    corpus = make_corpus(tmp_path, {"attaque": 20, "appel": 20})
    result = run_sampler(tmp_path, corpus)
    texts = {item["item_id"]: item["text"] for item in result["sheet"]}
    for entry in result["key"]:
        item_id = entry["item_id"]
        recomputed = "eval-" + hashlib.sha256(
            f"{entry['node']}\x00{texts[item_id]}".encode()
        ).hexdigest()[:12]
        assert item_id == recomputed


def test_refuse_famille_deficiente_en_nommant(tmp_path):
    """Propriete 1 : fail-closed, la famille deficiente est nommee dans l'erreur."""
    corpus = make_corpus(tmp_path, {"attaque": 50, "appel": 50, "flou": 4})
    with pytest.raises(SystemExit) as excinfo:
        run_sampler(tmp_path, corpus)
    assert "flou=4" in str(excinfo.value)


def test_refuse_n_intenable_en_citant_le_max(tmp_path):
    corpus = make_corpus(tmp_path, {"attaque": 15, "appel": 15})
    out_dir = tmp_path / "intenable"
    with pytest.raises(SystemExit) as excinfo:
        sampler.main(["--input", str(corpus), "--out-dir", str(out_dir),
                      "--n", "40", "--min-per-family", "10", "--seed", "42"])
    assert "maximum atteignable = 30" in str(excinfo.value)
    assert not out_dir.exists()  # rien n'est ecrit quand le tirage echoue


def test_manifeste_epingle_source_et_feuille(tmp_path):
    """Propriete 3 : le manifeste porte les SHA-256 de la source, de la feuille et de la cle."""
    corpus = make_corpus(tmp_path, {"attaque": 30, "appel": 30, "flou": 30})
    result = run_sampler(tmp_path, corpus)
    manifest = result["manifest"]
    assert manifest["source"]["sha256"] == sampler.sha256_of(corpus)
    assert manifest["sheet_sha256"] == sampler.sha256_of(result["out_dir"] / "sheet.jsonl")
    assert manifest["key_sha256"] == sampler.sha256_of(result["out_dir"] / "key.jsonl")


def test_ligne_invalide_fail_closed(tmp_path):
    """Une ligne sans champ 'node' fait echouer le chargement, pas un skip silencieux."""
    path = tmp_path / "broken.jsonl"
    path.write_text(json.dumps({"text": "texte sans noeud"}) + "\n", encoding="utf-8")
    with pytest.raises(SystemExit) as excinfo:
        sampler.load_corpus(path, "/")
    assert "node" in str(excinfo.value)
