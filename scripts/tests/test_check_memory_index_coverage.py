"""Tests for scripts/coordination/check_memory_index_coverage.py (#17885).

Trois cas : OK, FAIL (orphelin), FAIL (lien cassé).
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "coordination" / "check_memory_index_coverage.py"


def _run(tmp_path: Path, mem_text: str) -> dict:
    """Build a minimal memory/ directory and invoke the script."""
    (tmp_path / "MEMORY.md").write_text(mem_text, encoding="utf-8")
    (tmp_path / "alpha.md").write_text("# alpha", encoding="utf-8")
    (tmp_path / "beta.md").write_text("# beta", encoding="utf-8")
    (tmp_path / "gamma.md").write_text("# gamma", encoding="utf-8")
    out = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--memory-dir",
            str(tmp_path),
            "--json",
        ],
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    assert out.returncode in (0, 1), f"unexpected rc={out.returncode}: stderr={out.stderr}"
    return json.loads(out.stdout)


def test_full_coverage_ok(tmp_path: Path) -> None:
    """All files referenced => verdict OK, rc=0."""
    mem = (
        "# Memoire\n\n"
        "- [alpha](alpha.md)\n"
        "- [beta](beta.md)\n"
        "- [gamma](gamma.md)\n"
    )
    report = _run(tmp_path, mem)
    assert report["verdict"] == "OK"
    assert report["orphan_count"] == 0
    assert report["broken_link_count"] == 0
    assert report["total_files"] == 3
    assert report["referenced_files"] == 3


def test_orphan_detected(tmp_path: Path) -> None:
    """gamma.md non referenced => orphan, verdict FAIL."""
    mem = (
        "# Memoire\n\n"
        "- [alpha](alpha.md)\n"
        "- [beta](beta.md)\n"
    )
    report = _run(tmp_path, mem)
    assert report["verdict"] == "FAIL"
    assert report["orphan_count"] == 1
    assert "gamma.md" in report["orphan_files"]
    assert report["referenced_files"] == 2


def test_broken_link_detected(tmp_path: Path) -> None:
    """Lien vers missing.md qui n'existe pas => broken_link, verdict FAIL."""
    mem = (
        "# Memoire\n\n"
        "- [alpha](alpha.md)\n"
        "- [beta](beta.md)\n"
        "- [gamma](gamma.md)\n"
        "- [missing](missing.md)\n"
    )
    report = _run(tmp_path, mem)
    assert report["verdict"] == "FAIL"
    assert report["broken_link_count"] == 1
    assert any(u == "missing.md" for _, u in report["broken_links"])


def test_real_memory_dir() -> None:
    """Vérifie que l'organe fonctionne contre le MEMORY.md de la machine."""
    import os

    real_dir = Path(
        r"C:\Users\Jesse\.claude\projects\d--dev-CoursIA-2\memory"
    )
    if not real_dir.exists():
        return  # CI sans le bon chemin
    out = subprocess.run(
        [sys.executable, str(SCRIPT), "--memory-dir", str(real_dir), "--json"],
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    report = json.loads(out.stdout)
    # MEMORY.md reel : on accepte OK ou FAIL (c.874 travaille a couverture 100%)
    assert report["verdict"] in ("OK", "FAIL")
    assert report["total_files"] > 100  # au moins 100 fichiers de Tells


NL = chr(10)  # newline literal, heredoc-proof


def _run_args(tmp_path: Path, mem_text: str, extra_args: list) -> dict:
    """Comme _run mais avec des args CLI supplementaires."""
    (tmp_path / "MEMORY.md").write_text(mem_text, encoding="utf-8")
    (tmp_path / "alpha.md").write_text("# alpha", encoding="utf-8")
    (tmp_path / "beta.md").write_text("# beta", encoding="utf-8")
    (tmp_path / "gamma.md").write_text("# gamma", encoding="utf-8")
    out = subprocess.run(
        [sys.executable, str(SCRIPT), "--memory-dir", str(tmp_path), "--json", *extra_args],
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    assert out.returncode in (0, 1), f"unexpected rc={out.returncode}: stderr={out.stderr}"
    return json.loads(out.stdout)


def test_default_ceiling_oversize(tmp_path: Path) -> None:
    """MEMORY.md > 24 400 o au defaut #4204 => FAIL_OVERSIZE, rc=1."""
    line = "- [alpha](alpha.md)" + NL
    filler = "# Memoire" + NL + NL + (line * 1300)
    (tmp_path / "MEMORY.md").write_text(filler, encoding="utf-8")
    (tmp_path / "alpha.md").write_text("# alpha", encoding="utf-8")
    out = subprocess.run(
        [sys.executable, str(SCRIPT), "--memory-dir", str(tmp_path), "--json"],
        capture_output=True, text=True, encoding="utf-8",
    )
    report = json.loads(out.stdout)
    assert report["verdict"] == "FAIL_OVERSIZE"
    assert report["max_bytes"] == 24400
    assert out.returncode == 1


def test_alert_band_warns_without_failing(tmp_path: Path) -> None:
    """21 960 < taille <= 24 400 => size_alert vrai, verdict reste OK."""
    head = (
        "# Memoire" + NL + NL
        + "- [alpha](alpha.md)" + NL
        + "- [beta](beta.md)" + NL
        + "- [gamma](gamma.md)" + NL + NL
    )
    pad = "x" * (22500 - len(head))
    report = _run_args(tmp_path, head + pad, [])
    assert report["size_bytes"] > 21960
    assert report["size_bytes"] <= 24400
    assert report["size_alert"] is True
    assert report["verdict"] == "OK"


def test_no_max_bytes_binary_only(tmp_path: Path) -> None:
    """--no-max-bytes : pas de plafond, verdict binaire seul (pre-#4204)."""
    head = (
        "# Memoire" + NL + NL
        + "- [alpha](alpha.md)" + NL
        + "- [beta](beta.md)" + NL
        + "- [gamma](gamma.md)" + NL + NL
    )
    pad = "x" * (25000 - len(head))  # > 24 400 o
    report = _run_args(tmp_path, head + pad, ["--no-max-bytes"])
    assert report["max_bytes"] is None
    assert report["alert_bytes"] is None
    assert report["size_alert"] is False
    assert report["verdict"] == "OK"


# --- Couverture par grappes (#17885 Q10 : « complétude et consolidation en
#     grappes ») — l'index compacté pointe une grappe, la grappe liste les
#     fiches. Une fiche listée dans une grappe joignable n'est pas orpheline.


def _run_custom(tmp_path: Path, mem_text: str, extra_args: list | None = None) -> dict:
    """Comme _run mais SANS créer alpha/beta/gamma : le dossier est celui du test."""
    (tmp_path / "MEMORY.md").write_text(mem_text, encoding="utf-8")
    out = subprocess.run(
        [sys.executable, str(SCRIPT), "--memory-dir", str(tmp_path), "--json", *(extra_args or [])],
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    assert out.returncode in (0, 1), f"unexpected rc={out.returncode}: stderr={out.stderr}"
    return json.loads(out.stdout)


def test_wikilink_couvre_la_fiche(tmp_path: Path) -> None:
    """[[alpha]] est un lien : alpha.md est couvert, pas orphelin."""
    (tmp_path / "alpha.md").write_text("# alpha", encoding="utf-8")
    report = _run_custom(tmp_path, "# Memoire" + NL + NL + "- [[alpha]] c.1" + NL)
    assert report["verdict"] == "OK"
    assert report["orphan_count"] == 0
    assert report["direct_referenced_files"] == 1
    assert report["referenced_files"] == 1


def test_wikilink_mort_est_un_lien_casse(tmp_path: Path) -> None:
    """[[delta]] sans delta.md => lien mort, verdict FAIL."""
    report = _run_custom(tmp_path, "# Memoire" + NL + NL + "- [[delta]] c.1" + NL)
    assert report["verdict"] == "FAIL"
    assert report["broken_link_count"] == 1
    assert "liens_morts_index" in report["fail_reasons"]


def test_fiche_listee_dans_une_grappe_joignable_est_couverte(tmp_path: Path) -> None:
    """MEMORY.md pointe la grappe, la grappe liste gamma => gamma couvert."""
    (tmp_path / "annexes").mkdir()
    (tmp_path / "annexes" / "digest.md").write_text(
        "# digest" + NL + NL + "- [[gamma]] c.3" + NL, encoding="utf-8"
    )
    (tmp_path / "alpha.md").write_text("# alpha", encoding="utf-8")
    (tmp_path / "gamma.md").write_text("# gamma", encoding="utf-8")
    report = _run_custom(
        tmp_path,
        "# Memoire" + NL + NL
        + "- [alpha](alpha.md)" + NL
        + "- [grappe](annexes/digest.md)" + NL,
    )
    assert report["verdict"] == "OK"
    assert report["orphan_count"] == 0
    assert report["direct_referenced_files"] == 1
    assert report["via_cluster_referenced_files"] == 1
    assert report["cluster_files_present"] == 1
    assert report["cluster_files_reachable"] == 1


def test_grappe_non_joignable_laisse_la_fiche_orpheline(tmp_path: Path) -> None:
    """Une grappe que l'index ne pointe pas ne couvre rien : gamma orphelin."""
    (tmp_path / "annexes").mkdir()
    (tmp_path / "annexes" / "digest.md").write_text(
        "# digest" + NL + NL + "- [[gamma]] c.3" + NL, encoding="utf-8"
    )
    (tmp_path / "alpha.md").write_text("# alpha", encoding="utf-8")
    (tmp_path / "gamma.md").write_text("# gamma", encoding="utf-8")
    report = _run_custom(tmp_path, "# Memoire" + NL + NL + "- [alpha](alpha.md)" + NL)
    assert report["verdict"] == "FAIL"
    assert report["orphan_count"] == 1
    assert report["orphan_files"] == ["gamma.md"]
    assert report["cluster_files_reachable"] == 0
    assert report["cluster_files_unreachable"] == ["digest.md"]


def test_un_seul_saut_de_grappe(tmp_path: Path) -> None:
    """depth 1 : une grappe qui pointe une autre grappe ne couvre pas ses fiches."""
    (tmp_path / "annexes").mkdir()
    (tmp_path / "annexes" / "digest.md").write_text(
        "# digest" + NL + NL + "- [suite](sous.md)" + NL, encoding="utf-8"
    )
    (tmp_path / "annexes" / "sous.md").write_text(
        "# sous" + NL + NL + "- [[gamma]] c.3" + NL, encoding="utf-8"
    )
    (tmp_path / "gamma.md").write_text("# gamma", encoding="utf-8")
    report = _run_custom(tmp_path, "# Memoire" + NL + NL + "- [grappe](annexes/digest.md)" + NL)
    assert report["orphan_count"] == 1  # gamma : deux sauts, hors profondeur 1
    assert report["verdict"] == "FAIL"


def test_profondeur_deux_sauts_couvre_la_fiche(tmp_path: Path) -> None:
    """--cluster-depth 2 : le second saut est resolu."""
    (tmp_path / "annexes").mkdir()
    (tmp_path / "annexes" / "digest.md").write_text(
        "# digest" + NL + NL + "- [suite](sous.md)" + NL, encoding="utf-8"
    )
    (tmp_path / "annexes" / "sous.md").write_text(
        "# sous" + NL + NL + "- [[gamma]] c.3" + NL, encoding="utf-8"
    )
    (tmp_path / "gamma.md").write_text("# gamma", encoding="utf-8")
    report = _run_custom(
        tmp_path,
        "# Memoire" + NL + NL + "- [grappe](annexes/digest.md)" + NL,
        ["--cluster-depth", "2"],
    )
    assert report["orphan_count"] == 0
    assert report["verdict"] == "OK"


def test_lien_mort_dans_une_grappe_bloque_avec_sa_raison(tmp_path: Path) -> None:
    """Un lien mort dans une grappe est un lien mort : raison distincte."""
    (tmp_path / "annexes").mkdir()
    (tmp_path / "annexes" / "digest.md").write_text(
        "# digest" + NL + NL + "- [[delta]] c.3" + NL, encoding="utf-8"
    )
    report = _run_custom(tmp_path, "# Memoire" + NL + NL + "- [grappe](annexes/digest.md)" + NL)
    assert report["verdict"] == "FAIL"
    assert report["broken_link_count"] == 0  # l'index, lui, n'a pas de lien mort
    assert report["cluster_broken_link_count"] == 1
    assert "liens_morts_grappes" in report["fail_reasons"]


def test_un_chemin_en_backticks_inconnu_est_ignore(tmp_path: Path) -> None:
    """`docs/reference/x.md` (fichier du dépôt, hors memory/) n'est pas un lien mort."""
    (tmp_path / "alpha.md").write_text("# alpha", encoding="utf-8")
    report = _run_custom(
        tmp_path,
        "# Memoire" + NL + NL + "- [alpha](alpha.md)" + NL + "- voir `docs/reference/x.md`" + NL,
    )
    assert report["broken_link_count"] == 0
    assert report["cluster_broken_link_count"] == 0
    assert report["verdict"] == "OK"


def test_strict_direct_refuse_la_couverture_par_grappe(tmp_path: Path) -> None:
    """--strict-direct : une fiche listee dans une grappe n'est PAS couverte.

    Le critere d'origine est preserve dans un mode explicite : la PR ne
    relache rien, elle mesure les deux formes.
    """
    (tmp_path / "annexes").mkdir()
    (tmp_path / "annexes" / "digest.md").write_text(
        "# digest" + NL + NL + "- [[gamma]] c.3" + NL, encoding="utf-8"
    )
    (tmp_path / "gamma.md").write_text("# gamma", encoding="utf-8")
    report = _run_custom(
        tmp_path,
        "# Memoire" + NL + NL + "- [grappe](annexes/digest.md)" + NL,
        ["--strict-direct"],
    )
    assert report["strict_direct"] is True
    assert report["orphan_count"] == 1
    assert report["referenced_files"] == 0
    assert report["cluster_referenced_files"] == 1  # la grappe couvre, mais pas en strict
    assert report["verdict"] == "FAIL"


def test_strict_direct_et_les_evenus_listent_le_meme_etat(tmp_path: Path) -> None:
    """Un index plat (une ligne par fiche) est OK dans les deux modes."""
    (tmp_path / "alpha.md").write_text("# alpha", encoding="utf-8")
    (tmp_path / "beta.md").write_text("# beta", encoding="utf-8")
    mem = "# Memoire" + NL + NL + "- [[alpha]] c.1" + NL + "- [[beta]] c.2" + NL
    lenient = _run_custom(tmp_path, mem)
    strict = _run_custom(tmp_path, mem, ["--strict-direct"])
    assert lenient["verdict"] == "OK" and strict["verdict"] == "OK"
    assert lenient["referenced_files"] == strict["referenced_files"] == 2
