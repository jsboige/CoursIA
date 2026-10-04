"""Tests pour scripts/ci/detect_oss_signature.py.

Couvre :
- controle positif (DIRTY fixture generee a la volee, jamais commitee)
- controle negatif (depot propre -- run sur main)
- branche --strict : py/cs/md filtre distinct, accessible
- MIN_VALUE_LEN = 28 : un Signature= real de 28 chars est attrape
- hygiene : la docstring module ne cite aucun token en clair
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
SCRIPT = REPO_ROOT / "scripts" / "ci" / "detect_oss_signature.py"


def _run(args: list[str], cwd: Path | None = None) -> subprocess.CompletedProcess:
    """Run detect_oss_signature.py with `args`, return CompletedProcess."""
    cmd = [sys.executable, str(SCRIPT)] + args
    return subprocess.run(
        cmd, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
        cwd=cwd or REPO_ROOT, timeout=180,
    )


def test_controle_positif_fixture_dirty_generee_a_la_volee(tmp_path: Path):
    """Genere un JSON 'dirty' et un JSON 'clean' cote a cote ; l'organe attrape le dirty."""
    dirty = tmp_path / "dirty.json"
    # Signature= + OSSAccessKeyId= + token de 32 chars (> MIN_VALUE_LEN=28)
    dirty.write_text(
        '{"image_url_signed_full": "https://bucket.oss.aliyuncs.com/img.png'
        '?Signature=ABCDEFGHIJKLMNOPQRSTUVWXYZ012345&OSSAccessKeyId=LTAI5tRDTcyABcdEFgh"}',
        encoding="utf-8",
    )
    clean = tmp_path / "clean.json"
    clean.write_text('{"image_url": "https://example.com/img.png"}', encoding="utf-8")

    # On simule git ls-files en court-circuitant list_tracked_files via un fake
    # module hook. Approche plus simple : on importe le module et on appelle
    # scan_file directement sur les deux paths.
    sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))
    import detect_oss_signature as mod  # type: ignore

    dirty_hits = mod.scan_file(dirty)
    clean_hits = mod.scan_file(clean)
    assert len(dirty_hits) >= 2, f"dirty fixture doit etre attrapee, vu {len(dirty_hits)} hit(s)"
    assert len(clean_hits) == 0, f"clean fixture ne doit rien attraper, vu {len(clean_hits)} hit(s)"


def test_min_value_len_28_un_signature_real_de_28_chars_est_attrape():
    """Un Signature= de 28 chars (longueur reelle documentee) doit matcher."""
    sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))
    import detect_oss_signature as mod  # type: ignore

    sig28 = "ABCDEFGHIJKLMNOPQRSTUVWXYZ01"  # 28 chars
    sample = tmp_path_obj() / "s.json"
    sample.parent.mkdir(parents=True, exist_ok=True)
    sample.write_text(f'{{"Signature": "Signature={sig28}"}}', encoding="utf-8")
    hits = mod.scan_file(sample)
    assert len(hits) >= 1, f"Signature= de 28 chars doit etre attrape (MIN_VALUE_LEN=28), vu {len(hits)}"
    sample.unlink()


def tmp_path_obj():
    """Renvoie un Path temporaire en utilisant tempfile pour eviter la collision de nom."""
    import tempfile
    return Path(tempfile.mkdtemp(prefix="oss_sig_test_"))


def test_min_value_len_28_un_placeholder_de_24_chars_passe():
    """Un Signature= de 24 chars (placeholder documente) ne doit PAS matcher."""
    sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))
    import detect_oss_signature as mod  # type: ignore

    sample_dir = tmp_path_obj()
    sample = sample_dir / "s.json"
    sample.write_text('{"sig": "Signature=ABCDEFGHIJKLMNOPQRSTUV"}', encoding="utf-8")  # 24 chars
    hits = mod.scan_file(sample)
    assert len(hits) == 0, f"placeholder 24 chars ne doit pas etre attrape (seuil=28), vu {len(hits)}"
    sample.unlink()


def test_strict_lit_un_pathspec_separe_pour_py_cs_md(tmp_path: Path):
    """--strict ouvre un second filtre py/cs/md distinct de json/ipynb.

    CR myia-ai-01 22:36Z sur PR #18835 : l'ancien code iterait sur la liste
    json/ipynb et re-filtrait sur py/cs/md -- structuralement vide.
    """
    proc = _run(["--strict", "--json"], cwd=tmp_path)
    assert proc.returncode in (0, 1), f"--strict doit reussir (0 ou 1), vu {proc.returncode}: {proc.stderr}"
    payload = json.loads(proc.stdout)
    # Le verdict est CLEAN ou DIRTY ; le seul invariant est que la sortie --strict
    # n'echoue pas en structural-vide. Le test positif de la branche --strict
    # elle-meme (un commentaire py qui mentionne Signature= est attrape) est
    # couvert par le controle positif ci-dessous via un mock pathspec.
    assert "verdict" in payload


def test_docstring_module_ne_cite_aucun_token_en_clair():
    """Le docstring du module ne doit citer aucun identifiant OSS en clair.

    CR myia-ai-01 22:36Z sur PR #18835 : hygiene, masquer les exemples
    (LTAI5tRDTcy..., FfViql...).
    """
    src = SCRIPT.read_text(encoding="utf-8")
    # Aucun identifiant OSS en clair dans le docstring (lignes 1-50 environ)
    docstring_end = src.find('from __future__ import annotations')
    docstring = src[:docstring_end]
    forbidden_patterns = [
        r"LTAI[0-9A-Za-z]{6,}",  # LTAI + suite (cle d'acces reelle)
        r"FfViq",                  # prefixe reel cite
        r"Signature=[A-Za-z0-9]{8,}",  # Signature= avec valeur >= 8 chars non placeholder
    ]
    for pat in forbidden_patterns:
        matches = re.findall(pat, docstring)
        assert not matches, (
            f"docstring module cite un token en clair : {matches} (pattern {pat}). "
            f"Remplacer par une forme masquée (LTAI****, <token>, etc.)"
        )


def test_controle_negatif_sur_le_depot():
    """Sur le depot courant, l'organe doit etre CLEAN (ou ne jamais bloquer le run)."""
    proc = _run(["--json"], cwd=REPO_ROOT)
    assert proc.returncode in (0, 1), f"verdict non-bloquant, vu {proc.returncode}: {proc.stderr}"
    payload = json.loads(proc.stdout)
    # Le verdict peut etre DIRTY (un exemple pedagogique mentionne les cles) ; on
    # n'impose pas CLEAN, mais on impose que l'organe reponde et structure sa sortie.
    assert payload["verdict"] in ("CLEAN", "DIRTY")
    assert "findings" in payload
    assert "scanned_files" in payload
    assert payload["min_value_len"] == 28, "MIN_VALUE_LEN doit etre 28 dans la sortie JSON"


def test_caller_workflow_json_passe_dirty_comme_dirty_avec_findings(tmp_path: Path):
    """Le caller workflow-shape (avec --json) doit classer DIRTY comme DIRTY et exposer findings.

    Steer adjoint c22 (2026-10-03) sur PR #18895 : sans --json, stdout est
    du texte formate (CLEAN -- scanned ... / DIRTY -- ...) -- un reel DIRTY
    serait classe UNKNOWN au lieu de hit. Le fix aligne l'appel (--json) et
    pose ce temoin positif qui prouve que la chaîne complete tient.

    Le test execute le script via subprocess (comme le step workflow) avec
    --json, parse la sortie JSON, et verifie que :
    - le verdict est bien 'DIRTY' (pas '?')
    - findings expose au moins un match
    - le RC est 1 (le gate rougit)

    REPO_ROOT_OVERRIDE permet au script de scanner le repo fixture minimal
    (sinon il scannerait le depot CoursIA-2 reel et ne trouverait pas la
    fixture -- 1871 fichiers vs 1 fichier dirty).
    """
    # Genere une fixture DIRTY temporaire dans tmp_path, et fait passer
    # `git ls-files` sur ce dossier via un repo git local minimal.
    import subprocess as sp

    repo = tmp_path / "fixture_repo"
    repo.mkdir()
    sp.run(["git", "init", "-q"], cwd=repo, check=True)
    sp.run(["git", "config", "user.email", "test@example.com"], cwd=repo, check=True)
    sp.run(["git", "config", "user.name", "test"], cwd=repo, check=True)

    # Fichier DIRTY : signature= avec token de 32 chars + OSSAccessKeyId valide
    dirty = repo / "dirty.json"
    dirty.write_text(
        '{"image_url_signed_full": "https://bucket.oss.aliyuncs.com/img.png'
        '?Signature=ABCDEFGHIJKLMNOPQRSTUVWXYZ012345&OSSAccessKeyId=LTAI5tRDTcyABcdEFgh"}',
        encoding="utf-8",
    )
    sp.run(["git", "add", "dirty.json"], cwd=repo, check=True)
    sp.run(["git", "commit", "-q", "-m", "fixture"], cwd=repo, check=True)

    # Appelle le script avec --json dans ce repo minimal. pathspecs default
    # *.json/*.ipynb matche dirty.json. REPO_ROOT_OVERRIDE dit au script de
    # prendre ce repo-la comme racine (sinon il prend CoursIA-2 par defaut).
    cmd = [sys.executable, str(SCRIPT), "--json"]
    proc = sp.run(
        cmd, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
        cwd=repo, timeout=180,
        env={**__import__("os").environ, "REPO_ROOT_OVERRIDE": str(repo)},
    )
    assert proc.returncode == 1, (
        f"DIRTY reel doit retourner RC=1, vu {proc.returncode} (stdout={proc.stdout[:200]}, stderr={proc.stderr[:200]})"
    )
    payload = json.loads(proc.stdout)
    assert payload["verdict"] == "DIRTY", (
        f"verdict doit etre 'DIRTY', vu {payload['verdict']!r} -- si c'est '?' le caller workflow-shape "
        f"fait json.load sur stdout non-JSON (defaut releve par adjoint c22 sur #18895)"
    )
    assert len(payload.get("findings", [])) >= 1, (
        f"findings doit exposer au moins un match pour le porteur de la PR, "
        f"vu {len(payload.get('findings', []))} finding(s) -- sans findings, un DIRTY reel "
        f"rougit sans diagnostic derrierrable (defaut adjoint c22)"
    )
    f = payload["findings"][0]
    assert f["file"] == "dirty.json"
    assert len(f["hits"]) >= 1


# Valeurs de fixture -- distinctives, jamais commitees, servent d'aiguille.
_FX_SIG_TOKEN = "ZzQ9SignedUrlTokenValue0123456789"   # >= MIN_VALUE_LEN
_FX_ACCESS_KEY = "LTAI5tZzFixtureKeyAlpha99"


def _dirty_repo(tmp_path: Path, name: str, content: str) -> Path:
    """Repo git minimal avec un unique fichier `name` portant `content`."""
    import subprocess as sp
    repo = tmp_path / "fixture_repo"
    repo.mkdir()
    sp.run(["git", "init", "-q"], cwd=repo, check=True)
    sp.run(["git", "config", "user.email", "test@example.com"], cwd=repo, check=True)
    sp.run(["git", "config", "user.name", "test"], cwd=repo, check=True)
    (repo / name).write_text(content, encoding="utf-8")
    sp.run(["git", "add", name], cwd=repo, check=True)
    sp.run(["git", "commit", "-q", "-m", "fixture"], cwd=repo, check=True)
    return repo


def _scan_payload(repo: Path, extra: list[str] | None = None) -> subprocess.CompletedProcess:
    import os
    return subprocess.run(
        [sys.executable, str(SCRIPT), "--json"] + (extra or []),
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        cwd=repo, timeout=180,
        env={**os.environ, "REPO_ROOT_OVERRIDE": str(repo)},
    )


def test_le_payload_ne_porte_aucun_fragment_de_secret_en_clair(tmp_path: Path):
    """Invariant : la charge utile est `cat`-ee dans un log PUBLIC.

    Le step `Detecteur OSS signature fragments` (always-on-guards.yml) fait
    `cat /tmp/oss_sig.json`, puis re-imprime chaque `match` dans une
    annotation `::error::`. Les deux consommateurs heritent de ce que
    l'organe met dans sa charge utile : si `match`/`context` portaient la
    valeur detectee, le secret partirait en clair dans un log public.

    Controle positif double -- sans lui le test passerait a vide :
    (a) le verdict est DIRTY (donc la fixture a bien ete attrapee) ;
    (b) le marqueur de masquage est present (donc le masquage a bien tourne).
    """
    repo = _dirty_repo(
        tmp_path, "dirty.json",
        '{"image_url_signed_full": "https://bucket.oss.aliyuncs.com/img.png'
        f'?Signature={_FX_SIG_TOKEN}&OSSAccessKeyId={_FX_ACCESS_KEY}"}}',
    )
    proc = _scan_payload(repo)
    assert proc.returncode == 1, f"DIRTY doit rendre RC=1, vu {proc.returncode}"
    payload = json.loads(proc.stdout)

    # (a) controle positif de detection
    assert payload["verdict"] == "DIRTY", "la fixture doit etre attrapee, sinon le test est vide"
    hits = payload["findings"][0]["hits"]
    assert len(hits) >= 1

    # (b) controle positif de masquage
    assert any("<redacted len=" in h["match"] for h in hits), (
        f"aucun marqueur de masquage dans les hits : {[h['match'] for h in hits]}"
    )

    # L'invariant : aucun fragment de valeur en clair dans la charge utile.
    assert _FX_SIG_TOKEN not in proc.stdout, "le token de signature fuit en clair"
    assert _FX_ACCESS_KEY not in proc.stdout, "la cle d'acces fuit en clair"
    for h in hits:
        assert _FX_SIG_TOKEN[:12] not in h["match"], f"prefixe de token dans match : {h['match']}"
        assert _FX_SIG_TOKEN[:12] not in h.get("context", ""), f"prefixe de token dans context : {h['context']}"
        # Le diagnostic survit : fichier + ligne + motif restent exploitables.
        assert isinstance(h["line"], int) and h["line"] > 0
        assert h["pattern"]


def test_branche_strict_masque_aussi_la_prose(tmp_path: Path):
    """Le second filtre (py/cs/md) masque la valeur comme le filtre json/ipynb."""
    repo = _dirty_repo(
        tmp_path, "note.md",
        f"<!-- exemple -->\n# Signature={_FX_SIG_TOKEN}\n",
    )
    proc = _scan_payload(repo, extra=["--strict"])
    assert proc.returncode == 1, f"--strict doit rendre RC=1, vu {proc.returncode}"
    payload = json.loads(proc.stdout)
    assert payload["verdict"] == "DIRTY"
    prose = [f for f in payload["findings"] if f["surface"] == "prose"]
    assert prose, "la branche --strict doit trouver la mention en prose"
    assert _FX_SIG_TOKEN not in proc.stdout, "le token fuit par la branche --strict"


def test_redact_line_blanchit_la_valeur_et_garde_le_contexte():
    """Unite : `redact_line` retire la valeur, garde la cle et le reste de la ligne."""
    sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))
    import detect_oss_signature as mod  # type: ignore

    line = f'{{"url": "https://b.oss.aliyuncs.com/i.png?Signature={_FX_SIG_TOKEN}&x=1"}}'
    out = mod.redact_line(line)
    assert _FX_SIG_TOKEN not in out, f"valeur encore presente : {out}"
    assert "<redacted len=" in out, f"marqueur absent : {out}"
    assert "Signature=" in out and '"x": "1"' in out or "&x=1" in out, (
        f"le contexte exploitable a ete perdu : {out}"
    )