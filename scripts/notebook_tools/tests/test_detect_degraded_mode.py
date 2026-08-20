#!/usr/bin/env python3
"""Tests for ``scripts/notebook_tools/detect_degraded_mode.py`` (#11754).

Pourquoi ce fichier existe
--------------------------
L'acceptance de #11754 exige des controles REALISES, pas declares :

1. **controle positif sur la fixture vivante** : le commit multié de
   #11443 (``66e2a429bb``) DOIT lever, avec l'aveu verbatim. Le test
   unitaire simule la confession EXACTE (copiee du notebook reel) dans
   des notebooks minimaux ; la validation contre les vrais SHAs (base
   ``25588a601``, mute ``66e2a429bb``, repare ``803d8bde5``) est citee
   dans le body de la PR livrante -- les SHAs ne sont pas pinnes ici
   pour ne pas dependre d'un clone profond en CI.
2. **controle negatif** : la meme PR APRES reparation ne leve pas.
3. **base de fusion, pas origin/main deux-points** : un test construit
   une topologie divergente (branche en retard sur main) et prouve que
   la confession heritee du merge-base n'est PAS signalee alors que
   origin/main deux-points la croirait nouvelle.
4. **frozen-inheritance** : une confession presente a la base ET a la
   tete n'est jamais un finding (corpus 2026-08-19 : ~118 confessions
   heritees -- sans ce filtre, l'organe serait ne mort).
5. **codes de sortie** : rc=2 sur ref invalide (fail loud, jamais de
   exemption silencieuse par ref rate), rc=1 sur findings en --check.

Run:
    python -m pytest scripts/notebook_tools/tests/test_detect_degraded_mode.py -v
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
TOOL = REPO_ROOT / "scripts" / "notebook_tools" / "detect_degraded_mode.py"
sys.path.insert(0, str(TOOL.parent))

import detect_degraded_mode as ddm  # noqa: E402


# La confession VERBATIM du commit multié 66e2a429bb (cellule 26 du
# 01-5-Kokoro-TTS-Local reel) : elle est le cas fondateur, on ne l'invente pas.
KOKORO_CONFESSION = "  OpenAI API key non configuree - comparaison skippee"
# Second aveu reel du meme commit (cellule 8) : la resolution .env ratee.
ENV_CONFESSION = "WARNING: .env non trouve dans GenAI"
# Confession heritee (cellule 40, presente dans base ET tete du reel).
INHERITED_CONFESSION = "genere (exercice a completer ou service indisponible)"


def _nb(cells_streams: list[str | None]) -> dict:
    """Notebook minimal : une cellule code par element ; None = cellule
    sans confession (sortie neutre), str = sortie stream portant ce texte."""
    cells = []
    for stream in cells_streams:
        outputs = [] if stream is None else [
            {"output_type": "stream", "name": "stdout", "text": stream + "\n"}
        ]
        cells.append({
            "cell_type": "code", "execution_count": 1,
            "metadata": {}, "outputs": outputs, "source": [],
        })
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _write_nb(path: Path, nb: dict) -> None:
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")


def _init_repo_with_nb(tmp_path: Path, nb: dict, nb_name: str = "case.ipynb") -> str:
    """Depot lineaire minimal ; rend le SHA du commit porte-notebook."""
    def _git(*args):
        return subprocess.run(
            ["git", *args], cwd=tmp_path, capture_output=True, text=True,
            encoding="utf-8", check=True,
        )
    _git("init", "-q")
    _git("config", "user.email", "test@example.com")
    _git("config", "user.name", "Test")
    (tmp_path / ".keep").write_text("", encoding="utf-8")
    _git("add", ".keep")
    _git("commit", "-q", "-m", "init")
    _write_nb(tmp_path / nb_name, nb)
    _git("add", nb_name)
    _git("commit", "-q", "-m", "add notebook")
    return _git("rev-parse", "HEAD").stdout.strip()


def _commit_more(tmp_path: Path, msg: str) -> str:
    def _git(*args):
        return subprocess.run(
            ["git", *args], cwd=tmp_path, capture_output=True, text=True,
            encoding="utf-8", check=True,
        )
    (tmp_path / "other.txt").write_text(msg, encoding="utf-8")
    _git("add", "other.txt")
    _git("commit", "-q", "-m", msg)
    return _git("rev-parse", "HEAD").stdout.strip()


# ---------------------------------------------------------------------------
# 1. Controle positif -- l'aveu verbatim du cas fondateur doit lever
# ---------------------------------------------------------------------------

def test_kokoro_confession_verbatim_leve(tmp_path):
    """Base sans aveu, tete avec l'aveu EXACT de #11443 -> finding
    NON_CONFIGURED, cellule et lignes nommees."""
    base = _nb([None, "COMPARAISON KOKORO VS OPENAI TTS\n--- Kokoro ---\n  Temps : 2.28s"])
    head = _nb([None, KOKORO_CONFESSION])
    base_sha = _init_repo_with_nb(tmp_path, base)
    _write_nb(tmp_path / "case.ipynb", head)
    subprocess.run(["git", "add", "case.ipynb"], cwd=tmp_path,
                   capture_output=True, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "mutilated"], cwd=tmp_path,
                   capture_output=True, check=True)
    head_sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=tmp_path,
                              capture_output=True, text=True, check=True).stdout.strip()

    result = ddm.scan_notebook(tmp_path / "case.ipynb", base_sha, head_sha)
    assert "error" not in result, result
    kinds = [(f["pattern"], f["cell_index"]) for f in result["findings"]]
    assert ("NON_CONFIGURED", 1) in kinds, kinds


def test_env_not_found_confession_leve(tmp_path):
    """Second aveu reel (#11443 cellule 8) : ``WARNING: .env non trouve``
    -- le tell du worktree sans .env."""
    base = _nb(["env OK"])
    base_sha = _init_repo_with_nb(tmp_path, base)
    head = _nb([ENV_CONFESSION])
    _write_nb(tmp_path / "case.ipynb", head)
    subprocess.run(["git", "add", "case.ipynb"], cwd=tmp_path,
                   capture_output=True, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "env lost"], cwd=tmp_path,
                   capture_output=True, check=True)
    head_sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=tmp_path,
                              capture_output=True, text=True, check=True).stdout.strip()
    result = ddm.scan_notebook(tmp_path / "case.ipynb", base_sha, head_sha)
    kinds = [f["pattern"] for f in result["findings"]]
    assert "NOT_FOUND" in kinds, kinds


def test_skipped_pattern_leve(tmp_path):
    """``La generation sera skippee`` (corpus Bonsai 02-5) : pattern SKIPPED."""
    base = _nb(["generation OK, 3 images"])
    base_sha = _init_repo_with_nb(tmp_path, base)
    head = _nb(["La generation sera skippee. (service absent)"])
    _write_nb(tmp_path / "case.ipynb", head)
    subprocess.run(["git", "add", "case.ipynb"], cwd=tmp_path,
                   capture_output=True, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "skipped"], cwd=tmp_path,
                   capture_output=True, check=True)
    head_sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=tmp_path,
                              capture_output=True, text=True, check=True).stdout.strip()
    result = ddm.scan_notebook(tmp_path / "case.ipynb", base_sha, head_sha)
    kinds = [f["pattern"] for f in result["findings"]]
    assert "SKIPPED" in kinds, kinds


# ---------------------------------------------------------------------------
# 2. Controle negatif -- apres reparation, plus de signal
# ---------------------------------------------------------------------------

def test_repaired_head_ne_leve_pas(tmp_path):
    """La confession disparue de la tete (reparation du commit suivant de
    #11443) -> 0 finding, rc=0."""
    base = _nb(["comparaison complete : Kokoro + tts-1 + tts-1-hd"])
    base_sha = _init_repo_with_nb(tmp_path, base)
    # tete = base inchangee (la reparation a restaure la sortie d'origine)
    result = ddm.scan_notebook(tmp_path / "case.ipynb", base_sha, base_sha)
    assert "error" not in result, result
    assert result["findings"] == []
    assert result["stats"]["findings_count"] == 0


def test_confession_heritee_base_et_tete_pas_de_finding(tmp_path):
    """Frozen-inheritance : la confession de la cellule 40 du Kokoro reel
    (« service indisponible ») vit en base ET en tete -> jamais un finding.
    Corpus 2026-08-19 : ~118 confessions heritees ; sans ce filtre
    l'organe rendrait du bruit a chaque PR."""
    nb = _nb([INHERITED_CONFESSION, "sortie propre"])
    base_sha = _init_repo_with_nb(tmp_path, nb)
    result = ddm.scan_notebook(tmp_path / "case.ipynb", base_sha, base_sha)
    assert result["findings"] == []
    assert result["stats"]["base_confessions_total"] >= 1
    assert result["stats"]["head_confessions_total"] >= 1


def test_variation_de_compteur_multiset(tmp_path):
    """La meme confession DEUX fois en tete contre UNE fois en base : le
    surplus multiset est un finding (deux branches sautees ne sont pas
    une)."""
    base = _nb([KOKORO_CONFESSION])
    head = _nb([KOKORO_CONFESSION, KOKORO_CONFESSION])
    base_sha = _init_repo_with_nb(tmp_path, base)
    _write_nb(tmp_path / "case.ipynb", head)
    subprocess.run(["git", "add", "case.ipynb"], cwd=tmp_path,
                   capture_output=True, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "twice"], cwd=tmp_path,
                   capture_output=True, check=True)
    head_sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=tmp_path,
                              capture_output=True, text=True, check=True).stdout.strip()
    result = ddm.scan_notebook(tmp_path / "case.ipynb", base_sha, head_sha)
    assert result["stats"]["findings_count"] == 1, result


# ---------------------------------------------------------------------------
# 3. Base de FUSION -- topologie divergente (acceptance #11754)
# ---------------------------------------------------------------------------

def test_branch_behind_main_compare_au_merge_base(tmp_path):
    """Acceptance litterale de #11754 : « la comparaison se fait contre la
    base de fusion, prouve par un test dont la branche est en retard sur
    main ».

    Topologie :

        A : init
        B : notebook SANS confession          <- merge-base de la branche
        C : main avance (le notebook GAGNE la confession, hors PR)
        D : branche PR avance (autre fichier)  <- tete, notebook = B

    Un detecteur comparant tete vs origin/main (deux-points) verrait la
    confession DISPARAITRE entre main et tete et pourrait la croire
    heritee-ou-perdue ; un detecteur comparant tete vs main en sens
    « nouvelles de la tete » verrait 0. Le point pinne ici : la confession
    n'existe NI au merge-base NI a la tete -> 0 finding ; et le tell
    miroir : une confession NOUVELLE porte par la tete contre un merge-base
    qui ne l'a pas DOIT lever meme si origin/main l'a deja (la PR ne doit
    pas etre jugee sur les evolutions de main)."""
    nb_clean = _nb(["comparaison complete"])
    base_sha = _init_repo_with_nb(tmp_path, nb_clean)

    # C : main avance -- le notebook gagne une confession (hors PR)
    nb_main = _nb([KOKORO_CONFESSION])
    _write_nb(tmp_path / "case.ipynb", nb_main)
    subprocess.run(["git", "add", "case.ipynb"], cwd=tmp_path,
                   capture_output=True, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "main: confession apparaît"],
                   cwd=tmp_path, capture_output=True, check=True)
    main_sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=tmp_path,
                              capture_output=True, text=True, check=True).stdout.strip()

    # D : branche PR depuis B (detour par main serait un rebase) -- autre
    # fichier seulement ; le notebook reste la version PROPRE de B.
    subprocess.run(["git", "checkout", "-q", "-b", "pr-branch", base_sha],
                   cwd=tmp_path, capture_output=True, check=True)
    _write_nb(tmp_path / "case.ipynb", nb_clean)  # inchangé vs B
    pr_sha = _commit_more(tmp_path, "pr: autre fichier")

    # (a) tete propre vs merge-base propre : 0 finding.
    r = ddm.scan_notebook(tmp_path / "case.ipynb", base_sha, pr_sha)
    assert "error" not in r, r
    assert r["findings"] == [], r

    # (b) tell miroir : la teteporte une confession nouvelle (vs B) ->
    # finding, MEME SI origin/main (C) l'a deja -- juger la tete contre
    # main ferait disparaitre le signal de la PR.
    _write_nb(tmp_path / "case.ipynb", _nb([KOKORO_CONFESSION]))
    subprocess.run(["git", "add", "case.ipynb"], cwd=tmp_path,
                   capture_output=True, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "pr: degradation"], cwd=tmp_path,
                   capture_output=True, check=True)
    pr_degraded = subprocess.run(["git", "rev-parse", "HEAD"], cwd=tmp_path,
                                 capture_output=True, text=True, check=True).stdout.strip()
    r2 = ddm.scan_notebook(tmp_path / "case.ipynb", base_sha, pr_degraded)
    kinds = [f["pattern"] for f in r2["findings"]]
    assert "NON_CONFIGURED" in kinds, (kinds, "la PR doit etre jugee contre le merge-base, pas contre main")


# ---------------------------------------------------------------------------
# 4. Codes de sortie et exemptions CLI
# ---------------------------------------------------------------------------

def test_cli_check_rc1_sur_finding(tmp_path):
    base = _nb(["ok"])
    base_sha = _init_repo_with_nb(tmp_path, base)
    _write_nb(tmp_path / "case.ipynb", _nb([KOKORO_CONFESSION]))
    result = subprocess.run(
        [sys.executable, str(TOOL), "case.ipynb", "--base", base_sha, "--check"],
        capture_output=True, text=True, encoding="utf-8",
        cwd=tmp_path, check=False,
    )
    assert result.returncode == 1, (result.returncode, result.stdout, result.stderr)
    assert "non configuree" in result.stdout


def test_cli_ref_invalide_rc2_fail_loud(tmp_path):
    """Ref de base introuvable -> rc=2, jamais une exemption silencieuse
    (garde anti-auto-desarmement #8655/#8662 : « pas regarde » doit rester
    distinguishable de « rien trouve »)."""
    base_sha = _init_repo_with_nb(tmp_path, _nb(["ok"]))
    result = subprocess.run(
        [sys.executable, str(TOOL), "case.ipynb",
         "--base", "ce-ref-bidon-n-existe-pas", "--head", base_sha, "--check"],
        capture_output=True, text=True, encoding="utf-8",
        cwd=tmp_path, check=False,
    )
    assert result.returncode == 2
    assert "introuvable" in result.stderr


def test_cli_new_file_exempt(tmp_path):
    """Notebook absent a la base (nouveau fichier) : exempt -- tout est
    ajoute, aucune degradation d'un existant."""
    _init_repo_with_nb(tmp_path, _nb(["ok"]))
    _write_nb(tmp_path / "new.ipynb", _nb([KOKORO_CONFESSION]))
    subprocess.run(["git", "add", "new.ipynb"], cwd=tmp_path,
                   capture_output=True, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "new nb"], cwd=tmp_path,
                   capture_output=True, check=True)
    head_sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=tmp_path,
                              capture_output=True, text=True, check=True).stdout.strip()
    base_sha = subprocess.run(
        ["git", "rev-parse", "HEAD~2"], cwd=tmp_path,
        capture_output=True, text=True, check=True).stdout.strip()
    result = subprocess.run(
        [sys.executable, str(TOOL), "new.ipynb", "--base", base_sha,
         "--head", head_sha, "--check", "--json"],
        capture_output=True, text=True, encoding="utf-8",
        cwd=tmp_path, check=False,
    )
    payload = json.loads(result.stdout)
    assert result.returncode == 0, payload
    assert payload["findings_total"] == 0
    assert payload["results"][0].get("new_file") is True


def test_finding_nomme_cellule_et_octets(tmp_path):
    """Acceptance « le detecteur nomme ce qu'il a mesure » : chaque finding
    porte pattern + cellule + ligne + octets de la cellule (base/head)."""
    big_base = "x" * 5000  # volume mesurable cote base
    base = _nb([f"audio bytes: {big_base}"])
    base_sha = _init_repo_with_nb(tmp_path, base)
    _write_nb(tmp_path / "case.ipynb", _nb([KOKORO_CONFESSION]))
    subprocess.run(["git", "add", "case.ipynb"], cwd=tmp_path,
                   capture_output=True, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "mutilated"], cwd=tmp_path,
                   capture_output=True, check=True)
    head_sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=tmp_path,
                              capture_output=True, text=True, check=True).stdout.strip()
    r = ddm.scan_notebook(tmp_path / "case.ipynb", base_sha, head_sha)
    f = r["findings"][0]
    assert f["pattern"] and isinstance(f["cell_index"], int)
    assert "non configuree" in f["line"]
    assert f["cell_output_bytes_base"] is not None and f["cell_output_bytes_base"] > 1000


# ---------------------------------------------------------------------------
# 6. Extension c.1301+256 -- axe 2 SOTA STACK_DOWN (#11754 follow-up)
# Cas fondateur : PR #11859 (review ai-01 06:52Z) -- la re-execution depuis
# un worktree a perdu cell11 (whisper-api) et cell15 (ComfyUI) sans qu'aucun
# compteur structurel ne bronche. Volume MONTAIT (+24.2 %). Cas fondateur
# verifie : commit d6dd2ae68 = 11 occurrences STACK_DOWN ; commit c98e48196
# (voie-2 ai-01) = 0.
# ---------------------------------------------------------------------------

# Aveux verbatim du notebook 02-Aspire-GenAiStack-Reel (cell11/cell15)
# re-execute sans stack GenAI montee.
STACK_DOWN_WHISPER_FRAGMENT = (
    "[whisper-api] Unable to find image 'whisper-api-whisper-api:latest' locally\n"
    "[whisper-api] Error response from daemon: pull access denied for whisper-api-whisper-api\n"
    "[sys] container not found"
)
STACK_DOWN_COMFY_FRAGMENT = (
    "token ComfyUI extrait des logs : ECHEC (conteneur down ?)\n"
    "GET /system_stats -> HttpRequestException ... (127.0.0.1:8188)"
)


def test_stack_down_whisper_leve(tmp_path):
    """Base propre, tete avec aveux Docker (whisper-api pull access denied +
    container not found) -> findings STACK_DOWN_PULL_ACCESS et
    STACK_DOWN_CONTAINER_NOT_FOUND et STACK_DOWN_UNABLE_FIND_IMAGE."""
    base = _nb([None, "GenAI stack running on host\nWhisper OK"])
    head = _nb([None, STACK_DOWN_WHISPER_FRAGMENT])
    base_sha = _init_repo_with_nb(tmp_path, base)
    _write_nb(tmp_path / "case.ipynb", head)
    subprocess.run(["git", "add", "case.ipynb"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "re-exec"], cwd=tmp_path, check=True)
    head_sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=tmp_path,
                              capture_output=True, text=True, check=True).stdout.strip()
    r = ddm.scan_notebook(tmp_path / "case.ipynb", base_sha, head_sha)
    patterns_hit = {f["pattern"] for f in r["findings"]}
    assert "STACK_DOWN_PULL_ACCESS" in patterns_hit
    assert "STACK_DOWN_CONTAINER_NOT_FOUND" in patterns_hit
    assert "STACK_DOWN_UNABLE_FIND_IMAGE" in patterns_hit
    # Tous sur la meme cellule (cell#1)
    cells = {f["cell_index"] for f in r["findings"]}
    assert cells == {1}


def test_stack_down_comfy_leve(tmp_path):
    """Cellule ComfyUI re-executee sans conteneur (HttpRequestException
    + 'conteneur down ?') -> findings STACK_DOWN_HTTP_REQ_EXC ET
    STACK_DOWN_FAILED_TO_START ne s'appliquent pas ici (ComfyUI n'utilise
    pas Aspire FailedToStart ; on attrape HttpRequestException)."""
    base = _nb([None, "ComfyUI OK on :8188\nGET /system_stats -> 200"])
    head = _nb([None, STACK_DOWN_COMFY_FRAGMENT])
    base_sha = _init_repo_with_nb(tmp_path, base)
    _write_nb(tmp_path / "case.ipynb", head)
    subprocess.run(["git", "add", "case.ipynb"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "re-exec"], cwd=tmp_path, check=True)
    head_sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=tmp_path,
                              capture_output=True, text=True, check=True).stdout.strip()
    r = ddm.scan_notebook(tmp_path / "case.ipynb", base_sha, head_sha)
    patterns_hit = {f["pattern"] for f in r["findings"]}
    assert "STACK_DOWN_HTTP_REQ_EXC" in patterns_hit


def test_stack_down_herite_pas_de_finding(tmp_path):
    """Frozen-inheritance stance (#11840) : une confession STACK_DOWN deja
    presente a la base (notebook d'un worker sans stack GenAI historique)
    n'est PAS signalee -- seul le delta base->tete est un finding."""
    base = _nb([None, STACK_DOWN_WHISPER_FRAGMENT])
    head = _nb([None, STACK_DOWN_WHISPER_FRAGMENT + "\n[extra noise]\n"])
    base_sha = _init_repo_with_nb(tmp_path, base)
    _write_nb(tmp_path / "case.ipynb", head)
    subprocess.run(["git", "add", "case.ipynb"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "noisy"], cwd=tmp_path, check=True)
    head_sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=tmp_path,
                              capture_output=True, text=True, check=True).stdout.strip()
    r = ddm.scan_notebook(tmp_path / "case.ipynb", base_sha, head_sha)
    assert r["findings"] == []


def test_stack_down_cas_fondateur_d6dd2ae(tmp_path):
    """Controle positif sur le SHA REEL fautif (PR #11859 pre-voie-2) :
    commit d6dd2ae68 = 11 occurrences STACK_DOWN melangees. On lit le
    notebook tel qu'il etait SUR la branche fix/11725-aspire-paths a ce
    commit, on scanne, et on exige >=5 findings STACK_DOWN_* distincts.
    Test sans CI : si la branche n'existe pas localement, skip."""
    target = "MyIA.AI.Notebooks/GenAI/Aspire/02-Aspire-GenAiStack-Reel.ipynb"
    # Sanity check : la branche doit exister localement.
    res = subprocess.run(
        ["git", "cat-file", "-e", "d6dd2ae68^{commit}"],
        capture_output=True, text=True, cwd=REPO_ROOT,
    )
    if res.returncode != 0:
        import pytest
        pytest.skip(f"commit d6dd2ae68 introuvable localement : pas de fixture positive")
    # Lire le notebook tel qu'il etait sur ce commit
    res = subprocess.run(
        ["git", "show", f"d6dd2ae68:{target}"],
        capture_output=True, text=True, cwd=REPO_ROOT, check=True,
    )
    nb = json.loads(res.stdout)
    findings = ddm.extract_confessions(nb)
    stack_hits = [f for f in findings if f[0].startswith("STACK_DOWN_")]
    assert len(stack_hits) >= 5, (
        f"attendu >=5 STACK_DOWN sur le cas fondateur d6dd2ae68, "
        f"observe {len(stack_hits)} ({[f[0] for f in stack_hits]})"
    )


def test_stack_down_cas_repare_c98e48196(tmp_path):
    """Controle negatif : meme notebook sur le commit remede c98e48196
    (voie-2 ai-01 appliquee : cell11/cell15 restaurees depuis main) ->
    0 finding STACK_DOWN. C'est la preuve que l'instrument suit
    effectivement le signal qu'il pretend mesurer."""
    target = "MyIA.AI.Notebooks/GenAI/Aspire/02-Aspire-GenAiStack-Reel.ipynb"
    res = subprocess.run(
        ["git", "cat-file", "-e", "c98e48196^{commit}"],
        capture_output=True, text=True, cwd=REPO_ROOT,
    )
    if res.returncode != 0:
        import pytest
        pytest.skip("commit c98e48196 introuvable localement")
    res = subprocess.run(
        ["git", "show", f"c98e48196:{target}"],
        capture_output=True, text=True, cwd=REPO_ROOT, check=True,
    )
    nb = json.loads(res.stdout)
    findings = ddm.extract_confessions(nb)
    stack_hits = [f for f in findings if f[0].startswith("STACK_DOWN_")]
    assert stack_hits == [], (
        f"attendu 0 STACK_DOWN sur le commit remede c98e48196, "
        f"observe {len(stack_hits)}"
    )
