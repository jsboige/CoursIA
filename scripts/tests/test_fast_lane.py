"""Tests du moteur de voie rapide (#11835).

Trois proprietes sont sous test, et deux d'entre elles existent parce que le
depot a deja paye leur violation ailleurs :

1. **La selection par chemin ne doit pas SOUS-selectionner.** Un motif qui
   rate ne leve pas d'erreur : il rend moins de gardes, donc un CI plus vert
   et plus rapide. C'est la forme de defaut la plus difficile a voir, et
   `**/*.ipynb` contre un fichier a la racine en est le cas exact.
2. **Un garde advisory ne doit JAMAIS rougir**, et ne doit pas non plus etre
   blanchi en `success` : son verdict est `neutral`, sinon on perd le signal
   dans un sens ou dans l'autre.
3. **La restauration de l'arbre apres la bascule de base est verifiee**, et
   son echec interrompt tout plutot que de publier des verdicts calcules sur
   un arbre inconnu.

Les cas positifs (un garde qui echoue doit produire `failure`) sont aussi
couverts : une suite ou tout passe serait indiscernable d'un moteur debranche.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import fast_lane  # noqa: E402
from fast_lane_registry import PILOT, TRANCHE1, Guard  # noqa: E402


# ---------------------------------------------------------------------------
# 1. Selection par chemin
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("path,pattern,expected", [
    # le cas qui motive la fonction : `**/` couvre AUSSI la racine chez GitHub
    ("a.ipynb", "**/*.ipynb", True),
    ("MyIA.AI.Notebooks/x/y.ipynb", "**/*.ipynb", True),
    ("docs/z.md", "**/*.md", True),
    ("README.md", "**/*.md", True),
    # negatifs : le filtre doit rester un filtre
    ("scripts/foo.py", "**/*.ipynb", False),
    ("a.ipynbx", "**/*.ipynb", False),
    # chemin exact
    ("scripts/notebook_tools/strip_probe_banner.py",
     "scripts/notebook_tools/strip_probe_banner.py", True),
    ("scripts/notebook_tools/other.py",
     "scripts/notebook_tools/strip_probe_banner.py", False),
])
def test_path_matches(path, pattern, expected):
    assert fast_lane.path_matches(path, pattern) is expected


def test_path_matches_accepts_windows_separators():
    """Le diff peut arriver avec des separateurs natifs selon l'appelant."""
    assert fast_lane.path_matches("MyIA.AI.Notebooks\\x\\y.ipynb", "**/*.ipynb")


def test_guard_without_paths_always_applies():
    guard = Guard(name="g", argv=["true"], source="s", paths=[])
    assert fast_lane.guard_applies(guard, []) is True
    assert fast_lane.guard_applies(guard, ["n/importe/quoi.txt"]) is True


def test_guard_with_paths_is_skipped_when_nothing_matches():
    guard = Guard(name="g", argv=["true"], source="s", paths=["**/*.ipynb"])
    assert fast_lane.guard_applies(guard, ["docs/a.md"]) is False
    assert fast_lane.guard_applies(guard, ["docs/a.md", "x/b.ipynb"]) is True


def test_notebook_guards_select_a_root_level_notebook():
    """Controle de bout en bout du piege `**/` sur le registre reel."""
    changed = ["Notebook-A-La-Racine.ipynb"]
    selected = [g.name for g in PILOT if fast_lane.guard_applies(g, changed)]
    for expected in ("banner-guard", "pip-leak-guard", "solution-leak-guard",
                     "prose-counts-guard"):
        assert expected in selected, (
            f"{expected} devrait couvrir un notebook a la racine "
            "(motif `**/*.ipynb`)"
        )


# ---------------------------------------------------------------------------
# 2. Conclusions -- controle positif ET negatif
# ---------------------------------------------------------------------------

def test_blocking_guard_failure_is_a_failure():
    guard = Guard(name="g", argv=["true"], source="s", blocking=True)
    assert fast_lane.conclusion_for(guard, 1) == "failure"


def test_advisory_guard_failure_is_neutral_not_failure_nor_success():
    guard = Guard(name="g", argv=["true"], source="s", blocking=False)
    concl = fast_lane.conclusion_for(guard, 1)
    assert concl == "neutral"
    assert concl != "failure", "un advisory ne doit jamais rougir la PR"
    assert concl != "success", "un advisory en echec ne doit pas etre blanchi"


def test_success_is_success_for_both_kinds():
    for blocking in (True, False):
        guard = Guard(name="g", argv=["true"], source="s", blocking=blocking)
        assert fast_lane.conclusion_for(guard, 0) == "success"


def test_shadow_failure_cannot_block_the_required_pr_gate():
    """Le check ombre ne doit pas pouvoir bloquer le gate REQUIS.

    `pr_gate` ne traite en advisory que les check-runs dont le NOM contient
    `advisory` ; le prefixe ombre n'en contient pas. Un `failure` publie en
    mode ombre entrait donc dans `bad` et rendait rouge un gate requis, alors
    que le job, lui, rendait 0. Mesure du 2026-08-25 : 2 PR ouvertes (#12791,
    #12820) n'avaient pour seul rouge qu'un check ombre.

    Le test verifie les DEUX polarites. Sans le controle positif, un patch qui
    neutraliserait aussi le mode reel desarmerait le gate et passerait ici
    pour un correctif.
    """
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    import pr_gate

    guard = Guard(name="g", argv=["true"], source="s", blocking=True)

    # le nom ombre n'est pas advisory : c'est bien la conclusion qui portait
    # le defaut, pas seulement le libelle.
    assert not pr_gate.is_advisory(fast_lane.SHADOW_PREFIX + guard.name)

    ombre = fast_lane.conclusion_for(guard, 1, shadow=True)
    reel = fast_lane.conclusion_for(guard, 1, shadow=False)

    assert ombre in pr_gate.CONCLUSION_OK, (
        "un echec en mode ombre ne doit plus bloquer le gate requis")
    assert reel not in pr_gate.CONCLUSION_OK, (
        "CONTROLE POSITIF : hors ombre, un garde bloquant doit toujours "
        "rougir -- sinon le correctif a desarme le gate")
    assert fast_lane.conclusion_for(guard, 0, shadow=True) == "success"

# ---------------------------------------------------------------------------
# 2bis. Panne interne de la voie ombre -- ne publie rien, ne bloque pas
# ---------------------------------------------------------------------------

def _arm_unrestorable_tree(monkeypatch, published):
    """Amene `main()` jusqu'a l'arbre non restaure, sans depot reel.

    On neutralise ce qui precede (fichiers changes, execution des gardes,
    appels git) et on force `tree_is_clean` a repondre faux -- la situation
    exacte du run 32774643069 sur #12820.
    """
    delta = [g for g in fast_lane.PILOT if g.delta_argv]
    assert delta, ("le registre ne porte plus aucun garde delta : ce test "
                   "n'exerce plus rien, le corriger plutot que le supprimer")
    cible = delta[0]

    monkeypatch.setattr(fast_lane, "changed_files", lambda _ref: ["x.ipynb"])
    monkeypatch.setattr(fast_lane, "guard_applies", lambda g, c: True)
    monkeypatch.setattr(fast_lane, "run_argv", lambda argv, ctx: (0, "{}"))
    monkeypatch.setattr(fast_lane, "run_iter",
                        lambda argv, paths, ctx: (0, "{}"))
    monkeypatch.setattr(fast_lane, "git",
                        lambda *a: subprocess.CompletedProcess(a, 0, "", ""))
    monkeypatch.setattr(fast_lane, "stale_added_paths", lambda _p: [])
    monkeypatch.setattr(fast_lane, "tree_is_clean",
                        lambda _paths: (False, "  M scripts/fantome.py"))
    monkeypatch.setattr(fast_lane, "emit_check_run",
                        lambda *a, **k: published.append(a))
    return cible


def test_shadow_internal_failure_publishes_nothing_and_does_not_block(
        monkeypatch, tmp_path):
    """Une panne de la voie ombre ne doit pas retenir une PR saine.

    Le check du job s'appelle `Fast lane (ombre) -- N gardes, 1 checkout` : il
    ne contient pas `advisory`, donc `pr_gate` le compte comme un defaut. Un
    job rouge ici BLOQUE la PR, alors que la phase se declare observationnelle.
    Mesure du 2026-08-25 : #12820 etait retenue par ce seul chemin.

    Les deux moities comptent :
      - ne publie RIEN (le fail-closed est preserve : les verdicts porteraient
        sur un arbre inconnu) ;
      - rend 0 (l'ombre ne juge pas).
    Un test qui ne verifierait que le code de retour laisserait passer un
    correctif qui publierait des verdicts faux en silence.
    """
    monkeypatch.setenv("RUNNER_TEMP", str(tmp_path))
    published = []
    _arm_unrestorable_tree(monkeypatch, published)

    rc = fast_lane.main(["--base-ref", "main", "--base-sha", "dead" * 10,
                         "--head-sha", "beef" * 10, "--pr-number", "12820",
                         "--repo", "jsboige/CoursIA"])

    assert rc == 0, "en ombre, une panne interne ne doit pas rougir le job"
    assert published == [], (
        "aucun verdict ne doit etre publie sur un arbre non restaure -- "
        "le fail-closed prime sur le deblocage")


def test_non_shadow_internal_failure_still_stops_hard(monkeypatch, tmp_path):
    """CONTROLE POSITIF : hors ombre, la panne doit toujours arreter net.

    Sans lui, un correctif qui rendrait 0 dans les DEUX modes desarmerait la
    voie rapide le jour de sa bascule, et passerait pour un deblocage.
    """
    monkeypatch.setenv("RUNNER_TEMP", str(tmp_path))
    published = []
    _arm_unrestorable_tree(monkeypatch, published)

    with pytest.raises(SystemExit) as exc:
        fast_lane.main(["--base-ref", "main", "--base-sha", "dead" * 10,
                        "--head-sha", "beef" * 10, "--pr-number", "12820",
                        "--repo", "jsboige/CoursIA", "--no-shadow"])
    assert "PAS revenu" in str(exc.value)
    assert published == []


# ---------------------------------------------------------------------------
# 3. Coherence du registre avec les workflows d'origine
# ---------------------------------------------------------------------------

WORKFLOWS = Path(__file__).resolve().parents[2] / ".github" / "workflows"


def test_every_pilot_guard_names_an_existing_workflow():
    for guard in PILOT:
        assert (WORKFLOWS / guard.source).is_file(), (
            f"{guard.name} declare provenir de {guard.source}, absent du depot"
        )


def test_delta_guards_declare_what_they_swap():
    """Sans `swap_paths`, la phase 2 basculerait un ensemble vide et le delta
    comparerait HEAD a lui-meme -- un vert silencieux."""
    for guard in PILOT:
        if guard.delta_argv:
            assert guard.swap_paths, (
                f"{guard.name} est un delta sans swap_paths : sa phase base "
                "scannerait HEAD et le delta serait toujours vide"
            )


def test_delta_placeholders_are_resolvable():
    ctx = {"base_ref": "origin/main", "base_sha": "abc", "head_sha": "def",
           "pr_number": "1", "base_json": "/tmp/b.json",
           "head_json": "/tmp/h.json"}
    for guard in PILOT:
        fast_lane.substitute(guard.argv, ctx)
        if guard.delta_argv:
            resolved = fast_lane.substitute(guard.delta_argv, ctx)
            assert "/tmp/b.json" in resolved and "/tmp/h.json" in resolved


def test_advisory_flags_match_the_source_workflows():
    """Le caractere advisory est une propriete du garde, pas du moteur.

    `solution-leak-guard` et `prose-counts-guard` sont annonces advisory dans
    l'en-tete de leur workflow ; les inverser ici ferait rougir la flotte sur
    un stock que le depot a explicitement decide de ne pas bloquer.
    """
    by_name = {g.name: g for g in PILOT}
    assert by_name["solution-leak-guard"].blocking is False
    assert by_name["prose-counts-guard"].blocking is False
    assert by_name["banner-guard"].blocking is True
    assert by_name["pip-leak-guard"].blocking is True
    assert by_name["perimeter-review-guard"].blocking is True
    # 5 gardes ajoutees (extension 5 -> 10) -- bloquer par defaut
    assert by_name["bare-cross-dir-load-gate"].blocking is True
    assert by_name["notebook-navlink-check"].blocking is True
    assert by_name["notebook-interp-positioning-guard"].blocking is True
    assert by_name["markdown-rendering-guard"].blocking is True
    assert by_name["self-hosted-runner-policy"].blocking is True


def test_self_hosted_policy_guard_is_wired_fail_closed():
    guard = {item.name: item for item in PILOT}["self-hosted-runner-policy"]
    assert guard.source == "fast-lane-shadow.yml"
    assert guard.argv == [
        "python",
        "scripts/ci/check_self_hosted_runner_policy.py",
        "--check",
    ]
    assert ".github/workflows/*.yml" in guard.paths
    assert ".github/workflows/*.yaml" in guard.paths
    assert "scripts/ci/check_self_hosted_runner_policy.py" in guard.paths
    assert "scripts/ci/fast_lane_registry.py" in guard.paths


def test_iterates_paths_guards_carry_the_placeholder():
    """Le Pattern 1 (boucle bash absorbee) repose sur `{changed_paths}` dans
    argv. Si un garde `iterates_paths=True` ne porte pas ce placeholder,
    `run_iter` ne ferait qu'un seul appel avec un placeholder non-substitue
    -- un faux vert silencieux que ce test empeche."""
    for g in PILOT:
        if g.iterates_paths:
            assert "{changed_paths}" in g.argv, (
                f"{g.name} est iterates_paths=True mais argv ne porte pas "
                "le placeholder {changed_paths} -- run_iter ne ferait rien "
                "d'utile."
            )


def test_non_iterate_guards_have_no_paths_placeholder():
    """Inverse de la precedente : un garde non-iter ne devrait pas avoir
    `{changed_paths}` dans argv (le placeholder n'aurait pas de sens). On
    verifie au moins que les 5 gardes existants en sont exempts."""
    by_name = {g.name: g for g in PILOT}
    for name in ("banner-guard", "pip-leak-guard", "solution-leak-guard",
                 "prose-counts-guard", "perimeter-review-guard"):
        assert "{changed_paths}" not in by_name[name].argv, (
            f"{name} n'est pas iterates_paths mais porte le placeholder"
        )


# ---------------------------------------------------------------------------
# 7. iterates_paths : `expand_paths_token` + `run_iter`
# ---------------------------------------------------------------------------

def test_expand_paths_token_inserts_one_token_per_path():
    """Chaque chemin produit un token dans l'argv, les autres places sont
    preservees. C'est ce qui permet au Pattern 1 d'origine (boucle bash
    `while ... ; do python detector "$nb" --check ; done`) d'etre absorbe
    en un seul appel `run_iter`."""
    argv = ["python", "x.py", "{changed_paths}", "--check"]
    out = fast_lane.expand_paths_token(argv, ["a.ipynb", "b.ipynb"])
    assert out == ["python", "x.py", "a.ipynb", "b.ipynb", "--check"]


def test_expand_paths_token_preserves_when_no_placeholder():
    """Sans `{changed_paths}`, l'argv est inchange (no-op). Aucun garde
    non-iter ne devrait subir cette substitution accidentelle."""
    out = fast_lane.expand_paths_token(["python", "x.py", "--check"], ["a"])
    assert out == ["python", "x.py", "--check"]


def test_run_iter_empty_paths_is_a_zero_no_op():
    """Un CI sans chemin est un vert silencieux, pas un garde qui a travaille.
    Le rc=0 explicite + log temoin distingue ce cas d'un garde reussi."""
    rc, log = fast_lane.run_iter(["python", "x.py", "{changed_paths}"], [], {})
    assert rc == 0
    assert "iterates_paths vide" in log


def test_run_iter_aggregates_zero_for_all_success():
    """Si chaque iteration rend 0, l'agregat est 0 (succes global)."""
    argv = [sys.executable, "-c", "import sys; sys.exit(0)"]
    rc, log = fast_lane.run_iter(argv, ["a", "b", "c"], {})
    assert rc == 0
    assert "--- a ---" in log
    assert "--- b ---" in log
    assert "--- c ---" in log


def test_run_iter_aggregates_first_failure_to_one():
    """Au moins une iteration echoue => rc agrege > 0. Le moteur traduit
    ensuite `rc != 0` en conclusion `failure` (pour les gardes `blocking`).
    On verifie juste l'agregat > 0 ici."""
    argv = [sys.executable, "-c",
            "import sys; sys.exit(1 if '{changed_paths}' == 'b' else 0)"]
    rc, log = fast_lane.run_iter(argv, ["a", "b", "c"], {})
    assert rc == 1
    assert "exit 1" in log


# ---------------------------------------------------------------------------
# 4. Execution et capture
# ---------------------------------------------------------------------------

def test_run_argv_captures_exit_code_and_output():
    rc, log = fast_lane.run_argv(
        [sys.executable, "-c", "import sys; print('bonjour'); sys.exit(3)"], {})
    assert rc == 3
    assert "bonjour" in log
    assert "exit 3" in log


def test_payload_of_strips_the_header_added_by_run_argv():
    rc, log = fast_lane.run_argv(
        [sys.executable, "-c", "print('{\"k\": 1}')"], {})
    assert rc == 0
    assert fast_lane.payload_of(log).strip() == '{"k": 1}'


def test_substitute_leaves_unknown_braces_alone():
    """Regression : `str.format` aurait leve KeyError sur ces trois formes.

    Aucune n'est dans le registre pilote ; toutes apparaitront quand il
    grossira (filtre jq, quantificateur regex, litteral JSON). L'echec serait
    une panne d'infrastructure que le log rendrait indiscernable d'un verdict.
    """
    ctx = {"pr_number": "42", "base_ref": "origin/main"}
    argv = ['.workflow_runs[] | {n: .name}', 'a{2,3}b', '{"k": 1}',
            '--pr', '{pr_number}']
    assert fast_lane.substitute(argv, ctx) == [
        '.workflow_runs[] | {n: .name}', 'a{2,3}b', '{"k": 1}', '--pr', '42']


def test_run_argv_reports_timeout_as_a_verdict_not_an_exception(monkeypatch):
    monkeypatch.setattr(fast_lane, "GUARD_TIMEOUT_S", 1)
    rc, log = fast_lane.run_argv(
        [sys.executable, "-c", "import time; time.sleep(30)"], {})
    assert rc == 124
    assert "delai depasse" in log


# ---------------------------------------------------------------------------
# 5. Verification de restauration d'arbre
# ---------------------------------------------------------------------------

def test_tree_is_clean_detects_a_dirty_path(tmp_path, monkeypatch):
    subprocess.run(["git", "init", "-q", str(tmp_path)], check=True)
    (tmp_path / "f.txt").write_text("un", encoding="utf-8")
    subprocess.run(["git", "-C", str(tmp_path), "add", "f.txt"], check=True)
    subprocess.run(["git", "-C", str(tmp_path), "-c", "user.email=t@t",
                    "-c", "user.name=t", "commit", "-qm", "init"], check=True)
    monkeypatch.setattr(fast_lane, "REPO_ROOT", tmp_path)

    clean, dirt = fast_lane.tree_is_clean(["f.txt"])
    assert clean is True and dirt == ""

    (tmp_path / "f.txt").write_text("deux", encoding="utf-8")
    clean, dirt = fast_lane.tree_is_clean(["f.txt"])
    assert clean is False
    assert "f.txt" in dirt


# ---------------------------------------------------------------------------
# 6. Emission
# ---------------------------------------------------------------------------

def test_dry_run_publishes_nothing(capsys, monkeypatch):
    def explode(*a, **k):  # pragma: no cover - doit rester non appele
        raise AssertionError("aucun appel reseau ne doit avoir lieu a blanc")
    monkeypatch.setattr(subprocess, "run", explode)
    fast_lane.emit_check_run("o/r", "sha", "n", "success", "t", "s",
                             dry_run=True)
    assert "a-blanc" in capsys.readouterr().out


def test_summary_is_truncated_below_the_api_limit(monkeypatch):
    captured = {}

    class Fake:
        returncode = 0
        stdout = ""
        stderr = ""

    def fake_run(cmd, **kwargs):
        captured["payload"] = kwargs.get("input", "")
        return Fake()

    monkeypatch.setattr(subprocess, "run", fake_run)
    fast_lane.emit_check_run("o/r", "sha", "n", "success", "t", "x" * 200000,
                             dry_run=False)
    assert len(captured["payload"]) < 70000


# ---------------------------------------------------------------------------
# 5. Bascule rename-safe : purge des additions fantomes
# ---------------------------------------------------------------------------

def test_stale_added_paths_extrait_les_additions_staged():
    porcelain = (
        "A  MyIA.AI.Notebooks/GameTheory/GameTheory-1-Setup.ipynb\n"
        "A  MyIA.AI.Notebooks/GameTheory/GameTheory-2-NormalForm.ipynb\n"
        "?? .fast-lane-tmp/ecrit-par-un-garde.json\n"
        "M  scripts/ci/fast_lane.py\n"
    )
    assert fast_lane.stale_added_paths(porcelain) == [
        "MyIA.AI.Notebooks/GameTheory/GameTheory-1-Setup.ipynb",
        "MyIA.AI.Notebooks/GameTheory/GameTheory-2-NormalForm.ipynb",
    ]


def test_stale_added_paths_dequote_les_chemins_porcelain():
    # porcelain C-quotte les chemins avec caracteres speciaux
    porcelain = 'A  "MyIA.AI.Notebooks/GenAI/fig\303\251e.png"\n'
    assert fast_lane.stale_added_paths(porcelain) == [
        "MyIA.AI.Notebooks/GenAI/fig\303\251e.png"]


def test_stale_added_paths_vide_sur_arbre_propre():
    assert fast_lane.stale_added_paths("") == []


def test_bascule_rename_safe_sur_mini_depot(tmp_path):
    """Le cas exact de la PR zero-pad : base contient l'ancien nom, HEAD le
    nouveau. Deux bascules laissaient l'ancien en addition staged ; la purge
    doit restaurer l'arbre exact de HEAD."""
    def g(*args):
        return subprocess.run(["git", *args], cwd=tmp_path,
                              capture_output=True, text=True)
    g("init", "-q", ".")
    g("config", "user.email", "t@example.com")
    g("config", "user.name", "t")
    (tmp_path / "dir").mkdir()
    (tmp_path / "dir" / "old-name.txt").write_text("v1", encoding="utf-8")
    g("add", "-A")
    g("commit", "-qm", "base: old-name")
    base_sha = g("rev-parse", "HEAD").stdout.strip()
    (tmp_path / "dir" / "old-name.txt").rename(tmp_path / "dir" / "new-name.txt")
    g("add", "-A")
    g("commit", "-qm", "head: renamed")
    # -- bascule puis restauration, comme en phase 2 ----------------------
    assert g("checkout", base_sha, "--", "dir").returncode == 0
    assert g("checkout", "HEAD", "--", "dir").returncode == 0
    st = g("status", "--porcelain", "--", "dir")
    stale = fast_lane.stale_added_paths(st.stdout)
    assert stale == ["dir/old-name.txt"], (
        "le fantome doit etre detecte ; sans lui la bascule n'est pas "
        "rename-safe")
    assert g("rm", "-fq", "--", *stale).returncode == 0
    clean, dirt = fast_lane.tree_is_clean(["dir"]) if hasattr(
        fast_lane, "tree_is_clean") else (None, None)
    # tree_is_clean est bien expose : l'arbre doit etre revenu exact
    assert (tmp_path / "dir" / "new-name.txt").exists()
    assert not (tmp_path / "dir" / "old-name.txt").exists()
    assert clean is True, dirt


# ---------------------------------------------------------------------------
# 5. Tranche 1 d'absorption (#12567) -- mode mixte ombre/canonique
# ---------------------------------------------------------------------------

def test_tranche1_guards_are_absorbed_and_pilot_is_not():
    """Le flag `absorbed` est le contrat de la tranche : un garde absorbe
    rend son verdict sous son nom canonique (donc rougissant), un garde du
    pilote reste en observation. Si les deux lots se melangent, soit le
    pilote bloque sans preuve de comparaison, soit la tranche absorbee est
    neutralisee et son garde d'origine parti sans remplacement."""
    assert TRANCHE1, "la tranche 1 est vide : ce test n'exerce plus rien"
    for guard in TRANCHE1:
        assert guard.absorbed, f"{guard.name} doit porter absorbed=True"
    for guard in PILOT:
        assert not guard.absorbed, (
            f"{guard.name} est un garde PILOT : il reste en ombre jusqu'a "
            "la conclusion de la comparaison")


def test_absorbed_workflows_no_longer_trigger_on_pull_request():
    """Chaque garde absorbe voit son workflow d'origine retire du
    declenchement `pull_request` -- sinon le garde tourne deux fois (une
    fois canonique par la voie rapide, une fois par son workflow) et la
    mutualisation ne sauuche aucun run. Verification textuelle ancre'e :
    `pull_request:` en debut d'indentation sous `on:`."""
    import re as _re
    for guard in TRANCHE1:
        wf = WORKFLOWS / guard.source
        assert wf.is_file(), f"{guard.source} absent du depot"
        txt = wf.read_text(encoding="utf-8")
        assert not _re.search(r"^\s+pull_request:", txt, _re.M), (
            f"{guard.source} declenche encore sur pull_request alors que "
            f"{guard.name} est absorbe : double execution + zero run sauve")


def _drive_mixed_emission(monkeypatch, pilot_rc, tranche_rc):
    """Fait tourner main() en mode ombre avec un garde pilote et un garde
    absorbe, tous deux en echec, et capture les check-runs publies."""
    import fast_lane as fl
    pilot = Guard(name="pilote-bloquant", argv=["cmd-pilote"], source="s",
                  blocking=True)
    tranche = Guard(name="canonique-bloquant", argv=["cmd-tranche"], source="s",
                    blocking=True, paths=["**/*.ipynb"], absorbed=True)
    monkeypatch.setattr(fl, "PILOT", [pilot])
    monkeypatch.setattr(fl, "TRANCHE1", [tranche])
    monkeypatch.setattr(fl, "changed_files", lambda _ref: ["x.ipynb"])
    monkeypatch.setattr(
        fl, "run_argv",
        lambda argv, ctx: (tranche_rc if argv == ["cmd-tranche"]
                           else pilot_rc, "sortie"))
    monkeypatch.setattr(fl, "run_iter", lambda a, p, c: (0, ""))
    monkeypatch.setattr(
        fl, "git",
        lambda *a: subprocess.CompletedProcess(a, 0, "sha", ""))
    published = []
    monkeypatch.setattr(fl, "emit_check_run",
                        lambda *a, **k: published.append(a))
    rc = fl.main(["--shadow", "--base-sha", "abc"])
    return rc, published


def test_mixed_emission_absorbed_is_canonical_and_blocking(monkeypatch):
    """Le coeur du basculement #12567 : dans une lane qui tourne en ombre,
    un garde absorbe en echec rend (a) son nom SANS prefixe ombre, (b) une
    conclusion `failure` non neutralisee, (c) fait rougir le job -- sinon la
    voie rapide publierait des verdicts que personne ne peut voir."""
    rc, published = _drive_mixed_emission(monkeypatch, pilot_rc=1,
                                          tranche_rc=1)
    by_name = {args[2]: args for args in published}
    assert "canonique-bloquant" in by_name, (
        "le garde absorbe doit porter son nom exact, sans prefixe ombre")
    assert by_name["canonique-bloquant"][3] == "failure", (
        "un bloquant absorbe en echec doit rendre failure, pas neutral")
    assert rc == 1, (
        "l'echec d'un garde absorbe doit faire rougir le job de la voie "
        "rapide -- sinon le verdict existe mais rien ne bloque")


def test_mixed_emission_pilot_stays_shadowed_and_non_blocking(monkeypatch):
    """Contraste : dans la MEME lane, le garde pilote en echec reste prefixe,
    neutralise, et ne fait pas rougir le job -- la comparaison ombre n'est
    pas conclue et ne doit pas se mettre a bloquer par effet de bord."""
    rc, published = _drive_mixed_emission(monkeypatch, pilot_rc=1,
                                          tranche_rc=0)
    names = {args[2] for args in published}
    ombre = [n for n in names if n.startswith(fast_lane.SHADOW_PREFIX)]
    assert any("pilote-bloquant" in n for n in ombre), (
        "le garde pilote doit rester sous prefixe ombre")
    for args in published:
        if "pilote-bloquant" in args[2]:
            assert args[3] == "neutral", (
                "le pilote en echec doit rester neutralise")
    assert rc == 0, (
        "un echec purement ombre ne doit pas rougir le job")
