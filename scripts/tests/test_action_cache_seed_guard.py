#!/usr/bin/env python3
"""Le cache d'archives d'actions reste aligne sur les workflows (#14853, A1).

Ce que ce fichier garde
-----------------------
`seed_action_cache.py` embarque dans l'image runner les archives des actions
que les workflows du depot utilisent. La liste est ecrite **en dur** -- elle doit
l'etre, puisqu'un build ne peut pas lire un fichier qui n'existe pas encore.
Le risque est donc le trou silencieux : un workflow ajoute
`uses: actions/foo@v1`, personne ne touche la liste, et ce job continue de
telecharger son archive a la volee, donc de tomber sur le debit degrade de
codeload.

Ce test fait donc la seule chose qui ferme ce trou : il **rejoue la mesure** sur
`.github/workflows/*.yml` et compare l'ensemble obtenu a `ACTIONS`.

Le scanner se valide par ses faux negatifs ET par ses faux positifs
------------------------------------------------------------------
Un motif de detection ne se valide pas par ses hits. Les deux pieges mesures
ici, chacun avec son test :

- **la negation du mot** : `# uses: actions/checkout@v4` dans un commentaire
  n'est pas une action utilisee. Un scanner qui cherche `uses:` dans la ligne
  la compte ;
- **la meme action sous un sous-chemin** : `github/codeql-action/init@v4` et
  `.../analyze@v4` sont deux entrees `uses:` mais **un seul** depot a cacher.
  Le compte brut (13 entrees) n'est pas le compte des archives (11 depots).
"""

import os
import re
import sys
import tarfile

sys.path.insert(0, os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
    "scripts", "ci", "docker", "linux-runner"))

from seed_action_cache import (  # noqa: E402
    ACTIONS, SeedError, cache_archive_path, cache_dir_name, find_ref_conflicts,
    parse_uses, verify_archive,
)

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
WORKFLOWS = os.path.join(ROOT, ".github", "workflows")

# `uses:` doit ouvrir la ligne ou suivre un tiret de liste (`- uses:`), et la
# valeur doit avoir la forme d'une reference d'action : `owner/repo[...]@ref`,
# `./chemin`, ou `docker://image`. Un `# uses:` commente ne matche ni l'une ni
# l'autre forme. Le filtre de forme evite d'attraper une ligne `uses: ...` qui
# serait de la prose dans un bloc scalaire.
_USES_RE = re.compile(
    r"^[ \t]*(?:-[ \t]+)?uses:[ \t]*"
    r"(?P<value>(?:[A-Za-z0-9._-]+/[A-Za-z0-9._/-]+@[^ \t#\r\n]+)"
    r"|(?:\./[^ \t#\r\n]+)"
    r"|(?:docker://[^ \t#\r\n]+))"
)


def scan_workflow_actions(workflows_dir: str = WORKFLOWS) -> set[str]:
    """Actions distantes reellement utilisees par les workflows du depot.

    Exclut ce que le cache d'archives ne couvre pas : chemins locaux (`./...`),
    actions `docker://`, et les workflows reutilisables de CE depot
    (`jsboige/CoursIA/...`) que GitHub sert directement.
    """
    found: set[str] = set()
    for name in sorted(os.listdir(workflows_dir)):
        if not name.endswith((".yml", ".yaml")):
            continue
        with open(os.path.join(workflows_dir, name), encoding="utf-8") as fh:
            for line in fh:
                m = _USES_RE.match(line)
                if not m:
                    continue
                value = m.group("value")
                if value.startswith(("./", "docker://")):
                    continue
                if value.startswith("jsboige/CoursIA/"):
                    continue
                found.add(value)
    return found


def test_seed_list_matches_workflows_exactly():
    """Le trou silencieux : une action de workflow absente de `ACTIONS`."""
    declared = set(ACTIONS)
    used = scan_workflow_actions()
    manquantes = sorted(used - declared)
    obsoletes = sorted(declared - used)
    assert not manquantes, (
        f"action(s) utilisee(s) par un workflow mais ABSENTE(s) du cache "
        f"d'archives {manquantes} -- ce job continuera de telecharger son "
        f"archive a la volee (#14853, A1)"
    )
    assert not obsoletes, (
        f"entree(s) de cache sans workflow qui l'utilise {obsoletes} -- "
        f"l'image embarquerait une archive morte"
    )


def test_scanner_ignores_commented_uses():
    """La negation du mot : un `# uses:` commente n'est pas une action."""
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        with open(os.path.join(tmp, "w.yml"), "w", encoding="utf-8") as fh:
            fh.write("steps:\n"
                     "  # uses: actions/commented-out@v1\n"
                     "  - uses: actions/checkout@v4\n")
        assert scan_workflow_actions(tmp) == {"actions/checkout@v4"}


def test_scanner_excludes_local_docker_and_same_repo():
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        with open(os.path.join(tmp, "w.yml"), "w", encoding="utf-8") as fh:
            fh.write("  - uses: ./local/action\n"
                     "  - uses: docker://alpine:3.20\n"
                     "  - uses: jsboige/CoursIA/.github/workflows/lean-build.yml@main\n"
                     "  - uses: actions/cache@v4\n")
        assert scan_workflow_actions(tmp) == {"actions/cache@v4"}


def test_scanner_reads_inline_comment_stripped_value():
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        with open(os.path.join(tmp, "w.yml"), "w", encoding="utf-8") as fh:
            fh.write("  - uses: actions/setup-python@v5  # cache: pip\n")
        assert scan_workflow_actions(tmp) == {"actions/setup-python@v5"}


def test_scanner_covers_both_yaml_step_forms():
    """Les DEUX formes d'etape portent des actions ; en rater une = trou.

    Mesure du 2026-09-13 : `uses:` aligne sous un `name:` (224 occurrences) et
    la forme en ligne de liste `- uses:` (133 occurrences) coexistent dans le
    corpus. Un motif qui n'en couvre qu'une laisse toute action ecrite dans
    l'autre hors du cache, sans que rien ne rougisse.
    """
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        with open(os.path.join(tmp, "w.yml"), "w", encoding="utf-8") as fh:
            fh.write("      - name: Checkout\n"
                     "        uses: actions/checkout@v4\n"
                     "      - uses: actions/setup-node@v4\n")
        assert scan_workflow_actions(tmp) == {
            "actions/checkout@v4", "actions/setup-node@v4"}


def test_repo_stops_at_two_segments():
    """`ResolvedNameWithOwner` s'arrete au depot, pas au sous-chemin."""
    assert parse_uses("github/codeql-action/init@v4") == ("github/codeql-action", "v4")
    assert parse_uses("actions/checkout@v4") == ("actions/checkout", "v4")


def test_uses_without_ref_is_refused():
    for bad in ("actions/checkout", "actions@v4", "checkout@v4"):
        try:
            parse_uses(bad)
        except SeedError:
            continue
        raise AssertionError(f"{bad!r} aurait du etre refuse")


def test_cache_path_follows_runner_convention():
    """Le chemin doit etre celui que `ActionManager.cs` recalcule au run.

    Convention (runner v2.337.0) : `<cache>/<owner>_<repo>/<sha>.tar.gz`, ou le
    `/` du depot devient `_` et ou la cle est le SHA **resolu**, jamais le tag.
    """
    assert cache_dir_name("actions/setup-python") == "actions_setup-python"
    assert cache_dir_name("github/codeql-action") == "github_codeql-action"
    assert cache_archive_path("/c", "actions/setup-python", "a" * 40) == \
        os.path.join("/c", "actions_setup-python", "a" * 40 + ".tar.gz")


def test_verify_archive_accepts_single_root_and_refuses_many():
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        good = os.path.join(tmp, "good.tar.gz")
        with tarfile.open(good, "w:gz") as tf:
            for name in ("setup-python-abc/action.yml", "setup-python-abc/dist/index.js"):
                p = os.path.join(tmp, name)
                os.makedirs(os.path.dirname(p), exist_ok=True)
                with open(p, "w", encoding="utf-8") as fh:
                    fh.write("x")
                tf.add(p, arcname=name)
        verify_archive(good, "actions/setup-python")

        bad = os.path.join(tmp, "bad.tar.gz")
        with tarfile.open(bad, "w:gz") as tf:
            for name in ("root-a/action.yml", "root-b/action.yml"):
                p = os.path.join(tmp, name)
                os.makedirs(os.path.dirname(p), exist_ok=True)
                with open(p, "w", encoding="utf-8") as fh:
                    fh.write("x")
                tf.add(p, arcname=name)
        try:
            verify_archive(bad, "actions/composite")
        except SeedError:
            pass
        else:
            raise AssertionError("une archive a deux racines aurait du etre refusee")


def test_truncated_archive_is_refused():
    """Une archive tronquee par un debit degrade ne doit pas passer le build."""
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "trunc.tar.gz")
        with open(path, "wb") as fh:
            fh.write(b"\x1f\x8b\x08\x00tronque")
        try:
            verify_archive(path, "actions/checkout")
        except SeedError:
            return
        raise AssertionError("une archive illisible aurait du etre refusee")


def test_same_repo_under_two_refs_is_refused():
    """Deux refs pour un depot = deux cles dont une seule sera lue."""
    conflicted, messages = find_ref_conflicts(
        ("actions/checkout@v4", "actions/checkout@v5"))
    assert conflicted == {"actions/checkout"}
    assert len(messages) == 1

    conflicted_ok, messages_ok = find_ref_conflicts(
        ("github/codeql-action/init@v4", "github/codeql-action/analyze@v4"))
    assert conflicted_ok == set(), (
        "deux sous-chemins du MEME depot sous la meme ref ne sont pas un "
        "conflit : ils partagent une seule archive de cache"
    )
    assert messages_ok == []
