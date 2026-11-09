"""Import de `candidate_delivered` depuis un checkout REDUIT au sparse-checkout (#23762).

Panne fondatrice : du 29/10 au 01/11, les 4 runs planifies de
`candidate-delivered-advisory` mouraient sur `ModuleNotFoundError: No module
named 'pick_idle_grain'` -- le fichier n'etait pas dans le sparse-checkout, et
l'ajouter n'aurait pas suffi : il tire `series_saturation`, `grain_tag` et
`gh_payload_cache` au niveau module (commentaire #23762 c.6564437892). Le
predicat a donc ete extrait dans `released_covers`, importable seul.

Ce test REPRODUIT la condition de la panne : il copie dans un repertoire
temporaire EXACTEMENT les fichiers declares dans le sparse-checkout du
workflow, ni un de plus ni un de moins, et importe `candidate_delivered`
depuis la. Toute dependance nouvelle ajoutee a `candidate_delivered` ou a
`released_covers` casse ce test AVANT de casser le cron -- c'est un filet sur
l'incident, pas une preuve ponctuelle.

La liste des fichiers ne se recopie pas a la main : elle se LIT dans le
workflow, au sein du bloc `sparse-checkout:`. Si le workflow gagne un fichier,
ce test le suit ; s'il en perd un, le test le suit aussi. Un drift entre les
deux ne peut donc plus naitre ici.
"""

import re
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
WORKFLOW = REPO / ".github" / "workflows" / "candidate-delivered-advisory.yml"


def sparse_checkout_files():
    """Les chemins du bloc `sparse-checkout:` du workflow, lus a la source."""
    text = WORKFLOW.read_text(encoding="utf-8")
    match = re.search(
        r"^([ \t]*)sparse-checkout:\s*\|\s*\n((?:\1[ \t]+\S.*\n?)+)",
        text,
        re.MULTILINE,
    )
    assert match, "bloc sparse-checkout introuvable dans le workflow"
    indent = match.group(1) + "  "
    entries = []
    for line in match.group(2).splitlines():
        if line.startswith(indent) and line.strip():
            entries.append(line.strip())
    assert entries, "sparse-checkout vide"
    return entries


def test_le_workflow_declare_les_quatre_fichiers_attendus():
    files = sparse_checkout_files()
    for required in (
        "scripts/candidate_delivered.py",
        "scripts/issue_containers.py",
        "scripts/released_covers.py",
    ):
        assert required in files, f"{required} absent du sparse-checkout"


def test_import_depuis_le_seul_sparse_checkout():
    """Le module du balayage s'importe depuis exactement les fichiers embarques."""
    files = sparse_checkout_files()
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        for rel in files:
            if rel.endswith(".py"):
                target = root / rel
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((REPO / rel).read_bytes())
        # Aucun autre fichier du depot n'est visible : ni pick_idle_grain, ni
        # series_saturation, ni grain_tag, ni gh_payload_cache. C'est la
        # condition exacte du job CI.
        sys.path.insert(0, str(root / "scripts"))
        try:
            for banned in ("pick_idle_grain", "series_saturation",
                           "grain_tag", "gh_payload_cache"):
                sys.modules.pop(banned, None)
            import candidate_delivered  # noqa: F401

            assert not any(
                name in sys.modules
                for name in ("pick_idle_grain", "series_saturation",
                             "grain_tag", "gh_payload_cache")
            ), "candidate_delivered a tire un module hors sparse-checkout"

            verdict = candidate_delivered._released_covers_acceptance(
                "[RELEASED] lane x -- acceptance deja couverte, rien a reparer"
            )
            assert verdict is True
        finally:
            sys.path.remove(str(root / "scripts"))
            sys.modules.pop("candidate_delivered", None)
            sys.modules.pop("issue_containers", None)
            sys.modules.pop("released_covers", None)
