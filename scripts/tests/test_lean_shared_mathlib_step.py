#!/usr/bin/env python3
"""Le lien vers la source Mathlib partagee cree son parent avant de le poser (#27727).

Tranche 2 du cache source Mathlib (#27826) : quand le staging partage est un
HIT verifie au rev du manifeste, le step « Use the shared Mathlib source »
remplace la copie par un lien ``ln -sfn`` dans ``.lake/packages``. Or ``lake``
ne cree ce repertoire qu'en restaurant l'archive ``.lake`` de CE lac : sur un
miss de cache -- le cas courant d'une PR -- il n'existe pas encore, et ``ln``
echoue faute de parent. Mesure du 2026-11-25 sur la tete ``3bcec87a55b`` :
trente jambes ``lean-matrix`` rouges d'un coup, toutes au meme step, et le
message ``ln: failed to create symbolic link '.lake/packages/mathlib'``
verifie sur quatre d'entre elles -- y compris sur des lacs que la PR ne
touchait pas.

Ce test pin le correctif et sa TRIPLICATION : le step vit en trois copies
(l'action composite et les deux workflows autonomes qui ne l'appellent pas).
Une copie oubliee rouvrirait le defaut sur la jambe qu'elle sert, et une
quatrieme copie hors ``.github`` echapperait au garde sans qu'on le voie.
"""
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
COPIES = (
    REPO / ".github" / "actions" / "lean-build" / "action.yml",
    REPO / ".github" / "workflows" / "lean-build.yml",
    REPO / ".github" / "workflows" / "lean-axiom.yml",
)
LINK = 'ln -sfn "$RUNNER_TEMP/mathlib-src" .lake/packages/mathlib'
MKDIR = "mkdir -p .lake/packages"
ANCHOR = 'WANT_REV="${{ steps.mathlib-rev.outputs.rev }}"'


def test_every_copy_creates_the_packages_dir_before_linking():
    for copy in COPIES:
        text = copy.read_text(encoding="utf-8")
        assert text.count(LINK) == 1, f"{copy}: le lien doit y etre exactement une fois"
        preamble = text[: text.index(LINK)]
        assert MKDIR in preamble, f"{copy}: parent absent avant le lien"
        assert preamble.rindex(MKDIR) > preamble.rindex(ANCHOR), (
            f"{copy}: le mkdir doit vivre dans le meme step que le lien"
        )


def test_no_fourth_copy_escapes_the_guard():
    found = set()
    for pattern in ("*.yml", "*.yaml"):
        for path in (REPO / ".github").rglob(pattern):
            if LINK in path.read_text(encoding="utf-8", errors="replace"):
                found.add(path)
    assert found == set(COPIES), sorted(str(path.relative_to(REPO)) for path in found)