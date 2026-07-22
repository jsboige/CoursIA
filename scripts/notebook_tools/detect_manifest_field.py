"""detect_manifest_field - enforce that changed MANIFEST.md files include the
``description_visuelle`` field per image entry.

EPIC #5654 (figures README, doctrine #5780 amendée). Le champ
``description_visuelle`` est obligatoire depuis le PR #7771 (extract_readme_figures.py
enforce le champ côté code). Ce detecteur étend l'enforcement aux MANIFEST.md
**modifiés** dans une PR : tout nouveau contenu de MANIFEST doit déclarer le champ
``description_visuelle`` par figure.

**Distinction stricte** (doctrine #5780 + PR #7774 L733) :

- **description_visuelle** = ce que la figure MONTRE reellement, observé
  visuellement (type de graphique, axes, couleurs distinctives, disposition).
  Champ distinct du sujet du notebook source.
- **alt_text_fr** = accessibilité, court et fonctionnel (ex: "Carte de chaleur
  des poids du réseau"), ne se confond pas avec description_visuelle.

**Mode d'emploi** :

- ``python detect_manifest_field.py --check <path>`` → exit 0 si conforme,
  exit 1 sinon (utilisable dans CI pre-merge).
- ``python detect_manifest_field.py <path>`` → exit 0 toujours (informatif).

**Scope** : diff-scopé. Les MANIFEST.md existants sans le champ sont
GRANDFATHERED (ne sont pas en violation jusqu'à leur prochaine modification,
exactement comme `degenerate-figure-gate.yml` grandfathered les 8 quantbooks
QC #6891). Ce detecteur ne s'applique qu'aux MANIFEST.md modifiés.

**Format canonique d'une entrée** (cf ``extract_readme_figures.py::_append_manifest``) :

::

    ##  <filename>.png

    - **Source** : notebook `<relpath>` (cellule N, output M)
    - **Description visuelle** : <description_visuelle>  # OBLIGATOIRE
    - **Alt-text (FR)** : <alt_text_fr>
    - **Poids** : NN KB (PIL optimise / raw)

**Heuristique de comptage** : un MANIFEST.md conforme a un nombre de sections
``## <filename>.png`` egal au nombre de sections ``### <filename>.png``
(legacy) OU un nombre d'occurrences ``- **Description visuelle** :`` egal
au nombre de ``## .*\\.png`` OU ``### .*\\.png``. En cas de mix, on exige
que TOUTES les figures declarees soient conformes.

Triage sortie :
- exit 0 : clean
- exit 1 : champ manquant pour au moins une figure
- exit 2 : MANIFEST illisible (rc=2 = warning, pas FAIL)
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# Header level for a figure section: either `## filename.png` (canonical post-#7771)
# or `### filename.png` (legacy v1/v2).
FIGURE_HEADER_RE = re.compile(r"^(#{2,3})\s+(?P<fname>[^\s]+\.png)\s*$")
# Field marker, matches `- **Description visuelle** :` (FR canonical) and tolerant
# variants like `**Description visuelle** :` (sans tiret).
DESCRIPTION_FIELD_RE = re.compile(
    r"^\s*-\s*\*\*Description visuelle\*\*\s*:|^\s*\*\*Description visuelle\*\*\s*:",
    re.IGNORECASE,
)


def check_manifest(path: Path) -> int:
    """Return 0 if ``path`` is a conforming MANIFEST, 1 if a figure lacks
    ``description_visuelle``, 2 if file is unreadable."""
    if not path.is_file():
        print(f"detect_manifest_field: {path} missing", file=sys.stderr)
        return 2
    text = path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()

    # Index of figure section headers
    figure_sections: list[tuple[str, int]] = []
    for idx, line in enumerate(lines):
        m = FIGURE_HEADER_RE.match(line)
        if m:
            figure_sections.append((m.group("fname"), idx))

    if not figure_sections:
        # MANIFEST exists but no figure sections: structurally degenerate
        # (could be a new MANIFEST awaiting entries). Caller policy.
        print(
            f"::notice title=Manifest validator::{path} declares no figure section "
            f"(## / ### <filename>.png). Skipping."
        )
        return 0

    # For each figure header, scan from that line until the next header
    # (any `#` heading of level <= current). Inside that block, do we see a
    # `**Description visuelle** :` field?
    missing: list[str] = []
    for i, (fname, start) in enumerate(figure_sections):
        block_end = figure_sections[i + 1][1] if i + 1 < len(figure_sections) else len(lines)
        block = lines[start + 1 : block_end]
        has_field = any(DESCRIPTION_FIELD_RE.match(line) for line in block)
        if not has_field:
            missing.append(fname)

    if missing:
        print(
            f"::error title=Manifest validator::{path} declares "
            f"{len(missing)} figure(s) without `Description visuelle` field: "
            f"{', '.join(missing)}"
        )
        return 1

    print(
        f"::notice title=Manifest validator::{path} - {len(figure_sections)} "
        f"figure(s) checked, all declare `Description visuelle`."
    )
    return 0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument(
        "path",
        nargs="?",
        default=".",
        help="path to a MANIFEST.md (or a directory to scan recursively).",
    )
    p.add_argument(
        "--check",
        action="store_true",
        help="exit non-zero on defect (default: still informative but exit 0).",
    )
    args = p.parse_args(argv)

    target = Path(args.path)
    if target.is_dir():
        manifests = sorted(target.rglob("MANIFEST.md"))
    elif target.is_file():
        manifests = [target]
    else:
        print(f"detect_manifest_field: {target} not found.", file=sys.stderr)
        return 2

    if not manifests:
        print(f"::notice title=Manifest validator::No MANIFEST.md under {target}.")
        return 0

    fail = 0
    checked = 0
    for mpath in manifests:
        # Only assets/readme/MANIFEST.md is in scope (doctrine #5654)
        if "/assets/readme/MANIFEST.md" not in str(mpath).replace("\\", "/"):
            continue
        checked += 1
        rc = check_manifest(mpath)
        if rc == 1:
            fail += 1

    print(
        f"::notice title=Manifest validator::Checked {checked} MANIFEST.md "
        f"file(s); {fail} defect(s)."
    )
    return fail if args.check else 0


if __name__ == "__main__":
    sys.exit(main())
