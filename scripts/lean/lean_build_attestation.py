"""Format canonique de l'attestation de `lake build` local (garde Lean, #24989).

Un **seul** module porte le format : l'organe qui ECRIT
(`scripts/lean/attest_local_build.py`) et la garde qui LIT
(`scripts/coordination/merge_ready.py`) ne peuvent pas diverger en silence.
Regle d'organe : celui qui produit n'ecrit jamais son propre format, il
l'importe.

Contrat de l'attestation
-------------------------
- c'est un **commentaire de PR** (issue comment), pas une voix de review :
  l'attestation n'est ni une approbation ni une reserve, c'est une preuve ;
- son auteur est `myia-ai-01` -- l'attestation est un acte du **coordinateur**,
  la lane qui a produit la PR ne s'atteste pas elle-meme ;
- sa **premiere ligne non vide** est exactement ``[ACTION] lake build local`` ;
- le SHA atteste est porte par le champ etiquete ``tete: <40 hex>`` ;
- elle cite les **lakes** construits et le **nombre de jobs**.

Pourquoi le SHA est lu dans un champ etiquete et non « le premier 40-hex du
corps » : une attestation qui cite un autre SHA en prose (le SHA d'une base,
d'un commit de merge) ne doit pas etre lue comme une attestation de la tete.
Le champ etiquete est le seul point ou le redacteur place le SHA atteste.

La couverture de tete (une attestation posee sur une tete anterieure survit a
un rafraichissement de base PROUVE content-free, mais perime a un commit de
contenu) n'est PAS decidee ici : elle vit dans la garde, qui reutilise la
remontee first-parent du plancher DWELL -- la meme primitive que la couverture
de l'APPROVE du coordinateur.
"""

from __future__ import annotations

import re

#: Premiere ligne non vide que doit porter un commentaire d'attestation.
ATTESTATION_TAG = "[ACTION] lake build local"

#: Login du seul auteur d'une attestation valide (le coordinateur ai-01).
ATTESTATION_AUTHOR = "myia-ai-01"

#: Motif du SHA atteste : 40 hex, le SHA complet d'un commit.
SHA_RE = re.compile(r"\b([0-9a-f]{40})\b")

#: Champ etiquete qui porte le SHA atteste.
_HEAD_FIELD_RE = re.compile(r"^tete\s*:\s*([0-9a-f]{40})\s*$", re.MULTILINE)

#: Champ etiquete qui porte les lakes construits.
_LAKES_FIELD_RE = re.compile(r"^lakes?\s*:\s*(.+)$", re.MULTILINE)

#: Champ etiquete qui porte le nombre de jobs.
_JOBS_FIELD_RE = re.compile(r"^jobs\s*:\s*(\d+)\s*$", re.MULTILINE)

#: Fichiers dont la presence dans un diff rend la PR soumise a la garde Lean.
#: `lakefile.*` couvre `lakefile.lean` et `lakefile.toml` ; les deux fichiers
#: d'outillage (`lean-toolchain`, `lake-manifest.json`) sont eux aussi
#: bloquants : changer la toolchain ou le graphe de dependances change ce que
#: le build doit prouver.
LEAN_TOOLCHAIN_FILES = ("lean-toolchain", "lake-manifest.json")


def is_lean_path(path: str) -> bool:
    """Vrai si le chemin touche le build Lean (source, lake, ou outillage).

    Un `*.lean` n'importe ou qu'il soit : la preuve porte sur le module
    compile, pas sur le repertoire qui le contient.
    """
    if not path:
        return False
    name = path.replace("\\", "/").rsplit("/", 1)[-1]
    if name.endswith(".lean"):
        return True
    if name.startswith("lakefile."):
        return True
    return name in LEAN_TOOLCHAIN_FILES


def lean_paths(paths) -> list[str]:
    """Les chemins Lean d'un diff, dans l'ordre du diff."""
    out: list[str] = []
    for path in paths or []:
        text = str(path or "")
        if is_lean_path(text):
            out.append(text)
    return out


def first_line(body: str) -> str:
    """Premiere ligne non vide d'un corps de commentaire."""
    for line in str(body or "").splitlines():
        if line.strip():
            return line.strip()
    return ""


def parse_attestation(body: str) -> dict | None:
    """Attestation contenue dans un corps de commentaire, ou None.

    Retourne ``{"sha": ..., "lakes": [...], "jobs": int | None}`` quand le
    corps porte le tag en premiere ligne non vide ET un champ `tete:` a 40
    hex. Le SHA est pris dans le champ etiquete ; a defaut de champ, aucun
    SHA n'est lu ailleurs dans le corps (cf. docstring du module).
    """
    if first_line(body) != ATTESTATION_TAG:
        return None
    match = _HEAD_FIELD_RE.search(str(body or ""))
    if not match:
        return None
    lakes: list[str] = []
    lakes_match = _LAKES_FIELD_RE.search(str(body or ""))
    if lakes_match:
        lakes = [
            part.strip()
            for part in lakes_match.group(1).split(",")
            if part.strip()
        ]
    jobs_match = _JOBS_FIELD_RE.search(str(body or ""))
    jobs = int(jobs_match.group(1)) if jobs_match else None
    return {"sha": match.group(1), "lakes": lakes, "jobs": jobs}


def _comment_author(comment: dict) -> str:
    author = comment.get("author") or {}
    if isinstance(author, dict):
        return str(author.get("login") or "")
    return str(author or "")


def attestation_from_comments(comments) -> dict | None:
    """Attestation la plus recente d'une liste de commentaires de PR, ou None.

    Seuls les commentaires d'un `myia-ai-01` sont lus : une attestation posee
    par une autre lane ne vaut rien. Entre deux attestations valides, la plus
    **recente** gagne -- une attestation posterieure sur une tete anterieure
    est donc la seule qui compte (une attestation perimee ne « repousse » pas
    une attestation plus recente en arriere : l'ordre est celui du serveur,
    `createdAt`).

    La forme des commentaires est celle de ``gh pr view --json comments`` :
    ``{"author": {"login": ...}, "body": ..., "createdAt": ...}``.
    """
    rows = []
    for comment in comments or []:
        if not isinstance(comment, dict):
            continue
        if _comment_author(comment) != ATTESTATION_AUTHOR:
            continue
        parsed = parse_attestation(str(comment.get("body") or ""))
        if parsed is None:
            continue
        rows.append((str(comment.get("createdAt") or ""), parsed))
    if not rows:
        return None
    rows.sort(key=lambda row: row[0])
    return rows[-1][1]


def render_attestation(
    *,
    sha: str,
    lakes,
    jobs: int | None,
    pr: int | None = None,
    duration_s: float | None = None,
    extra: str | None = None,
) -> str:
    """Corps d'un commentaire d'attestation, au format canonique.

    La premiere ligne est le tag : la garde reconnait l'attestation par elle,
    pas par la presence du SHA ailleurs dans le corps.
    """
    lines = [ATTESTATION_TAG, ""]
    if pr is not None:
        lines.append(f"PR #{pr}")
    lines.append(f"tete: {sha}")
    lake_list = [str(item) for item in (lakes or []) if str(item).strip()]
    lines.append("lakes: " + (", ".join(lake_list) if lake_list else "-"))
    if jobs is not None:
        lines.append(f"jobs: {int(jobs)}")
    if duration_s is not None:
        lines.append(f"duree: {round(float(duration_s), 1)}s")
    if extra:
        lines.append("")
        lines.append(str(extra).strip())
    return "\n".join(lines) + "\n"
