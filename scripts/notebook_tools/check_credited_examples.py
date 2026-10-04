#!/usr/bin/env python3
"""Detect perte d'exemples guides credites entre base et tete d'une PR (#18740).

Issue #18740 acceptance: etendre l'organe existant
``scripts/notebook_tools/check_pr_exercises.py`` (qui compare deja base et tete
pour les exercices) pour qu'il compare AUSSI les **exemples guides credites**
sur la base et la tete, et signale toute baisse non declaree.

Convention d'attribution d'un exemple credite (au choix, additive non
intrusive) :
1. Champ metadata cellule : ``cell.metadata.credited_from = "#NNNN"`` (numero
   de PR d'origine), avec header markdown ``### Exemple ...`` ou
   ``### Exemple : <titre>``.
2. OU mention inline dans le body markdown du header Exemple, sur la meme
   ligne ou la suivante : ``[crédité #NNNN]`` ou ``(crédité #NNNN)`` ou
   ``(crédite #NNNN)``.

Empirique : sur le depot, la convention n'est pas encore systematique
(#18740 cite le cas #18585+#18590 ou les 3 exemples credites a #18553 ont
ete supprimes sans trace). L'organe doit donc tolerer les deux formes et
rendre une liste d'identifiants -- pas une stricte regex.

Convention d'exemption (analogue ``plan-loss:`` de #14532) : une baisse est
legitime si elle est declaree dans le body PR par un marker
``exemples-loss: section assumee -- <notebook> section: <titre> : <raison>``
(un par exemple perdu, comme pour plan-loss).

Portee : le script est appele par check_pr_exercises.py -- il n'est pas
un organe CI isole. Il lit un notebook, retourne la liste des exemples
credites, et un comparateur base/head.

Usage:
    python scripts/notebook_tools/check_credited_examples.py NB.ipynb --json
    python scripts/notebook_tools/check_credited_examples.py NB.ipynb --base origin/main --head origin/fix/ma-branche --json
    python scripts/notebook_tools/check_credited_examples.py NB.ipynb --base origin/main --pr-body-file /tmp/body.md --json --check

Sortie JSON: ``{"base": [...], "head": [...], "lost": [{"id": ..., "title": ..., "credit": "..."}], "exempted": [...]}.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable

# Imported lazily to avoid pulling count_exercises unless we need to read a cell.


# --- marqueur d'attribution dans le body markdown -----------------------------
# Strict : on exige SOIT le prefixe "credite"/"crédité" explicite, SOIT le
# caractere '#' colle au numero. "Exemple 2 : autre chose" ne matche PAS --
# un nombre isole dans une phrase n'est pas une attribution PR. Accepte les
# separateurs usuels (crochet, parenthese, virgule, debut de ligne).
_CREDIT_INLINE_RE = re.compile(
    r"""(?ix)
    (?:cr[eé]dit[eé]?\s+)?        # prefixe optionnel "crédité #NN" / "credite #NN"
    \# (?P<num>\d+)                 # numero PR avec '#' obligatoire
    \b                             # frontiere word
    """,
)

# --- marker d'exemption body PR (analogue plan-loss:) -----------------------
# Le format : ``exemples-loss: section assumee -- NB section : TITLE : REASON``.
# TITLE peut contenir des ':' (ex. "## Exemple : truc") -- on capture donc
# en mode "le dernier ': REASON$'" via split logique, pas par regex pure.
_EXEMPTION_LINE_PREFIX_RE = re.compile(
    r"""(?ix)
    ^\s* exemples-loss \s* : \s* section \s+ assum[eé]+(?:e|ée)? \s*
    (?:-- | — ) \s*
    (?P<nb> \S+? ) \s+            # chemin notebook
    section \s* : \s*
    (?P<rest> .+ )                # reste = TITLE : TITRE : ... : REASON
    $ """,
)


def _exemption_markers(pr_body: str) -> list[dict]:
    """Parse les markers ``exemples-loss:`` du body (cf. plan-loss convention).

    Le format canonique : ``exemples-loss: section assumee -- NB section : TITLE : REASON``.
    TITLE peut contenir des ':' -- le dernier ':' est pris comme séparateur de
    REASON, le reste est le titre concatene.
    """
    if not pr_body:
        return []
    out = []
    for ln in pr_body.splitlines():
        m = _EXEMPTION_LINE_PREFIX_RE.match(ln)
        if not m:
            continue
        nb = m.group("nb").strip()
        rest = m.group("rest").strip()
        # split sur le dernier " : "
        if " : " in rest:
            title, reason = rest.rsplit(" : ", 1)
        else:
            title, reason = rest, ""
        out.append({
            "notebook": nb,
            "title": title.strip(),
            "reason": reason.strip(),
            "raw": ln.strip(),
        })
    return out


def _is_example_header(source: str) -> bool:
    """Header markdown qui demarre un exemple (pas un exercice).

    Couvre `### Exemple ...`, `### Exemple : ...`, `## Exemple ...` ainsi
    que les numeros en prefixe (`## 5. Exemple ...`). Tout ce que la regle
    three-exercises compte comme exercice est ici exclu -- un compteur
    qui melange les deux raterait l'objet meme de #18740.
    """
    if not source:
        return False
    lines = source.splitlines()
    for ln in lines:
        stripped = ln.strip()
        if not stripped:
            continue
        # matche ### Exemple ... ou ## 5. Exemple ...
        m = re.match(r"^#{1,6}\s*(?:\d+\.\s*)?[Ee]xemple\b", stripped)
        if m:
            return True
        # tout autre en-tete arrete la recherche -- l'exemple est dans la
        # premiere ligne non-vide d'apres le compteur canonique.
        break
    return False


def _extract_credit(cell: dict) -> str | None:
    """Trouve l'attribution '#NNNN' d'une cellule Exemple (None si absente)."""
    # 1) metadata explicite
    md = cell.get("metadata", {}) or {}
    credited = md.get("credited_from")
    if isinstance(credited, str) and credited.startswith("#") and credited[1:].isdigit():
        return credited
    # 2) inline dans le body markdown
    if cell.get("cell_type") == "markdown":
        src = "".join(cell.get("source", []))
        m = _CREDIT_INLINE_RE.search(src)
        if m:
            return "#" + m.group("num")
    return None


def _cell_title(cell: dict) -> str:
    """Titre normalise d'une cellule markdown (1re ligne non-vide, sans #)."""
    if cell.get("cell_type") != "markdown":
        return ""
    src = "".join(cell.get("source", []))
    for ln in src.splitlines():
        s = ln.strip()
        if not s:
            continue
        # retire le prefixe markdown (#, numero, "Exemple", ":")
        s = re.sub(r"^#+\s*", "", s)
        s = re.sub(r"^\d+\.\s*", "", s)
        s = re.sub(r"^[Ee]xemple\b\s*:?\s*", "", s)
        return s.strip()
    return ""


def _read_nb(path: Path) -> dict:
    """Charge un .ipynb ; raise si non parsable (le caller decide du label)."""
    return json.loads(path.read_text(encoding="utf-8"))


def _read_git_blob(ref: str, nb_path: str) -> Path:
    """Dump le notebook sur la ref git vers un fichier temporaire, retourne le Path.

    Utilise `git show <ref>:<path>`. Le fichier ecrit est un tempfile
    portable (``tempfile.mkstemp``, pas ``Path('/tmp')`` -- ce dernier
    casse sous Windows et n'est pas garanti sous Linux sans $TMPDIR).
    On ne supprime pas le fichier (le caller nettoie s'il veut, on reste
    conservateur).
    """
    import tempfile
    blob = subprocess.check_output(
        ["git", "show", f"{ref}:{nb_path}"],
        stderr=subprocess.PIPE, encoding="utf-8", errors="replace",
    )
    safe = re.sub(r"[^A-Za-z0-9._-]", "_", ref)
    stem = Path(nb_path).stem
    fd, name = tempfile.mkstemp(
        suffix=".ipynb",
        prefix=f"{stem}-{safe}-",
    )
    os.close(fd)
    Path(name).write_text(blob, encoding="utf-8")
    return Path(name)


def _blob_absent_from_ref(ref: str, nb_path: str) -> bool:
    """True UNIQUEMENT pour « chemin absent de la ref » (fichier ajoute).

    ``git cat-file -e`` rend rc 128 pour l'absence de chemin ET pour une
    ref invalide (mesure Windows/Linux git >= 2.40 : « fatal: path 'x'
    does not exist in 'ref' » vs « fatal: invalid object name 'ref'. ») —
    le discriminateur fiable est donc le **message** stderr, pas le code :
    - « does not exist » : absence légitime -> True (zéro exemples de
      base, l'équivalent d'un fichier ajouté) ;
    - tout autre message (ref inconnue/ambiguë, dépôt cassé...) : False,
      et le ``git show`` qui suit échouera **bruyamment** — sans cette
      sonde, toute erreur git était avalée en faux zéro et blanchissait
      une perte réelle d'exemples crédités.
    """
    p = subprocess.run(
        ["git", "cat-file", "-e", f"{ref}:{nb_path}"],
        capture_output=True, encoding="utf-8", errors="replace",
    )
    if p.returncode == 0:
        return False
    return "does not exist" in (p.stderr or "")


def count_credited_examples(nb: dict) -> list[dict]:
    """Liste des cellules Exemple creditees dans un notebook deja parse.

    Retourne ``[{"cell_id": ..., "title": ..., "credit": "#NNNN"}, ...]``.
    """
    out = []
    for c in nb.get("cells", []):
        if c.get("cell_type") != "markdown":
            continue
        src = "".join(c.get("source", []))
        if not _is_example_header(src):
            continue
        credit = _extract_credit(c)
        if credit is None:
            continue
        out.append({
            "cell_id": c.get("id", ""),
            "title": _cell_title(c),
            "credit": credit,
        })
    return out


def diff_examples(base_examples: list[dict], head_examples: list[dict]) -> dict:
    """Compare deux listes et isole les exemples perdus (sans exemption).

    Sortie: ``{"lost": [...], "kept": [...], "added": [...]}``. ``lost``
    contient les exemples presents dans base mais absents de head, tries
    par ``credit`` puis ``cell_id``.
    """
    base_keys = {(e["credit"], e["cell_id"]): e for e in base_examples}
    head_keys = {(e["credit"], e["cell_id"]): e for e in head_examples}
    lost = [base_keys[k] for k in base_keys.keys() - head_keys.keys()]
    added = [head_keys[k] for k in head_keys.keys() - base_keys.keys()]
    kept = [head_keys[k] for k in head_keys.keys() & base_keys.keys()]
    lost.sort(key=lambda e: (e["credit"], e["cell_id"]))
    return {"lost": lost, "added": added, "kept": kept}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Comparateur d'exemples guides credites base vs tete (#18740).",
    )
    parser.add_argument("path", help="Chemin du notebook (relatif a la racine)")
    parser.add_argument("--base", default="origin/main",
                        help="Ref git de la base (defaut origin/main). Vide pour skip base.")
    parser.add_argument("--head", default="",
                        help="Ref git de la tete (defaut: fichier local). Vide pour skip head ref.")
    parser.add_argument("--pr-body-file", default="",
                        help="Chemin vers le body PR (pour lire les exemptions).")
    parser.add_argument("--json", dest="json_out", action="store_true",
                        help="Sortie JSON machine-readable.")
    parser.add_argument("--check", action="store_true",
                        help="Exit 1 si perte non-exemptee detectee.")
    args = parser.parse_args(argv)

    head_nb = _read_nb(Path(args.path))
    head_examples = count_credited_examples(head_nb)

    base_examples: list[dict] = []
    if args.base:
        # chemin absent de la base = fichier ajoute -> 0 legitime ; toute
        # AUTRE erreur git reste bruyante (un faux zero ici blanchirait
        # une perte reelle d'exemples credites).
        if _blob_absent_from_ref(args.base, args.path):
            base_examples = []
        else:
            base_path = _read_git_blob(args.base, args.path)
            base_nb = _read_nb(base_path)
            base_examples = count_credited_examples(base_nb)

    # Si --head est fourni, le contenu "tete" est lu sur ref plutot que
    # sur le fichier de travail. Cela permet de rejouer le test sur une
    # branche feature sans avoir a checkout le worktree. Symetrie du cote
    # base : absence legitime (chemin absent de la ref) = 0, toute autre
    # erreur git reste bruyante (faux zero = fausse perte ici).
    if args.head:
        if _blob_absent_from_ref(args.head, args.path):
            head_examples = []
        else:
            head_path = _read_git_blob(args.head, args.path)
            head_nb = _read_nb(head_path)
            head_examples = count_credited_examples(head_nb)

    diff = diff_examples(base_examples, head_examples)
    exemptions: list[dict] = []
    if args.pr_body_file:
        pr_body = Path(args.pr_body_file).read_text(encoding="utf-8", errors="replace")
        exemptions = _exemption_markers(pr_body)

    # Les exemptions s'appliquent par titre + notebook (cf. plan-loss).
    exempted_titles = {
        (e["notebook"], _norm_title(e["title"]))
        for e in exemptions
    }
    final_lost = []
    for ex in diff["lost"]:
        # match sur cell_id OU (notebook+title)
        match_norm = (str(Path(args.path).name), _norm_title(ex["title"]))
        if match_norm in exempted_titles:
            ex["exempted"] = True
            ex["exemption_raw"] = next(
                e["raw"] for e in exemptions
                if (e["notebook"], _norm_title(e["title"])) == match_norm
            )
        else:
            ex["exempted"] = False
        final_lost.append(ex)

    payload = {
        "path": args.path,
        "base": args.base,
        "head_examples": head_examples,
        "base_examples": base_examples,
        "lost": final_lost,
        "added": diff["added"],
        "kept": diff["kept"],
        "exemptions_found": len(exemptions),
    }

    if args.json_out:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print(f"Base examples   : {len(base_examples)}")
        print(f"Head examples   : {len(head_examples)}")
        print(f"Lost (raw)      : {len(diff['lost'])}")
        print(f"Exempted        : {sum(1 for e in final_lost if e['exempted'])}")
        for ex in final_lost:
            tag = "[EXEMPTED]" if ex["exempted"] else "[LOST]"
            print(f"  {tag} {ex['credit']} {ex['cell_id'][:8]} - {ex['title'][:60]}")

    if args.check:
        unexempted = [e for e in final_lost if not e["exempted"]]
        return 1 if unexempted else 0
    return 0


def _norm_title(t: str) -> str:
    """Normalisation permissive (lower + strip) pour matcher les markers."""
    return re.sub(r"\s+", " ", t.strip().lower())


if __name__ == "__main__":
    sys.exit(main())