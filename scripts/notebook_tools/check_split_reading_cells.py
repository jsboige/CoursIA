#!/usr/bin/env python3
"""Recensement des cellules de lecture scindees « Lecture » puis « Lecture chiffree ».

Demande user (nit #16554, 2026-09-17, parapluie #16762) : quand un notebook
porte deja une cellule « Lecture », la tranche de densite suivante ajoute une
seconde cellule d'interpretation -- « Lecture chiffree » -- au lieu de
fusionner. Resultat : deux cellules d'interpretation consecutives avec
recouvrement PARTIEL de contenu, l'une derriere l'autre. Ce n'est pas un
doublon franc (les deux cellules disent des choses differentes ET se
repetent en partie) : un detecteur de duplication verbatim ne le voit pas,
et pedagogiquement le lecteur ne sait plus laquelle fait foi.

Ce script fait le RECENSEMENT structurel + la mesure de recouvrement :

  1. Signal structurel : paires de cellules markdown CONSECUTIVES dont les
     titres sont des en-tetes d'interpretation (Lecture / Lecture chiffree /
     Interpretation / Analyse). Sous-classes :
       - ``named_split``   : « Lecture ... » puis « Lecture chiffree ... » --
                             le defaut nomme par le user ;
       - ``generic_pair``  : autre couple d'en-tetes d'interpretation consecutifs.
  2. Mesure de recouvrement entre les deux cellules : Jaccard sur les mots
     pleins + containment des mots rares intra-notebook (df <= 4, meme
     mecanique que detect_repeated_prose.py signal B, reutilise par import).

Variante secondaire ``separated_by_code`` : meme couple d'en-tetes separe par
UNE cellule de code (la lecture chiffree interprete la sortie) -- signale
separement, le defaut user est la paire consecutive.

Le seuil de recouvrement N'EST PAS un verdict de fusion : la fusion est une
decision pedagogique par notebook (acceptance #16762). Le recensement dit
ou regarder ; il ne dit pas quoi couper.

Mode DIFF (#17464) : ``detect_added_readings`` signale les cellules markdown
INSEREES dans une PR qui violent la regle user « une sortie = une lecture » :

  - ``SECOND_READING``      : cellule markdown ajoutee juste avant ou apres
                              une lecture existante (les bases de la campagne
                              #13410 ajoutaient des paragraphes *sans en-tete*
                              derives de la lecture -- invisibles au detecteur
                              consecutive) ;
  - ``READING_BEFORE_CODE`` : cellule markdown ajoutee directement devant une
                              cellule de code AVEC sortie (la lecture doit
                              suivre la sortie, pas la preceder) ;
  - ``EXERCISE_READING``    : cellule markdown ajoutee juste apres une cellule
                              d'exercice (stub sans sortie) -- l'etudiant ne
                              verra pas la lecture tant qu'il n'a pas complete.

Le mode diff prend deux notebooks en argument (``--base``) et signale chaque
cellule ajoutee (par multiset de sources) dont la **nouvelle** position viole
la regle. La difference des en-tetes vides vient de la campagne #17021
(26 lectures inserees sur App-1-NQueens, 16 sur App-14b-ConnectFour) qui
passait sous l'organe consecutive d'origine -- le veto user dit pourtant la
meme regle.

Codes de retour : 0 = aucun finding ; 1 = cible introuvable ou fichier designe
illisible ; 2 = findings (avec --fail-on-findings). En mode dossier, un carnet
illisible est **rapporte sur stderr et saute** : il n'interrompt pas le
recensement et ne fait pas rougir le scan (cf #17044).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import unicodedata
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from detect_repeated_prose import content_words, markdown_cells  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[2]
MAX_DF = 4  # un mot "rare" apparait dans <= 4 cellules du notebook

TITLE_STRIP_RE = re.compile(r"^[#*\-\s`>]+|[#*\s`>:]+$")
INTERPRETATION_RE = re.compile(
    r"^(lecture|interpre|interpret|analyse)\b", re.IGNORECASE
)
NAMED_SECOND_RE = re.compile(r"^lecture\s+chiffr", re.IGNORECASE)
NAMED_FIRST_RE = re.compile(r"^lecture\b", re.IGNORECASE)

# Heuristique cellule d'exercice : un stub TODO sans sortie ni execution_count.
EXERCISE_TOKENS = ("TODO", "A completer", "à compléter", "Exercice")


def deaccent(s: str) -> str:
    return "".join(
        c for c in unicodedata.normalize("NFKD", s) if not unicodedata.combining(c)
    )


def cell_source(c: dict) -> str:
    s = c.get("source", "")
    return "".join(s) if isinstance(s, list) else s


def cell_output_text(cell: dict) -> str:
    """Concatene le texte de toutes les sorties d'une cellule de code."""
    parts = []
    for o in cell.get("outputs") or []:
        if isinstance(o, dict):
            t = o.get("text")
            if isinstance(t, list):
                parts.append("".join(t))
            elif isinstance(t, str):
                parts.append(t)
            data = o.get("data")
            if isinstance(data, dict) and "text/plain" in data:
                d = data["text/plain"]
                parts.append("".join(d) if isinstance(d, list) else str(d))
    return "\n".join(parts)


def cell_title(src: str) -> str:
    """Premiere ligne non vide, nettoyee des marques markdown."""
    for line in src.splitlines():
        line = line.strip()
        if not line:
            continue
        return TITLE_STRIP_RE.sub("", line).strip()
    return ""


def is_interpretation_title(title: str) -> bool:
    return bool(INTERPRETATION_RE.match(deaccent(title).lower()))


def is_named_second(title: str) -> bool:
    return bool(NAMED_SECOND_RE.match(deaccent(title).lower()))


def is_reading_cell(cell: dict) -> bool:
    """Une cellule markdown est une 'lecture' au sens de la regle user si elle
    porte un en-tete d'interpretation (Lecture / Lecture chiffree /
    Interpretation / Analyse). Les '### Conclusion', '### Mise en place',
    '### Resultats' ne sont PAS des lectures : ce sont des transitions /
    organisation, pas des commentaires de sortie.

    Cette definition sert de discriminant dans le mode DIFF : on signale
    une 'lecture ajoutee' quand la cellule de code en base avait DEJA une
    lecture (de ce type la) derriere elle -- pas une simple transition.
    """
    if cell.get("cell_type") != "markdown":
        return False
    return is_interpretation_title(cell_title(cell_source(cell)))


def looks_like_reading_after_exercise(cell: dict) -> bool:
    """Heuristique plus large qu'``is_reading_cell`` : une cellule md qui
    suit un exercice peut etre une 'lecture pour la sortie attendue' meme
    si elle n'a pas d'en-tete 'Lecture / Analyse'. Le spec #17464 (bucket
    3) dit « apres une cellule d'exercice (stub TODO / sans sortie) » sans
    exiger un en-tete : un paragraphe descriptif sur la sortie attendue
    apres un stub compte autant qu'un '### Lecture' formel.

    On accepte une md SI :
      - elle porte un en-tete d'interpretation (Lecture / Analyse / etc.)
        ; OU
      - elle est constituee d'un (ou plusieurs) paragraphe(s) de prose
        substantielle (> 80 caracteres au total hors titre eventuel) sans
        etre une simple section structurelle.

    On REJETTE les md purement structurels (## Conclusion, ## Exercice
    N, ## References), qui n'ont qu'un en-tete suivi d'un corps court
    ou vide -- ce sont des transitions, pas des lectures.
    """
    if cell.get("cell_type") != "markdown":
        return False
    if is_reading_cell(cell):
        return True
    src = cell_source(cell).strip()
    if not src:
        return False
    # Si la premiere ligne est un titre markdown (# ## ### ...), on
    # accepte si le corps (apres la premiere ligne) fait > 80 chars.
    first_line = src.split("\n", 1)[0].lstrip()
    if first_line.startswith("#"):
        body = src.split("\n", 1)[1].strip() if "\n" in src else ""
        return len(body) > 80
    # Pas de titre markdown : c'est un paragraphe libre. S'il est > 80 chars,
    # c'est vraisemblablement une lecture descriptive (pas juste un
    # en-tete de section).
    return len(src) > 80


def is_exercise_cell(cell: dict) -> bool:
    """Une cellule de code est 'exercise' si elle porte un marqueur d'exercice
    OU un stub TODO dans son source. On accepte aussi une sortie litterale
    ``Exercice a completer`` : la convention des carnets CoursIA est d'afficher
    ce message quand l'etudiant n'a pas complete (cf C.1) -- la cellule reste
    pedagogiquement un exercice, meme si elle a ete executee une fois.

    Cette definition suit le contrat C.1 (``pas d'erreur volontaire dans un
    exercice``) : un exercice abouti a execution_count != None et une sortie
    utile, donc il ne ressemble plus a un stub -- l'heuristique reste
    aplicable tant que la cellule declare sa nature d'exercice.
    """
    if cell.get("cell_type") != "code":
        return False
    src = cell_source(cell)
    if any(tok in src for tok in EXERCISE_TOKENS):
        return True
    # Sortie litterale "Exercice a completer" (avec/sans accent, casse libre)
    out_text = cell_output_text(cell).strip().lower()
    out_text_deac = deaccent(out_text)
    return (
        "exercice a completer" in out_text_deac
        or "exercice a terminer" in out_text_deac
        or "a completer" in out_text_deac
    )


def overlap_metrics(nb: dict, i: int, j: int) -> dict:
    """Jaccard mots pleins + containment mots rares entre cellules i et j."""
    words = {ci: content_words(t) for ci, t in markdown_cells(nb)}
    df: Counter[str] = Counter()
    for ws in words.values():
        df.update(ws)
    wi, wj = words.get(i, set()), words.get(j, set())
    union = wi | wj
    jaccard = round(len(wi & wj) / len(union), 3) if union else 0.0
    rare_i = {w for w in wi if df[w] <= MAX_DF}
    rare_shared = rare_i & wj
    containment = round(len(rare_shared) / len(rare_i), 3) if rare_i else 0.0
    return {
        "jaccard": jaccard,
        "rare_containment": containment,
        "shared_rare_words": len(rare_shared),
        "shared_rare_sample": sorted(rare_shared)[:8],
    }


def detect(nb: dict) -> list[dict]:
    cells = nb.get("cells", [])
    titles = {
        i: cell_title(cell_source(c))
        for i, c in enumerate(cells)
    }
    findings: list[dict] = []
    for i in range(len(cells) - 1):
        a, b = cells[i], cells[i + 1]
        if a.get("cell_type") != "markdown" or b.get("cell_type") != "markdown":
            continue
        ta, tb = titles[i], titles[i + 1]
        if not (is_interpretation_title(ta) and is_interpretation_title(tb)):
            continue
        kind = (
            "named_split"
            if NAMED_FIRST_RE.match(deaccent(ta).lower()) and is_named_second(tb)
            else "generic_pair"
        )
        findings.append({
            "type": kind,
            "cells": [i, i + 1],
            "titles": [ta[:70], tb[:70]],
            **overlap_metrics(nb, i, i + 1),
        })
    # Variante secondaire : meme couple separe par UNE cellule de code.
    for i in range(len(cells) - 2):
        a, mid, b = cells[i], cells[i + 1], cells[i + 2]
        if mid.get("cell_type") != "code":
            continue
        if a.get("cell_type") != "markdown" or b.get("cell_type") != "markdown":
            continue
        ta, tb = titles[i], titles[i + 2]
        if not (is_interpretation_title(ta) and is_named_second(tb)):
            continue
        # Ne pas doubler un named_split deja compte (cas impossible ici :
        # la cellule du milieu est du code), garder pour la lisibilite.
        findings.append({
            "type": "separated_by_code",
            "cells": [i, i + 2],
            "titles": [ta[:70], tb[:70]],
            **overlap_metrics(nb, i, i + 2),
        })
    return findings


# --- #17464 : mode DIFF -- cellule ajoutee qui viole la regle ----------------


def _classify_context(cells: list[dict], idx: int) -> tuple[str, str]:
    """Renvoie (prev_role, next_role) pour la cellule idx.

    prev_role / next_role sont parmi : "md", "code_with_output", "exercise", "BOUNDARY".
    "code_with_output" = cellule de code executee (a une sortie ou un exec_count).
    """
    def role(c):
        if c is None:
            return "BOUNDARY"
        if c.get("cell_type") == "markdown":
            return "md"
        if is_exercise_cell(c):
            return "exercise"
        return "code_with_output"

    prev = cells[idx - 1] if idx > 0 else None
    nxt = cells[idx + 1] if idx + 1 < len(cells) else None
    return role(prev), role(nxt)


def detect_added_readings(head_nb: dict, base_nb: dict | None) -> list[dict]:
    """Mode DIFF (#17464) : signale les cellules markdown **ajoutees** dans une PR
    dont la position viole la regle user « une sortie = une lecture ».

    Algorithme :
      1. Si ``base_nb`` est None, retourne une liste vide.
      2. Diff par multiset de sources (entre par sources, pas par id -- la
         campagne a produit des cellules sans id et des ids dupliques).
      3. Pour chaque cellule ajoutee qui est markdown, classifier via le
         **contexte HEAD** :
           - ``EXERCISE_READING``    prev_role == "exercise"
           - ``READING_BEFORE_CODE`` next_role == "code_with_output"
           - ``SECOND_READING``      prev_role == "md"
                                       (lecture ajoutee derriere une lecture
                                       deja presente)
                                     OU prev_role == "code_with_output"
                                        ET la cellule de code en question
                                        etait **elle-meme deja precede d'une
                                        lecture en base** (sinon : ajout
                                        legitime d'une premiere lecture pour
                                        un nouveau code)

    Le discriminant pour ``SECOND_READING`` apres code : on regarde en base
    la cellule qui precede le meme code (identifiee par egalite de source).
    Si en base cette cellule de code etait deja suivie d'une lecture markdown,
    l'ajout est un doublonnage ; sinon, c'est la premiere lecture legitime.

    Sortie : liste de dicts ``{type, cells, src_first_120, prev_role,
    next_role, prev_src_last_60, next_src_first_60}``.
    """
    if base_nb is None:
        return []
    base_cells = base_nb.get("cells", [])
    head_cells = head_nb.get("cells", [])
    base_srcs = [cell_source(c) for c in base_cells]
    head_srcs = [cell_source(c) for c in head_cells]

    # Pour le discriminant SECOND_READING : index par source de toutes les
    # cellules de base dont la source est DU CODE A SORTIE UTILE, et map
    # "ce code etait-il deja suivi d'une cellule de LECTURE" (pas
    # n'importe quelle markdown -- un "Conclusion" terminal n'est pas une
    # lecture au sens de la regle, meme s'il suit une cellule de code).
    base_code_positions: dict[str, list[int]] = {}
    for i, src in enumerate(base_srcs):
        c = base_cells[i]
        if c.get("cell_type") == "code":
            ec = c.get("execution_count")
            outs = c.get("outputs") or []
            if (ec is not None or outs) and not is_exercise_cell(c):
                base_code_positions.setdefault(src, []).append(i)

    base_counter: Counter[str] = Counter(base_srcs)
    head_counter: Counter[str] = Counter(head_srcs)

    findings: list[dict] = []
    for idx, src in enumerate(head_srcs):
        if head_counter[src] <= base_counter[src]:
            base_counter[src] += 1
            continue
        cell = head_cells[idx]
        if cell.get("cell_type") != "markdown":
            base_counter[src] += 1
            continue

        # Discriminant 0 : REWRITE (pas d'insertion). On considere qu'une
        # cellule est une REWRITE -- et NON un ajout -- quand au moins
        # l'UN des deux signaux tient :
        #   (a) meme position index-for-index ET meme source (meme
        #       contenu exact) ;
        #   (b) meme position index-for-index ET meme id de cellule
        #       (attribue par Jupyter dans les exports -- les rewriting
        #       preservent l'id, les insertions en ont un neuf ou
        #       doublonne). Le ticket #17464 note que la campagne a
        #       produit des cellules sans id ET des ids dupliques -- donc
        #       l'id seul ne suffit pas, mais combine a la position il
        #       tranche la majorite des cas de rewriting legitimes.
        # La regle user dit « fusionner / reecrire, pas empiler » : la
        # reecriture EST l'action prescrite. Ne pas la signaler.
        is_rewrite = False
        if idx < len(base_cells) and base_cells[idx].get("cell_type") == "markdown":
            if cell_source(base_cells[idx]) == src:
                is_rewrite = True
            else:
                base_id = base_cells[idx].get("id")
                head_id = cell.get("id")
                if base_id and head_id and base_id == head_id:
                    is_rewrite = True
        if is_rewrite:
            base_counter[src] += 1
            continue

        prev_role, next_role = _classify_context(head_cells, idx)
        bucket = _bucket_for(prev_role, next_role)
        # Discriminant SECOND_READING : si prev_role == "code_with_output",
        # verifier en base si ce code etait **deja suivi** d'une cellule
        # markdown (au sens large du ticket user : « deja suivie d'au moins
        # une cellule markdown » -- la distinction lecture vs transition
        # est tranchee par la pedagogie, pas par le format).
        # Si la base avait deja une md derriere ce code, ajouter une md
        # supplementaire derriere est un doublonnage. Si la base n'avait
        # rien derriere ce code (markdown), c'est la premiere lecture
        # legitime (et NON une violation).
        if bucket == "SECOND_READING" and prev_role == "code_with_output":
            prev_cell = head_cells[idx - 1] if idx > 0 else None
            if prev_cell is not None:
                prev_src = cell_source(prev_cell)
                prev_positions = base_code_positions.get(prev_src, [])
                already_had_md_after = any(
                    (i + 1 < len(base_cells)
                     and base_cells[i + 1].get("cell_type") == "markdown")
                    for i in prev_positions
                )
                if not already_had_md_after:
                    # premiere lecture legitime pour ce code -> ne pas signaler
                    bucket = None
        # Filtre final : EXERCISE_READING_CANDIDATE -> EXERCISE_READING si
        # la cellule ressemble a une lecture (titre d'interpretation OU
        # prose > 80 chars apres la premiere ligne). On REJETTE les
        # en-tetes purement structurels (## Conclusion, ## Exercice N,
        # ## References entre exercices).
        if bucket == "EXERCISE_READING_CANDIDATE":
            bucket = "EXERCISE_READING" if looks_like_reading_after_exercise(cell) else None
        if bucket is None:
            base_counter[src] += 1
            continue
        prev = head_cells[idx - 1] if idx > 0 else None
        nxt = head_cells[idx + 1] if idx + 1 < len(head_cells) else None
        prev_src = (cell_source(prev)[-60:] if prev is not None else "")
        nxt_src = (cell_source(nxt)[:60] if nxt is not None else "")
        findings.append({
            "type": bucket,
            "cells": [idx],
            "src_first_120": src[:120].replace("\n", " | "),
            "prev_role": prev_role,
            "next_role": next_role,
            "prev_src_last_60": prev_src.replace("\n", " | "),
            "next_src_first_60": nxt_src.replace("\n", " | "),
        })
        base_counter[src] += 1
    return findings


def _bucket_for(prev_role: str, next_role: str) -> str | None:
    """Map (prev, next) vers un bucket preliminaire, ou None si rien a signaler.

    Pour ``SECOND_READING`` apres code, l'organe applique un discriminant
    base (voir ``detect_added_readings``) pour distinguer premiere lecture
    legitime d'un doublonnage. Cette fonction ne tranche que la topologie
    immediate. Le filtre final (is_reading_cell) affine : on ne signale
    ``EXERCISE_READING`` que si la cellule est reellement une LECTURE
    (en-tete d'interpretation), pas un simple en-tete structurel (Conclusion,
    Exercice N, References).
    """
    if prev_role == "exercise":
        return "EXERCISE_READING_CANDIDATE"
    if next_role in ("code_with_output", "exercise"):
        # Une lecture ajoutee devant un exercice OU un code deja execute
        # precede le resultat qu'elle est censee commenter -- dans les deux
        # cas la place canonique est APRES, pas avant.
        return "READING_BEFORE_CODE"
    if prev_role in ("md", "code_with_output"):
        return "SECOND_READING"
    return None


def iter_notebooks(root: Path) -> list[Path]:
    skip_parts = {".lake", "_output", ".ipynb_checkpoints", "node_modules", "_peters"}
    return sorted(
        p for p in root.rglob("*.ipynb")
        if not (skip_parts & set(p.parts))
    )


def _read_nb(path: Path) -> dict:
    """Lecture tolerante : un carnet corrompu leve JSONDecodeError, handled
    par l'appelant (cf #17044)."""
    return json.loads(path.read_text(encoding="utf-8"))


def scan_root(root: Path, as_json: bool, fail_on_findings: bool = False,
              base_root: Path | None = None) -> int:
    """Mode dossier. Si ``base_root`` est fourni, applique le mode diff : pour
    chaque carnet du head, cherche son pendant dans base (par chemin relatif).
    Un carnet present dans head mais absent dans base est scanne en mode
    standalone (toutes ses lectures sont des ajouts). Un carnet present dans
    base mais absent dans head est ignore : on ne signale pas des retraits.
    """
    total = 0
    per_kind: Counter[str] = Counter()
    unreadable: list[str] = []
    rows = []

    targets = list(iter_notebooks(root))
    base_by_rel: dict[str, Path] = {}
    if base_root is not None:
        for p in iter_notebooks(base_root):
            try:
                rel = p.relative_to(base_root)
            except ValueError:
                continue
            base_by_rel[str(rel).replace("\\", "/")] = p

    for head_path in targets:
        try:
            rel = head_path.relative_to(root)
        except ValueError:
            rel = Path(head_path.name)
        rel_str = str(rel).replace("\\", "/")
        try:
            head_nb = _read_nb(head_path)
        except (OSError, json.JSONDecodeError) as e:
            # #17044 : un carnet illisible ne doit PAS annuler le recensement.
            print(f"ERREUR lecture {head_path}: {e}", file=sys.stderr)
            unreadable.append(str(head_path.relative_to(root)))
            continue

        base_nb = None
        if base_root is not None:
            base_path = base_by_rel.get(rel_str)
            if base_path is not None:
                try:
                    base_nb = _read_nb(base_path)
                except (OSError, json.JSONDecodeError) as e:
                    print(f"ERREUR lecture base {base_path}: {e}", file=sys.stderr)
                    # base illisible : degrade en mode standalone (pas de diff)

        if base_root is not None:
            findings = detect_added_readings(head_nb, base_nb)
        else:
            findings = detect(head_nb)

        if not findings:
            continue
        total += len(findings)
        for f in findings:
            per_kind[f["type"]] += 1
            rows.append({"file": rel_str, **f})

    if unreadable:
        print(
            f"\nATTENTION : {len(unreadable)} carnet(s) illisible(s), NON recenses "
            f"-- le total ci-dessous est partiel :",
            file=sys.stderr,
        )
        for u in unreadable:
            print(f"  - {u}", file=sys.stderr)
    if as_json:
        print(json.dumps(rows, ensure_ascii=False, indent=1))
    else:
        for r in rows:
            extra = ""
            if "prev_role" in r:
                extra = (
                    f" prev={r['prev_role']:8s} next={r['next_role']:8s}"
                    f" src[:120]={r.get('src_first_120','')[:90]}"
                )
            print(
                f"{r['type']:22s} {r['file']}  cellules {r['cells']}{extra}"
            )
        suffix = f" -- {len(unreadable)} illisible(s)" if unreadable else ""
        print(f"\nTotal : {total} ({dict(per_kind)}){suffix}")
    return 2 if (fail_on_findings and total) else 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("path", nargs="?", default=str(REPO_ROOT / "MyIA.AI.Notebooks"),
                    help="notebook ou dossier a scanner (head, en mode diff)")
    ap.add_argument("--json", action="store_true", dest="as_json")
    ap.add_argument("--fail-on-findings", action="store_true")
    ap.add_argument(
        "--base",
        default=None,
        help=(
            "Chemin du notebook ou dossier de BASE pour le mode diff "
            "(#17464). Avec --base, l'organe signale les cellules markdown "
            "INSEREES dans head qui violent la regle 'une sortie = une "
            "lecture' ; sans --base, comportement historique (recensement "
            "consecutive d'en-tetes)."
        ),
    )
    args = ap.parse_args(argv)
    target = Path(args.path)
    if not target.exists():
        print(f"introuvable : {target}", file=sys.stderr)
        return 1
    base_path = Path(args.base) if args.base else None
    if base_path is not None and not base_path.exists():
        print(f"introuvable : {base_path}", file=sys.stderr)
        return 1

    if target.is_file():
        try:
            head_nb = _read_nb(target)
        except (OSError, json.JSONDecodeError) as e:
            print(f"ERREUR lecture {target}: {e}", file=sys.stderr)
            return 1
        if base_path is not None:
            if base_path.is_file():
                try:
                    base_nb = _read_nb(base_path)
                except (OSError, json.JSONDecodeError) as e:
                    print(f"ERREUR lecture {base_path}: {e}", file=sys.stderr)
                    return 1
            else:
                # base is a folder but target is a file -- mismatch
                print(
                    f"mode diff fichier-a-dossier non supporte : --base={base_path}",
                    file=sys.stderr,
                )
                return 1
            findings = detect_added_readings(head_nb, base_nb)
        else:
            findings = detect(head_nb)
        if args.as_json:
            print(json.dumps(findings, ensure_ascii=False, indent=1))
        elif findings:
            for f in findings:
                if "prev_role" in f:
                    print(
                        f"{f['type']:22s} cellules {f['cells']} "
                        f"prev={f['prev_role']:8s} next={f['next_role']:8s} "
                        f"src[:120]={f.get('src_first_120','')[:90]}"
                    )
                else:
                    print(
                        f"{f['type']} cellules {f['cells']} J={f['jaccard']} "
                        f"C={f['rare_containment']} «{f['titles'][0]}» + «{f['titles'][1]}»"
                    )
        else:
            print("clean")
        return 2 if (args.fail_on_findings and findings) else 0
    rc = scan_root(target, args.as_json, args.fail_on_findings, base_path)
    return rc


if __name__ == "__main__":
    sys.exit(main())
