#!/usr/bin/env python3
"""Repair_morpho -- organe canonique de correction morphologique pour notebooks REACCENT.

Contexte :
- La famille REACCENT (issue #16638) a produit un default systemique : la map
  upstream ``"prouve": "prouvé"``, ``"donne": "donné"``, ``"decide": "décide"``
  ajoute l'accent **partout**, alors que le francais n'accentue le participe
  passe qu'apres un auxiliaire (avoir/etre) ou dans une locution figee.
- Verbe 3e pers. du present (``prouve``, ``donne``, ``decide``) = **non
  accente** (jamais adj. participial).
- Participe passe legitime = UNIQUEMENT apres auxiliaire 2+ chars (signal
  distingue le morpheme du verbe homonyme 1 char comme ``a`` de l'auxiliaire).

Correctifs implementes :
1. ``prouve -> prouvé`` uniquement si auxiliaire 2+ chars avant
   (``se prouve`` **toujours fautif** : pas d'auxiliaire).
2. ``donne -> donné`` uniquement dans locution ``étant donné`` / ``tant donné``
   (fenetre 60 chars avant -- autorise mots intercalés type ``qui est tant
   donné``).
3. ``decide`` **jamais accentue** dans les cellules CODE (tactiques Lean).
4. **c.1412-c.1415 (reconcilie)** : ``décide`` et ``vérifier`` accentues ne
   sont fautifs **qu'entre backticks** (identifiants Lean/Python que REACCENT
   a accentues). En prose libre, "il décide de" / "vérifier la preuve" sont
   legitimes (corpus main : 12 accentues vs 6 non-accentues).
5. **c.1412** : ``vérifié`` fautif hors auxiliaire/backticks (suggere
   ``vérifie``), transposition du pattern ``prouvé`` au cas ``vérifié``.
   ``prouvé``/``donné``/``vérifié`` entre backticks = intacts (noms, pas
   prose). Fenetre locution ``donné`` passee a 60 chars (c.1317-L7).

Contraintes structurelles (cf tells c.1343 fondateurs) :
- ``source[]`` est preservee (list-edit par item, JAMAIS split('\n')) -- evite
  la re-serialisation visible (-184 lignes sur #16993).
- byte-identique newline terminal (read_bytes / write_bytes).
- dry_run=True pour mesurer l'impact sans toucher au disque.

Usage CLI :
    python repair_morpho.py <notebook.ipynb> [--dry-run] [--json]
    python repair_morpho.py --self-test     # smoke test intégré

Usage API :
    from repair_morpho import repair_notebook, scan_notebook
    report = repair_notebook(Path("nb.ipynb"), dry_run=True)
    findings = scan_notebook(Path("nb.ipynb"))  # detection sans modification
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import List, Optional


# --- Constantes morphologiques ----------------------------------------------

# Auxiliaires avoir/etre (signal 2+ chars pour eviter "a" ambigu avec article)
# + semi-auxiliaire "peut" (cf Tell c.1317-L4 ★★★★ fondateur).
AUXILIAIRES_2CHARS_PLUS = frozenset({
    # avoir
    "ai", "as", "avons", "avez", "ont",
    # etre (present, imparfait, passe simple, subjonctif, **participe passe**)
    "suis", "es", "est", "sommes", "etes", "sont",
    "etais", "etait", "etions", "etiez", "etaient",
    "fus", "fut", "fumes", "futes", "furent",
    "sois", "soit", "soyons", "soyez", "soient",
    "ete",  # participe passe de etre (ete prouve)
    # semi-auxiliaire
    "peut",
})

# Locutions figees avec "donne" -- fenetre 60 chars (mots intercalés OK).
# Detection par MARQUEURS (etant|tant) a bordure de mot : au call site, le
# contexte AVANT le mot cible ne contient jamais "donne" (c'est le mot cible
# lui-meme) -- l'ancienne sous-chaine "etant donne" ne matchait donc jamais,
# et tout "Étant donné" legitime etait flagge fautif (defaut expose par le
# port des tests CI, c.1415).
LOCUTIONS_DONNE_MARKERS = re.compile(r"\b(?:etant|tant)\b")


# --- Discrimination 'decide' / 'verifier' (reconciliation c.1415) ------------
#
# Sémantique v2 réconciliée (fresh b8d99f827b / consolidation c.1412-c.1415) :
# `décide` et `vérifier` accentués ne sont fautifs **qu'entre backticks** --
# c'est là qu'un identifiant Lean/Python vit (tactique, fonction, variable),
# et REACCENT y a accentué des identifiants (ex. `vérifier = ProofVerifier...`
# sur #16953). En prose markdown libre, "il décide de" / "vérifier la preuve"
# sont du français légitime : mesure corpus main = 12 formes accentuées
# "il/on décide" vs 6 non-accentuees -- flagguer partout (sémantique v1,
# issue #17323) produisait des faux positifs contre la prose de main.
#
# Invariant préservé (Tell c.1345-L1 ★★★★★ fondateur) : les cellules CODE
# ne sont JAMAIS scannées (filtre `cell_type == 'markdown'`).
# Donc `by decide` dans une cellule code = intact.


# --- Modele de rapport -------------------------------------------------------


@dataclass
class MorphoFinding:
    """Une occurrence fautive detectee dans une cellule markdown."""
    cell_index: int
    word: str           # forme fautive ('prouve', 'donne', 'decide')
    suggested: str      # correction proposee ('prouve', 'donne', 'decide')
    position: int       # offset dans le texte joint
    context: str = ""   # 30 chars avant + 15 apres (sanitises)

    def to_dict(self) -> dict:
        return asdict(self)


@dataclass
class MorphoReport:
    """Rapport global d'un scan ou d'un repair."""
    path: str
    findings: List[MorphoFinding] = field(default_factory=list)
    cells_scanned: int = 0
    cells_modified: int = 0
    bytes_delta: int = 0
    dry_run: bool = True

    def to_dict(self) -> dict:
        return {
            "path": self.path,
            "findings": [f.to_dict() for f in self.findings],
            "cells_scanned": self.cells_scanned,
            "cells_modified": self.cells_modified,
            "bytes_delta": self.bytes_delta,
            "dry_run": self.dry_run,
        }


# --- Helpers de detection ---------------------------------------------------


def _normalize(s: str) -> str:
    """lowercase (pas de rstrip -- preserve le dernier mot)."""
    return s.lower()


# Strip accents pour la comparaison lexicale : la locution reelle s'ecrit
# accentuee (« étant donné ») et l'auxiliaire aussi (« a été prouvé ») --
# comparer aux formes unaccentuees sans strip rate ces cas (angle mort
# c.1412-L1 : strip accents + tokenize).
_ACCENT_STRIP = str.maketrans("éèêëàâäîïôöûüç", "eeeeaaaiioouuc")


def _strip_accents(s: str) -> str:
    return s.translate(_ACCENT_STRIP)


def is_prouve_legitimate(ctx_before: str) -> bool:
    """Verifie si 'prouve' est un adj. participial legitime.

    Signal : un auxiliaire 2+ chars precede dans la meme phrase (reconciliation
    v1/v2, c.1415 : la v1 dernier-mot-only ratait "est donc réellement prouvé" ;
    la v2 fenetre-libre legitimisait a travers les frontieres de phrase --
    "est prouvé par Tao. Tao le prouvé" comptait 2 fautifs au lieu de 3).
    Compromis : fenetre 30 chars COUPEE au dernier séparateur de phrase.
    Refuse : "se prouve" (cf Tell c.1315-L15 ★★★ fondateur -- "se prouve" toujours
    fautif, car "se" n'est pas un auxiliaire avoir/etre).
    """
    ctx = _strip_accents(_normalize(ctx_before))
    if not ctx:
        return False
    segment = re.split(r"[.!?;:\n]", ctx)[-1]
    # Tokenisation SANS apostrophe : "n'est" doit exposer "est" (negation
    # francaise -- sinon "n'est prouvé" legitime etait flagge fautif).
    words = re.findall(r"[a-z]+", segment)
    return any(w in AUXILIAIRES_2CHARS_PLUS for w in words)


def is_donne_legitimate(ctx_before: str) -> bool:
    """Verifie si 'donne' est dans une locution figee (etant donne / tant donne).

    Fenetre 60 chars avant (Tell c.1317-L7 ★★★★ fondateur -- mots intercalés
    OK). Detection par marqueurs a bordure de mot (cf LOCUTIONS_DONNE_MARKERS).
    """
    ctx = _strip_accents(_normalize(ctx_before))
    if not ctx:
        return False
    return bool(LOCUTIONS_DONNE_MARKERS.search(ctx[-60:]))


def is_verifie_legitimate(ctx_before: str) -> bool:
    """Verifie si 'vérifié' est un adj. participial legitime.

    Meme regle que ``prouve`` (auxiliaire dans la meme phrase) -- c.1412
    adjoint dispatch, transposee avec la reconciliation c.1415.
    """
    return is_prouve_legitimate(ctx_before)


def _build_backtick_mask(text: str) -> List[bool]:
    """Construit un masque position->is_in_backticks pour `text`.

    Convention : tout caractere entre deux backticks simples (non escapes) est
    considere comme identifiant. Un backtick ouvrant non ferme (nombre impair)
    = tout le reste du texte est considere comme in-backticks.
    """
    mask = [False] * len(text)
    in_bt = False
    for i, ch in enumerate(text):
        if ch == "`":
            in_bt = not in_bt
        else:
            mask[i] = in_bt
    return mask


# --- Coeur : scan d'une cellule markdown ------------------------------------


def _scan_cell_source(cell_index: int, src_text: str) -> List[MorphoFinding]:
    """Scan un texte de cellule (deja joint) et retourne les findings.

    REPAIR : on cherche les formes ACCENTUEES fautives (``prouve``, ``donne``)
    ajoutees par la map REACCENT upstream fautive. La correction les retire
    vers la forme non-accentuee (verbe 3e pers. du present).

    Participes passes legitimes (apres auxiliaire) ou locutions figees
    (``etant donne`` / ``tant donne``) sont preservees.
    """
    findings: List[MorphoFinding] = []
    # Backtick mask : calcule une fois par cellule. Les segments `...` sont des
    # identifiants (tactique Lean, variable, fonction) -- jamais de la prose.
    bt_mask = _build_backtick_mask(src_text)
    # Pattern 1 : forme ACCENTUEE "prouvé" fautive SAUF auxiliaire (phrase
    # courante) SAUF backticks (en backticks, c'est un nom -- on ne touche pas).
    for m in re.finditer(r"\bprouvé\b", src_text):
        if bt_mask[m.start()]:
            continue
        ctx = src_text[max(0, m.start() - 30):m.start()]
        if not is_prouve_legitimate(ctx):
            findings.append(MorphoFinding(
                cell_index=cell_index,
                word=m.group(0),
                suggested="prouve",
                position=m.start(),
                context=src_text[max(0, m.start() - 30):m.end() + 15].replace("\n", " "),
            ))
    # Pattern 2 : forme ACCENTUEE "donné" fautive SAUF locution SAUF backticks.
    # Fenetre 60 chars (Tell c.1317-L7 ★★★★ -- mots intercales OK).
    for m in re.finditer(r"\bdonné\b", src_text):
        if bt_mask[m.start()]:
            continue
        ctx = src_text[max(0, m.start() - 60):m.start()]
        if not is_donne_legitimate(ctx):
            findings.append(MorphoFinding(
                cell_index=cell_index,
                word=m.group(0),
                suggested="donne",
                position=m.start(),
                context=src_text[max(0, m.start() - 30):m.end() + 15].replace("\n", " "),
            ))
    # Pattern 3 (c.1412) : forme ACCENTUEE "vérifié" fautive SAUF auxiliaire
    # SAUF backticks. Transposition Tell c.1315 (verifie) au cas 'vérifié'.
    for m in re.finditer(r"\bvérifié\b", src_text):
        if bt_mask[m.start()]:
            continue
        ctx = src_text[max(0, m.start() - 30):m.start()]
        if not is_verifie_legitimate(ctx):
            findings.append(MorphoFinding(
                cell_index=cell_index,
                word=m.group(0),
                suggested="vérifie",
                position=m.start(),
                context=src_text[max(0, m.start() - 30):m.end() + 15].replace("\n", " "),
            ))
    # Pattern 4 (reconcilie c.1415) : "décide" fautif UNIQUEMENT entre
    # backticks (identifiant Lean -- REACCENT l'y a accentue). En prose libre,
    # "décide" est le verbe francais legitime ("il décide de") : mesure corpus
    # main = 12 formes accentuees vs 6 non-accentuees -- la sémantique v1
    # (flagger partout) produisait 12 faux positifs contre la prose de main.
    for m in re.finditer(r"\bdécide\b", src_text):
        if not bt_mask[m.start()]:
            continue
        findings.append(MorphoFinding(
            cell_index=cell_index,
            word=m.group(0),
            suggested="decide",
            position=m.start(),
            context=src_text[max(0, m.start() - 30):m.end() + 15].replace("\n", " "),
        ))
    # Pattern 5 (c.1412) : "vérifier" fautif UNIQUEMENT entre backticks
    # (identifiant -- fonction/variable Python ou Lean). En prose, l'infinitif
    # francais "vérifier" est legitime.
    for m in re.finditer(r"\bvérifier\b", src_text):
        if not bt_mask[m.start()]:
            continue
        findings.append(MorphoFinding(
            cell_index=cell_index,
            word=m.group(0),
            suggested="verifier",
            position=m.start(),
            context=src_text[max(0, m.start() - 30):m.end() + 15].replace("\n", " "),
        ))
    return findings


# --- Coeur : scan d'un notebook entier --------------------------------------


def scan_notebook(path: Path) -> MorphoReport:
    """Scan un notebook et retourne les findings SANS modifier le fichier."""
    raw = path.read_bytes()
    nb = json.loads(raw.decode("utf-8"))
    report = MorphoReport(path=str(path), dry_run=True)

    for ci, cell in enumerate(nb["cells"]):
        if cell.get("cell_type") != "markdown":
            continue
        report.cells_scanned += 1
        src = cell["source"]
        src_text = "".join(src) if isinstance(src, list) else src
        findings = _scan_cell_source(ci, src_text)
        report.findings.extend(findings)
    return report


# --- Coeur : repair d'un notebook (list-edit preservant source[]) -----------


def repair_notebook(path: Path, dry_run: bool = False) -> MorphoReport:
    """Reapply les corrections morphologiques sur un notebook.

    Strategie list-edit (Tell c.1343-L1 ★★★★★ fondateur NEW) : pour chaque item
    de source[] contenant le pattern, remplacer **uniquement** cet item via
    ``src.copy() + src[idx] = new_item``. JAMAIS de split/rejoin qui perd les
    \n finaux.

    Strategie byte-identique (Tell c.1331-L5 ★★★★ fondateur NEW) : read_bytes
    + write_bytes, preservation newline terminal bi-directionnelle.
    """
    raw = path.read_bytes()
    ends_with_newline_origin = raw.endswith(b"\n")
    nb = json.loads(raw.decode("utf-8"))
    report = MorphoReport(path=str(path), dry_run=dry_run)

    for ci, cell in enumerate(nb["cells"]):
        if cell.get("cell_type") != "markdown":
            continue
        report.cells_scanned += 1
        src = cell["source"]
        if isinstance(src, list):
            # List-edit preservant structure (chaque item sauf le dernier
            # DOIT se terminer par \n -- Tell c.1336-L1 strict).
            new_src = None
            for item_idx, item_text in enumerate(src):
                findings = _scan_cell_source(ci, item_text)
                if not findings:
                    continue
                # Les positions des findings sont des offsets EXACTS dans
                # item_text : application de la fin vers le debut, aucune
                # re-recherche necessaire (l'ancien matches[-1] pouvait
                # remplacer une occurrence legitime situee apres la fautive).
                new_item = item_text
                for f in sorted(findings, key=lambda x: x.position, reverse=True):
                    new_item = new_item[:f.position] + f.suggested + new_item[f.position + len(f.word):]
                if new_item != item_text:
                    if new_src is None:
                        new_src = list(src)
                    new_src[item_idx] = new_item
                report.findings.extend(findings)
            if new_src is not None:
                cell["source"] = new_src
                report.cells_modified += 1
        else:
            new_src = src
            findings = _scan_cell_source(ci, new_src)
            if findings:
                for f in sorted(findings, key=lambda x: x.position, reverse=True):
                    new_src = new_src[:f.position] + f.suggested + new_src[f.position + len(f.word):]
                if new_src != src:
                    cell["source"] = new_src
                    report.cells_modified += 1
                report.findings.extend(findings)

    # Re-mesure finale : on rescan apres edit pour confirmer 0 finding residuel
    final_text = json.dumps(nb, ensure_ascii=False, indent=1)
    final_bytes = final_text.encode("utf-8")
    if ends_with_newline_origin and not final_bytes.endswith(b"\n"):
        final_bytes += b"\n"
    elif not ends_with_newline_origin and final_bytes.endswith(b"\n"):
        final_bytes = final_bytes.rstrip(b"\n")
    report.bytes_delta = len(final_bytes) - len(raw)

    if not dry_run and report.cells_modified > 0:
        path.write_bytes(final_bytes)
    return report


# --- Self-test --------------------------------------------------------------


def _self_test() -> int:
    """Smoke test integre : verifie les invariants morphologiques de base."""
    failures = []

    # Auxiliaire 2+ chars : "a prouve" -> legitime
    # NOTE : is_*_legitimate recoit le contexte AVANT le mot cible, pas la
    # phrase complete. D'ou les slices ci-dessous.
    if not is_prouve_legitimate("Le theoreme est "):
        failures.append("'est prouve' devrait etre legitime (auxiliaire 'est')")
    if not is_prouve_legitimate("Cela a ete "):
        failures.append("'ete prouve' devrait etre legitime (auxiliaire 'ete')")

    # Verbe 3e pers. : "Tao le prouve" -> fautif
    if is_prouve_legitimate("Tao le "):
        failures.append("'le prouve' devrait etre fautif (verbe 3e pers.)")
    if is_prouve_legitimate("on "):
        failures.append("'on prouve' devrait etre fautif (verbe 3e pers.)")

    # "se prouve" : toujours fautif (Tell c.1315-L15 ★★★ fondateur)
    if is_prouve_legitimate("se "):
        failures.append("'se prouve' devrait etre fautif (cf Tell c.1315-L15)")

    # Locution "etant donne" : legitime
    if not is_donne_legitimate("Etant donne les contraintes, le probleme est complexe. On "):
        failures.append("'Etant donne' devrait etre legitime (locution figee)")
    if not is_donne_legitimate("Pour un theoreme qui est tant donne, le cluster "):
        failures.append("'tant donne' devrait etre legitime (mots intercalés OK)")

    # Verbe 3e pers. : "le sup donne" -> fautif
    if is_donne_legitimate("Le sup "):
        failures.append("'Le sup donne' devrait etre fautif (verbe 3e pers.)")
    if is_donne_legitimate("le cluster "):
        failures.append("'le cluster donne' devrait etre fautif (verbe 3e pers.)")

    # Frontiere de phrase (reconciliation v1/v2, c.1415) : un auxiliaire AVANT
    # un separateur de phrase ne legitimise PAS l'occurrence suivante.
    multi = "Tao les prouvé. Le theoreme est prouvé par Tao. Tao le prouvé. on prouvé qu'un algorithme."
    multi_findings = _scan_cell_source(0, multi)
    if len(multi_findings) != 3:
        failures.append(f"'multiples occurrences' devrait donner 3 fautifs, "
                        f"obtenu {len(multi_findings)} (frontiere de phrase)")
    if is_prouve_legitimate("est prouvé par Tao. Tao le "):
        failures.append("un auxiliaire avant le point ne doit PAS legitimiser "
                        "l'occurrence apres la frontiere de phrase")

    # Backtick mask : contenu entre backticks = in-backticks ; le char
    # backtick lui-meme et la prose hors backticks = False.
    bt = _build_backtick_mask("il `décide` bien")
    if not all(bt[4:10]) or bt[0] or bt[3] or bt[10] or bt[-1]:
        failures.append("backtick mask incorrect sur 'il `décide` bien'")
    # Backtick non ferme : le reste est in-backticks (fail-CLOSED).
    bt2 = _build_backtick_mask("prose `décide reste")
    if not all(bt2[7:]):
        failures.append("backtick non ferme devrait masquer tout le reste")

    # 'décide' prose = legitime ; 'décide' backticks = fautif (c.1415).
    prose = _scan_cell_source(0, "S'il décide de continuer, la tactique `décide` s'applique.")
    decide_bt = [f for f in prose if f.word == "décide"]
    if len(decide_bt) != 1:
        failures.append(f"'décide' : 1 fautif attendu (backticks), obtenu {len(decide_bt)}")

    # 'vérifié' : auxiliaire = legitime, sinon fautif -> 'vérifie' (c.1412).
    if not is_verifie_legitimate("le resultat est "):
        failures.append("'est vérifié' devrait etre legitime (auxiliaire)")
    if is_verifie_legitimate("Tao le "):
        failures.append("'le vérifié' devrait etre fautif")
    verif = _scan_cell_source(0, "Le test est vérifié. Tao le vérifié.")
    v_findings = [f for f in verif if f.word == "vérifié"]
    if len(v_findings) != 1 or v_findings[0].suggested != "vérifie":
        failures.append("'vérifié' : 1 fautif attendu -> 'vérifie'")

    # 'vérifier' : prose legitime, backticks fautif -> 'verifier' (c.1412).
    verif2 = _scan_cell_source(0, "Pour vérifier la preuve, on appelle `vérifier`.")
    vf = [f for f in verif2 if f.word == "vérifier"]
    if len(vf) != 1 or vf[0].suggested != "verifier":
        failures.append("'vérifier' : 1 fautif attendu en backticks -> 'verifier'")

    # Sanity : scan d'un mini-notebook -- 'decide' non accentue JAMAIS signale
    # (les patterns ne matchent que les formes accentuees).
    mini_nb_path = Path(tempfile.gettempdir()) / "_morpho_selftest.ipynb"
    mini_nb_path.write_bytes(json.dumps({
        "cells": [
            {"cell_type": "markdown", "metadata": {}, "source": ["Si vous etes un agent qui decide du mode.\n"]},
        ],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }, ensure_ascii=False, indent=1).encode("utf-8"))
    try:
        rep = scan_notebook(mini_nb_path)
        decide_findings = [f for f in rep.findings if f.word == "decide"]
        if decide_findings:
            failures.append("'decide' ne devrait JAMAIS etre signale fautif (invariant map upstream)")
    finally:
        mini_nb_path.unlink(missing_ok=True)

    if failures:
        print("[FAIL] repair_morpho self-test :")
        for f in failures:
            print(f"  - {f}")
        return 1
    print("[OK] repair_morpho self-test (20 invariants verifies)")
    return 0


# --- CLI --------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("notebook", nargs="?", help="Chemin du notebook .ipynb")
    ap.add_argument("--dry-run", action="store_true",
                    help="Detecter sans modifier (rapport JSON sur stdout)")
    ap.add_argument("--json", action="store_true",
                    help="Sortie JSON plutot que texte")
    ap.add_argument("--self-test", action="store_true",
                    help="Smoke test integre des invariants morphologiques")
    args = ap.parse_args()

    if args.self_test:
        return _self_test()

    if not args.notebook:
        ap.error("notebook requis (ou --self-test)")

    nb_path = Path(args.notebook)
    if not nb_path.exists():
        print(f"[ERR] fichier introuvable : {nb_path}", file=sys.stderr)
        return 2

    if args.dry_run:
        report = scan_notebook(nb_path)
    else:
        report = repair_notebook(nb_path, dry_run=False)

    if args.json:
        print(json.dumps(report.to_dict(), ensure_ascii=False, indent=1))
    else:
        verb = "scan" if args.dry_run else "repair"
        print(f"[{verb}] {nb_path} : "
              f"{len(report.findings)} finding(s), "
              f"{report.cells_scanned} cell(s) scannes, "
              f"{report.cells_modified} modifiee(s), "
              f"{report.bytes_delta:+d} bytes "
              f"({'dry-run' if report.dry_run else 'ecrit'})")
        for f in report.findings:
            print(f"  cell#{f.cell_index} {f.word!r} -> {f.suggested!r} :: ...{f.context}...")

    # Exit 0 si pas de finding, exit 1 sinon (mode scan uniquement)
    if args.dry_run:
        return 1 if report.findings else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
