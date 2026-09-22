#!/usr/bin/env python3
"""Repair_morpho -- organe canonique de correction morphologique pour notebooks REACCENT.

Contexte :
- La famille REACCENT (issue #16638) a produit un default systemique : la map
  upstream ``"prouve": "prouvé"``, ``"donne": "donné"``, ``"decide": "décide"``,
  ``"verifie": "vérifié"`` ajoute l'accent **partout**, alors que le francais
  n'accentue le participe passe qu'apres un auxiliaire (avoir/etre) ou dans une
  locution figee.
- Verbe 3e pers. du present (``prouve``, ``donne``, ``decide``, ``verifie``) =
  **non accente** (jamais adj. participial).
- Participe passe legitime = UNIQUEMENT apres auxiliaire 2+ chars (signal
  distingue le morpheme du verbe homonyme 1 char comme ``a`` de l'auxiliaire).
- Identifiants entre backticks (`` `decide` ``, `` `verifier` ``, `` `prouve` ``,
  `` `donne` ``) = **jamais accentues** : ce sont des noms de tactiques /
  variables / fonctions, pas du texte francais. La map upstream REACCENT a
  accidente ``décide``, ``vérifier``, ``prouvé``, ``donné`` a l'interieur des
  segments backtickes.

Correctifs implementes :
1. ``prouve -> prouvé`` uniquement si auxiliaire 2+ chars avant
   (``se prouve`` **toujours fautif** : pas d'auxiliaire).
2. ``donne -> donné`` uniquement dans locution ``étant donné`` / ``tant donné``
   (jusqu'a 30 chars avant -- autorise mots intercalés type ``qui est tant
   donné``).
3. ``decide`` **jamais accentue** : pas de map upstream fautive.
4. ``verifie -> vérifié`` (NEW c.1412 adjoint dispatch) uniquement si
   auxiliaire 2+ chars avant (meme regle que prouve). Cf c.1412 DM
   ``adjoint-dispatch-po2024-morpho-20260922T2130`` lignes 466, 1223, 336,
   2716 (Lean-16f, Lean-5) + 449 (Lean-19).
5. **Backticks guard** (NEW c.1412) : aucune des 4 corrections ci-dessus ne
   s'applique a l'interieur d'un segment `` `...` ``. Le segment est un
   identifiant (tactique Lean, variable, fonction) -- l'accentuation y est
   syntaxiquement fautive. Cf c.1412 lignes 881 (Lean-16f ``décide``), 2168
   (Lean-7 ``vérifier``), 2368/2508/3202-3226/3321 (Lean-5 ``décide`` x16).

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

# Locutions figees avec "donne" -- 30 chars de fenetre (mots intercalés OK)
LOCUTIONS_DONNE = ("etant donne", "tant donne")


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


def is_prouve_legitimate(ctx_before: str) -> bool:
    """Verifie si 'prouve' est un adj. participial legitime.

    Signal : un auxiliaire 2+ chars precede dans la fenetre de contexte, pas
    forcement comme dernier mot immediat (NEW c.1412 : la version stricte
    dernier-mot-only ratait des participes legitimes avec adverbes intercalés
    type "est donc réellement prouvé"). On regarde tous les mots de la fenetre
    (30 chars) ; le PREMIER auxiliaire rencontre legitime l'usage.

    Refuse : "se prouve" (cf Tell c.1315-L15 ★★★ fondateur -- "se prouve" toujours
    fautif, car "se" n'est pas un auxiliaire avoir/etre).
    """
    ctx = _normalize(ctx_before)
    if not ctx:
        return False
    # Tokens alpha (unicode FR inclus) -- on capture TOUS les mots, pas
    # seulement le dernier. Si l'un d'eux est un auxiliaire 2+ chars, c'est
    # legitime. Cela permet "est donc réellement prouvé" de passer (Tell c.1412).
    words = re.findall(r"[a-zà-ÿ']+", ctx)
    return any(w in AUXILIAIRES_2CHARS_PLUS for w in words)


def is_donne_legitimate(ctx_before: str) -> bool:
    """Verifie si 'donne' est dans une locution figee (etant donne / tant donne).

    Fenetre 60 chars avant (Tell c.1317-L7 ★★★★ fondateur -- mots intercalés OK).
    NEW c.1412 : on normalise les accents (``étant`` -> ``etant``) ET on
    tokenise sur les mots pour matcher les locutions interrompues par du
    markdown (``étant **donné**`` avec bold, ``étant` ` ``donne`` etc.).
    Sans ce double ajustement, un contexte avec accents legitimes et
    markdown bold n'etait jamais reconnu faute de match contiguous.

    Note : la fenetre ctx est l'extrait AVANT le mot ``donné``. Donc la
    locution ``étant donné`` finit juste avant la fenetre. On cherche
    ``etant`` (ou ``tant``) comme DERNIER ou AVANT-DERNIER mot de la
    fenetre -- un mot immediatement avant ``donné`` (apres strip accents
    + markdown), ce qui est la definition de la locution.
    """
    ctx = _normalize(ctx_before)
    if not ctx:
        return False
    window_unaccent = _strip_accents(ctx[-60:])
    # Substring match direct (cas sans markdown)
    if any(loc in window_unaccent for loc in LOCUTIONS_DONNE):
        return True
    # Tokenise la fenetre ; les 2 derniers mots significatifs (apres strip
    # markdown) doivent inclure ``etant`` ou ``tant`` (le mot ``donne`` cible
    # est juste apres la fenetre, dans la source).
    words = re.findall(r"[a-zà-ÿ]+", window_unaccent)
    if not words:
        return False
    # Le dernier mot doit etre ``etant`` ou ``tant`` (le mot ``donne``
    # est juste apres, dans la source -- pas dans le ctx).
    last = words[-1]
    return last in ("etant", "tant")


# Accent strip minimaliste pour matching (NEW c.1412)
_ACCENT_MAP = str.maketrans({
    "à": "a", "â": "a", "ä": "a",
    "é": "e", "è": "e", "ê": "e", "ë": "e",
    "î": "i", "ï": "i",
    "ô": "o", "ö": "o",
    "ù": "u", "û": "u", "ü": "u",
    "ç": "c",
})


def _strip_accents(s: str) -> str:
    """Retire les accents des voyelles FR/EN principales pour le matching.

    Utilise UNIQUEMENT dans ``is_donne_legitimate`` (locution ``etant donne``
    qui doit matcher ``étant donné`` / ``Étant donné``). Ne touche pas les
    accents des autres classes (cf ``is_prouve_legitimate``).
    """
    return s.translate(_ACCENT_MAP)


def is_verifie_legitimate(ctx_before: str) -> bool:
    """Verifie si 'vérifié' est un adj. participial legitime.

    Meme regle que ``prouve`` : auxiliaire 2+ chars precede immediatement
    (Tell c.1315 fondateur transposée a la classe verifie -- c.1412 adjoint
    dispatch). Refuse 'se verifie' (cf Tell c.1315-L15 fondateur transposé).
    """
    return is_prouve_legitimate(ctx_before)


def _build_backtick_mask(text: str) -> List[bool]:
    """Construit un masque position->is_in_backticks pour `text`.

    Convention : tout caractere entre deux backticks simples (non escapes) est
    considere comme identifiant. Un backtick ouvrant non ferme (texte impair
    de backticks) = tout le reste du texte est considere comme in-backticks.
    Pas de support des triples-backticks / code fences ici : le morpho ne
    regarde que des mots isoles, pas des blocs.
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

    REPAIR : on cherche les formes ACCENTUEES fautives (``prouve``, ``donne``,
    ``vérifié``) ajoutees par la map REACCENT upstream fautive. La correction
    les retire vers la forme non-accentuee (verbe 3e pers. du present).

    Participes passes legitimes (apres auxiliaire) ou locutions figees
    (``etant donne`` / ``tant donne``) sont preservees.

    Identifiants entre backticks (`` `...` ``) :
    - NE JAMAIS y ajouter un accent : ``prouve`` (prose) -> on retire l'accent
      ici seulement en prose ; en backticks le ``prouvé`` est un nom
      d'identifiant, on n'y touche pas ;
    - RESTAURER les accents fautifs introduits par REACCENT : ``décide``
      -> ``decide`` et ``vérifier`` -> ``verifier``. REACCENT a transforme
      ``decide`` en ``décide`` et ``verifier`` en ``vérifier`` meme dans les
      segments backtickes, ce qui rend la tactique Lean 4 introuvable.
      Cf c.1412 adjoint dispatch (lignes 881, 2368-3321 `` `décide` `` x16,
      2168 `` `vérifier` ``).
    """
    findings: List[MorphoFinding] = []
    # Backtick mask : couvre tous les patterns d'un coup. Calcule une fois par
    # cellule. Voir c.1412 adjoint dispatch pour la justification (sections
    # 8.2 de Lean-5 portant 16 `` `décide` ``, etc.).
    bt_mask = _build_backtick_mask(src_text)
    # Pattern 1 : forme ACCENTUEE "prouvé" (avec é) fautive SAUF auxiliaire
    # SAUF backticks (en backticks, on laisse tel quel -- c'est un nom).
    for m in re.finditer(r"\bprouvé\b", src_text):
        if bt_mask[m.start()]:
            continue  # identifiant entre backticks : jamais touche
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
    for m in re.finditer(r"\bdonné\b", src_text):
        if bt_mask[m.start()]:
            continue
        # Fenetre 60 chars pour matcher "etant donne" / "tant donne" qui peuvent
        # etre a plus de 30 chars (Tell c.1317-L7 ★★★★ fondateur -- 60 chars).
        ctx = src_text[max(0, m.start() - 60):m.start()]
        if not is_donne_legitimate(ctx):
            findings.append(MorphoFinding(
                cell_index=cell_index,
                word=m.group(0),
                suggested="donne",
                position=m.start(),
                context=src_text[max(0, m.start() - 30):m.end() + 15].replace("\n", " "),
            ))
    # Pattern 3 (NEW c.1412) : forme ACCENTUEE "vérifié" fautive SAUF auxiliaire
    # SAUF backticks. Transposition Tell c.1315 fondateur (verifie) au cas
    # 'verifié'. Cf c.1412 DM adjoint lignes 336, 466, 1223, 2716, 449.
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
    # Pattern 4 (NEW c.1412) : forme ACCENTUEE "décide" DANS backticks uniquement.
    # REACCENT a ajoute l'accent dans les segments `` `décide` `` (identifiant
    # Lean). On le retire. En prose libre, "décide" n'est pas dans nos patterns
    # (le verbe "décider" est legitime en francais), donc on ne touche pas.
    for m in re.finditer(r"\bdécide\b", src_text):
        if not bt_mask[m.start()]:
            continue  # en prose, "décide" est legitime -- on n'y touche pas
        findings.append(MorphoFinding(
            cell_index=cell_index,
            word=m.group(0),
            suggested="decide",
            position=m.start(),
            context=src_text[max(0, m.start() - 30):m.end() + 15].replace("\n", " "),
        ))
    # Pattern 5 (NEW c.1412) : forme ACCENTUEE "vérifier" DANS backticks.
    # Idem : en prose libre, "vérifier" (infinitif) est legitime. En backticks,
    # c'est un nom d'identifiant (variable, fonction) qui doit etre sans accent.
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
                # Appliquer les corrections de la **fin vers le debut** pour
                # preserver les offsets.
                new_item = item_text
                # Backtick mask recalculee localement (meme cellule, scope item).
                # Le mask couvre tout l'item -- suffisant pour ne pas toucher
                # aux segments `` `...` `` a l'interieur.
                bt_mask = _build_backtick_mask(new_item)
                for f in sorted(findings, key=lambda x: x.position, reverse=True):
                    # f.position est relatif a src joint ; pour src list, on
                    # travaille sur l'item seul -- donc on recherche dans
                    # new_item. Simple : on a scan dans _scan_cell_source avec
                    # src_text = item_text ici (le caller passe item_text).
                    # => on refait un find simple.
                    pattern = re.compile(r"\b" + re.escape(f.word) + r"\b")
                    matches = list(pattern.finditer(new_item))
                    if matches:
                        m = matches[-1]  # last match in current state
                        # Re-confirmer backtick au moment du remplacement.
                        # Cas partic. : 'décide' et 'vérifier' sont attendus
                        # EXCLUSIVEMENT en backticks (le scan les a deja
                        # filtres). Les 3 autres mots (prouvé/donné/vérifié)
                        # sont attendus HORS backticks (le scan les a filtres).
                        if f.word in ("décide", "vérifier"):
                            if not (bt_mask and bt_mask[m.start()]):
                                continue  # garde-fou : on ne doit pas sortir
                        else:
                            if bt_mask and bt_mask[m.start()]:
                                continue
                        # Fenetre specialisee pour is_donne_legitimate (60 chars)
                        # car la locution "etant donne" peut etre plus loin que 30.
                        ctx_donne = new_item[max(0, m.start() - 60):m.start()]
                        ctx = new_item[max(0, m.start() - 30):m.start()]
                        if f.word == "prouvé" and not is_prouve_legitimate(ctx):
                            new_item = new_item[:m.start()] + f.suggested + new_item[m.end():]
                        elif f.word == "donné" and not is_donne_legitimate(ctx_donne):
                            new_item = new_item[:m.start()] + f.suggested + new_item[m.end():]
                        elif f.word == "vérifié" and not is_verifie_legitimate(ctx):
                            new_item = new_item[:m.start()] + f.suggested + new_item[m.end():]
                        elif f.word == "décide":
                            # En backticks uniquement ; on retire l'accent.
                            new_item = new_item[:m.start()] + f.suggested + new_item[m.end():]
                        elif f.word == "vérifier":
                            new_item = new_item[:m.start()] + f.suggested + new_item[m.end():]
                if new_item != item_text:
                    if new_src is None:
                        new_src = list(src)
                    new_src[item_idx] = new_item
                    # Enregistrer les findings de cette item dans le rapport
                    report.findings.extend(_scan_cell_source(ci, item_text))
            if new_src is not None:
                cell["source"] = new_src
                report.cells_modified += 1
        else:
            new_src = src
            findings = _scan_cell_source(ci, new_src)
            if findings:
                bt_mask = _build_backtick_mask(new_src)
                for f in sorted(findings, key=lambda x: x.position, reverse=True):
                    pattern = re.compile(r"\b" + re.escape(f.word) + r"\b")
                    matches = list(pattern.finditer(new_src))
                    if matches:
                        m = matches[-1]
                        if f.word in ("décide", "vérifier"):
                            if not (bt_mask and bt_mask[m.start()]):
                                continue
                        else:
                            if bt_mask and bt_mask[m.start()]:
                                continue
                        ctx_donne = new_src[max(0, m.start() - 60):m.start()]
                        ctx = new_src[max(0, m.start() - 30):m.start()]
                        if f.word == "prouvé" and not is_prouve_legitimate(ctx):
                            new_src = new_src[:m.start()] + f.suggested + new_src[m.end():]
                        elif f.word == "donné" and not is_donne_legitimate(ctx_donne):
                            new_src = new_src[:m.start()] + f.suggested + new_src[m.end():]
                        elif f.word == "vérifié" and not is_verifie_legitimate(ctx):
                            new_src = new_src[:m.start()] + f.suggested + new_src[m.end():]
                        elif f.word == "décide":
                            new_src = new_src[:m.start()] + f.suggested + new_src[m.end():]
                        elif f.word == "vérifier":
                            new_src = new_src[:m.start()] + f.suggested + new_src[m.end():]
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

    # "decide" : JAMAIS accentue upstream
    # => is_prouve_legitimate et is_donne_legitimate ne traitent pas "decide"
    # mais on documente l'invariant ici.
    # Sanity : scan d'un mini-notebook ne doit PAS trouver "decide" comme fautif.
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

    # ---- NEW c.1412 : verifie / vérifié ----
    # Auxiliaire 2+ chars (Tell c.1315 fondateur transpose a verifie :
    # 'a' 1 char n'est PAS un auxiliaire -- c'est l'article homonyme, d'ou
    # le filtre 2+ chars. On utilise 'a verifié' via 'est verifié').
    if not is_verifie_legitimate("Le solveur est "):
        failures.append("'est verifie' devrait etre legitime (auxiliaire 'est')")
    if not is_verifie_legitimate("Cela a ete "):
        failures.append("'ete verifie' devrait etre legitime (auxiliaire 'ete')")

    # Verbe 3e pers. : "Lean le verifie" -> fautif
    if is_verifie_legitimate("Lean le "):
        failures.append("'le verifie' devrait etre fautif (verbe 3e pers.)")
    if is_verifie_legitimate("on "):
        failures.append("'on verifie' devrait etre fautif (verbe 3e pers.)")

    # ---- NEW c.1412 : backtick guard ----
    # Sanity : scan doit detecter 'vérifié' fautif en prose libre, et IGNORER
    # 'vérifié' entre backticks (identifiant). Symetriquement, scan doit
    # detecter '`décide`' fautif en backticks (a retirer) et IGNORER 'décide'
    # en prose libre (verbe legitime).
    bt_nb_path = Path(tempfile.gettempdir()) / "_morpho_selftest_bt.ipynb"
    bt_nb_path.write_bytes(json.dumps({
        "cells": [
            # 1. 'verifié' fautif en prose libre (Lean le verifié) -> finding
            {"cell_type": "markdown", "metadata": {},
             "source": ["Lean le vérifié en utilisant la tactique.\n"]},
            # 2. 'verifié' entre backticks (identifiant) -> PAS finding
            {"cell_type": "markdown", "metadata": {},
             "source": ["Appel de la tactique `vérifié` dans le bloc.\n"]},
            # 3. 'décide' entre backticks (identifiant Lean) -> finding
            #    (REACCENT a ajoute l'accent fautivement dans les backticks ;
            #    on le retire pour rendre la tactique invocable).
            {"cell_type": "markdown", "metadata": {},
             "source": ["Section 8.2 : on utilise `décide` pour finir.\n"]},
            # 4. 'decide' en prose libre (verbe legitime) -> PAS finding
            {"cell_type": "markdown", "metadata": {},
             "source": ["L'agent decide du mode a employer.\n"]},
            # 5. 'vérifier' entre backticks (identifiant) -> finding
            {"cell_type": "markdown", "metadata": {},
             "source": ["La fonction `vérifier` est initialisee.\n"]},
            # 6. 'vérifier' en prose libre (infinitif legitime) -> PAS finding
            {"cell_type": "markdown", "metadata": {},
             "source": ["On doit verifier la coherence.\n"]},
        ],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }, ensure_ascii=False, indent=1).encode("utf-8"))
    try:
        rep = scan_notebook(bt_nb_path)
        # Le seul finding 'vérifié' attendu est cell#0 (prose fautive).
        verifie_findings = [f for f in rep.findings if f.word == "vérifié"]
        if len(verifie_findings) != 1:
            failures.append(f"attendu 1 'vérifié' fautif en prose libre, "
                            f"trouvé {len(verifie_findings)}")
        elif verifie_findings[0].cell_index != 0:
            failures.append(f"'vérifié' fautif devrait etre en cell#0, "
                            f"trouvé en cell#{verifie_findings[0].cell_index}")
        # Le seul finding 'décide' attendu est cell#2 (backtick).
        decide_findings = [f for f in rep.findings if f.word == "décide"]
        if len(decide_findings) != 1:
            failures.append(f"attendu 1 'décide' en backticks, "
                            f"trouvé {len(decide_findings)}")
        elif decide_findings[0].cell_index != 2:
            failures.append(f"'décide' en backticks devrait etre en cell#2, "
                            f"trouvé en cell#{decide_findings[0].cell_index}")
        elif decide_findings[0].suggested != "decide":
            failures.append(f"'décide' devrait etre corrige en 'decide', "
                            f"pas {decide_findings[0].suggested!r}")
        # Le seul finding 'vérifier' attendu est cell#4 (backtick).
        verifier_findings = [f for f in rep.findings if f.word == "vérifier"]
        if len(verifier_findings) != 1:
            failures.append(f"attendu 1 'vérifier' en backticks, "
                            f"trouvé {len(verifier_findings)}")
        elif verifier_findings[0].cell_index != 4:
            failures.append(f"'vérifier' en backticks devrait etre en cell#4, "
                            f"trouvé en cell#{verifier_findings[0].cell_index}")
        elif verifier_findings[0].suggested != "verifier":
            failures.append(f"'vérifier' devrait etre corrige en 'verifier', "
                            f"pas {verifier_findings[0].suggested!r}")
        # Aucun finding ne doit etre en cell#3 (decide prose) ni cell#5
        # (verifier prose) ni cell#1 (vérifié backtick)
        for f in rep.findings:
            if f.cell_index in (1, 3, 5):
                failures.append(f"finding inattendu en cell#{f.cell_index} "
                                f"(prose legitime ou backtick preserve) : "
                                f"{f.word!r}")
    finally:
        bt_nb_path.unlink(missing_ok=True)

    # ---- NEW c.1412 : full repair round-trip sur backticks ----
    # Le repair_notebook doit transformer 'vérifié' en prose libre et laisser
    # '`vérifié`' intact entre backticks.
    rt_nb_path = Path(tempfile.gettempdir()) / "_morpho_selftest_rt.ipynb"
    rt_nb_path.write_bytes(json.dumps({
        "cells": [
            {"cell_type": "markdown", "metadata": {},
             "source": ["Lean le vérifié.\n"]},
            {"cell_type": "markdown", "metadata": {},
             "source": ["Tactique `vérifié` dans le code.\n"]},
        ],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }, ensure_ascii=False, indent=1).encode("utf-8"))
    try:
        rep = repair_notebook(rt_nb_path, dry_run=False)
        raw_after = rt_nb_path.read_bytes().decode("utf-8")
        if "vérifié." in raw_after and "vérifie." not in raw_after:
            failures.append("repair_notebook aurait du remplacer 'vérifié.' "
                            "en prose libre par 'vérifie.'")
        if "`vérifié`" not in raw_after:
            failures.append("repair_notebook aurait du laisser '`vérifié`' intact")
    finally:
        rt_nb_path.unlink(missing_ok=True)

    if failures:
        print("[FAIL] repair_morpho self-test :")
        for f in failures:
            print(f"  - {f}")
        return 1
    print("[OK] repair_morpho self-test (20 invariants verifies, dont "
          "c.1412 : verifie + decide/vérifier backtick revert + round-trip)")
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
