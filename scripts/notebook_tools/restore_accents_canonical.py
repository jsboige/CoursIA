#!/usr/bin/env python3
"""Cure canonique des accents francais (registre #2876) — markdown-CELL-SOURCE STRICT.

Pourquoi cet outil existe
-------------------------
Le registre #2876 (restauration des accents francais) a accumule ~60 PRs manuelles,
chacune faite avec un **script ad-hoc non-committe**. Ces scripts ad-hoc sont la
source racine des regressions repetees qui ont mine le registre :

  - #7094/#7143/#7154/#7162/#7167/#7179 : scripts ad-hoc on accentue des
    **identifiants de code** (variables/parametres/proprietes) — HORS scope.
  - #7135/#7145 : scripts ad-hoc accentuent les **cibles de liens markdown**
    `](...ipynb)` -> lien casse (le fichier reel sur disque reste sans accent).
  - #7105/#7124/#7132 : scripts ad-hoc re-executent / regenerent les **outputs**
    et **execution_count** -> diff non-accents-only, re-execute des cellules.

Chaque regression = un script ad-hoc qui n'appliquait PAS les 4 bright-lines du
registre. Cet outil les applique PAR CONSTRUCTION :

  1. **markdown-cell-source ONLY** : `if cell_type != 'markdown': continue`.
     Les cellules code sont integres (ni identifiants, ni commentaires, ni stdout
     touches). C'est le contrat #2876 "markdown-only STRICT" (adjudication ai-01
     17/07).
  2. **skip link targets** : les spans `]( ... )` sont proteges (masques avant la
     cure, restaures apres). Accentuer une cible de lien la decoit du fichier reel
     sur disque (bright-line raffine ai-01 18/07).
  3. **skip code** : consequence de (1) — aucune cellule code n'est touchee.
  4. **skip outputs / execution_count** : seule la cle `source` de chaque cellule
     markdown est re-ecrite ; `outputs`, `execution_count`, `metadata` sont
     intacts. Diff = accents-only, jamais un delta de re-execution.

Comment ca marche
-----------------
Reutilise le dictionnaire CONSERVATEUR `ACCENT_PAIRS` + la regex de
`detect_accent_stripping.py` (source unique de la PAIRE stripped->accentue).
Ce dictionnaire n'inclut QUE les paires ou la forme *stripped* n'est PAS un mot
francais valide (ex. "parametre"->"parametre") : la restauration est donc non-
ambigue ("a"/"ou"/"la"/"tres" exclus car mots FR valides sans accent).

La restauration preserve la casse : le match reutilise `m.group(0)` tel quel pour
remplacer la sous-chaine matchee, et la suggestion est case-ajustee (capitalisee
si le match commence par une majuscule).

Usage
-----
    # dry-run : liste les cures prevues sans ecrire
    python restore_accents_canonical.py NB.ipynb --dry-run
    # applique en place (re-ecrit NB.ipynb)
    python restore_accents_canonical.py NB.ipynb
    # --check : exit 1 si des cures sont disponibles (CI-ready, n'ecrit rien)
    python restore_accents_canonical.py NB.ipynb --check
    # --check --scope : exit 1 aussi si le notebook contient deja des cures dans
    #                   des cellules CODE (signe qu'un script ad-hoc a precede)
    python restore_accents_canonical.py NB.ipynb --check --scope

Exit codes
----------
    0 -- rien a curer (ou mode non --check)
    1 -- cures disponibles (--check seulement)
    2 -- erreur (notebook illisible)

Voir aussi
----------
- detect_accent_stripping.py : la moitie DETECTION (dictionnaire + regex source).
- check_identifier_regression.py : le GATE anti-regression-identifiant (vet les
  PRs accents pour le over-reach code, complementaire de cette cure defensive).
- Memoires : issue-2876-scope-boundary-markdown-vs-code-pending-adjudication
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Reutilisation de la source unique de verite : dictionnaire + regex de detection.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import detect_accent_stripping as das  # noqa: E402

ACCENT_PAIRS = das.ACCENT_PAIRS
# La regex matche les formes *stripped* (frontieres de mot, insensible casse).
_CURE_RE = das._build_regex()

# Regex protegeant les spans de cible de lien markdown : ]( ... ). On MASQUE ces
# spans avant la cure (remplace par un placeholder sans lettres accentuables) et
# on les restaure apres, pour ne JAMAIS accentuer une cible de lien/chemin/URL.
# Couvre [display](target), ![alt](src), et les refs de type ](url "title").
# On matche depuis le `](` jusqu'a la parenthese fermante (greedy minimal sur la
# meme ligne ; les liens markdown ne contiennent pas de ")" nu dans la cible).
_LINK_TARGET_RE = re.compile(r"\]\([^)]*\)")
# #14613 point 4 (porte de la cure #14139 dans l'organe canonique) : les spans
# de code inline `...` et les URLs NUES (hors cible de lien) sont masques au
# meme titre que les cibles de lien. Un mot du dictionnaire dans un span de code
# (nom de variable, argument CLI) ou dans le chemin d'une URL n'est pas de la
# prose -- l'accentuer casse le code ou le lien. Ces masques vivent dans le
# COEUR `_cure_line` (pas seulement l'adaptateur decks) : le chemin notebook en
# beneficie aussi, uniformement.
_INLINE_SPAN_RE = re.compile(r"`[^`\n]*`")
_BARE_URL_RE = re.compile(r"\bhttps?://\S+")


def _preserve_case(match_str: str, suggestion: str) -> str:
    """Ajuste la casse de la suggestion a celle du match.

    Le dictionnaire est en minuscules ; si le match original commence par une
    majuscule (ex. 'Parametre' en debut de phrase), on capitalise la suggestion.
    Le tout-majuscule (rare en prose FR) est aussi preserve.
    """
    if match_str.isupper() and len(match_str) > 1:
        return suggestion.upper()
    if match_str[0].isupper():
        return suggestion[0].upper() + suggestion[1:]
    return suggestion


def _cure_line(line: str) -> tuple[str, int]:
    """Cure une ligne de markdown : accentue les formes stripped dans la PROSE,
    en protegeant les cibles de liens ]( ... ), les spans de code inline et les
    URLs nues (#14613 point 4).

    Retourne (ligne_curee, n_cures).
    """
    # 1. extraire + masquer les zones non-prose. Chaque span protege est remplace
    # par un placeholder indexe qui ne peut matcher aucun mot du dictionnaire
    # (lettres uniquement). Le contenu original est preserve tel quel dans la
    # liste masked_spans, restaure byte-identique a l'etape 3.
    masked_spans: list[str] = []

    def _mask(m):
        masked_spans.append(m.group(0))
        return "\x00MS{}\x00".format(len(masked_spans) - 1)

    masked = _LINK_TARGET_RE.sub(_mask, line)
    masked = _INLINE_SPAN_RE.sub(_mask, masked)
    masked = _BARE_URL_RE.sub(_mask, masked)

    # 2. curer la prose (hors spans masques)
    n = [0]

    def _repl(m):
        key = m.group(0).lower()
        suggestion = ACCENT_PAIRS.get(key)
        if suggestion is None:
            return m.group(0)
        n[0] += 1
        return _preserve_case(m.group(0), suggestion)

    cured = _CURE_RE.sub(_repl, masked)

    # 3. restaurer les spans proteges (byte-identiques a l'original)
    for i, original in enumerate(masked_spans):
        cured = cured.replace("\x00MS{}\x00".format(i), original, 1)
    return cured, n[0]


def _cure_source(source) -> tuple[object, int]:
    """Cure le `source` d'une cellule (list[str] nbformat ou str).

    Retourne (nouveau_source, n_cures) en PRESERVANT le type original
    (list reste list, str reste str) et la structure nbformat (chaque element
    de la liste garde son saut de ligne final eventuel).
    """
    if isinstance(source, str):
        lines = source.split("\n")
        cured_lines = []
        total = 0
        in_fence = False
        for ln in lines:
            # #14613 point 4 : une fence reproduit souvent une sortie LITTERALE
            # de programme (« Entrainement PPO ... : eval deterministe finale =
            # 418.9 », fences 22/24 de #14139). Accentuer une transcription
            # d'execution la falsifie (Stop & Repair, secrets-hygiene regle 6) :
            # les lignes de fence (delimiteurs inclus) ne sont JAMAIS curees.
            if _FENCE_RE.match(ln):
                cured_lines.append(ln)
                in_fence = not in_fence
                continue
            if in_fence:
                cured_lines.append(ln)
                continue
            cl, n = _cure_line(ln)
            cured_lines.append(cl)
            total += n
        return "\n".join(cured_lines), total
    # list nbformat : chaque chunk peut porter son \n final. On cure CHAQUE CHUNK
    # IN-PLACE (split le chunk en lignes, cure chaque ligne, rejoinde), SANS JAMAIS
    # concatener les chunks entre eux. Pourquoi : un join global -> split -> re-chunk
    # perd l'alignement quand un chunk est un separateur de paragraphe nu ("\n") — le
    # re-decoupage l'absorbe et COLLAPSE les paragraph breaks markdown ("\n\n" -> "\n").
    # Bug firsthand sur Infer-14 (28/33 cellules avec paragraph breaks collapsees,
    # po-2024 c.634) : le chunk standalone "\n" disparait. La cure per-chunk preserve
    # byte-pour-byte la structure de liste (boundaries chunk + trailing \n + blank-line
    # separators) ET applique les accents ligne-par-ligne dans chaque chunk.
    original = list(source)
    new_chunks = []
    total = 0
    in_fence = False  # l'etat persiste d'un chunk a l'autre de la MEME cellule
    for chunk in original:
        lines = chunk.split("\n")
        cured_lines = []
        for ln in lines:
            if _FENCE_RE.match(ln):
                cured_lines.append(ln)
                in_fence = not in_fence
                continue
            if in_fence:
                cured_lines.append(ln)
                continue
            cl, n = _cure_line(ln)
            cured_lines.append(cl)
            total += n
        new_chunks.append("\n".join(cured_lines))
    if new_chunks == original:
        return original, 0  # rien change -> retourner l'original byte-identique
    return new_chunks, total


# --------------------------------------------------------------------------
# Adaptateur markdown pur (.md) — decks Slidev, Epic #11508 lot L1.
#
# Pourquoi un adaptateur et pas un second outil : `accent-cure-defense-in-depth.md`
# interdit la cure ad-hoc, qui est la cause racine de chaque regression #2876.
# Le coeur (`_cure_line`, masquage des cibles de liens, preservation de casse) est
# reutilise tel quel ; seules les ZONES A PROTEGER changent entre un notebook et
# un deck.
#
# Mesure qui a motive ces masques, prise en lecture seule sur les 18 decks de
# `slides/` le 2026-08-17 (detail sur l'issue #11508) : la cure notebook appliquee
# telle quelle proposait 979 cures, dont 146 STRUCTURELLEMENT fausses. La plus
# grave etait unanime :
#
#     theme: ../theme-ia101      ->      theme: ../theme-ia101   (accentue)
#
# `theme:` est la cle de configuration Slidev, ligne 2, presente dans 18 decks
# sur 18. La cure cassait donc CHAQUE deck. Ce n'est pas un defaut du coeur : il
# a ete ecrit pour la `source` de cellules nbformat, ou aucun frontmatter YAML
# n'apparait.
#
# Quatre zones protegees, chacune adossee a un faux positif mesure :
#   - frontmatter YAML (document + par-slide)  : 46 occurrences
#   - blocs de code ``` / ~~~                  : 64 occurrences
#   - code inline `...`                        : 30 occurrences
#   - attributs HTML src=/href=/style=         :  6 occurrences
#
# `alt=` est DELIBEREMENT laisse curable : l'inventaire de #11508 demande
# explicitement de curer le texte alternatif (lu par les lecteurs d'ecran et
# l'indexation), et les commentaires HTML le sont aussi — verifie sur
# `S1-argumentation:144`.

_FENCE_RE = re.compile(r"^\s{0,3}(?:```|~~~)")
_SEPARATOR_RE = re.compile(r"^-{3,}\s*$")
# Une ligne de frontmatter : `cle:` eventuellement indentee, ou une continuation
# indentee / un item de liste sous une cle.
_YAML_KEY_RE = re.compile(r"^\s*[A-Za-z_][\w.-]*\s*:")
_YAML_CONT_RE = re.compile(r"^(?:\s+\S|\s*-\s)")
_INLINE_CODE_RE = re.compile(r"`[^`\n]*`")
# Cles de frontmatter dont la VALEUR est du texte AFFICHE par Slidev : `title`
# alimente l'onglet du navigateur et les metadonnees du PDF exporte, `info` le
# panneau d'information. Les laisser sous le masque global protegeait donc de la
# prose visible — mesure le 2026-08-18 sur les 18 decks : 8 lignes, dont
# `title: "Intelligence Artificielle - Theorie des jeux"` et
# `title: "Web Semantique - dotNetRDF & Python"`. Le deck exportait « Theorie »
# dans ses propres metadonnees PDF.
#
# Toutes les AUTRES cles restent protegees en bloc, sans exception : `theme:`,
# `layout:`, `class:`, `src:`, `transition:` sont de la configuration, et une
# seule d'entre elles accentuee casse le deck (c'est le faux positif fondateur).
# La liste est donc une whitelist de prose, jamais une blacklist de config.
_YAML_PROSE_RE = re.compile(r"^(\s*(?:title|info)\s*:\s*)(\S.*)$")
# src / href / style / class / id : jamais de prose. `alt` en est ABSENT a dessein.
_HTML_ATTR_RE = re.compile(
    r"""\b(?:src|href|style|class|id|width|height|data-[\w-]+)\s*=\s*(?:"[^"]*"|'[^']*')""",
    re.IGNORECASE,
)

# Zone grise FR/EN : formes du dictionnaire qui sont AUSSI des mots anglais valides
# (`strategies`, `execution`, `role`, `iteration`...). Mesure #11508 (commentaire
# de l'inventaire) : ~15 formes, dont les FP reels ASPIC *Structured Preferences*,
# Boole *Mathematical Theories*, **Value/Policy Iteration**. Une cure sans garde
# accentue une ligne entierement anglaise (« The strategies of execution and the
# role of the model » -> « The stratégies of exécution and the rôle of the model »,
# mesure firsthand sur l'adaptateur #11548). La detection NEGATIVE (chercher des
# mots-outils anglais) sous-detecte : « - **Value Iteration** » n'en porte aucun.
# On exige donc la PREUVE POSITIVE d'un contexte francais (mot-outil univoquement
# FR sur la ligne) pour curer une forme en collision — doctrine
# accent-cure-defense-in-depth : ne pas toucher vaut mieux que risquer.
_EN_COLLIDING_FORMS = {
    "strategies", "execution", "executions", "experience", "experiences",
    "preferences", "preference", "role", "roles", "selection",
    "iteration", "iterations", "theories", "theorie", "scenarios",
    "element", "elements", "difference", "differences",
    "operations", "operation", "categories", "categorie",
    "theme", "themes", "different", "generation", "generations",
    "scenario", "resultat", "resultats",
    # Famille RL #14613 : mots anglais valides ajoutes a ACCENT_PAIRS -- la
    # garde a preuve positive de contexte FR s'applique a eux aussi. NB
    # « evaluation » reste hors table (exclusion EN-valide délibérée,
    # cf das.ACCENT_PAIRS).
    "equivalent", "creation", "episode", "episodes",
}
_EN_COLLIDING = {k for k in ACCENT_PAIRS if k in _EN_COLLIDING_FORMS}
_FR_MARKER_RE = re.compile(
    r"\b(le|la|les|des|du|de|une|et|ou|dans|pour|sur|avec|par|au|aux|ce|cet|"
    r"cette|ces|sont|nous|vous|il|elle|ils|elles|qui|que|quoi|dont|mais|donc|"
    r"puis|en)\b")


def _fence_mask(lines: list[str]) -> list[bool]:
    """True pour chaque ligne d'un bloc de code, delimiteurs inclus.

    Isole du masque global parce que la distinction porte une decision : dans un
    frontmatter, la valeur d'une cle de prose est curable (cf `_YAML_PROSE_RE`) ;
    dans une fence, `title: ...` peut etre un exemple de YAML montre au lecteur,
    et rien n'y est curable.
    """
    protected = [False] * len(lines)
    in_fence = False
    for i, ln in enumerate(lines):
        if _FENCE_RE.match(ln):
            protected[i] = True
            in_fence = not in_fence
            continue
        protected[i] = in_fence
    return protected


def _frontmatter_and_fence_mask(lines: list[str]) -> list[bool]:
    """Retourne, pour chaque ligne, True si elle est PROTEGEE (frontmatter ou fence).

    Le fence est suivi en premier : un `---` a l'interieur d'un bloc de code n'est
    pas un separateur de slide.

    Un segment (entre deux `---`) est reconnu comme frontmatter quand sa premiere
    ligne non vide est une cle YAML et que toutes les suivantes sont cles ou
    continuations indentees. Un segment qui porte la moindre ligne de prose n'en
    est pas un — la direction sure : dans le doute, on ne protege pas plus large
    que necessaire, mais on ne cure jamais un segment dont chaque ligne ressemble
    a de la configuration.

    L'exigence sur la PREMIERE ligne non vide est le correctif d'un faux negatif
    mesure (po-2024, 2026-08-18) : `_YAML_CONT_RE` matche aussi les items de
    liste (`^\\s*-\\s`), donc un segment fait uniquement de puces — une slide
    sans phrase, cas frequent — satisfaisait "toutes lignes = cles ou
    continuations" et etait protege en bloc : 0 cure la ou la prose etait
    accentuable. Un frontmatter reel de Slidev commence TOUJOURS par une cle.
    """
    n = len(lines)
    # 1. fences
    protected = _fence_mask(lines)
    # 2. segments delimites par `---` hors fence
    seps = [i for i, ln in enumerate(lines)
            if _SEPARATOR_RE.match(ln) and not protected[i]]
    bounds = [-1] + seps + [n]
    for a, b in zip(bounds, bounds[1:]):
        seg = range(a + 1, b)
        body = [lines[i] for i in seg if lines[i].strip()]
        if not body:
            continue
        if not _YAML_KEY_RE.match(body[0]):
            continue
        if all(_YAML_KEY_RE.match(ln) or _YAML_CONT_RE.match(ln) for ln in body[1:]):
            for i in seg:
                protected[i] = True
    return protected


def _cure_markdown_line(line: str) -> tuple[str, int]:
    """Cure une ligne de markdown pur : masque code inline + attributs HTML,
    applique la zone grise FR/EN (preuve positive de contexte francais pour les
    formes en collision), puis delegue au coeur `_cure_line` (qui protege deja
    les cibles de liens).
    """
    spans: list[str] = []

    def _mask(m):
        spans.append(m.group(0))
        return "\x00MD{}\x00".format(len(spans) - 1)

    masked = _INLINE_CODE_RE.sub(_mask, line)
    masked = _HTML_ATTR_RE.sub(_mask, masked)
    if _EN_COLLIDING and not _FR_MARKER_RE.search(masked):
        # Pas de preuve de contexte francais : neutraliser les formes en
        # collision en les masquant (le coeur ne les verra pas).
        def _mask_form(m):
            spans.append(m.group(0))
            return "\x00MD{}\x00".format(len(spans) - 1)
        masked = _CURE_RE.sub(
            lambda m: _mask_form(m) if m.group(0).lower() in _EN_COLLIDING
            else m.group(0),
            masked)
    cured, n = _cure_line(masked)
    for i, original in enumerate(spans):
        cured = cured.replace("\x00MD{}\x00".format(i), original, 1)
    return cured, n


def cure_markdown(path: Path, write: bool):
    """Cure un fichier markdown pur (.md). Retourne dict {cures, lines_touched, lines}."""
    try:
        text = path.read_bytes().decode("utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        return {"error": str(exc)}

    ends_with_newline = text.endswith("\n")
    raw_lines = text.split("\n")
    if ends_with_newline:
        raw_lines = raw_lines[:-1]

    # Fin de ligne PRESERVEE, par ligne. Les decks du depot sont incoherents :
    # mesure du 2026-08-18, `slides/02-resolution-problemes/slides.md` est
    # committe en CRLF quand `slides/01-introduction/slides.md` l'est en LF, et
    # `.gitattributes` ne couvre pas `slides/**/*.md`. Ecrire LF sans regarder
    # renormalisait donc le deck 02 en entier : 1605 lignes de diff pour 25
    # cures — un diff qui n'est plus accents-only, exactement la classe de
    # defaut #7105/#7124/#7132 du registre #2876 dans un autre habit. Un `\r`
    # n'est retire que lorsqu'un `\n` le suivait ; le residu d'une derniere
    # ligne non terminee reste du contenu.
    n_lines = len(raw_lines)
    crlf: list[bool] = []
    lines: list[str] = []
    for idx, ln in enumerate(raw_lines):
        followed_by_nl = ends_with_newline or idx < n_lines - 1
        if followed_by_nl and ln.endswith("\r"):
            crlf.append(True)
            lines.append(ln[:-1])
        else:
            crlf.append(False)
            lines.append(ln)

    protected = _frontmatter_and_fence_mask(lines)
    in_fence = _fence_mask(lines)
    total = 0
    touched = 0
    out = []
    for ln, is_protected, is_fence in zip(lines, protected, in_fence):
        if is_protected:
            # Seule exception au masque : la VALEUR d'une cle de prose dans un
            # frontmatter (jamais dans une fence, ou `title:` peut etre un
            # exemple de YAML montre au lecteur). La cle elle-meme n'est jamais
            # touchee — c'est le groupe 1, reinjecte tel quel.
            if not is_fence:
                m = _YAML_PROSE_RE.match(ln)
                if m:
                    cured_value, n = _cure_markdown_line(m.group(2))
                    if n:
                        total += n
                        touched += 1
                        out.append(m.group(1) + cured_value)
                        continue
            out.append(ln)
            continue
        cured, n = _cure_markdown_line(ln)
        if n:
            total += n
            touched += 1
        out.append(cured)

    if write and total > 0:
        parts: list[str] = []
        for idx, (ln, is_crlf) in enumerate(zip(out, crlf)):
            parts.append(ln)
            if idx < len(out) - 1 or ends_with_newline:
                parts.append("\r\n" if is_crlf else "\n")
        path.write_bytes("".join(parts).encode("utf-8"))
    return {"cures": total, "lines_touched": touched, "lines": len(lines)}


def cure_notebook(path: Path, write: bool, check_scope: bool = False):
    """Cure un notebook. Retourne dict {cures, cells_touched, md_cells, code_hits}.

    code_hits > 0 (mode --check --scope) = le notebook contient des formes
    accentuables dans des cellules CODE -> signe qu'un script ad-hoc precedent
    a peut-etre laisse du code a curer (HORS scope #2876) -> flag.
    """
    try:
        with open(path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return {"error": str(exc)}

    total_cures = 0
    cells_touched = 0
    md_cells = 0
    code_hits = 0
    shadow_cells: list[dict] = []

    for cell in nb.get("cells", []):
        ctype = cell.get("cell_type", "")
        source = cell.get("source", "")
        if ctype == "markdown":
            md_cells += 1
            new_source, n = _cure_source(source)
            # copie ombre avec la source CUREE (ecrite ou simulee) pour le
            # rapport hors-table ci-dessous -- jamais ecrite sur disque
            shadow_cells.append({**cell, "source": new_source})
            if n > 0:
                total_cures += n
                cells_touched += 1
                if write:
                    cell["source"] = new_source
                    # outputs/execution_count/metadata intacts (jamais touches)
        else:
            shadow_cells.append(cell)
        if ctype == "code" and check_scope:
            # mode scope : detecter les formes accentuables residuelles en code
            code_text = "".join(source) if isinstance(source, list) else (source or "")
            code_hits += sum(1 for _ in _CURE_RE.finditer(code_text))

    if write and total_cures > 0:
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            json.dump(nb, f, ensure_ascii=False, indent=1)
            f.write("\n")
    result = {
        "cures": total_cures,
        "cells_touched": cells_touched,
        "md_cells": md_cells,
        "code_hits": code_hits,
    }
    # #14613 point 1 : un cureur qui ne peut pas atteindre le critere du
    # detecteur doit le DIRE. Apres la passe (ecrite ou simulee), on rejoue
    # l'heuristique OUVERTE du detecteur sur le notebook cure et on rapporte
    # les formes qu'elle voit encore et que la table fermee ne sait pas curer
    # -- l'ecart qui coutait un aller-retour complet sur #14139 : « CURED (written)
    # N accents » en succes muet alors que le compte detecteur restait au-dessus
    # du seuil. Import paresseux (le module n'est utile que pour ce rapport).
    try:
        import detect_markdown_deaccent as dmd
        shadow = {"cells": shadow_cells}
        auto = dmd.find_candidates(shadow).get("auto") or {}
        hors_table = {w: c for w, c in auto.items()
                      if w.lower() not in ACCENT_PAIRS}
        if hors_table:
            result["hors_table"] = hors_table
            result["hors_table_total"] = sum(hors_table.values())
    except Exception:
        pass  # le rapport est un service, jamais un bloqueur de cure
    return result


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("notebook", help="Chemin du notebook (.ipynb) ou du markdown (.md)")
    p.add_argument("--dry-run", action="store_true",
                   help="Liste les cures prevues sans ecrire (defaut)")
    p.add_argument("--apply", action="store_true",
                   help="Applique les cures en place (re-ecrit le notebook)")
    p.add_argument("--check", action="store_true",
                   help="Exit 1 si des cures sont disponibles (CI-ready, n'ecrit rien)")
    p.add_argument("--scope", action="store_true",
                   help="Avec --check : exit 1 aussi si du code contient des formes "
                        "accentuables residuelles (signe de script ad-hoc precedent)")
    p.add_argument("--json", action="store_true", help="Sortie machine JSON")
    args = p.parse_args(argv)

    if args.apply and args.check:
        print("--apply et --check sont mutuellement exclusifs", file=sys.stderr)
        return 2
    write = args.apply

    nb_path = Path(args.notebook)
    if not nb_path.exists():
        print(f"Notebook introuvable: {nb_path}", file=sys.stderr)
        return 2

    is_md = nb_path.suffix.lower() in {".md", ".markdown"}
    if is_md:
        if args.scope:
            print("--scope n'a pas de sens sur un .md (pas de cellules code)",
                  file=sys.stderr)
            return 2
        res = cure_markdown(nb_path, write=write)
    else:
        res = cure_notebook(nb_path, write=write, check_scope=args.scope)
    if "error" in res:
        msg = f"Fichier illisible: {res['error']}"
        if args.json:
            print(json.dumps({"error": msg}, ensure_ascii=False))
        else:
            print(msg, file=sys.stderr)
        return 2

    if args.json:
        out = {
            "notebook": str(nb_path),
            "mode": "apply" if write else "dry-run",
            **res,
        }
        print(json.dumps(out, ensure_ascii=False, indent=2))
    else:
        verb = "CURED (written)" if write else "would cure"
        if is_md:
            print(f"{nb_path}: {verb} {res['cures']} accent(s) on "
                  f"{res['lines_touched']}/{res['lines']} lines")
        else:
            print(f"{nb_path}: {verb} {res['cures']} accent(s) in "
                  f"{res['cells_touched']}/{res['md_cells']} markdown cells")
        if args.scope and res.get("code_hits"):
            print(f"  WARNING: {res['code_hits']} accentable form(s) found in CODE cells "
                  f"(HORS scope #2876 — possible ad-hoc script residue)")
        if res.get("hors_table"):
            detail = ", ".join(f"{w} (x{c})" for w, c
                               in sorted(res["hors_table"].items(),
                                         key=lambda kv: -kv[1]))
            print(f"  ATTENTION: {res['hors_table_total']} forme(s) hors table — "
                  f"le detecteur les voit encore, la table ne les cure pas "
                  f"(cures incompletes, pas un succes) : {detail}")

    if args.check:
        if res["cures"] > 0 or (args.scope and res.get("code_hits", 0) > 0):
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
