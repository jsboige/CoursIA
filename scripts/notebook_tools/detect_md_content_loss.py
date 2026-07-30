#!/usr/bin/env python3
"""Detecte la perte de contenu markdown entre la base d'une PR et sa tete (#8655).

Pourquoi cet outil existe
-------------------------
Le rollout #3966 (demotion des titres-H1/H2 en callouts blockquote `> **X :**`)
a un defaut mecanique silencieux : quand le correcteur one-shot opere "a la
granularite ligne" sur une cellule dont le `source` est une **chaine unique
jointe** (et non une liste de lignes), remplacer la "ligne" du titre remplace
la **cellule entiere**. Une cellule de 941 caracteres se reduit a 16 ; un
bloc `**Navigation**` + 5 objectifs + contexte disparait au profit d'un simple
titre H2. Et la CI reste verte : `scan_md_hierarchy`, le verificateur de liens,
le catalogue, la parite des jumeaux -- aucun ne mesure le **volume de prose
markdown**. Une cellule 941c -> 16c compte pour `1-/1+` au `git diff --stat`.

Deux PR reelles ont passe tous les gardes en detruisant du contenu
(issue #8655, verifie firsthand) :

  | PR    | Notebook                              | Cell | Avant | Apres | Contenu perdu                    |
  |-------|---------------------------------------|------|-------|-------|----------------------------------|
  | #8654 | Sudoku/Sudoku-1-...Python.ipynb       | 9    | 941 c | 16 c  | enonce + 4 contraintes + 3 indices|
  | #8630 | GenAI/Texte/11_Quantization.ipynb     | 3    | 998 c | 28 c  | Navigation + duree + prerequis   |
  | #8630 | GenAI/Texte/12_Test_Time_Scaling.ipynb| 2    | 1655c | 61 c  | Navigation + ref Snell 2024      |

Comment ca marche
-----------------
Pour chaque notebook compare entre sa base git (defaut origin/main) et sa tete
(working tree ou ref explicite), cet outil :

  1. NORMALISE le contenu markdown de chaque cellule : retire les marqueurs de
     titre `#{1,6}` et les callouts `> **... :**` (la transformation LEGITIME
     du rollout #3966), plus les espaces. La demotion d'un titre en callout
     laisse alors une empreinte NORMALISEE IDENTIQUE -> invisible. Une perte
     reelle de contenu se traduit par une chute du volume normalise.

  2. COMPARAISON PAR FICHIER (total normalise) puis, **uniquement quand le
     nombre de cellules est inchange**, descente au niveau cellule (design #1
     de l'issue #8655). Une fusion/scission de cellule decale les index et
     produirait des faux positifs position-par-position : on s'en garde en
     restant au niveau fichier quand le compte bouge.

  3. SEUIL DE CHUTE RELATIVE par cellule : signal si le volume normalise
     devient < 75 % du volume d'origine, ET l'original etait substantiel
     (>= MIN_ORIG_CHARS, pour ignorer les cellules triviales). Les 3 cas reels
     chutent a 1-4 %, avec une marge enorme sous le seuil ; une reformulation
     honnete qui resserre de 10-20 % reste au-dessus de 75 %.

  4. MOTIFS STRUCTURANTS PERDUS : signale explicitement la disparition de
     `**Navigation**`, `**Objectif(s)**`, `**Prerequis**`, `### Enonce`, et
     des liens de navigation `[...](*.ipynb)` -- des elements dont la perte
     est un signal fort independamment du seuil de caracteres.

  5. NE BLOQUE PAS LA REFORMULATION LEGITIME : le detecteur SIGNALE, la PR
     justifie en review (design #4). Sortie exploitable : fichier / cellule /
     avant-apres / ratio / motifs perdus.

  6. EXEMPT LES NOTEBOOKS NOUVEAUX : un fichier absent a la base (creation)
     n'a rien a perdre (tout est ajout). On le distingue d'un notebook
     existant illisible via ``path_exists_at_ref`` (``git cat-file -e``) pour
     ne pas confondre "nouveau fichier" et "detecteur casse" -- sinon le garde
     anti-auto-desarmement (#8655/#8662) fail-loud sur toute creation de
     notebook. Un nouveau fichier renvoie rc=0 (exempt), un fichier existant
     illisible renvoie toujours rc=2 (fail loud preserve).

Usage
-----
    # un notebook, diff vs origin/main (head = working tree)
    python detect_md_content_loss.py NB.ipynb --check
    python detect_md_content_loss.py NB.ipynb --base origin/main --head origin/fix/ma-branche --check
    # sortie machine
    python detect_md_content_loss.py NB.ipynb --json

Exit codes
----------
    0 -- aucune perte de contenu detectee (ou mode non --check), y compris un
         notebook NOUVEAU (absent a la base : rien a comparer -> exempt)
    1 -- une ou plusieurs pertes detectees (--check)
    2 -- erreur (notebook EXISTANT illisible, ref git introuvable). Un notebook
         absent a la base (nouveau fichier) ne declenche PAS rc=2 : il est exempt.

Voir aussi
----------
- detect_link_target_regression.py -- modele de detecteur base-vs-head
- detect_caps_regression.py (#7198) -- autre regression markdown base-vs-head
- scan_md_hierarchy / check_notebook_navlinks -- gardes existants (volume-aveugles)
- Issue #8655 -- cahier des charges + 3 cas reels
- Registre #3966 -- le rollout demotion-de-titres dont provient le defaut
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# Seuil de chute relative : une cellule signale si son volume normalise devient
# strictement inferieur a DROP_THRESHOLD x le volume d'origine (issue #8655 :
# "p. ex. < 75 % du volume d'origine"). Les 3 cas reels chutent a 1-4 %.
DROP_THRESHOLD = 0.75
# Volume normalise minimal d'origine pour qu'une chute soit signalee : evite
# le bruit sur les cellules triviales (un titre seul, un separateur).
MIN_ORIG_CHARS = 100

# Motifs structurants dont la disparition est un signal fort (design #3 #8655).
# Notes : "Navigation" / "Objectif(s)" / "Prerequis" sont matches aussi bien en
# titre (`## Navigation`) qu'en callout (`> **Navigation :**`) car la regex
# cible le mot-cle hors-marqueurs. Les liens de navigation vers un notebook
# sont comptes collectivement (perte = N liens disparus).
MOTIF_PATTERNS = [
    (re.compile(r"\bNavigation\b", re.I), "Navigation"),
    (re.compile(r"\bObjectifs?\b", re.I), "Objectif(s)"),
    (re.compile(r"\bPr[eé]requis\b", re.I), "Prerequis"),
    (re.compile(r"^#{1,6}\s*Enonc[eé]", re.I | re.M), "Enonce"),
]
NAV_LINK_RE = re.compile(r"\[[^\]]+\]\([^)]+\.ipynb\)")

# Bloc frontmatter YAML `---\n...\n---` en TETE de cellule markdown (#8904/#8919).
# Quand un notebook migre son cost de ce bloc vers nb['metadata']['cost'], le bloc
# disparait de la cellule -> chute mecanique du ratio -> faux positif de content-loss.
# On detecte ce cas pour le distinguer d'une troncature reelle (issue #8919).
FRONTMATTER_RE = re.compile(r"\A---\s*\n(.*?)\n---[ \t]*(?:\n|\Z)", re.DOTALL)
# Une cle cost dans le frontmatter : ligne indentee `  key: value` sous un `cost:`.
_COST_KEY_LINE = re.compile(r"^([ \t]+)([A-Za-z_][\w]*)\s*:\s*(.*?)\s*$")


def _strip_yaml_inline_comment(s: str) -> str:
    """Retire un commentaire YAML inline (`` # ...``) hors d'une valeur quotee.

    Un ``#`` ne compte comme debut de commentaire que s'il est precede d'un blanc
    (espace/tab) : un ``#`` colle a un caractere (ex: URL ``http://h#frag``) ou a
    l'interieur de guillemets est preserve (issue #8921-1 : les frontmatters reels
    portent leur justification en commentaire de fin de ligne -- ``cpu_min: 1  #
    cpu-only`` -- qu'il faut ignorer pour juger l'equivalence, sans quoi ``1`` est
    declare divergent de... ``1``).
    """
    quote = None
    for i, ch in enumerate(s):
        if quote:
            if ch == quote:
                quote = None
        elif ch in "\"'":
            quote = ch
        elif ch == "#" and i > 0 and s[i - 1] in " \t":
            return s[:i].rstrip()
    return s


def _normalize_cost_value(v) -> str:
    """Normalise une valeur cost (str YAML du frontmatter OU objet JSON de metadata)
    en une cle de comparaison canonique, insensible aux commentaires inline, a la
    casse, aux guillemets et a l'ecriture numerique (issues #8919 + #8921-1/#8921-2).

    Rend str YAML ("none", "true", "0.10", "1  # cpu-only") et objet JSON (None,
    True, 0.1, 1) comparables : ``None`` / "none" / "null" / "~" -> "none" ;
    booleens -> "true"/"false" ; nombres -> forme canonique ``str(float)``
    (``0.10`` == ``0.1``, ``1`` == ``1.0`` -- #8921-2 : la comparaison est
    numerique la ou elle etait textuelle) ; chaines -> depouillees du commentaire
    inline (#8921-1), des guillemets et lowercasees.
    """
    if v is None:
        return "none"
    if isinstance(v, bool):  # NB: avant int (bool sous-classe de int en Python)
        return "true" if v else "false"
    if isinstance(v, (int, float)):
        f = float(v)
        if f != f or f in (float("inf"), float("-inf")):  # nan/inf -> texte brut
            return str(v)
        return str(f)  # #8921-2 : forme canonique (1 -> "1.0", 0.1 -> "0.1")
    s = str(v).strip()
    s = _strip_yaml_inline_comment(s).strip()  # #8921-1 : retire ` # commentaire`
    if len(s) >= 2 and s[0] in "\"'" and s[-1] == s[0]:
        s = s[1:-1]
    low = s.lower()
    if low in ("none", "null", "~", ""):
        return "none"
    try:  # #8921-2 : comparaison NUMERIQUE (0.10 == 0.1, pas textuelle)
        f = float(low)
    except ValueError:
        return low
    if f != f or f in (float("inf"), float("-inf")):  # nan/inf -> texte brut
        return low
    return str(f)


def _parse_frontmatter_cost(md_text: str) -> dict | None:
    """Parse le sous-bloc ``cost:`` d'un frontmatter YAML en tete de cellule.

    Parser manuel (le detecteur reste stdlib-only, sans PyYAML -- cf
    ``check_cost_metadata.parse_cost_frontmatter`` qui, lui, import yaml mais
    n'est pas un gate CI leger). Structure attendue (cas #8904/#8916) :

        ---
        title: Foo/bar
        cost:
          api_usd_est: 0.0
          cpu_min: 15
          reduced_pedagogical: path/to/nb.ipynb
          free_alternative: null
        ---
        # H1 ...

    Retourne ``{key: raw_value_str}`` pour les cles du bloc ``cost:`` (None si la
    cellule n'a pas de frontmatter ou pas de bloc ``cost:``). Les valeurs brutes
    sont normalisees plus tard par ``_normalize_cost_value``.
    """
    m = FRONTMATTER_RE.match(md_text)
    if not m:
        return None
    cost: dict[str, str] = {}
    in_cost = False
    cost_indent: str | None = None
    for line in m.group(1).split("\n"):
        if not in_cost:
            if re.match(r"^cost\s*:\s*$", line):
                in_cost = True
            continue
        kv = _COST_KEY_LINE.match(line)
        if kv and kv.group(1) and not line.lstrip().startswith("#"):
            # Ligne indentee `  key: value` -> cle du bloc cost.
            cost[kv.group(2)] = kv.group(3)
        elif line.strip() == "":
            continue  # ligne vide dans le bloc cost -> on reste dedans
        elif re.match(r"^\S", line):
            # Ligne non indentee -> on sort du bloc cost (ex: autre cle top-level).
            in_cost = False
    return cost or None


def _cost_equivalent(base_frontmatter_cost: dict, head_metadata_cost: dict | None
                     ) -> tuple[bool, list[str]]:
    """Compare champ-par-champ le cost du frontmatter base vs le metadata.cost head.

    Retourne ``(equivalent, divergent_fields)``. Un champ diverge si sa valeur
    normalisee differe (ou s'il manque d'un cote) -- SAUF deux progres legitimes
    d'une migration (issue #8921-3) :

    * ``base=none -> head=valeur`` (ex: ``free_alternative`` null -> chemin reel) :
      une apparition de valeur est un GAIN, jamais une perte de contenu.
    * ``metadata_written`` : horodatage d'ecriture, rafraichi au moment de la
      migration -> exclu (une date plus recente est le comportement attendu, pas
      une divergence).

    Le test reste mordant sur le piege de #8908/#8912/#8914 : ``metadata.cost`` y
    existait deja mais n'etait PAS equivalent (``cpu_min`` 0 au lieu de 20/45,
    ``reduced_pedagogical`` None au lieu d'un chemin) -> la "suppression seche"
    doit rester signaler.
    """
    head = head_metadata_cost or {}
    divergent: list[str] = []
    for key, base_val in base_frontmatter_cost.items():
        if key == "metadata_written":  # #8921-3b : date rafraichie = attendue
            continue
        base_norm = _normalize_cost_value(base_val)
        if base_norm == "none":  # #8921-3a : none -> valeur = gain, pas perte
            continue
        if base_norm != _normalize_cost_value(head.get(key)):
            divergent.append(key)
    return (len(divergent) == 0, divergent)


def _frontmatter_non_cost_keys(md_text: str) -> list[str]:
    """Cles top-level du frontmatter autres que ``title`` et le sous-bloc ``cost:``.

    Une cle informative colocataire (ex: ``notes:``) doit etre migree vers
    ``metadata.cost`` (``notes`` -> ``metadata.cost.notes``) pour que la
    suppression du frontmatter soit invisible ; sinon sa perte est signalee
    (issue #8921-4, cas Claudish : 5 lignes de routage perdues en silence parce
    que le strip retirait le frontmatter ENTIER sur la seule foi du ``cost:``).
    """
    m = FRONTMATTER_RE.match(md_text)
    if not m:
        return []
    extras: list[str] = []
    in_cost = False
    for line in m.group(1).split("\n"):
        if re.match(r"^cost\s*:\s*$", line):
            in_cost = True
            continue
        if in_cost:
            if re.match(r"^\S", line):  # non-indente -> on sort du bloc cost
                in_cost = False
            else:
                continue  # encore dans le bloc cost
        kv = re.match(r"^([A-Za-z_][\w]*)\s*:", line)  # cle top-level (non indente)
        if kv and kv.group(1) != "title":
            extras.append(kv.group(1))
    return extras


def _normalize(md_text: str) -> str:
    """Normalise le contenu markdown pour la comparaison de volume.

    Retire les transformations LEGITIMES du rollout #3966 (titre H1-H6 ->
    callout blockquote `> **X :**`) afin qu'une demotion honnete laisse une
    empreinte identique (pas de signal), puis retire les espaces. Une perte
    reelle de contenu (cellule tronquee) se traduit par une chute du volume.
    """
    # 1. Marqueurs de titre en debut de ligne : "## Foo" -> "Foo".
    t = re.sub(r"^[ \t]*#{1,6}[ \t]+", "", md_text, flags=re.M)
    # 2. Callouts blockquote de la forme "> **Mot :** ..." (leger data du
    #    rollout #3966) : on retire la LIGNE-entiere de callout quand elle
    #    n'est QU'un marqueur (pas de contenu supplaitre apres). Cela evite
    #    qu'un titre legitiment demote en callout soit compte comme "nouveau"
    #    contenu par rapport au titre original.
    t = re.sub(r"^[ \t]*>\s*\*\*[^*\n]*:\*\*\s*$", "", t, flags=re.M)
    # 3. Espaces : on compare le volume de PROSE, pas la mise en forme.
    t = re.sub(r"\s+", "", t)
    return t


def _norm_len(md_text: str) -> int:
    return len(_normalize(md_text))


def extract_md_cells(nb: dict) -> list[tuple[int, str]]:
    """Retourne [(cell_idx, source_str)] pour les cellules markdown seulement."""
    out = []
    for idx, c in enumerate(nb.get("cells", [])):
        if c.get("cell_type") != "markdown":
            continue
        src = c.get("source", [])
        src = "".join(src) if isinstance(src, list) else (src or "")
        out.append((idx, src))
    return out


def _collect_motifs(nb: dict) -> dict:
    """Compte les occurrences de chaque motif structurant dans le notebook.

    Retourne {motif_label: count} + {'nav_links': count}. La comparaison
    base/head revelera les motifs disparus (count tombe a 0).
    """
    counts: dict = {}
    full_md = "\n".join(src for _, src in extract_md_cells(nb))
    for pat, label in MOTIF_PATTERNS:
        counts[label] = len(pat.findall(full_md))
    counts["nav_links"] = len(NAV_LINK_RE.findall(full_md))
    return counts


def read_notebook_at_ref(nb_path: Path, ref: str) -> dict | None:
    """Lit le contenu d'un notebook a un ref git donne via `git show ref:path`."""
    rel = nb_path.as_posix()
    try:
        out = subprocess.run(
            ["git", "show", f"{ref}:{rel}"],
            capture_output=True, text=True, encoding="utf-8", check=False,
        )
    except (FileNotFoundError, OSError):
        return None
    if out.returncode != 0 or not out.stdout:
        return None
    try:
        return json.loads(out.stdout)
    except json.JSONDecodeError:
        return None


def path_exists_at_ref(nb_path: Path, ref: str) -> bool:
    """True si le chemin existe a ce ref (``git cat-file -e``), False sinon.

    Permet de distinguer un notebook **NOUVEAU** (absent a la base -> il n'y a
    rien a comparer, on l'exempte) d'un notebook **existant mais illisible**
    (``read_notebook_at_ref`` renvoie None -> detecteur casse ou ref git
    manquant -> on le signale en rc=2 pour que le garde anti-auto-desarmement
    (#8655/#8662) continue de fail loud). Sans cette distinction, toute creation
    de notebook tripe le garde : un fichier absent a la base est lu comme
    "unreadable" et fait echouer la CI sur une fausse perte de contenu.

    NB: un ref git **invalide** fait aussi echouer ``cat-file -e`` (sur tous les
    chemins) ; on valide donc le ref separement via ``ref_resolves`` AVANT
    d'appeler cette fonction, sinon un BASE casse desarmerait silencieusement le
    garde (tout semblerait "nouveau").
    """
    rel = nb_path.as_posix()
    try:
        out = subprocess.run(
            ["git", "cat-file", "-e", f"{ref}:{rel}"],
            capture_output=True, check=False,
        )
    except (FileNotFoundError, OSError):
        return False
    return out.returncode == 0


def ref_resolves(ref: str) -> bool:
    """True si le ref git existe (``git cat-file -e <ref>``), False sinon.

    Garde anti-regression : si le ref de base est invalide (ref manquant,
    actions/checkout rate), ``path_exists_at_ref`` renverrait False pour tous
    les chemins et toute la PR semblerait "nouveau fichier" -> rc=0 ->
    desarmement silencieux du garde #8655/#8662. On valide le ref en amont pour
    que ce cas reste un rc=2 (fail loud preserve).
    """
    try:
        out = subprocess.run(
            ["git", "cat-file", "-e", ref],
            capture_output=True, check=False,
        )
    except (FileNotFoundError, OSError):
        return False
    return out.returncode == 0


def _compare_cells(base_md: list[tuple[int, str]],
                   head_md: list[tuple[int, str]],
                   head_cost: dict | None = None) -> list[dict]:
    """Compare cellule-par-cellule (INDEX STABLE requis, design #1 #8655).

    Ne descend au niveau cellule QUE quand le nombre de cellules markdown est
    inchange entre base et head ; sinon une fusion/scission decale les index et
    produirait des faux positifs position-par-position (26 FP observes sur
    10_LocalLlama.ipynb, cite dans l'issue). Retourne les cellules tronquees.

    ``head_cost`` = ``nb_head['metadata']['cost']`` : permet de reconnaitre une
    migration LEGITIME frontmatter ``cost:`` -> ``metadata.cost`` (issue #8919).
    Quand la cellule base porte un bloc ``cost:`` equivalent champ-par-champ au
    ``head_cost``, on retire le frontmatter du texte de base AVANT le ratio (la
    cellule migree est invisible, comme une demotion #3966). Si le cost diverge
    ou disparait sans migration, on signale ``FRONTMATTER_COST_DIVERGENCE`` -- le
    gate reste mordant sur la suppression seche (piege #8908/#8912/#8914).

    #8921 : le strip n'a lieu QUE si (a) le cost est equivalent ET (b) aucune cle
    informative colocataire (ex: ``notes:``) n'est reste sur le carreau. Une cle
    non migree vers ``metadata.cost`` est nommee divergente (cas Claudish : le
    strip du frontmatter entier faisait disparaitre ``notes:`` en silence). Les
    commentaires YAML inline sont ignores (#8921-1), la comparaison est numerique
    (#8921-2), et ``none -> valeur`` / ``metadata_written`` sont des progres
    legitimes, pas des divergences (#8921-3).
    """
    findings: list[dict] = []
    if len(base_md) != len(head_md):
        return findings  # compte modifie -> la comparaison fichier suffit
    for (b_idx, b_src), (h_idx, h_src) in zip(base_md, head_md):
        # Migration frontmatter cost -> metadata.cost (#8919) : si la cellule base
        # porte un bloc cost equivalent au head_cost, on retire le frontmatter du
        # ratio. #8921-4 : on ne le fait QUE si aucune cle informative colocataire
        # (ex: ``notes:``) n'est reste sur le carreau -- sinon le strip retirait le
        # frontmatter ENTIER et faisait disparaitre ``notes:`` en silence (Claudish).
        b_src_ratio = b_src
        divergent_cost: list[str] | None = None
        base_cost = _parse_frontmatter_cost(b_src)
        if base_cost is not None:
            equiv, divergent = _cost_equivalent(base_cost, head_cost)
            unmigrated = [k for k in _frontmatter_non_cost_keys(b_src)
                           if not (head_cost and k in head_cost)]
            if equiv and not unmigrated:
                b_src_ratio = FRONTMATTER_RE.sub("", b_src, count=1)
            else:
                divergent_cost = divergent + unmigrated
        b_norm = _norm_len(b_src_ratio)
        h_norm = _norm_len(h_src)
        if b_norm < MIN_ORIG_CHARS:
            continue  # cellule d'origine trop courte pour qu'une chute soit du bruit
        if h_norm < DROP_THRESHOLD * b_norm:
            ratio = (h_norm / b_norm) if b_norm else 0.0
            findings.append({
                "kind": "TRUNCATED_CELL",
                "cell_idx": h_idx,
                "before_chars": b_norm,
                "after_chars": h_norm,
                "ratio": round(ratio, 3),
                "before_excerpt": b_src.strip().split("\n", 1)[0][:90],
                "after_excerpt": h_src.strip().split("\n", 1)[0][:90],
            })
        if divergent_cost:
            # Le bloc cost a disparu de la cellule SANS migration equivalente :
            # perte reelle de cost (le squelette metadata.cost ne suffit pas).
            findings.append({
                "kind": "FRONTMATTER_COST_DIVERGENCE",
                "cell_idx": h_idx,
                "divergent_fields": divergent_cost,
            })
    return findings


def _compare_motifs(base_counts: dict, head_counts: dict) -> list[dict]:
    """Signale les motifs structurants disparus (present en base, absent en head)."""
    findings: list[dict] = []
    for key, b_count in base_counts.items():
        h_count = head_counts.get(key, 0)
        if b_count > 0 and h_count == 0:
            findings.append({
                "kind": "LOST_MOTIF",
                "motif": key,
                "before_count": b_count,
            })
        elif key == "nav_links" and h_count < b_count:
            # Perte PARTIELLE de liens de navigation : signalee (secondary).
            findings.append({
                "kind": "LOST_NAV_LINKS",
                "motif": "nav_links",
                "before_count": b_count,
                "after_count": h_count,
                "delta": b_count - h_count,
            })
    return findings


def scan_notebook(nb_path: Path, base_ref: str, head_ref: str | None = None) -> dict:
    """Compare le contenu markdown d'un notebook entre base_ref et head_ref."""
    if head_ref is None:
        try:
            nb_head = json.loads(nb_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as e:
            return {"notebook": str(nb_path), "error": f"head unreadable: {e}"}
        head_label = "working_tree"
    else:
        nb_head = read_notebook_at_ref(nb_path, head_ref)
        if nb_head is None:
            return {"notebook": str(nb_path), "error": f"head_ref {head_ref} unreadable"}
        head_label = head_ref

    # Ref de base invalide (ref manquant, checkout rate) = detecteur/ref casse,
    # PAS un nouveau fichier. On le signale en erreur (rc=2) pour que le garde
    # anti-auto-desarmement (#8655/#8662) fail loud -- sinon un BASE casse
    # ferait passer tous les chemins pour "nouveaux" et desarmerait le gate.
    if not ref_resolves(base_ref):
        return {"notebook": str(nb_path), "error": f"base_ref {base_ref} introuvable (ref git invalide)"}

    # Notebook NOUVEAU (absent a la base) : rien a perdre (tout est ajout),
    # donc exempt de content-loss. On retourne un resultat propre (pas
    # d'erreur, pas de findings) plutot que de laisser read_notebook_at_ref
    # renvoyer None -> "unreadable" -> declenchement intempestif du garde
    # anti-auto-desarmement (#8655/#8662) sur toute creation de notebook.
    if not path_exists_at_ref(nb_path, base_ref):
        head_md_new = extract_md_cells(nb_head)
        head_total_new = sum(_norm_len(s) for _, s in head_md_new)
        return {
            "notebook": str(nb_path),
            "base_ref": base_ref,
            "head_ref": head_label,
            "new_file": True,
            "findings": [],
            "stats": {
                "base_md_cells": 0,
                "head_md_cells": len(head_md_new),
                "cell_count_stable": False,
                "base_total_normalized_chars": 0,
                "head_total_normalized_chars": head_total_new,
                "findings_count": 0,
            },
        }

    nb_base = read_notebook_at_ref(nb_path, base_ref)
    if nb_base is None:
        return {"notebook": str(nb_path), "error": f"base_ref {base_ref} unreadable"}

    base_md = extract_md_cells(nb_base)
    head_md = extract_md_cells(nb_head)
    # metadata.cost du head : permet de reconnaitre la migration frontmatter->cost
    # (#8919). absent (None) si le head n'a pas de cost metadata.
    head_cost = nb_head.get("metadata", {}).get("cost")

    findings: list[dict] = []
    findings.extend(_compare_cells(base_md, head_md, head_cost))
    findings.extend(_compare_motifs(_collect_motifs(nb_base), _collect_motifs(nb_head)))

    base_total = sum(_norm_len(s) for _, s in base_md)
    head_total = sum(_norm_len(s) for _, s in head_md)

    return {
        "notebook": str(nb_path),
        "base_ref": base_ref,
        "head_ref": head_label,
        "findings": findings,
        "stats": {
            "base_md_cells": len(base_md),
            "head_md_cells": len(head_md),
            "cell_count_stable": len(base_md) == len(head_md),
            "base_total_normalized_chars": base_total,
            "head_total_normalized_chars": head_total,
            "findings_count": len(findings),
        },
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("notebook", type=Path, help="Chemin vers le .ipynb")
    p.add_argument("--base", default="origin/main", help="Ref git de la base (defaut origin/main)")
    p.add_argument("--head", default=None, help="Ref git du head (defaut working tree)")
    p.add_argument("--check", action="store_true", help="Exit 1 si perte detectee (CI)")
    p.add_argument("--json", action="store_true", help="Sortie JSON machine")
    args = p.parse_args(argv)

    if not args.notebook.exists():
        print(f"ERROR: notebook introuvable: {args.notebook}", file=sys.stderr)
        return 2

    result = scan_notebook(args.notebook, args.base, args.head)

    if "error" in result:
        print(f"ERROR: {result['error']}", file=sys.stderr)
        return 2

    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    else:
        nb = result["notebook"]
        st = result["stats"]
        fins = result["findings"]
        print(f"[NOTEBOOK] {nb}")
        print(f"[BASE]     {result['base_ref']}")
        print(f"[HEAD]     {result['head_ref']}")
        if result.get("new_file"):
            print("[NEW FILE] absent a la base -> exempt de content-loss "
                  "(rien a perdre, tout est ajout ; #8655/#8662).")
        print(f"[STATS]    md_cells base={st['base_md_cells']} head={st['head_md_cells']} "
              f"stable={st['cell_count_stable']} | "
              f"normalized_chars base={st['base_total_normalized_chars']} "
              f"head={st['head_total_normalized_chars']} | findings={st['findings_count']}")
        if fins:
            print("\n[FINDINGS]")
            for f in fins:
                if f["kind"] == "TRUNCATED_CELL":
                    print(f"  - cell {f['cell_idx']} {f['kind']}: "
                          f"{f['before_chars']}c -> {f['after_chars']}c "
                          f"(ratio {f['ratio']}, seuil {DROP_THRESHOLD})")
                    print(f"      before: {f['before_excerpt']!r}")
                    print(f"      after:  {f['after_excerpt']!r}")
                elif f["kind"] == "LOST_MOTIF":
                    print(f"  - {f['kind']}: '{f['motif']}' disparu "
                          f"(base={f['before_count']})")
                elif f["kind"] == "LOST_NAV_LINKS":
                    print(f"  - {f['kind']}: {f['delta']} lien(s) de navigation en moins "
                          f"({f['before_count']} -> {f['after_count']})")
                elif f["kind"] == "FRONTMATTER_COST_DIVERGENCE":
                    print(f"  - cell {f['cell_idx']} {f['kind']}: le bloc cost du "
                          f"frontmatter a disparu sans migration equivalente ; "
                          f"champ(s) divergent(s) ou manquant(s) dans metadata.cost "
                          f"du head : {', '.join(f['divergent_fields'])}")

    if args.check and result["findings"]:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
