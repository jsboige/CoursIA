#!/usr/bin/env python3
"""Detecte la perte de volume de RENDU d'un notebook entre sa base de PR et sa tete (#11656).

Pourquoi cet outil existe
-------------------------
Les detecteurs de defaut visuels presents dans le depot
(``detect_blank_figures.py``, ``detect_svg_empty_display.py``,
``scan_figure_visual_signature.py``) mesurent tous un **seuil ABSOLU**, sur un
seul arbre. Le cas fondateur (mesure ai-01 sur PR #11351, base
``41fb9df9d5``, head ``18d13ddf2133``) prouve leur angle mort :

    Infer-3-Factor-Graphs       45 715 ->    840 B   (-98,2 %)
    Infer-8-TrueSkill          127 081 ->  1 613 B   (-98,7 %)
    Infer-13-Crowdsourcing      22 896 ->    840 B   (-96,3 %)
                                 -------     ------     integralement text/html
    TOTAL                      195 692 ->  3 293 B   (-98,3 %)

Ces sorties ne sont PAS vides (840-1613 B reste mesurable, > seuil
blank_figures 70 B) ; elles ne sont PAS ``outputs: []`` (la cellule a un
output) ; elles ne contiennent PAS de PNG (la perte est du text/html inline
d'un helper Graphviz). Les trois instruments ne peuvent pas voir ce cas, et
aucune vigilance supplementaire ne comble cette classe : il faut un organe
different.

Comment ca marche
-----------------
Pour chaque notebook modifie compare entre sa base de PR (defaut
``origin/main``) et sa tete (working tree ou ref explicite), cet outil :

1. Sommes les volumes de sortie par cellule, par type MIME declare
   (output ``data`` = MIME majoritaire dans la sortie rendue).

2. Agrège en volume total par (notebook, mime_family) ou ``mime_family in
   {"text", "image", "html"}``. La cle de granularite est le MIME prefix,
   pas la MIME exacte (un ``image/png`` 5 100 B et un ``image/jpeg`` 4 500 B
   sont groupes en ``image``).

3. Seuils (cf. body #11656) :
   - **DELTA_SIGNAL** : chute >= 50 % du volume (ratio <= 0.5) entre base
     et head, **ET** volume d'origine >= MIN_BASE_BYTES (1 000 B par
     famille : eviter le bruit sur quelques octets -- un PNG 70 B qui
     devient 60 B n'est pas une perte de rendu).
   - **NEW_MIME** : un type MIME apparait en head absent en base, signale
     (secondaire -- peut etre un enrichissement legit).
   - **LOST_MIME** : un type MIME present en base absent en head,
     signale (primaire -- c'est la signature exacte du cas fondateur).

4. Exemptions explicites (cf. body #11656 + commentaire ai-01) :
   - Un notebook absent a la base (nouveau fichier, ``path_exists_at_ref``
     False) est **exempt** : tout est ajout, rien a perdre.
   - Un ref git invalide (ref manquant, actions/checkout rate) renvoie
     ``rc=2`` : fail loud preserve (cf. garde anti-auto-desarmement
     #8655/#8662).
   - Une sortie EXEMPTE_CELL (cellule explicitement marquee
     ``"metadata": {"render_exempt": true}`` ou equivalent) ne compte pas
     dans la somme -- pour les cas ou l'auteur a delibere que le rendu
     de cette cellule n'etait pas pertinent.

5. Sortie JSON stable (CI machine) ou texte (lecture humaine). Exit codes :
   - 0 : aucune perte de volume detectee (ou mode non --check)
   - 1 : perte detectee, --check arme
   - 2 : erreur structurelle (ref invalide, notebook illisible)

Le seuil -50 % est le compromis demande par ai-01 dans le body #11656 :
"un defaut **relatif** ; les trois instruments sont **absolus**". Une
reformulation legitime qui resserre de 10-30 % reste invisible ; une
detruction de 50 % et plus (le cas fondateur : -96 a -99 %) rougit.

Usage
-----
    # un notebook, diff vs origin/main (head = working tree)
    python check_render_volume_delta.py NB.ipynb --check
    python check_render_volume_delta.py NB.ipynb --base origin/main --head origin/fix/ma-branche --check
    # sortie machine
    python check_render_volume_delta.py NB.ipynb --json
    # seuils ajustes (utile pour debug ; ne pas toucher en CI)
    python check_render_volume_delta.py NB.ipynb --threshold 0.7 --min-base 500 --check

Voir aussi
----------
- detect_md_content_loss.py -- modele de detecteur base-vs-head (#8655)
- detect_blank_figures.py / detect_svg_empty_display.py -- instruments
  absolus qui ratent ce cas
- scan_figure_visual_signature.py -- signature RGB d'un PNG complet
- Issue #11656 -- cahier des charges + mesure du cas fondateur
- PR #11351 -- la PR vivante qui demontre l'angle mort des 3 absolus
"""
from __future__ import annotations

import argparse
import base64
import json
import re
import subprocess
import sys
from pathlib import Path

# --- Seuils -----------------------------------------------------------------

# Chute >= 50 % du volume (cf. body #11656 : "seuil -50 %"). Une reformulation
# legitime qui resserre de 10-30 % reste au-dessus ; une destruction de 50 % et
# plus rougit (cas fondateur : -96 a -99 %).
DEFAULT_DELTA_THRESHOLD = 0.50
# Volume d'origine minimal, par (notebook, mime_family), pour qu'une chute
# soit signalee. Un PNG de 70 B qui devient 60 B n'est pas une perte ; les
# sorties de 1 000 B ou plus sont ou du vrai rendu, ou des stubs detectes
# par d'autres detecteurs.
DEFAULT_MIN_BASE_BYTES = 1000

# Granularite de MIME prefix : on agrege par famille, pas par MIME exacte. Un
# ``image/png`` 5 100 B et un ``image/jpeg`` 4 500 B sont groupes en ``image``.
MIME_PREFIX = re.compile(r"^([^/]+)/")


def _mime_family(mime: str) -> str:
    """Reduit une MIME a sa famille (text, image, html, ...).

    ``text/html`` -> ``text`` ; ``image/png`` -> ``image`` ; ``application/json``
    -> ``application``. On NE distingue pas text/html de text/plain : un chart
    SVG inline (``text/html``) et un message d'erreur (``text/plain``)
    partagent la meme famille ``text``, c'est voulu (le cas fondateur a des
    sorties ``text/html`` qui passent en dessous du seuil).
    """
    m = MIME_PREFIX.match(mime or "")
    return m.group(1) if m else "other"


def _read_notebook_at_ref(nb_path: Path, ref: str) -> dict | None:
    """Lit le contenu d'un notebook a un ref git donne via ``git show ref:path``."""
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


def _path_exists_at_ref(nb_path: Path, ref: str) -> bool:
    """True si le chemin existe a ce ref (``git cat-file -e``), False sinon.

    Distingue un notebook **NOUVEAU** (exempt -- rien a perdre, tout est
    ajout) d'un notebook **EXISTANT mais illisible** (rc=2 -- ref casse,
    detecteur defectueux, ou NB corrompu a la base). Sans cette distinction,
    un BASE casse desarme silencieusement le garde -- toute la PR semblerait
    "nouveau fichier" et rc=0 partout (cf. garde anti-auto-desarmement
    #8655/#8662).
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


def _ref_resolves(ref: str) -> bool:
    """True si le ref git existe, False sinon (gates anti-auto-desarmement)."""
    try:
        out = subprocess.run(
            ["git", "cat-file", "-e", ref],
            capture_output=True, check=False,
        )
    except (FileNotFoundError, OSError):
        return False
    return out.returncode == 0


def _cell_is_exempt(cell: dict) -> bool:
    """True si la cellule porte une exemption explicite (``render_exempt``).

    Forme attendue : ``cell.metadata.render_exempt == true`` (booleen YAML)
    ou ``cell.metadata["render_exempt"] == "true"`` (chaine YAML). On
    accepte les deux pour tolerer le round-trip YAML/JSON de nbformat. Pas
    d'exemption au niveau notebook : si l'auteur veut exempter tout un
    notebook, il pose ``render_exempt: true`` sur chaque cellule concernee
    (ou split le notebook).
    """
    meta = cell.get("metadata") or {}
    val = meta.get("render_exempt", False)
    if isinstance(val, bool):
        return val
    if isinstance(val, str) and val.lower() in ("true", "yes", "1"):
        return True
    return False


def _decode_output_bytes(output: dict) -> int:
    """Decode les data base64 d'un output Jupyter et retourne le nombre d'octets.

    Gere les deux formes rencontrees dans le depot :
    - ``output.data`` dict avec MIME -> data : { 'image/png': 'base64,...' }
    - ``output.text`` str (text/html, text/plain, stream, ...)
    """
    data = output.get("data")
    if isinstance(data, dict):
        total = 0
        for mime, payload in data.items():
            if isinstance(payload, str):
                # Les data base64 commencent par le payload brut (avec ou sans
                # prefixe ``data:<mime>;base64,``). On accepte les deux.
                if payload.startswith("data:"):
                    try:
                        b64 = payload.split(",", 1)[1]
                        total += len(base64.b64decode(b64, validate=False))
                    except (ValueError, IndexError):
                        total += len(payload)
                else:
                    total += len(payload.encode("utf-8"))
            elif isinstance(payload, (list, tuple)):
                # forme stream/output_data : on prend tout en str
                total += sum(len(p) for p in payload if isinstance(p, str))
        return total
    text = output.get("text")
    if isinstance(text, str):
        return len(text.encode("utf-8"))
    if isinstance(text, (list, tuple)):
        return sum(len(t) for t in text if isinstance(t, str))
    return 0


def _summarize_outputs(nb: dict) -> dict[tuple[str, str], int]:
    """Agrege les volumes de sortie par (cell_id_or_index, mime_family).

    Retourne ``{(cell_key, mime_family): bytes}``. La cle ``cell_key`` est
    l'attribut ``id`` de cellule nbformat 4.5+ quand present, sinon l'index
    de cellule en str. Volume mesure : base64 decode si MIME-image,
    longueur utf-8 si MIME-text / plaintext / HTML inline.

    NB : on cumule par ``(cell_key, mime_family)`` et pas par MIME exacte :
    un meme chart SVG inline peut apparaitre sous ``text/html`` ET
    ``image/svg+xml`` dans le meme output, on veut agreger cela en un seul
    volume.
    """
    out: dict[tuple[str, str], int] = {}
    for idx, cell in enumerate(nb.get("cells", [])):
        if _cell_is_exempt(cell):
            continue
        cid = cell.get("id") or f"idx{idx}"
        outs = cell.get("outputs") or []
        for outp in outs:
            mime_fam = "other"
            data = outp.get("data")
            if isinstance(data, dict) and data:
                # Famille = la premiere cle MIME trouvee
                first_mime = next(iter(data.keys()), "")
                mime_fam = _mime_family(first_mime)
            elif "text" in outp:
                mime_fam = _mime_family("text/plain")
            nbytes = _decode_output_bytes(outp)
            key = (cid, mime_fam)
            out[key] = out.get(key, 0) + nbytes
    return out


def _aggregate_by_family(per_cell: dict[tuple[str, str], int]) -> dict[str, int]:
    """Agrege par famille MIME en sommant sur les cellules.

    Retourne ``{mime_family: bytes_total}``.
    """
    agg: dict[str, int] = {}
    for (_, fam), n in per_cell.items():
        agg[fam] = agg.get(fam, 0) + n
    return agg


def _diff_families(base_agg: dict[str, int], head_agg: dict[str, int],
                   threshold: float, min_base: int) -> list[dict]:
    """Compare les volumes agreges par famille entre base et head.

    Genere les findings ``DELTA_SIGNAL`` (chute >= threshold dans une famille
    deja presente), ``LOST_MIME`` (famille disparue), ``NEW_MIME`` (famille
    apparue, secondaire).
    """
    findings: list[dict] = []
    families = set(base_agg) | set(head_agg)
    for fam in sorted(families):
        b = base_agg.get(fam, 0)
        h = head_agg.get(fam, 0)
        if b == 0 and h == 0:
            continue
        if b > 0 and h == 0:
            # Famille disparue -- le cas fondateur strict : la famille `text`
            # etait a 195 692 B en base, tombe a 3 293 B en head par perte
            # majoritaire ; ici on signale aussi une disparition totale
            # (famille absente du head) qui est un sous-cas.
            findings.append({
                "kind": "LOST_MIME",
                "mime_family": fam,
                "before_bytes": b,
                "after_bytes": h,
            })
            continue
        if b == 0 and h > 0:
            # Famille apparue : peut etre un enrichissement legitime. On
            # signale en secondaire (le reviewer tranche).
            findings.append({
                "kind": "NEW_MIME",
                "mime_family": fam,
                "before_bytes": b,
                "after_bytes": h,
            })
            continue
        # b > 0 et h > 0 : on mesure la chute relative.
        ratio = h / b
        if b >= min_base and ratio <= threshold:
            findings.append({
                "kind": "DELTA_SIGNAL",
                "mime_family": fam,
                "before_bytes": b,
                "after_bytes": h,
                "ratio": round(ratio, 3),
                "threshold": threshold,
                "min_base_bytes": min_base,
            })
    return findings


def scan_notebook(nb_path: Path, base_ref: str, head_ref: str | None = None,
                  threshold: float = DEFAULT_DELTA_THRESHOLD,
                  min_base: int = DEFAULT_MIN_BASE_BYTES) -> dict:
    """Compare le volume de rendu d'un notebook entre base_ref et head_ref."""
    if head_ref is None:
        try:
            nb_head = json.loads(nb_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as e:
            return {"notebook": str(nb_path), "error": f"head unreadable: {e}"}
        head_label = "working_tree"
    else:
        nb_head = _read_notebook_at_ref(nb_path, head_ref)
        if nb_head is None:
            return {"notebook": str(nb_path), "error": f"head_ref {head_ref} unreadable"}
        head_label = head_ref

    # Garde anti-auto-desarmement : un ref de base invalide (ref manquant,
    # actions/checkout rate) ferait passer toute la PR pour "nouveau
    # fichier" via ``path_exists_at_ref`` -> False -> exemption -> rc=0.
    if not _ref_resolves(base_ref):
        return {"notebook": str(nb_path),
                "error": f"base_ref {base_ref} introuvable (ref git invalide)"}

    # Notebook NOUVEAU (absent a la base) : exempt (rien a perdre, tout est
    # ajout). Renvoie un resultat propre (findings=[]) plutot que de
    # declencher rc=2 / "unreadable" sur toute creation de notebook.
    if not _path_exists_at_ref(nb_path, base_ref):
        head_agg = _aggregate_by_family(_summarize_outputs(nb_head))
        return {
            "notebook": str(nb_path),
            "base_ref": base_ref,
            "head_ref": head_label,
            "new_file": True,
            "findings": [],
            "stats": {
                "base_total_bytes": 0,
                "head_total_bytes": sum(head_agg.values()),
                "head_mime_families": sorted(head_agg),
                "threshold": threshold,
                "min_base_bytes": min_base,
                "findings_count": 0,
            },
        }

    nb_base = _read_notebook_at_ref(nb_path, base_ref)
    if nb_base is None:
        return {"notebook": str(nb_path),
                "error": f"base_ref {base_ref} unreadable"}

    base_agg = _aggregate_by_family(_summarize_outputs(nb_base))
    head_agg = _aggregate_by_family(_summarize_outputs(nb_head))
    findings = _diff_families(base_agg, head_agg, threshold, min_base)

    return {
        "notebook": str(nb_path),
        "base_ref": base_ref,
        "head_ref": head_label,
        "findings": findings,
        "stats": {
            "base_total_bytes": sum(base_agg.values()),
            "head_total_bytes": sum(head_agg.values()),
            "base_mime_families": sorted(base_agg),
            "head_mime_families": sorted(head_agg),
            "threshold": threshold,
            "min_base_bytes": min_base,
            "findings_count": len(findings),
        },
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("notebook", type=Path, help="Chemin vers le .ipynb")
    p.add_argument(
        "--base",
        default=None,
        help=(
            "Ref git de la base de PR (defaut: aucun). RECOMMANDE : "
            "`git merge-base origin/main HEAD` (la base de fusion), PAS "
            "`origin/main` deux-points. Sur une branche en retard, le "
            "deux-points inclut les evolutions de main hors PR et fait "
            "signaler des pertes que la PR n'a pas causees (cf. c.357-L1)."
        ),
    )
    p.add_argument("--head", default=None, help="Ref git du head (defaut working tree)")
    p.add_argument("--threshold", type=float, default=DEFAULT_DELTA_THRESHOLD,
                   help=f"Chute relative declenchant un signal (defaut {DEFAULT_DELTA_THRESHOLD})")
    p.add_argument("--min-base", type=int, default=DEFAULT_MIN_BASE_BYTES,
                   dest="min_base",
                   help=f"Volume d'origine min par famille (defaut {DEFAULT_MIN_BASE_BYTES} B)")
    p.add_argument("--check", action="store_true", help="Exit 1 si perte detectee (CI)")
    p.add_argument("--json", action="store_true", help="Sortie JSON machine")
    args = p.parse_args(argv)

    if not args.notebook.exists():
        print(f"ERROR: notebook introuvable: {args.notebook}", file=sys.stderr)
        return 2

    # Garde anti-auto-desarmement (c.357-L1 NEW durable) : aucun fallback
    # silencieux sur `origin/main` deux-points. Si l'appelant ne precise pas
    # --base, on exige le merge-base explicite. Mieux : echec loud qu'un
    # verdict silencieusement faux sur 35 notebooks que la PR n'a pas
    # touches.
    if args.base is None:
        print(
            "ERROR: --base est obligatoire. Precisez la base de fusion "
            "(`git merge-base origin/main HEAD`) -- PAS `origin/main` "
            "deux-points (cf. c.357-L1).",
            file=sys.stderr,
        )
        return 2

    result = scan_notebook(args.notebook, args.base, args.head,
                           args.threshold, args.min_base)

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
            print("[NEW FILE] absent a la base -> exempt "
                  "(rien a perdre, tout est ajout ; #11656).")
        print(f"[STATS]    total base={st['base_total_bytes']}B "
              f"head={st['head_total_bytes']}B | "
              f"families base={st['base_mime_families']} "
              f"head={st['head_mime_families']} | "
              f"seuil={st['threshold']} min_base={st['min_base_bytes']}B | "
              f"findings={st['findings_count']}")
        if fins:
            print("\n[FINDINGS]")
            for f in fins:
                kind = f["kind"]
                fam = f["mime_family"]
                before = f["before_bytes"]
                after = f["after_bytes"]
                if kind == "DELTA_SIGNAL":
                    print(f"  - {kind}: famille '{fam}' chute de {before}B a {after}B "
                          f"(ratio {f['ratio']}, seuil {f['threshold']}, "
                          f"min_base {f['min_base_bytes']}B)")
                elif kind == "LOST_MIME":
                    print(f"  - {kind}: famille '{fam}' disparue du head "
                          f"(base {before}B, head {after}B)")
                elif kind == "NEW_MIME":
                    print(f"  - {kind}: famille '{fam}' apparue au head "
                          f"(base {before}B, head {after}B)")

    if args.check and result["findings"]:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
