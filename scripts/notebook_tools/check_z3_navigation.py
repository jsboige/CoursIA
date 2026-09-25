#!/usr/bin/env python3
"""
Check Z3-Python notebook navigation consistency (stale-navigation sweep).

Pourquoi cet outil existe
-------------------------
La classe d'erreur « stale-navigation pattern » (cellule [0] d'un notebook qui
pointe vers un autre notebook avec un lien cassé, sauté ou inversé) a été
identifiée transversalement sur la série Z3-Python lors des audits Z3-04/05/06
/09/10/11/16/16b/17/18 (issue #17419, partition Hermes #17073). Défauts observés :
  - absence : cellule [0] n'a pas de flèche vers suivant alors que le notebook
              NN+1 existe
  - saut    : cellule [0] a flèche vers NN-3 qui saute les notebooks intermédiaires
  - inverse : cellule [0] a flèche (->) au lieu de (<-) pour le précédent
  - 404     : lien markdown vers un notebook inexistant

`check_notebook_navlinks.py` couvre les 404 (cible absente), pas la navigation
incohérente (cible présente mais mal chaînée ou de mauvais sens). Cet outil
ferme la classe stale-navigation-pattern sur la série Z3-Python.

Conventions de nommage (Z3-API) -- périmètre Python :
  - `Z3-NN-...-Python.ipynb` : convention dominante (19 fichiers)
  - `Z3-Python-NN-...ipynb`  : convention inverse, 2 fichiers (Z3-13 / Z3-17)
  - `Z3-NNb-...ipynb`         : sous-numéros (16b/16c/16d/16e), kernelspec Python
  - `Z3-NNb-...-Linq.ipynb`   : 3ᵉ convention, kernelspec Python malgré suffix -Linq
                                (ex. Z3-01b-Style-Declaratif-Linq, mesuré kernelspec=python)
  - `Z3-NN-...-CSharp.ipynb`  : kernelspec C#/.NET, **exclus du périmètre**

Le critère discriminant **fiable** est le `kernelspec.language` du notebook
(Python vs C#), pas le nom de fichier : un notebook sans `-Python` suffix
peut être Python (kernelspec décide). Le glob initial couvrait la convention
dominante seulement et ratait 3 notebooks (mesure 2026-09-25, 19 vs 22).

Sortie : tableau par notebook avec type de défaut, sortie non-zero si findings.

Usage :
    python scripts/notebook_tools/check_z3_navigation.py
    python scripts/notebook_tools/check_z3_navigation.py --json
    python scripts/notebook_tools/check_z3_navigation.py --dir MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API

Read-only : ne touche aucun notebook.
"""
import argparse
import json
import re
import sys
from pathlib import Path

# Regex pour extraire numero + sous-numero.
# Couvre 3 conventions de nommage Z3-Python :
#   - dominante : Z3-NN (Z3-01, Z3-12, Z3-16b, Z3-16c)
#   - inverse   : Z3-Python-NN (Z3-Python-13, Z3-Python-17)
#   - sous-num  : Z3-NNb (Z3-01b, Z3-16b)
# Le suffixe `-Python` est optionnel ; les sous-numeros lettres sont captures.
NOTEBOOK_RE = re.compile(r"Z3-(?:Python-)?(\d+)([a-z])?(?:-[A-Za-z0-9._-]*)?")
# Lien markdown vers un notebook Z3 (memes conventions)
LINK_RE = re.compile(r"\[([^\]]+)\]\((Z3-(?:Python-)?(\d+)([a-z])?-[^)]+\.ipynb)\)")
# Fleches Unicode (Z3-08+)
ARROW_RE = re.compile(r"(←|→)\s*\[?([^\]\n]*?Z3-(?:Python-)?(\d+)([a-z])?)?\]?")
# Fleches ASCII (Z3-01 a Z3-06) : << / >> dans un lien markdown
ASCII_ARROW_RE = re.compile(r"(<<|>>)\s*\[?([^\]\n]*?Z3-(?:Python-)?(\d+)([a-z])?)?\]?")


def parse_notebook_number(name: str) -> tuple[int, str]:
    """Extrait (num, suffix) du nom de fichier. Z3-16b-Meal-... -> (16, 'b')."""
    m = NOTEBOOK_RE.search(name)
    if not m:
        return (0, "")
    return (int(m.group(1)), m.group(2) or "")


def list_z3_python_notebooks(z3_dir: Path) -> list[Path]:
    """Liste les notebooks Z3-Python du dossier, tries par numero.

    Critere discriminant : kernelspec.language == 'python'.
    Couvre les 4 conventions de nommage : dominante (`-Python` suffix),
    inverse (`Z3-Python-NN`), sous-numeros (`Z3-NNb`), et 3ᵉ convention
    (`Z3-NNb-...-Linq` avec kernelspec Python malgre suffix -Linq).
    Les notebooks C# (.NET-CSharp) sont exclus.
    """
    if not z3_dir.exists():
        return []
    import nbformat
    candidates = list(z3_dir.glob("Z3-*.ipynb"))
    python_nb = []
    for p in candidates:
        try:
            nb = nbformat.read(str(p), as_version=4)
            lang = nb.metadata.get("kernelspec", {}).get("language", "")
            if lang == "python":
                python_nb.append(p)
        except Exception:
            # Notebook illisible / non-nbformat : on l'ignore (read-only).
            continue
    return sorted(python_nb, key=lambda p: parse_notebook_number(p.name))


def extract_cell0_links(notebook: Path) -> dict:
    """Lit la cellule [0] markdown et extrait les liens vers d'autres Z3-."""
    import nbformat
    nb = nbformat.read(str(notebook), as_version=4)
    if not nb.cells or nb.cells[0].cell_type != "markdown":
        return {"raw": "", "links": [], "arrows": []}
    src = nb.cells[0].source
    links = []
    for m in LINK_RE.finditer(src):
        text = m.group(1)
        target = m.group(2)
        num, suf = parse_notebook_number(target)
        links.append({"text": text, "target": target, "num": num, "suf": suf})
    arrows = []
    # Unicode (←/→) hors lien markdown
    for m in ARROW_RE.finditer(src):
        direction = m.group(1)
        if m.group(3):
            num = int(m.group(3))
            suf = m.group(4) or ""
            arrows.append({"direction": direction, "num": num, "suf": suf, "raw": m.group(0)})
    # Fleches dans le TEXTE d'un lien markdown (ex: "[Z3-Python-08 ->](Z3-08-...)")
    TEXT_ARROW_RE = re.compile(r"\[([^\]]*?)(←|→)([^\]]*?)\]\((Z3-(?:Python-)?(\d+)([a-z])?-[^)]+\.ipynb)\)")
    for m in TEXT_ARROW_RE.finditer(src):
        direction = m.group(2)
        num = int(m.group(5))
        suf = m.group(6) or ""
        arrows.append({"direction": direction, "num": num, "suf": suf, "raw": m.group(0)})
    # ASCII (<< / >>) -- equivalent semantique : << = back, >> = forward
    ASCII_ARROW_V2 = re.compile(r"(<<|>>)([^\n]*?Z3-(?:Python-)?(\d+)([a-z]?))")
    for m in ASCII_ARROW_V2.finditer(src):
        direction_ascii = m.group(1)
        num = int(m.group(3))
        suf = m.group(4) or ""
        direction = "←" if direction_ascii == "<<" else "→"
        arrows.append({"direction": direction, "num": num, "suf": suf, "raw": m.group(0)})
    return {"raw": src[:300], "links": links, "arrows": arrows}


def check_navigation(notebooks: list[Path]) -> list[dict]:
    """Pour chaque notebook, verifie la coherence de la navigation cellule [0]."""
    if not notebooks:
        return []

    nums = [(parse_notebook_number(p.name), p) for p in notebooks]
    nums.sort(key=lambda x: (x[0][0], x[0][1]))
    by_num = {(n, s): p for (n, s), p in nums}

    findings = []
    for (num, suf), path in nums:
        cell0 = extract_cell0_links(path)
        notebook_findings = []

        # Chercher les notebooks suivants et precedents dans la liste
        idx = nums.index(((num, suf), path))
        prev_in_list = nums[idx - 1][0] if idx > 0 else None
        next_in_list = nums[idx + 1][0] if idx + 1 < len(nums) else None

        # Separer fleches back / forward
        back_arrows = [a for a in cell0["arrows"] if a["direction"] == "←"]
        forward_arrows = [a for a in cell0["arrows"] if a["direction"] == "→"]

        # Verifier les fleches back : sens ET cible
        for ba in back_arrows:
            actual = (ba["num"], ba["suf"])
            # Sens : ← devrait etre vers un numero <= num (precedent ou soi-meme en serie)
            if actual[0] > num:
                notebook_findings.append({
                    "type": "back_inverted",
                    "detail": f"fleche (←) pointe vers Z3-{ba['num']}{ba['suf']} qui est APRES Z3-{num}{suf} (sens inverse)",
                    "raw": ba["raw"]
                })
            # Cible : devrait etre le precedent dans la liste, OU le notebook principal si sous-numero
            elif prev_in_list is not None and actual != prev_in_list:
                # Tolerance : si c'est un sous-numero (16b, 16c...), le back peut etre vers le main (16)
                if not (suf and actual == (num, "")):
                    notebook_findings.append({
                        "type": "back_skip",
                        "detail": f"fleche (←) pointe vers Z3-{ba['num']}{ba['suf']} au lieu de Z3-{prev_in_list[0]}{prev_in_list[1]} (saut)",
                        "raw": ba["raw"]
                    })

        # Verifier les fleches forward : sens ET cible
        for fa in forward_arrows:
            actual = (fa["num"], fa["suf"])
            # Sens : → devrait etre vers un numero >= num (suivant ou soi-meme)
            if actual[0] < num:
                notebook_findings.append({
                    "type": "forward_inverted",
                    "detail": f"fleche (→) pointe vers Z3-{fa['num']}{fa['suf']} qui est AVANT Z3-{num}{suf} (sens inverse)",
                    "raw": fa["raw"]
                })
            # Cible : devrait etre le suivant dans la liste
            elif next_in_list is not None and actual != next_in_list:
                # Tolerance : serie terminee (Z3-18) sans successeur
                if actual[0] > next_in_list[0]:
                    notebook_findings.append({
                        "type": "forward_skip",
                        "detail": f"fleche (→) pointe vers Z3-{fa['num']}{fa['suf']} au lieu de Z3-{next_in_list[0]}{next_in_list[1]} (saut)",
                        "raw": fa["raw"]
                    })

        # Verifier que les liens markdown pointent vers des notebooks existants (404)
        for lnk in cell0["links"]:
            target_num, target_suf = lnk["num"], lnk["suf"]
            target_path = by_num.get((target_num, target_suf))
            if target_path is None:
                notebook_findings.append({
                    "type": "link_404",
                    "detail": f"lien [{lnk['text']}]({lnk['target']}) pointe vers un notebook Python inexistant dans le dossier (404)"
                })

        # Verifier qu'il existe AU MOINS une fleche forward si next_in_list existe
        # ET que la serie n'est pas terminee intentionnellement
        if next_in_list is not None and not forward_arrows:
            # Chercher si la cellule [0] a un "README" ou "Serie" sans fleche forward
            has_readme_link = any("README" in lnk["text"] for lnk in cell0["links"])
            if not has_readme_link:
                notebook_findings.append({
                    "type": "absence_forward",
                    "detail": f"cellule [0] n'a pas de fleche (->) vers le notebook suivant Z3-{next_in_list[0]}{next_in_list[1]}"
                })

        if notebook_findings:
            findings.append({
                "notebook": path.name,
                "num": num,
                "suf": suf,
                "findings": notebook_findings
            })

    return findings


def main():
    parser = argparse.ArgumentParser(description="Check Z3-Python notebook navigation consistency")
    parser.add_argument("--dir", default="MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API",
                        help="Dossier des notebooks Z3-Python (relatif au repo root)")
    parser.add_argument("--json", action="store_true", help="Sortie JSON")
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parent.parent.parent
    z3_dir = repo_root / args.dir
    if not z3_dir.exists():
        print(f"ERROR: dossier introuvable: {z3_dir}", file=sys.stderr)
        sys.exit(2)

    notebooks = list_z3_python_notebooks(z3_dir)
    findings = check_navigation(notebooks)

    if args.json:
        out = {
            "scanned": len(notebooks),
            "findings_count": len(findings),
            "findings": findings
        }
        print(json.dumps(out, ensure_ascii=False, indent=2))
    else:
        print(f"Z3-Python notebooks scannes : {len(notebooks)}")
        print(f"Findings : {len(findings)}")
        print()
        if findings:
            for f in findings:
                print(f"  {f['notebook']}")
                for fd in f["findings"]:
                    print(f"    [{fd['type']}] {fd['detail']}")
            print()
            print("FAIL: navigation stale detectee (cf docstring -- stale-navigation-pattern)")
            sys.exit(1)
        else:
            print("OK: navigation coherente sur tous les Z3-Python")

    sys.exit(0 if not findings else 1)


if __name__ == "__main__":
    main()
