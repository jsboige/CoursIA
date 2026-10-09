"""Organe de fraicheur des cellules qui lisent un fichier du depot en direct.

Issue #20049 (``Part of #17465``), ouverte pour fermer la CLASSE du cas
fondateur ``Lean-16b`` / ``Pillars.lean``.

Le defaut structurel
--------------------

Une cellule code peut lire un fichier du depot et en committer la sortie : le
compte de lignes du fichier, ses declarations, leur numero de ligne. Rien ne
la relie ensuite a ce fichier. Le jour ou une tranche reecrit le fichier lu,
la sortie committee devient un temoignage du PASSE -- et aucun organe du depot
ne le voit :

  ``check_kernel_drift.py``        derive de kernel
  ``scan_native_both_drift.py``    derive de jumeaux FR/EN
  ``check_catalog_freshness.py``   fraicheur du catalogue
  ``check_output_collapse.py``     perte de sortie entre base et tete
  ``check_source_collapse.py``     perte de source entre base et tete

Les deux derniers comparent une base a une tete ; ce n'est pas la question ici.
Ce qui est demande est une comparaison entre la sortie COMMITTEE d'une cellule
et l'etat COURANT du fichier qu'elle lit -- un troisieme axe, que personne ne
mesure. Consequence : la peremption est invisible, et c'est un lecteur humain
qui la decouvre (ici une revue de bot structurelle, pas un gate).

Aucun seuil sur le contenu du fichier ne peut remplacer cette mesure : le
fichier lu n'est pas en cause, c'est la COHERENCE entre les deux artefacts qui
derive. L'organe est donc un invariant, pas un ratchet de volume.

Ce que l'organe verifie
-----------------------

Une cellule est declaree dans ``live_read_registry.json`` (notebook, ``id`` de
cellule, chemin du fichier lu). Pour chaque declaration, l'organe derive de la
sortie COMMITTEE les invariants qu'elle affirme, puis les confronte au fichier :

  LINE_COUNT     un nombre accole au nom du fichier lu sur la meme ligne
                 (« Pillars.lean (246 lignes) ») doit egaler son compte de
                 lignes courant ;
  LINE_CITATION  chaque citation ``L<n>: <texte>`` doit designer, a la ligne
                 ``n`` du fichier, une ligne qui COMMENCE par le texte cite.
                 Prefixe et non egalite : la sortie tronque volontiers une
                 ligne longue (ellipse), et une citation tronquee reste
                 attestable ; une citation dont la ligne a BOUGE ne l'est pas.
                 Le prefixe se clore a une frontiere de mot -- une declaration
                 renommee en gardant le prefixe commun ne l'atteste pas ; sur le
                 chemin ellipse, la troncature est declaree et reste toleree.

Le discriminant est mecanique et falsifiable : les deux invariants sont
extraits de la sortie elle-meme, pas d'une configuration par cellule. Une
re-execution fraiche du carnet suffit a les satisfaire ; c'est exactement le
geste de reparation attendu (``Stop & Repair``, regle 6 de secrets-hygiene --
jamais d'edition a la main de la sortie).

Controles (mesures le 2026-10-09, a la pose de l'organe)
--------------------------------------------------------

  POSITIF   ``feature/otca-real-grid`` (#20019, ouverte) reecrit ``Pillars.lean``
            a 348 lignes alors que la cellule ``50dcfe8c`` de ``Lean-16b``
            atteste « 246 lignes » et cite ``L88: unitcell_witness``. La branche
            ne touche PAS ``Lean-16b`` : le rouge est authentique, pas fabrique.
  NEGATIF   ``main`` est coherent au meme instant (246 lignes, symboles cites
            aux lignes citees) -- l'organe y reste vert.

Un organe qui resterait vert sur le controle positif ne serait pas livre ;
c'est la seule chose qui separe un invariant d'un blanc-seing.

Usage
-----

    python check_live_read_freshness.py                 # arbre de travail
    python check_live_read_freshness.py --ref origin/main
    python check_live_read_freshness.py --json
    python check_live_read_freshness.py --self-test

Sortie 0 si toutes les declarations sont fraiches, 1 sinon (un rouge est un
findings nommant la ligne et les deux textes).
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
REGISTRY = Path(__file__).resolve().parent / "live_read_registry.json"

ANSI_RE = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")
COUNT_RE = re.compile(r"(\d[\d   ]*)\s*lignes?\b", re.IGNORECASE)
CITE_RE = re.compile(r"\bL\s*(\d+)\s*:\s*(.*)")
# #20076 (reserve 2) : un nom de fichier dans la sortie, pour distinguer « la
# ligne voisine porte le compte du fichier declare » de « elle porte celui d'un
# AUTRE fichier ». Exige une lettre avant le point, donc un decimal (« 0.9326 »)
# n'est pas pris pour un nom de fichier.
FILEISH_RE = re.compile(r"[\w/-]*[A-Za-z_][\w/-]*\.[A-Za-z]\w{0,7}")


def _norm(text: str) -> str:
    """Retire les sequences ANSI et normalise les espaces."""
    return " ".join(ANSI_RE.sub("", text).split())


def cell_output_text(cell: dict) -> str:
    """Concatene le texte de toutes les sorties d'une cellule."""
    chunks: list[str] = []
    for out in cell.get("outputs", []) or []:
        if isinstance(out.get("text"), list):
            chunks.append("".join(out["text"]))
        elif isinstance(out.get("text"), str):
            chunks.append(out["text"])
        data = out.get("data") or {}
        plain = data.get("text/plain")
        if isinstance(plain, list):
            chunks.append("".join(plain))
        elif isinstance(plain, str):
            chunks.append(plain)
    return "\n".join(chunks)


def count_claims(text: str, basename: str) -> list[tuple[int, str]]:
    """Nombres de lignes affirmes par la sortie, accoles au nom du fichier lu.

    L'accollement tolere UNE ligne d'ecart (#20076, reserve 2). Une sortie
    reflowee peut porter le nom du fichier sur une ligne et son compte sur la
    suivante (« Pillars.lean » puis « 348 lignes »), ou les repartir dans un
    tableau a deux colonnes ; exiger l'identite stricte de ligne laissait alors
    le compte NON confronte, et ``NO_INVARIANT`` ne rattrapait rien puisque les
    citations rendaient ``citations(text)`` non vide. L'organe rendait FRESH
    sur un compte perime par simple mise en forme -- le defaut meme qu'il ferme.

    La ligne voisine n'est retenue que si elle ne nomme AUCUN autre fichier :
    sans cette borne, le compte d'un fichier voisin serait attribue au fichier
    declare (cf ``test_count_claims_scoped_to_basename``). Le compte est
    dedoublonne : une meme ligne voisine de deux occurrences du basename n'est
    confrontee qu'une fois.
    """
    lines = text.splitlines()
    claims: list[tuple[int, str]] = []
    seen: set[tuple[int, str]] = set()

    def _add(line: str) -> None:
        for m in COUNT_RE.finditer(line):
            digits = re.sub(r"\D", "", m.group(1))
            if not digits:
                continue
            item = (int(digits), _norm(line))
            if item not in seen:
                seen.add(item)
                claims.append(item)

    for i, line in enumerate(lines):
        if basename not in line:
            continue
        _add(line)
        for j in (i - 1, i + 1):
            if not 0 <= j < len(lines):
                continue
            if any(Path(t).name != basename for t in FILEISH_RE.findall(lines[j])):
                continue
            _add(lines[j])
    return claims


def citations(text: str) -> list[tuple[int, str]]:
    """Citations ``L<n>: <texte>`` portees par la sortie."""
    found: list[tuple[int, str]] = []
    for line in text.splitlines():
        m = CITE_RE.search(line)
        if m:
            found.append((int(m.group(1)), m.group(2).strip()))
    return found


def citation_matches(src_line: str, cited: str) -> bool:
    """La ligne source commence-t-elle par le texte cite (ellipse toleree) ?

    #20076 (nit) : sur le chemin NON-ellipse, l'acceptation par prefixe exige
    une frontiere de mot. Sans elle, un symbole renomme en gardant le prefixe
    commun (« theorem foo » -> « theorem foobar ») restait vert : la citation ne
    designait plus la meme ligne, et LINE_CITATION -- dont le metier est de
    detecter qu'une ligne a bouge -- laissait passer le cas qu'il ferme.

    Le chemin ellipse (``...``) reste volontairement lenient : l'ellipse
    DECLARE la troncature, et une coupe peut tomber a l'interieur d'un
    identifiant. Le residu est donc nomme, pas silencieux -- une collision de
    prefixe sur une citation TRONQUEE reste attestable.
    """
    c = _norm(cited)
    s = _norm(src_line)
    if not c:
        return True  # citation sans texte : rien a confronter
    if s.startswith(c):
        rest = s[len(c):]
        return not rest or not (rest[0].isalnum() or rest[0] == "_")
    core = c.rstrip(". …")
    return bool(core) and s.startswith(core)


def audit_cell(src_lines: list[str], text: str, basename: str) -> list[str]:
    """Findings d'une cellule : liste vide = fraiche."""
    findings: list[str] = []
    n_lines = len(src_lines)

    for claimed, line in count_claims(text, basename):
        if claimed != n_lines:
            findings.append(
                f"LINE_COUNT: la sortie affirme « {claimed} lignes » pour "
                f"{basename}, le fichier en porte {n_lines} ({line!r})"
            )

    for n, cited in citations(text):
        if n < 1 or n > n_lines:
            findings.append(
                f"LINE_CITATION: la sortie cite L{n}, hors du fichier "
                f"({n_lines} lignes)"
            )
            continue
        if not citation_matches(src_lines[n - 1], cited):
            findings.append(
                f"LINE_CITATION: la sortie cite L{n} = {_norm(cited)!r}, le "
                f"fichier porte {_norm(src_lines[n - 1])!r}"
            )
    return findings


def read_from_ref(rel_path: str, ref: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "show", f"{ref}:{rel_path}"],
        capture_output=True, text=True, encoding="utf-8",
    )
    if proc.returncode != 0:
        raise FileNotFoundError(proc.stderr.strip() or f"{ref}:{rel_path}")
    return proc.stdout


def load(ref: str | None):
    def _load_text(rel_path: str) -> str:
        if ref:
            return read_from_ref(rel_path, ref)
        return (REPO_ROOT / rel_path).read_text(encoding="utf-8")

    def _load_nb(rel_path: str) -> dict:
        return json.loads(_load_text(rel_path))

    return _load_text, _load_nb


def run(ref: str | None = None) -> dict:
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    load_text, load_nb = load(ref)
    rows: list[dict] = []
    stale = 0

    for entry in registry.get("cells", []):
        nb_path = entry["notebook"]
        cell_id = entry["cell_id"]
        src_path = entry["source"]
        basename = Path(src_path).name
        row = {"notebook": nb_path, "cell_id": cell_id, "source": src_path,
               "verdict": None, "findings": []}

        try:
            nb = load_nb(nb_path)
        except (FileNotFoundError, json.JSONDecodeError) as exc:
            row["verdict"] = "NOTEBOOK_UNREADABLE"
            row["findings"] = [str(exc)]
            rows.append(row)
            stale += 1
            continue

        cell = next((c for c in nb.get("cells", []) if c.get("id") == cell_id), None)
        if cell is None:
            row["verdict"] = "CELL_NOT_FOUND"
            row["findings"] = [
                f"aucune cellule d'id {cell_id!r} dans {Path(nb_path).name} -- "
                "la declaration est perimee, pas le fichier lu"
            ]
            rows.append(row)
            stale += 1
            continue

        try:
            src = load_text(src_path)
        except FileNotFoundError:
            row["verdict"] = "SOURCE_MISSING"
            row["findings"] = [f"fichier lu introuvable : {src_path}"]
            rows.append(row)
            stale += 1
            continue

        text = cell_output_text(cell)
        if not text.strip():
            row["verdict"] = "NO_OUTPUT"
            row["findings"] = ["cellule sans sortie committee"]
            rows.append(row)
            stale += 1
            continue

        findings = audit_cell(src.splitlines(), text, basename)
        if not count_claims(text, basename) and not citations(text):
            row["verdict"] = "NO_INVARIANT"
            row["findings"] = [
                "aucun invariant extractible de la sortie (ni compte de "
                "lignes accole au fichier, ni citation L<n>) -- rien a "
                "verifier, la declaration ne sert a rien"
            ]
            rows.append(row)
            stale += 1
            continue

        row["verdict"] = "STALE" if findings else "FRESH"
        row["findings"] = findings
        if findings:
            stale += 1
        rows.append(row)

    return {"ref": ref or "WORKTREE", "declared": len(rows),
            "stale": stale, "rows": rows}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        description="Fraicheur des cellules qui lisent un fichier du depot.")
    ap.add_argument("--ref", default=None,
                    help="git-ref a evaluer (defaut : l'arbre de travail)")
    ap.add_argument("--json", action="store_true", dest="as_json")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args(argv)

    if args.self_test:
        return _self_test()

    report = run(args.ref)
    if args.as_json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(f"Cellules live-read declarees : {report['declared']} "
              f"(ref {report['ref']})")
        for row in report["rows"]:
            mark = "OK  " if row["verdict"] == "FRESH" else "ROUGE"
            print(f"  [{mark}] {row['verdict']} -- {Path(row['notebook']).name}"
                  f"::{row['cell_id']} -> {Path(row['source']).name}")
            for f in row["findings"]:
                print(f"          {f}")
        if report["stale"]:
            print(f"\n{report['stale']} cellule(s) perimee(s) : re-executer le "
                  "carnet (Stop & Repair), jamais editer la sortie a la main.")
    return 1 if report["stale"] else 0


def _self_test() -> int:
    """Verifie le discriminant sur des cas construits a la main."""
    src = ["alpha", "def unitcellInitial : Grid := ([] : Grid)", "| x | y |"]
    ok = [
        ("fichier (3 lignes)", 0),
        ("L2: def unitcellInitial", 0),
        ("L3: | x | y |", 0),
        ("L1: alpha ...", 0),
        ("fichier\n3 lignes", 0),     # #20076 : nom et compte sur deux lignes
    ]
    bad = [
        ("fichier (4 lignes)", 1),
        ("L2: def otcaInitial", 1),
        ("L9: alpha", 1),
        ("fichier\n4 lignes", 1),     # idem, compte faux : doit rougir
    ]
    failures = 0
    for text, expected in ok + bad:
        got = len(audit_cell(src, text, "fichier"))
        if bool(got) != bool(expected):
            failures += 1
            print(f"  ECHEC self-test : {text!r} -> {got} (attendu "
                  f"{'rouge' if expected else 'vert'})")
    if failures:
        print(f"self-test : {failures} echec(s)")
        return 1
    print(f"self-test : {len(ok) + len(bad)} cas, discriminant conforme")
    return 0


if __name__ == "__main__":
    sys.exit(main())
