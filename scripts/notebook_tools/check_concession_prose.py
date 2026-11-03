#!/usr/bin/env python3
"""T5 de l'Epic #21424 : detecteur de prose de concession AJOUTEE (#21433).

Repere, commit par commit, les lignes de prose ajoutees dans un carnet pour
avouer un etat degrade : « limites honnetes », « illustratif », « non
disponible », « execution sautee », verdict INTRINSIC, etc. Contrairement au
stock au head, on ne compte ici que les lignes AJOUTEES par le diff
sha^..sha (correction F1 de la revue de clusterManager-Myia sur #21425) :
une ligne d'aveu deja presente au parent ne compte pas.

Le CONCESSION_RE est repris tel quel de #21425 (fermee pour doublon de T1,
branche conservée). Ce detecteur n'est PAS un discriminant du mode bloquant
de check_output_collapse.py (T2, #21426) : la prose d'aveu ne dit pas si la
sortie s'est effondree -- elle sert a inventorier les aveux a verifier
(mesure lane : ~99 % de faux positifs pour n_concessions >= 5 sur 5 242
lignes ; mesure ai-01 concordante).

Sorties :
  - mode --commit / --history : une ligne JSON (JSONL) par ligne d'aveu
    ajoutee, champs {commit, date, notebook, cell, line, motif, kind} ; plus
    un resume par commit sur stderr et un resume final sur stdout.
    - "cell" : id nbformat de la cellule (stable au deplacement), position
      "pos-N" en repli (apport #21443) ;
    - "line" : la ligne BRUTE, accents et casse d'origine -- le match et la
      comparaison au parent portent sur la forme normalisee (apport #21443) ;
    - "kind" : "added" (ligne prouvee ajoutee sur un carnet existant) vs
      "notebook-added" (carnet CREE par le commit, aucune baseline -- espece
      separee, comptee a part : la mesurer lane montre ~95 degrades de
      naissance vs ~189 ajoutes sur 3 jours, les melanger fausserait la
      calibration T2 ; apport #21443).

  - mode --self-test : controles positif/negatif (voir SELF_TEST_*).

Historique reprenable : --state <fichier> retient le dernier commit traite ;
un relancement reprend apres ce commit (exclusif). Les commits de merge sont
ecartes (leur diff n'est pas de la prose d'auteur) et comptes a part.

Codes de sortie (enumeres, jamais silencieux) :
  0 = inventaire OK (des hits ne sont PAS une erreur : c'est un inventaire,
      pas un gate bloquant) ;
  1 = erreur d'usage ou d'acces git ;
  2 = echec d'un controle du --self-test.
"""

import argparse
import json
import re
import subprocess
import sys
import unicodedata

# Repris tel quel de #21425 (feature/21424-output-collapse-history-mode).
# Match accent-blind grace a _normalize() : « saute » et « sautée » hitent
# « sautee » ; « honnête » hit « honnete ».
CONCESSION_RE = re.compile(
    r"honnete|illustrati|non disponible|pas disponible|indisponible|non tenu"
    r"|sautee|simulee?s?\b|mode (simulation|degrade|simule)"
    r"|hors scope|limites"
    r"|n'a pas pu|non execute|cle api absente|api non configuree|placeholder"
)

# Contextes ou « limites » n'est PAS un aveu (#21424 T5, mesure du 2026-10-27).
# Sur 58 lignes vivantes portant le motif, 12 (21 %) sont des faux positifs
# semantiques, en six familles mesurees : bornes de phrases (chunking), cas
# limites (edge cases), verification aux limites (bornes d'intervalle),
# contraintes de portefeuille (exposition/institutionnelles/position), DFS
# borne, parametres de cout et de taux. Ces occurrences nomment une contrainte
# technique, pas un etat degrade assume : elles ne doivent pas designer un
# travail. Le motif reste actif partout ailleurs.
NON_CONCESSION_CONTEXT_RE = re.compile(
    r"limites? (de |d.)(exposition|position|cout|taux|phrase|mots)"
    r"|limites? institutionnelles?"
    r"|limites? par (une )?borne"
    r"|aux limites"
    r"|cas limites?"
    r"|tester les limites"
)

# Controle positif reel (#21433 attendu 2) : ce commit ajoute EXACTEMENT une
# ligne de prose de concession (cellule 39, « le cote honnete du verdict »).
SELF_TEST_COMMIT = "6eb23754b7ee88856cc96a42bcd6fe2a5a5b8550"
SELF_TEST_NOTEBOOK = ("MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/"
                      "Argumentation-Obs-04-Recollement-Strate6-Python.ipynb")
SELF_TEST_EXPECTED_HITS = 1


def _normalize(text):
    """Minuscule + accents retires : le match de motif est accent-blind."""
    decomposed = unicodedata.normalize("NFD", text)
    stripped = "".join(c for c in decomposed
                       if unicodedata.category(c) != "Mn")
    return stripped.lower()


def concession_match(norm):
    """Premier match de concession dont l'occurrence n'est pas neutralisee.

    « limites » est le motif le plus bruyant du detecteur. Une occurrence qui
    tombe DANS l'empan d'un contexte de NON_CONCESSION_CONTEXT_RE nomme une
    contrainte technique (bornes de phrases, cas limites, bornes
    d'intervalle, contraintes de portefeuille, DFS borne, parametres de cout
    ou de taux) : elle ne compte pas.

    Les autres motifs de la meme ligne restent actifs : une ligne peut porter
    une vraie concession ailleurs, et la neutralisation porte sur
    l'occurrence, pas sur la ligne.

    Rend un objet match (compatible `.group(0)` et `.search`) ou None.
    """
    neutral = [m.span() for m in NON_CONCESSION_CONTEXT_RE.finditer(norm)]
    for m in CONCESSION_RE.finditer(norm):
        if m.group(0).startswith("limite"):
            if any(start <= m.start() and m.end() <= end
                   for start, end in neutral):
                continue
        return m
    return None


def _source_text(cell):
    """nbformat stocke la source en str ou list[str] ; aplatit les deux."""
    src = cell.get("source", "")
    if isinstance(src, list):
        return "".join(str(x) for x in src)
    return str(src or "")


def markdown_cells(nb):
    """Cellules markdown -> {adresse: [lignes brutes]}.

    Adresse stable (apport #21443) : l'id nbformat (4.5) de la cellule quand
    present, la position "pos-N" en repli -- un id survit au deplacement de
    la cellule, une position non.
    """
    out = {}
    if not nb:
        return out
    for i, cell in enumerate(nb.get("cells") or []):
        if cell.get("cell_type") != "markdown":
            continue
        key = cell.get("id") or ("pos-%d" % i)
        out[key] = _source_text(cell).splitlines()
    return out


def added_concession_lines(parent_nb, head_nb):
    """Lignes d'aveu AJOUTEES entre deux carnets parses.

    Une ligne du head compte comme ajoutee seulement si sa forme normalisee
    n'apparait dans AUCUNE cellule markdown du parent (comparaison
    normalisee exacte) : une ligne deja presente au parent -- meme deplacee
    d'une cellule a l'autre -- ne compte pas (correction F1, attendu 2 de
    #21433).

    Le MATCH de motif et la comparaison au parent portent sur la ligne
    normalisee ; le champ "line" du hit garde la ligne BRUTE, accents et
    casse d'origine -- c'est elle que le tri humain lira (apport #21443).

    Rend la liste ET le compte (lecons count-vs-list) :
    [{cell, line, motif}] avec cell = id nbformat ou "pos-N".
    """
    parent_all = set()
    for lines in markdown_cells(parent_nb).values():
        parent_all.update(_normalize(ln) for ln in lines)
    hits = []
    for key, lines in markdown_cells(head_nb).items():
        for line in lines:
            norm = _normalize(line)
            if norm in parent_all:
                continue
            m = concession_match(norm)
            if m:
                hits.append({"cell": key,
                             "line": line.strip()[:200],
                             "motif": m.group(0)})
    return hits


def git(*args, cwd=None):
    """Rend la sortie stdout d'une commande git, ou None si elle echoue."""
    proc = subprocess.run(["git", *args], capture_output=True,
                          text=True, encoding="utf-8", errors="replace",
                          cwd=cwd)
    if proc.returncode != 0:
        return None
    return proc.stdout


def parse_notebook(blob):
    """Parse un blob ipynb ; rend None si binaire/JSON illisible."""
    try:
        return json.loads(blob)
    except (ValueError, TypeError):
        return None


def commit_hits(sha, cwd=None):
    """Hits d'un commit : carnets ipynb ajoutes/modifies, parent vs head.

    Les commits de merge (plusieurs parents) sont ecartes : leur diff
    n'est pas de la prose d'auteur. Un carnet CREE par le commit (absent au
    parent) est une espece separee, kind="notebook-added" : sans baseline,
    aucune ligne ne peut etre prouvee ajoutee (apport #21443). Un parent
    present mais illisible (JSON casse, historique ancien) ecarte le carnet
    -- lui fabriquer une baseline vide attribuerait a tort tout le stock du
    head a ce commit. Rend (hits, notebooks_vus, skipped).
    """
    raw = git("log", "-1", "--format=%P", sha, cwd=cwd)
    if raw is None:
        return None
    if len(raw.split()) > 1:
        return [], [], "merge"
    files = git("diff-tree", "--no-commit-id", "--name-only", "-r",
                "--diff-filter=AM", sha, "--", "*.ipynb", cwd=cwd)
    if files is None:
        return None
    hits = []
    seen = []
    for nb_path in (f for f in files.splitlines() if f.strip()):
        head_blob = git("show", f"{sha}:{nb_path}", cwd=cwd)
        if head_blob is None:
            continue
        head_nb = parse_notebook(head_blob)
        if head_nb is None:
            continue
        parent_blob = git("show", f"{sha}~1:{nb_path}", cwd=cwd)
        if parent_blob is None:
            parent_nb = None  # carnet cree par ce commit
        else:
            parent_nb = parse_notebook(parent_blob)
            if parent_nb is None:
                continue  # parent illisible : pas de baseline, on ecarte
        seen.append(nb_path)
        kind = "notebook-added" if parent_nb is None else "added"
        for h in added_concession_lines(parent_nb, head_nb):
            h.update({"commit": sha, "notebook": nb_path, "kind": kind})
            hits.append(h)
    return hits, seen, None


def iter_commits(cwd=None, after=None, limit=None):
    """Commits touchant au moins un ipynb, du plus ancien au plus recent.

    after : reprend APRES ce sha (exclusif) -- cote reprenable.
    """
    args = ["log", "--reverse", "--format=%H %ci"]
    if after:
        args.append(f"{after}..HEAD")
    args += ["--", "*.ipynb"]
    raw = git(*args, cwd=cwd)
    if raw is None:
        return None
    rows = [ln.split(" ", 1) for ln in raw.splitlines() if ln.strip()]
    if limit:
        rows = rows[:limit]
    return [(sha, date.strip()) for sha, date in rows]


def self_test(cwd=None):
    """Controles de #21433 attendu 2. Rend (ok, [descriptions])."""
    notes = []
    ok = True

    # (a) Positif synthetique : une ligne d'aveu ajoutee au head.
    parent = {"cells": [
        {"cell_type": "markdown", "source": ["# Titre ordinaire\n",
                                             "Prose sans aveu."]}]}
    head = {"cells": [
        {"cell_type": "markdown", "source": ["# Titre ordinaire\n",
                                             "Prose sans aveu.\n",
                                             "Resultat illustratif."]}]}
    hits = added_concession_lines(parent, head)
    if (len(hits) == 1 and hits[0]["motif"] == "illustrati"
            and hits[0]["cell"] == "pos-0"
            and hits[0]["line"] == "Resultat illustratif."):
        notes.append("PASS positif synthetique: 1 hit motif=illustrati, "
                     "ligne brute conservee")
    else:
        ok = False
        notes.append(f"FAIL positif synthetique: hits={hits}")

    # (b) Negatif : prose ordinaire ajoutee -> 0 hit.
    head2 = {"cells": [
        {"cell_type": "markdown", "source": ["Le modele converge en 12 "
                                             "epoques, perte 0.03."]}]}
    if added_concession_lines(parent, head2) == []:
        notes.append("PASS negatif prose ordinaire: 0 hit")
    else:
        ok = False
        notes.append("FAIL negatif prose ordinaire: sur-declenchement")

    # (c) Deja presente au parent -> ne compte pas (correction F1) : la
    # ligne d'aveu existe au parent et n'est que DEPLACEE au head.
    parent_c = {"cells": [
        {"cell_type": "markdown", "source": ["Resultat illustratif.\n",
                                             "Contexte initial."]}]}
    head3 = {"cells": [
        {"cell_type": "markdown", "source": ["Contexte initial.\n"]},
        {"cell_type": "markdown", "source": ["Resultat illustratif."]}]}
    if added_concession_lines(parent_c, head3) == []:
        notes.append("PASS ligne deplacee (deja au parent): 0 hit")
    else:
        ok = False
        notes.append("FAIL ligne deplacee (deja au parent): compte a tort")

    # (d) Accent-blind : « exécution sautée » hit « sautee », et le hit
    #     garde la ligne BRUTE (apport #21443).
    head4 = {"cells": [
        {"cell_type": "markdown", "source": ["Exécution sautée (locale)"]}]}
    hits4 = added_concession_lines({"cells": []}, head4)
    if (len(hits4) == 1 and hits4[0]["motif"] == "sautee"
            and hits4[0]["line"] == "Exécution sautée (locale)"):
        notes.append("PASS accent-blind (sautee), ligne brute conservee")
    else:
        ok = False
        notes.append(f"FAIL accent-blind (sautee): {hits4}")

    # (e) Code ne compte pas : cellule code avec « placeholder » ->
    #     hors champ (markdown seulement).
    head5 = {"cells": [
        {"cell_type": "code", "source": ["x = placeholder"]}]}
    if added_concession_lines({"cells": []}, head5) == []:
        notes.append("PASS cellule code hors champ")
    else:
        ok = False
        notes.append("FAIL cellule code hors champ")

    # (f) Replay reel sur le commit de controle, si present dans le depot.
    if git("cat-file", "-e", SELF_TEST_COMMIT, cwd=cwd) is not None:
        res = commit_hits(SELF_TEST_COMMIT, cwd=cwd)
        n_hits = len(res[0]) if res else -1
        good_nb = (res is not None and n_hits == SELF_TEST_EXPECTED_HITS
                   and all(h["notebook"] == SELF_TEST_NOTEBOOK
                           and h["kind"] == "added"
                           for h in res[0]))
        if good_nb:
            notes.append(f"PASS replay {SELF_TEST_COMMIT[:12]}: exactement "
                         f"{SELF_TEST_EXPECTED_HITS} hit")
        else:
            ok = False
            notes.append(f"FAIL replay {SELF_TEST_COMMIT[:12]}: "
                         f"{n_hits} hits, attendus "
                         f"{SELF_TEST_EXPECTED_HITS}")
    else:
        notes.append(f"SKIP replay {SELF_TEST_COMMIT[:12]} "
                     "(sha absent de ce depot/clonage)")

    return ok, notes


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Detecteur de prose de concession AJOUTEE (T5, #21433)")
    ap.add_argument("--commit", metavar="SHA",
                    help="analyse un seul commit")
    ap.add_argument("--history", action="store_true",
                    help="itère l'historique des commits touchant un ipynb")
    ap.add_argument("--since", metavar="SHA",
                    help="(history) reprend APRES ce commit (exclusif)")
    ap.add_argument("--state", metavar="FICHIER",
                    help="(history) retient le dernier commit traite ; "
                         "un relancement reprend apres lui")
    ap.add_argument("--limit", type=int, metavar="N",
                    help="(history) borne le nombre de commits traites")
    ap.add_argument("--cwd", metavar="DIR",
                    help="depot git a parcourir (defaut: courant)")
    ap.add_argument("--out", metavar="FICHIER",
                    help="ecrit les lignes JSONL dans ce fichier "
                         "(defaut: stdout, resume sur stderr)")
    ap.add_argument("--self-test", action="store_true",
                    help="controles positif/negatif puis sortie")
    args = ap.parse_args(argv)
    cwd = args.cwd or None

    if args.self_test:
        ok, notes = self_test(cwd=cwd)
        for n in notes:
            print(n)
        print("self-test:", "PASS" if ok else "FAIL")
        return 0 if ok else 2

    if args.commit:
        res = commit_hits(args.commit, cwd=cwd)
        if res is None:
            print("commit introuvable ou git inaccessible", file=sys.stderr)
            return 1
        hits, seen, skipped = res
        for h in hits:
            h["date"] = (git("log", "-1", "--format=%ci",
                             args.commit, cwd=cwd) or "").strip()
        emit(hits, args.out)
        n_added = sum(1 for h in hits if h.get("kind") == "added")
        n_new = len(hits) - n_added
        print(f"{args.commit[:12]}: {n_added} hit(s) ajoute(s), "
              f"{n_new} notebook-added, {len(seen)} carnet(s)"
              f"{' [merge ecarte]' if skipped else ''}")
        return 0

    if args.history:
        after = args.since
        if args.state and not after:
            try:
                with open(args.state, "r", encoding="utf-8") as fh:
                    after = fh.read().strip() or None
            except OSError:
                after = None
        rows = iter_commits(cwd=cwd, after=after, limit=args.limit)
        if rows is None:
            print("historique inaccessible (git log a echoue)",
                  file=sys.stderr)
            return 1
        total_added = 0
        total_new = 0
        merges = 0
        last_sha = after
        out = open(args.out, "a", encoding="utf-8") if args.out else sys.stdout
        try:
            for sha, date in rows:
                res = commit_hits(sha, cwd=cwd)
                if res is None:
                    print(f"{sha[:12]}: lecture impossible, arret",
                          file=sys.stderr)
                    return 1
                hits, seen, skipped = res
                if skipped == "merge":
                    merges += 1
                    last_sha = sha
                    continue
                for h in hits:
                    h["date"] = date
                    print(json.dumps(h, ensure_ascii=False), file=out)
                total_added += sum(1 for h in hits
                                   if h.get("kind") == "added")
                total_new += sum(1 for h in hits
                                 if h.get("kind") == "notebook-added")
                last_sha = sha
        finally:
            if out is not sys.stdout:
                out.close()
        if args.state and last_sha:
            with open(args.state, "w", encoding="utf-8") as fh:
                fh.write(last_sha + "\n")
        print(f"historique: {len(rows)} commit(s) ipynb, "
              f"{merges} merge(s) ecarte(s), {total_added} hit(s) ajoute(s) "
              f"+ {total_new} notebook-added au total"
              + (f", repris apres {after[:12]}" if after else ""))
        return 0

    ap.print_usage()
    return 1


def emit(hits, out_path):
    """Ecrit les hits en JSONL sur stdout ou dans un fichier."""
    out = open(out_path, "a", encoding="utf-8") if out_path else sys.stdout
    try:
        for h in hits:
            print(json.dumps(h, ensure_ascii=False), file=out)
    finally:
        if out is not sys.stdout:
            out.close()


if __name__ == "__main__":
    sys.exit(main())
