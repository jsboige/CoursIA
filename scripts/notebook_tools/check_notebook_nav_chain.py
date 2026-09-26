#!/usr/bin/env python3
"""Check that every notebook of a series is REACHABLE through its navigation chain.

Pourquoi cet outil existe
-------------------------
`check_notebook_navlinks.py` verifie que chaque cible de lien **existe** (404).
Il ne verifie pas que la chaine de navigation **atteint** chaque notebook. Les
deux proprietes divergent exactement sur un notebook **insere** dont les voisins
pointent encore l'un vers l'autre :

    avant :  12 -> 13        13 -> 12        (chaine intacte, 12b invisible)
    apres :  12 -> 12b       12b -> 13       13 -> 12

Dans l'etat « avant », `12b` n'a **aucun lien entrant**. Tous les liens de la
serie resolvent, donc le garde 404 est **vert**, et pourtant aucun lecteur ne
peut atteindre `12b` en suivant la navigation. C'est ce qui a laisse passer
`QC-Py-12b` et `QC-Py-23c` sur toute la serie QC-Py (corrige par #17277 en tant
qu'**instance**, jamais en tant que **classe**).

Comment ca marche
-----------------
Le depot est lu comme un graphe oriente : noeuds = notebooks git-tracked sous
`MyIA.AI.Notebooks/`, aretes = liens de navigation d'un notebook vers un autre
`.ipynb`. Une **serie** = le dossier parent d'un notebook.

Pour chaque serie S on calcule :

- `entries(S)` : les notebooks de S sans **aucun lien entrant** (depuis n'importe
  ou dans le depot). Une serie pedagogique a **un** point d'entree : la premiere
  notebook. Deux entrees = un notebook que rien ne relie a la chaine.
- `chain_starts(S)` : les non-entrees dont **tout lien entrant vient d'un
  notebook qu'elles atteignent elles-memes**. Dans la forme canonique
  mutualisee (#17277 : Suivant ET Precedent sur chaque paire), le PREMIER
  notebook recoit le Precedent du deuxieme -- il a un lien entrant, donc
  `entries` ne le voit pas, et la chaine principale parait « inatteignable »
  (angle mort #17625, mesure sur QC-Py : 42 faux inatteignables). Un depart de
  chaine rejoint la base du parcours : sa chaine est jugee navigable.
- `independent_chain` : finding emis quand un depart de chaine n'est atteint
  par AUCUNE entree. Le graphe ne peut pas decider si une composante mutualisee
  deconnectee est « la serie principale » (QC-Py) ou « un ilot oublie »
  (07 <-> 08) -- les deux formes sont isomorphes vues des liens. Le seeding
  l'accepte comme navigable, mais la deconnection reste RAPPORTEE : la serie ne
  devient jamais silencieuse sur ce cas.
- `unreachable(S)` : les notebooks de S **non-entries** qu'aucune entree ni
  depart de chaine n'atteint (ilot non mutualise, chaines cassees). Calcul par
  parcours en largeur.
- `wrapped` : les series ou **tout** notebook a un lien entrant (la chaine
  **boucle** : le « suivant » du dernier pointe le premier). C'est une
  convention legitime, pas un cas non jugeable — la serie est jugee depuis son
  depart le plus couvrant. Les declarer non jugeables laissait **18 series**
  hors du garde (mesure du 2026-09-21).

`entries` et `unreachable` sont **disjoints** : une entree orpheline est
rapportee une seule fois, comme entree.

Ce qui est juge, et ce qui ne l'est pas
---------------------------------------
Une serie n'est jugee que si elle **exhibe** une convention de navigation (au
moins une arete interne). Un dossier de recherche, de scripts ou de brouillons
n'en a aucune : le juger produirait un finding par notebook, tous faux. Ces
dossiers sont ecartes, **comptes et publies** (`not_judged`), jamais ecartes en
silence.

L'arete est reconnue a **trois portees**, chacune ajoutee apres mesure d'un faux
orphelin (detail dans `_looks_nav` et `NAV_LINE_MARKERS`) : le texte du lien, la
ligne entiere, la cellule. Ce qui n'est **pas** une arete, volontairement : une
mention en prose (nom de fichier entre `backticks`), une liste « voir aussi »
titree, un lien de parite de jumeaux C#/Python. Ce sont des references, pas la
chaine de navigation — et c'est la chaine qui est jugee.

**Calibration (mesure du 2026-09-21)**, sur un echantillon aleatoire de 30
orphelins declares : 12 portaient une reference entrante d'apres `grep`. Les 12
ont ete instrutes un par un — **toutes** sont de la prose, une liste « voir
aussi » ou un lien de jumeaux, donc **aucun faux positif** dans l'echantillon.
Le taux brut de `grep` (12/30) est une borne **superieure**, pas le taux de FP.
Residu connu et assume : une rangee d'en-tete de type « Ladder L1 · L2 · L3 »
sans mot de navigation n'est pas reconnue comme une arete.

Ce que cet outil ne dit PAS
---------------------------
- Il ne juge pas la **qualite** d'un ordre : une chaine qui passe par tous les
  notebooks dans un ordre pedagogicalement absurde est « atteignable ».
- Il ne remplace pas le garde 404 : les deux sont necessaires ensemble.

Modes (convention check_notebook_navlinks.py / check_docs_links.py)
------------------------------------------------------------------
    python check_notebook_nav_chain.py                  # scan complet, exit 1 si findings
    python check_notebook_nav_chain.py --baseline       # ecrit scripts/tests/baseline_nb_nav_chain.json
    python check_notebook_nav_chain.py --check          # check vs baseline (exit 1 si NEW)
    python check_notebook_nav_chain.py --family Sharp   # limiter le RAPPORT a une famille
    python check_notebook_nav_chain.py NB.ipynb         # limiter le rapport a la serie de ce notebook
    python check_notebook_nav_chain.py --json           # sortie machine
    python check_notebook_nav_chain.py --quiet          # sortie minimale (CI)

Exit codes
----------
    0 = aucun finding (ou mode --check : aucun NEW finding)
    1 = findings presents (ou NEW findings vs baseline)
    2 = erreur d'execution (aucun notebook, argument introuvable)

Voir aussi
----------
- scripts/notebook_tools/check_notebook_navlinks.py (garde 404, source unique
  de l'extraction de liens et de la decouverte : ce tool l'importe au lieu de
  redupliquer sa logique)
- #17093 (chaine QC-Py cassee), #17277 (l'instance corrigee)
"""
import argparse
import json
import sys
from collections import defaultdict, deque
from pathlib import Path

# Source unique de l'extraction de liens, de la resolution de cible et de la
# decouverte de notebooks : on importe le garde 404 au lieu de redupliquer sa
# logique (meme convention que son propre `from notebook_walk import SKIP_DIRS`).
# Si ces primitives divergent un jour, les deux gardes divergeraient ensemble --
# ce qui est le comportement recherche.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_notebook_navlinks import (  # noqa: E402
    LINK_PATTERN,
    NOTEBOOKS_ROOT,
    REPO_ROOT,
    _iter_notebooks,
    _resolve_target,
    _should_skip,
)

BASELINE_PATH = REPO_ROOT / "scripts" / "tests" / "baseline_nb_nav_chain.json"

# Vocabulaire de navigation. Base sur celui de check_notebook_navlinks.py (ou il
# sert a CLASSER un lien casse), **complete par mesure** : il sert ici a decider
# si un lien est une ARETE du graphe, et un mot manquant fabrique un faux
# orphelin. Mesure du 2026-09-21, sur un echantillon de 30 orphelins declares :
# 13 portaient une reference entrante, dont la rangee de nav canonique ecrite
# avec des FLECHES plutot que des chevrons --
#
#     [← MGS-7b LandscapeMultidim](MGS-07b-LandscapeMultidim.ipynb) · [MGS-8 LandscapeExplorer →](MGS-08-LandscapeExplorer.ipynb)
#
# ni « precedent »/« suivant » ni marqueur `Navigation` dans la cellule : la
# rangee etait donc invisible au detecteur. Les fleches sont ajoutees ici.
# Les autres references de l'echantillon sont de la PROSE (un nom de fichier en
# `backticks`) ou des listes « voir aussi » titrees : elles ne sont pas des
# aretes, et ne doivent pas le devenir -- c'est la chaine de navigation qui est
# jugee, pas la simple mention.
NAV_KEYWORDS = (
    "precedent", "précédent", "prec", "préc",
    "suivant", "suivante", "next", "prev",
    "navigation", "index", ">>", "<<",
    "←", "→", "↑", "↓",  # ← → ↑ ↓
)

# Sous-ensemble employe pour scanner la LIGNE ENTIERE (et non le seul texte du
# lien). Mesure du 2026-09-21 : `MGS-10-CenterBias` ecrit sa rangee de nav ainsi
#
#     **Série MetaGeneticSharp** | Précédent : [MGS-9 - Relief Everest](MGS-09-EverestRelief.ipynb) | [↑ Série MGS](README.md)
#
# -- le mot « Précédent » est sur la ligne, HORS du texte du lien, et le texte du
# lien est le titre du voisin. Scanner le seul `text+target` manquait l'arete.
# `index`/`prec`/`préc` sont EXCLUS de ce scan large : trop frequents en prose
# (« l'index de la liste », « precisement ») pour y servir de marqueur.
NAV_LINE_MARKERS = (
    "precedent", "précédent", "suivant", "suivante", "next", "prev",
    "navigation", ">>", "<<",
    "←", "→", "↑", "↓",
)


def _rel(path: Path) -> str:
    """Chemin repo-relatif POSIX (stable cross-OS pour le baseline)."""
    return path.relative_to(REPO_ROOT).as_posix()


def _looks_nav(text: str, target: str, line: str, cell_is_nav: bool) -> bool:
    """True si le lien est une arete de navigation.

    Trois portees, parce que les trois conventions coexistent dans le depot et
    qu'une portee trop etroite fabrique un faux orphelin (mesures du 2026-09-21) :

      1. **le lien** — `[Suivant >>](13-foo.ipynb)` : le mot est dans le texte du
         lien ou dans la cible.
      2. **la ligne** — `**Série MGS** | Précédent : [MGS-9 ...](MGS-09-....ipynb)` :
         le mot est sur la ligne, HORS du lien, et le texte du lien est le titre
         du voisin. Scan restreint a `NAV_LINE_MARKERS`.
      3. **la cellule** — le bloc canonique est une TABLE sous un titre, donc le
         marqueur et les liens sont sur deux lignes differentes :

             ## Navigation
             | [Sudoku-05-PSO](Sudoku-05-PSO-Csharp.ipynb) | | [Sudoku-07-...](...) |

    Ce qui n'est **pas** une arete, volontairement : une mention en prose (nom de
    fichier entre `backticks`), une liste « voir aussi » titree, un lien de
    parite de jumeaux (`| ↔ Python | [Search-03c — LDS (Python)](...)`). Ce sont
    des references, pas la chaine de navigation — c'est la chaine qui est jugee.
    """
    low = f"{text} {target}".lower()
    if any(k in low for k in NAV_KEYWORDS):
        return True
    if any(k in line.lower() for k in NAV_LINE_MARKERS):
        return True
    return cell_is_nav


def nav_edges(nb_path: Path):
    """Aretes sortantes de `nb_path` : les .ipynb cibles de ses liens de nav.

    Retourne une liste de chemins resolus (absolus, dedupliques). Un lien dont
    la cible n'existe pas est **ignore** : c'est un 404, deja le metier de
    check_notebook_navlinks.py, et il ne peut pas etre un noeud du graphe.
    """
    try:
        with open(nb_path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError):
        return []
    out = []
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "markdown":
            continue
        src = cell.get("source", [])
        text_lines = src if isinstance(src, str) else "".join(src)
        cell_is_nav = "navigation" in text_lines.lower()
        for line in text_lines.splitlines():
            for m in LINK_PATTERN.finditer(line):
                text, target = m.group(1), m.group(2)
                if not _looks_nav(text, target, line, cell_is_nav):
                    continue
                resolved = _resolve_target(nb_path, target)
                if resolved.suffix.lower() != ".ipynb":
                    continue
                if not resolved.is_file():
                    continue
                out.append(resolved)
    # dedup en preservant l'ordre (determinisme du parcours)
    seen, uniq = set(), []
    for r in out:
        if r not in seen:
            seen.add(r)
            uniq.append(r)
    return uniq


def broken_nav_links(nb_path: Path):
    """Liens de nav d'un notebook dont la cible .ipynb est ABSENTE (404).

    Meme portee trois-niveaux que `_looks_nav` : on ne retourne que les liens
    RECONNUS comme navigation (mot-cle dans le texte, sur la ligne, ou cellule
    `## Navigation`), sinon on confondrait un 404 de prose et un 404 de nav.
    Un lien de prose est deja le metier de check_notebook_navlinks.py.

    Retourne une liste de dicts {text, target} -- un par lien casse.
    """
    try:
        with open(nb_path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError):
        return []
    out = []
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "markdown":
            continue
        src = cell.get("source", [])
        text_lines = src if isinstance(src, str) else "".join(src)
        cell_is_nav = "navigation" in text_lines.lower()
        for line in text_lines.splitlines():
            for m in LINK_PATTERN.finditer(line):
                text, target = m.group(1), m.group(2)
                if not _looks_nav(text, target, line, cell_is_nav):
                    continue
                resolved = _resolve_target(nb_path, target)
                if resolved.suffix.lower() != ".ipynb":
                    continue
                if resolved.is_file():
                    continue
                out.append({"text": text, "target": target})
    return out


def scan_broken_nav(notebooks) -> list:
    """Scanne tous les notebooks du set et rapporte les 404 de nav.

    Les liens casses du Z3-08 sweep d'origine (un seul exemple fondateur :
    `Z3-01b-Style-Declaratif-Linq` pointe depuis Z3-08 sans exister dans la
    serie Python) etaient ajustes par un organe dedie Z3-only -- doublon
    structurel de check_notebook_navlinks.py, qui couvrait deja le 404
    universel sans discrimination nav. La discrimination nav est ce qui
    manquait ; elle vit ici.
    """
    findings = []
    for nb in sorted(notebooks, key=_rel):
        for bl in broken_nav_links(nb):
            findings.append({
                "kind": "link_404",
                "notebook": _rel(nb),
                "target": bl["target"],
                "text": bl["text"],
            })
    return findings


def build_graph(notebooks):
    """Construit le graphe et indexe les series.

    Retourne (inbound, outbound, series) ou :
      - `inbound[node]`  = ensemble des noeuds pointant vers `node`
      - `outbound[node]` = liste des noeuds pointes par `node`
      - `series[dir]`    = liste triee des noeuds de ce dossier
    Seuls les noeuds de `notebooks` sont des noeuds ; une arete vers un notebook
    hors du set (gitignored, hors perimetre) est ignoree.
    """
    nodes = set(notebooks)
    inbound = defaultdict(set)
    outbound = defaultdict(list)
    for nb in nodes:
        for dst in nav_edges(nb):
            if dst not in nodes:
                continue
            outbound[nb].append(dst)
            inbound[dst].add(nb)
    series = defaultdict(list)
    for nb in nodes:
        series[nb.parent].append(nb)
    return inbound, outbound, series


def _reachable_from(entries, outbound):
    """Noeuds atteignables par parcours en largeur depuis `entries`."""
    seen = set(entries)
    queue = deque(entries)
    while queue:
        node = queue.popleft()
        for nxt in outbound.get(node, ()):
            if nxt not in seen:
                seen.add(nxt)
                queue.append(nxt)
    return seen


def analyse(inbound, outbound, series):
    """Applique le jugement par serie. Retourne un dict de rapport.

    Un finding est un couple (kind, key) ou `key` identifie la ligne :
      - `orphan_entry` : notebook sans lien entrant, dans une serie qui en a
        plus d'un (donc : rien ne mene a lui depuis la chaine) ;
      - `independent_chain` : la serie porte au moins un depart de chaine
        (forme mutualisee) qu'aucune entree n'atteint -- composante navigable
        mais deconnectee (#17625). Cle = la serie, un finding par serie ;
      - `unreachable`  : notebook non-entry qu'aucune entree ni depart de
        chaine n'atteint.
    Une serie sans entree (chaine bouclee) est jugee depuis son depart le plus
    couvrant -- jamais declaree saine par defaut.

    Une serie n'est jugee que si elle **exhibe** une convention de navigation,
    c'est-a-dire au moins une arete INTERNE. Sans cela le dossier n'est pas une
    serie navigable (dossier de recherche, de scripts, de brouillons) : le juger
    produirait un finding par notebook, tous faux, et un baseline de bruit.
    L'exclusion est **comptee et publiee** (`not_judged`), jamais silencieuse.
    """
    findings = []
    wrapped = []
    not_judged = []
    per_series = []
    for directory in sorted(series, key=lambda d: _rel(d)):
        members = series[directory]
        if len(members) < 2:
            # Une serie d'un seul notebook n'a pas de chaine a juger.
            not_judged.append({"series": _rel(directory), "notebooks": len(members),
                               "reason": "series_single_notebook"})
            continue
        member_set = set(members)
        internal_edges = sum(1 for nb in members
                             for dst in outbound.get(nb, ()) if dst in member_set)
        if internal_edges == 0:
            not_judged.append({"series": _rel(directory), "notebooks": len(members),
                               "reason": "no_internal_nav_edge"})
            continue
        entries = sorted((nb for nb in members if not inbound.get(nb)), key=_rel)
        chain_starts = []
        reach_entries = set()
        if entries:
            reach_entries = _reachable_from(entries, outbound)
            # Departs de chaine (#17625) : non-entrees dont tout inbound vient
            # d'un notebook qu'elles atteignent. Detectees par BFS individuel --
            # le Precedent du 2e vers le 1er est l'exemple type.
            for nb in sorted(members, key=_rel):
                if not inbound.get(nb):
                    continue
                if inbound.get(nb) <= _reachable_from([nb], outbound):
                    chain_starts.append(nb)
            basis = list(entries) + chain_starts
            reach = _reachable_from(basis, outbound)
        else:
            # Aucun notebook n'est sans lien entrant : la chaine **boucle** (le
            # « suivant » du dernier pointe le premier). C'est une convention de
            # navigation legitime, pas une serie non jugeable -- la declarer
            # telle laissait 18 series hors du garde. On se juge alors depuis le
            # depart le plus couvrant : si partir de la atteint toute la serie,
            # elle se parcourt en entier quel que soit le point d'entree.
            wrapped.append({"series": _rel(directory), "notebooks": len(members)})
            best = max(sorted(members, key=_rel),
                       key=lambda n: len(_reachable_from([n], outbound) & member_set))
            basis = [best]
            reach = _reachable_from(basis, outbound)
        entry_set = set(basis)
        unreachable = sorted(
            (nb for nb in members if nb not in entry_set and nb not in reach), key=_rel
        )
        # Une seule entree = serie saine par construction : pas de finding.
        if len(entries) > 1:
            for nb in entries:
                findings.append({"kind": "orphan_entry", "notebook": _rel(nb),
                                 "series": _rel(directory)})
        # Un depart de chaine qu'aucune entree n'atteint : composante mutualisee
        # deconnectee. Navigable en soi (seeding), mais deconnectee -- rapporte,
        # un finding par serie (la cle baseline est la serie, pas chaque membre).
        # NB : reach_entries couvre deja les departs de chaine rattaches a la
        # partie atteignable (BFS transitif), la condition tient en un test.
        independent_heads = [nb for nb in chain_starts if nb not in reach_entries]
        if independent_heads:
            findings.append({"kind": "independent_chain",
                             "notebook": _rel(directory),
                             "series": _rel(directory)})
        for nb in unreachable:
            findings.append({"kind": "unreachable", "notebook": _rel(nb),
                             "series": _rel(directory)})
        per_series.append({
            "series": _rel(directory),
            "notebooks": len(members),
            "entries": [_rel(nb) for nb in entries],
            "basis": [_rel(nb) for nb in basis],
            "wrapped": not entries,
            "chain_starts": len(chain_starts),
            "independent_chains": len(independent_heads),
            "unreachable": [_rel(nb) for nb in unreachable],
        })
    findings.sort(key=lambda f: (f["kind"], f["notebook"]))
    return {"findings": findings, "wrapped": wrapped,
            "not_judged": not_judged, "series": per_series}


def _finding_keys(report):
    """Cles de baseline : (kind, notebook, identifiant discrimant). Le message
    est du confort, pas la cle. `identifiant` = target pour link_404 (plusieurs
    liens casses possibles par notebook), vide sinon (kind+notebook suffit)."""
    keys = set()
    for f in report["findings"]:
        ident = f.get("target", "")
        keys.add((f["kind"], f["notebook"], ident))
    return keys


def _write_baseline(report):
    """Ecrit le baseline (snapshot des findings, supposes connus)."""
    BASELINE_PATH.parent.mkdir(parents=True, exist_ok=True)
    snapshot = sorted(report["findings"], key=lambda f: (f["kind"], f["notebook"]))
    payload = {
        "findings": snapshot,
        "wrapped": sorted(report["wrapped"], key=lambda s: s["series"]),
    }
    with open(BASELINE_PATH, "w", encoding="utf-8", newline="\n") as f:
        json.dump(payload, f, ensure_ascii=False, indent=2)
        f.write("\n")
    return BASELINE_PATH


def _load_baseline():
    """Charge les cles du baseline, ou set() si absent/illisible.

    Format-compatible avec les baselines anciens : si un baseline n'a que
    (kind, notebook) on retombe sur cette cle (target vide).
    """
    if not BASELINE_PATH.is_file():
        return set()
    try:
        with open(BASELINE_PATH, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError):
        return set()
    keys = set()
    for f in data.get("findings", []):
        ident = f.get("target", "")
        keys.add((f["kind"], f["notebook"], ident))
    return keys


def _select_report(report, series_filter):
    """Restreint le rapport a un ensemble de series (--family / notebook cible)."""
    if series_filter is None:
        return report
    keep = set(series_filter)
    return {
        "findings": [f for f in report["findings"] if f["series"] in keep],
        "wrapped": [s for s in report["wrapped"] if s["series"] in keep],
        "not_judged": [s for s in report["not_judged"] if s["series"] in keep],
        "series": [s for s in report["series"] if s["series"] in keep],
    }


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Verifie que chaque notebook d'une serie est ATTEIGNABLE "
                    "par sa chaine de navigation."
    )
    parser.add_argument("notebook", nargs="?",
                        help="Un notebook : limite le rapport a sa serie (defaut: tout)")
    parser.add_argument("--family", help="Limiter le RAPPORT a une famille (ex. Search, Sudoku)")
    parser.add_argument("--baseline", action="store_true",
                        help="Ecrire le baseline (snapshot des findings actuels)")
    parser.add_argument("--check", action="store_true",
                        help="Comparer au baseline ; exit 1 si NEW finding (regression)")
    parser.add_argument("--json", action="store_true", help="Sortie JSON machine-readable")
    parser.add_argument("--quiet", action="store_true", help="Sortie minimale (CI)")
    parser.add_argument("--include-untracked", action="store_true", default=False,
                        help="Inclut les .ipynb sur disque non-tracked par git (legacy)")
    args = parser.parse_args(argv)

    tracked_only = not args.include_untracked

    # Le graphe est TOUJOURS global : l'ensemble des entrees d'une serie depend
    # des liens entrants venus de n'importe ou. --family / notebook ne font que
    # restreindre le RAPPORT, jamais le calcul.
    notebooks = list(_iter_notebooks(None, tracked_only=tracked_only))
    if not notebooks:
        print("error: aucun notebook trouve sous MyIA.AI.Notebooks/", file=sys.stderr)
        return 2

    # Le filtre est exprime en chemins REPO-RELATIFS POSIX : c'est la cle sous
    # laquelle `analyse` publie ses series. Comparer des Path a ces chaines
    # filtrait silencieusement tout (0 serie jugee, rc=0 -- le pire des verts).
    series_filter = None
    if args.notebook:
        p = Path(args.notebook)
        if not p.is_absolute():
            p = REPO_ROOT / args.notebook
        if not p.is_file():
            print(f"error: notebook introuvable: {args.notebook}", file=sys.stderr)
            return 2
        series_filter = {_rel(p.resolve().parent)}
    elif args.family:
        series_filter = {_rel(nb.parent) for nb in notebooks
                         if nb.relative_to(NOTEBOOKS_ROOT).parts[0] == args.family}
        if not series_filter:
            print(f"error: famille inconnue: {args.family}", file=sys.stderr)
            return 2

    inbound, outbound, series = build_graph(notebooks)
    report = _select_report(analyse(inbound, outbound, series), series_filter)
    # Scan des 404 de nav : s'execute APRES le graphe (les liens casses ne sont
    # pas des noeuds du graphe, mais bien des findings a rapporter). Filtre
    # applique a la selection de rapport comme pour le graphe.
    broken_nav = scan_broken_nav(notebooks)
    if series_filter is not None:
        broken_nav = [f for f in broken_nav if _rel(Path(f["notebook"]).parent) in series_filter]
    report["findings"].extend(broken_nav)
    report["findings"].sort(key=lambda f: (f["kind"], f.get("notebook", "")))

    if args.baseline:
        path = _write_baseline(report)
        print(f"baseline ecrit: {path} ({len(report['findings'])} findings connus, "
              f"{len(report['not_judged'])} dossier(s) non juge(s), "
              f"{len(report['wrapped'])} serie(s) bouclee(s))")
        return 0

    if args.check:
        known = _load_baseline()
        current = _finding_keys(report)
        new = sorted(current - known)
        fixed = sorted(known - current)
        if new:
            if not args.quiet:
                print(f"FAIL: {len(new)} NEW finding(s) vs baseline:")
                for kind, notebook, target in new:
                    extra = f" -> {target}" if target else ""
                    print(f"  [{kind}] {notebook}{extra}")
            return 1
        if fixed and not args.quiet:
            print(f"INFO: {len(fixed)} finding(s) resolus depuis le baseline "
                  f"(mettre le baseline a jour).")
        if not args.quiet:
            print(f"OK: 0 NEW finding vs baseline ({len(current)} connus, "
                  f"{len(notebooks)} notebook(s) au graphe).")
        return 0

    findings = report["findings"]
    if args.json:
        json.dump({"total_findings": len(findings),
                   "findings": findings,
                   "wrapped": report["wrapped"],
                   "not_judged": report["not_judged"],
                   "series": report["series"],
                   "scanned": len(notebooks)}, sys.stdout, ensure_ascii=False, indent=2)
        sys.stdout.write("\n")
    elif not args.quiet:
        # Les exclusions sont PUBLIEES, jamais silencieuses : un dossier ecarte
        # faute de convention de navigation n'est pas un dossier sain.
        by_reason = defaultdict(int)
        for s in report["not_judged"]:
            by_reason[s["reason"]] += 1
        if by_reason:
            detail = ", ".join(f"{n} {r}" for r, n in sorted(by_reason.items()))
            print(f"INFO: {len(report['not_judged'])} dossier(s) NON juge(s) ({detail}).")
        if report["wrapped"]:
            # Convention « le suivant du dernier pointe le premier » : la serie
            # est jugee quand meme, depuis son depart le plus couvrant.
            print(f"INFO: {len(report['wrapped'])} serie(s) a chaine BOUCLEE "
                  f"(aucune entree ; jugee(s) depuis un depart arbitraire) : "
                  f"{', '.join(s['series'] for s in report['wrapped'][:4])}"
                  f"{' ...' if len(report['wrapped']) > 4 else ''}")
        if not findings:
            print(f"OK: chaque notebook est atteignable dans sa serie "
                  f"({len(report['series'])} serie(s) jugee(s), "
                  f"{len(notebooks)} notebook(s) au graphe).")
        else:
            orphan = [f for f in findings if f["kind"] == "orphan_entry"]
            unreach = [f for f in findings if f["kind"] == "unreachable"]
            link_404 = [f for f in findings if f["kind"] == "link_404"]
            print(f"FOUND {len(findings)} finding(s) "
                  f"({len(orphan)} entree(s) orpheline(s), "
                  f"{len(unreach)} notebook(s) inatteignable(s), "
                  f"{len(link_404)} lien(s) de nav casse(s)):")
            for f in findings:
                if f["kind"] == "link_404":
                    print(f"  [link_404] {f['notebook']} -> {f.get('target', '?')}")
                else:
                    print(f"  [{f['kind']}] {f['notebook']}  (serie {f['series']})")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
