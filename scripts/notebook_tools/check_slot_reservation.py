#!/usr/bin/env python3
"""Preflight de reservation de slot (#15489, defaut 4).

Origine -- W0 de #5081/#11840, point 4 de #15489 :

    "Un slot peut etre libre sur `main` mais deja reserve par une PR ouverte ou
     une table de mapping publiee."

Le livrable nomme par l'issue -- "registre ou preflight de reservation des slots
contre arbre + cibles de la PR + PR ouvertes" -- est exactement ce fichier.

DEUX TROUS MESURES, ET POURQUOI AUCUN ORGANE NE LES COUVRAIT
------------------------------------------------------------
1. **Deux cibles identiques dans une MEME revision.** Mesure d'execution sur
   l'organe frere `check_duplicate_notebook_index.py` : sa fonction
   `collisions(added, base_files)` compare les ajouts a la BASE, jamais les
   ajouts ENTRE EUX. Deux notebooks neufs au meme index, dans le meme
   repertoire, slot libre sur `main` :

       collisions(["X/04-2-Alpha.ipynb", "X/04-2-Beta.ipynb"],
                  ["X/04-1-Previous.ipynb"])   ->   0 hit

   Le critere d'acceptation de l'issue ("deux cibles proposees identiques dans
   une meme PR sont detectees avant edition") n'etait donc pas couvert.

2. **Le meme slot vise par deux PRs sous des noms DIFFERENTS.**
   `check_pr_path_collisions.py` compare les *chemins* partages entre PRs
   ouvertes. Deux PRs qui visent le meme slot avec des noms differents
   (`04-2-Alpha` et `04-2-Beta`) ne partagent aucun chemin : une collision de
   chemins n'est pas une collision de slot, et cet organe-la reste muet sur ce
   cas par construction -- ce n'est pas un defaut de sa part, c'est une autre
   question.

CE QUE L'ORGANE FAIT, ET CE QU'IL NE FAIT PAS
---------------------------------------------
Il repond a UNE question : « ce slot est-il deja tenu par quelqu'un d'autre ? »,
contre quatre sources, chacune imprimee avec son etat -- une source indisponible
est dite indisponible, jamais silencieuse :

    base        l'arbre de la base (defaut `origin/main`)
    revision    les cibles de la revision examinee, lue en `--no-renames` comme
                le garde d'index : un rename vers un slot est une prise de
                position sur ce slot et doit etre vu comme telle
    open_prs    les PRs ouvertes (`gh`) -- optionnel, et jamais exige en CI
    declared    une table de reservation publiee (`slot_reservations.json`)

Il n'invente **aucun lock** et ne reserve rien : il rend la collision lisible
avant l'edition. Le seul verrou d'arbitrage cross-lane reste
`check_lane_claim.py` -- decision deja actee par #13359 ("Invent NO new claim
lock"), et cet organe ne la rouvre pas.

UNE DIVERGENCE DELIBEREE AVEC L'ORGANE FRERE : LA LIBERATION
------------------------------------------------------------
Le garde d'index ne lit que les AJOUTS. Un renommage `04-2-Ancien ->
04-2-Nouveau` -- le meme slot, retitre -- y ressort donc en collision, mesure
faite :

    collisions(["x/04-2-New-Title.ipynb"], ["x/04-2-Old-Title.ipynb"])  ->  1 hit

Or l'arbre resultant ne porte qu'UN notebook sur le slot 4.2 : le conflit est
avec un fichier que la revision supprime elle-meme. Cet organe-ci lit donc aussi
les suppressions et ne compte pas comme occupant un fichier que la revision
examinee libere. Ce n'est pas une correction du garde d'index -- la question
n'est pas la meme. Lui demande « cet ajout percute-t-il une position ? » ; celui
ici demande « le slot est-il tenu par QUELQU'UN D'AUTRE ? ». Le premier
comportement n'est pas modifie par cette tranche (signal seulement, sujet
separe).

SOURCES : CE QU'UNE PR OUVERTE DIT DE SES SLOTS
-----------------------------------------------
`gh pr list --json files` ne rend que `path`, `additions`, `deletions` -- pas de
`changeType` (mesure faite). Une ecriture se reconnait donc a `additions > 0` :
un chemin a `additions == 0` est une suppression PURE, c'est-a-dire un slot
LIBERE, pas un slot reserve. Sans ce filtre, chaque PR qui renomme un notebook
reserverait le slot qu'elle vient de quitter.

MESURES SUR L'ARBRE ET LE POOL VIVANTS (2026-09-11)
---------------------------------------------------
Ce que la source `open_prs` trouve, et ce qu'elle ne trouve pas -- ecrit ici
pour que personne ne presente ce trou comme une hemorragie :

- 59 PRs ouvertes lues, **22 slots reserves** par au moins une PR, dont **16 par
  plusieurs**. Les 16 le sont TOUS par des chemins identiques (les paires
  companion #15610 / #15085) -- c'est-a-dire par le cas que
  `check_pr_path_collisions.py` voit deja. **Aucune instance vivante** du cas
  « meme slot, noms differents » : la source est un signal PREVENTIF, pas un
  incendie. La justification mesuree de cette tranche est le trou n.1
  (deux cibles du meme slot dans une revision), pas celui-ci.
- Neutrallite verifiee contre les trois PRs ouvertes qui renumerotent le plus :
  `fix/11840-...` (10 cibles), `renum/15612-...` (17), `fix/14944-...` (8) ->
  **exit 0, zero conflit** sur les trois. La lecture des suppressions est ce qui
  produit ce resultat : sans elle, chacune de ces 35 cibles aurait rougi sur le
  slot qu'elle venait de liberer.

Ce que le smoke test a corrige
------------------------------
Une cible qui porte le nom EXACT d'un fichier deja ecrit par une PR ouverte
etait exemptee comme « rendu alternatif du meme item » (`same_item` compare le
nom delangue, et un chemin identique est evidemment egal a lui-meme). Mesure :
`--target MyIA.AI.Notebooks/GenAI/Texte/01_OpenAI_Intro.ipynb` rendait
`taken_on_base` en passant sous silence #15610 et #15085, qui ecrivent
precisement ce fichier. L'exemption de sibling ne vaut desormais que si le NOM
DIFFERE : un chemin identique est la reservation la plus forte qui soit, jamais
un soi-meme. Le pendant est teste symetriquement (une cible que MA propre
revision porte reste a moi).

Sortie : 0 = tous les slots examines sont libres (ou exempts) ; 1 = au moins un
conflit ; 2 = erreur d'invocation, ou controle de self-test non satisfait (le
detecteur est casse -- distinct d'une collision reelle, qui sort 1).
Le denombrement des cibles et de chaque source est TOUJOURS imprime : « rien
trouve » et « rien regarde » ne doivent jamais partager la meme sortie.

Usage
-----
    # Revision : ce que la branche courante prend comme slots
    python scripts/notebook_tools/check_slot_reservation.py --base origin/main

    # Preflight AVANT edition : ce slot est-il libre ?
    python scripts/notebook_tools/check_slot_reservation.py --target \
        MyIA.AI.Notebooks/GenAI/Audio/04-2-Transcription.ipynb

    # Sans reseau (CI, voie rapide) : sources arbre + revision + declarees
    python scripts/notebook_tools/check_slot_reservation.py --offline

    python scripts/notebook_tools/check_slot_reservation.py --self-test
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

# Grammaire de nom partagee (#5081) : `index_key` normalise le zero-pad et les
# separateurs de niveau (04-2 et 4.2 sont le meme slot) et `strip_lang` apparie
# les rendus alternatifs d'un meme item (-Csharp, _en, -Lean). Redefinir un
# motif ici rouvrirait le defaut 2 de #15489 : deux lectures du meme nom.
_here = str(Path(__file__).resolve().parent)
if _here not in sys.path:
    sys.path.insert(0, _here)
from naming_canon import index_key, strip_lang  # noqa: E402

DEFAULT_RESERVATIONS = Path(__file__).resolve().parent / "slot_reservations.json"

SOURCE_BASE = "base"
SOURCE_REVISION = "revision"
SOURCE_OPEN_PRS = "open_prs"
SOURCE_DECLARED = "declared"

# Precedence du verdict quand plusieurs sources se disputent le meme slot. Du
# plus local au plus lointain : ce que la revision fait a elle-meme d'abord
# (l'agent peut le corriger immediatement), puis ce qui est en vol cette minute,
# puis l'etat statique de la base, puis une declaration publiee -- la plus
# lente a corriger, et celle qui doit le plus rarement gagner.
VERDICT_PRECEDENCE = (
    "duplicate_within_revision",
    "reserved_by_open_pr",
    "taken_on_base",
    "declared_reserved",
)


def _git(args):
    env = dict(os.environ, MSYS_NO_PATHCONV="1")
    r = subprocess.run(["git"] + args, capture_output=True, text=True,
                       encoding="utf-8", errors="replace", env=env)
    if r.returncode != 0:
        raise RuntimeError("git %s -> %s" % (" ".join(args), (r.stderr or "").strip()[:200]))
    return r.stdout


def _ipynb(lines):
    return [l.strip() for l in lines if l.strip().lower().endswith(".ipynb")]


def added_notebooks(base, head):
    """Cibles de la revision : ajouts ET renames, vus comme des prises de slot."""
    return _ipynb(_git(["diff", "--no-renames", "--diff-filter=A", "--name-only",
                        "%s...%s" % (base, head)]).splitlines())


def removed_notebooks(base, head):
    """Slots que la revision LIBERE -- invisibles dans le garde d'index (cf docstring)."""
    return _ipynb(_git(["diff", "--no-renames", "--diff-filter=D", "--name-only",
                        "%s...%s" % (base, head)]).splitlines())


def notebooks_at(ref):
    return _ipynb(_git(["ls-tree", "-r", "--name-only", ref]).splitlines())


def split_dir(path):
    """(repertoire, basename) en separateur POSIX -- les chemins git ne connaissent que '/'."""
    if "/" in path:
        d, b = path.rsplit("/", 1)
        return d, b
    return "", path


def slot_of(path):
    """Slot d'un chemin : (repertoire, index normalise), ou None s'il ne porte pas d'index."""
    d, b = split_dir(path)
    key = index_key(b)
    if key is None:
        return None
    return (d, key)


def same_item(a, b):
    """Deux rendus du meme item (suffixe de langue seul different) : pas concurrents."""
    return strip_lang(split_dir(a)[1]).lower() == strip_lang(split_dir(b)[1]).lower()


@dataclass(frozen=True)
class Occupant:
    """Un chemin qui tient un slot, et d'ou il vient."""
    path: str
    source: str
    detail: str = ""


def group_by_slot(paths, source, detail=""):
    """{slot: [Occupant, ...]} -- les chemins sans index sont ecartes (rien a reserver)."""
    out: dict[tuple[str, str], list[Occupant]] = {}
    for p in paths:
        slot = slot_of(p)
        if slot is None:
            continue
        out.setdefault(slot, []).append(Occupant(p, source, detail))
    return out


def pr_claims(prs):
    """Slots tenus par les PRs ouvertes.

    `prs` = la charge rendue par ``gh pr list --json number,files``. Un chemin a
    ``additions == 0`` est une suppression pure : la PR LIBERE ce slot, elle ne
    le reserve pas (cf docstring).
    """
    claims: dict[tuple[str, str], list[Occupant]] = {}
    for pr in prs or []:
        num = pr.get("number")
        for f in pr.get("files") or []:
            path = f.get("path") or ""
            if not path.lower().endswith(".ipynb"):
                continue
            if not (f.get("additions") or 0) > 0:
                continue
            slot = slot_of(path)
            if slot is None:
                continue
            claims.setdefault(slot, []).append(Occupant(path, SOURCE_OPEN_PRS, "#%s" % num))
    return claims


def declared_claims(doc):
    """Slots declares reserves par une table publiee (`slot_reservations.json`)."""
    claims: dict[tuple[str, str], list[Occupant]] = {}
    for entry in (doc or {}).get("reserved") or []:
        d = (entry.get("dir") or "").strip("/")
        key = str(entry.get("index") or "").strip()
        if not key:
            continue
        holder = (entry.get("holder") or "").strip() or "sans detenteur nomme"
        note = (entry.get("note") or "").strip()
        detail = "%s%s" % (holder, (" -- %s" % note) if note else "")
        claims.setdefault((d, key.lower()), []).append(
            Occupant("%s/%s" % (d, entry.get("index")), SOURCE_DECLARED, detail))
    return claims


def merge(*maps):
    out: dict[tuple[str, str], list[Occupant]] = {}
    for m in maps:
        for slot, occs in m.items():
            out.setdefault(slot, []).extend(occs)
    return out


def verdict_for(target, occupants, releases):
    """Verdict d'une cible contre l'ensemble des occupants de son slot."""
    slot = slot_of(target)
    if slot is None:
        return {"target": target, "slot": None, "state": "no_slot",
                "verdict": "ok", "conflicts": []}

    conflicts = []
    exempt = False
    t_base = split_dir(target)[1].lower()
    for occ in occupants.get(slot, []):
        # La cible se reconnait elle-meme UNIQUEMENT parmi les cibles de la
        # revision : en mode revision les deux ensembles sont le meme, et se
        # compter comme occupant de soi-meme ferait rougir chaque ligne. Un
        # occupant de la BASE ou d'une PR OUVERTE qui porte exactement le meme
        # chemin est au contraire la reservation la plus forte qui soit -- il ne
        # doit jamais etre ecarte comme un « soi-meme ».
        if occ.source == SOURCE_REVISION and occ.path == target:
            continue
        if occ.path in releases:
            continue                      # libere par la revision examinee
        # Rendu alternatif du meme item (`-Csharp`, `_en`) : legitime, mais
        # SEULEMENT si le nom de fichier differe. Un chemin identique n'est pas
        # un sibling, c'est le meme fichier -- etre passe sous silence ici etait
        # le defaut revele par la mesure sur le pool vivant (target
        # `01_OpenAI_Intro.ipynb` : la PR qui l'ecrit etait exemptee).
        if same_item(occ.path, target) and split_dir(occ.path)[1].lower() != t_base:
            exempt = True
            continue
        state = {
            SOURCE_REVISION: "duplicate_within_revision",
            SOURCE_OPEN_PRS: "reserved_by_open_pr",
            SOURCE_BASE: "taken_on_base",
            SOURCE_DECLARED: "declared_reserved",
        }[occ.source]
        conflicts.append({"state": state, "source": occ.source,
                          "path": occ.path, "detail": occ.detail})

    if not conflicts:
        # Un slot tenu par un sibling n'est pas « libre » : la distinction est
        # imprimee, jamais confondue -- c'est la meme discipline que les etats
        # distincts du garde de suffixes.
        return {"target": target, "slot": "%s%s" % (slot[0] + "/" if slot[0] else "", slot[1]),
                "state": "exempt_sibling" if exempt else "free",
                "verdict": "ok", "conflicts": []}

    conflicts.sort(key=lambda c: VERDICT_PRECEDENCE.index(c["state"]))
    return {"target": target, "slot": "%s%s" % (slot[0] + "/" if slot[0] else "", slot[1]),
            "state": conflicts[0]["state"], "verdict": "conflict",
            "conflicts": conflicts}


def examine(targets, occupants, releases):
    return [verdict_for(t, occupants, releases) for t in targets]


# ---------------------------------------------------------------- sources

def load_open_pr_claims(limit, repo, exclude_pr, offline, status):
    """Source PR ouvertes. Toute indisponibilite est ECRITE dans `status`."""
    if offline:
        status[SOURCE_OPEN_PRS] = {"status": "unavailable", "reason": "--offline"}
        return {}
    args = ["pr", "list", "--state", "open", "--limit", str(limit),
            "--json", "number,files"]
    if repo:
        args += ["--repo", repo]
    try:
        r = subprocess.run(["gh"] + args, capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
    except FileNotFoundError:
        status[SOURCE_OPEN_PRS] = {"status": "unavailable", "reason": "gh introuvable"}
        return {}
    if r.returncode != 0:
        status[SOURCE_OPEN_PRS] = {"status": "unavailable",
                                   "reason": (r.stderr or "").strip()[:160] or "gh rc=%d" % r.returncode}
        return {}
    try:
        prs = json.loads(r.stdout or "[]")
    except json.JSONDecodeError:
        status[SOURCE_OPEN_PRS] = {"status": "unavailable", "reason": "reponse gh illisible"}
        return {}
    if exclude_pr:
        prs = [p for p in prs if p.get("number") != exclude_pr]
    status[SOURCE_OPEN_PRS] = {"status": "ok", "prs": len(prs)}
    return pr_claims(prs)


def load_declared(path, status):
    if path is None or not Path(path).exists():
        status[SOURCE_DECLARED] = {"status": "absent", "path": str(path) if path else ""}
        return {}
    try:
        doc = json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        status[SOURCE_DECLARED] = {"status": "unavailable", "reason": str(e)[:160]}
        return {}
    claims = declared_claims(doc)
    status[SOURCE_DECLARED] = {"status": "ok", "reserved": sum(len(v) for v in claims.values())}
    return claims


# ---------------------------------------------------------------- self-test

def _occ(path, source, detail=""):
    return Occupant(path, source, detail)


_SLOT_CASES = [
    ("04-2-Alpha.ipynb", ("", "4.2")),
    ("MyIA.AI.Notebooks/X/04-2-Alpha.ipynb", ("MyIA.AI.Notebooks/X", "4.2")),
    ("4.2-Alpha.ipynb", ("", "4.2")),          # zero-pad et separateur resorbes
    ("MGS-26-Equilibrium.ipynb", None),        # prefixe alphabetique : aucun slot
    ("README-notes.ipynb", None),
]


def _scenario(targets, occupants, releases, want):
    got = [v["state"] for v in examine(targets, occupants, releases)]
    return got == list(want), got


def self_test():
    ko = 0
    print("--- lecture de slot (%d cas) ---" % len(_SLOT_CASES))
    for name, want in _SLOT_CASES:
        got = slot_of(name)
        ok = got == want
        ko += 0 if ok else 1
        print("  %-4s %-46s -> %-28s (attendu %s)"
              % ("OK" if ok else "KO", name, got, want))

    A = "MyIA.AI.Notebooks/X/04-2-Alpha.ipynb"
    B = "MyIA.AI.Notebooks/X/04-2-Beta.ipynb"
    C = "MyIA.AI.Notebooks/X/04-2-Existing.ipynb"
    OD = "MyIA.AI.Notebooks/Other/04-2-Alpha.ipynb"

    scenarios = [
        # --- controles POSITIFS : le signal doit sortir ---
        ("VRAI POSITIF  deux cibles du meme slot dans une revision",
         [A, B], merge(group_by_slot([A, B], SOURCE_REVISION)), set(),
         ["duplicate_within_revision", "duplicate_within_revision"]),
        ("VRAI POSITIF  slot tenu par la base",
         [A], merge(group_by_slot([C], SOURCE_BASE)), set(), ["taken_on_base"]),
        ("VRAI POSITIF  slot reserve par une PR ouverte",
         [A], merge(group_by_slot([], SOURCE_BASE),
                    {("MyIA.AI.Notebooks/X", "4.2"): [_occ(C, SOURCE_OPEN_PRS, "#15600")]}),
         set(), ["reserved_by_open_pr"]),
        ("VRAI POSITIF  slot declare reserve (table publiee)",
         [A], merge({("MyIA.AI.Notebooks/X", "4.2"): [_occ("X/04-2", SOURCE_DECLARED, "lane X")]}),
         set(), ["declared_reserved"]),
        ("VRAI POSITIF  zero-pad divergent = meme slot",
         ["MyIA.AI.Notebooks/X/4.2-Alpha.ipynb"],
         merge(group_by_slot([C], SOURCE_BASE)), set(), ["taken_on_base"]),
        ("VRAI POSITIF  chemin IDENTIQUE tenu par la base",
         [A], merge(group_by_slot([A], SOURCE_BASE)), set(), ["taken_on_base"]),
        ("VRAI POSITIF  chemin IDENTIQUE ecrit par une PR ouverte",
         [A], pr_claims([{"number": 3, "files": [
             {"path": A, "additions": 4, "deletions": 0}]}]), set(), ["reserved_by_open_pr"]),
        # --- controles NEGATIFS : le bruit doit rester dehors ---
        ("NEGATIF       cible deja ajoutee par MA revision (soi-meme)",
         [A], merge(group_by_slot([A], SOURCE_REVISION)), set(), ["free"]),
        ("FAUX POSITIF  sibling de langue -Csharp",
         ["MyIA.AI.Notebooks/X/04-2-Alpha-Csharp.ipynb"],
         merge(group_by_slot([A], SOURCE_BASE)), set(), ["exempt_sibling"]),
        ("FAUX POSITIF  sibling i18n _en",
         ["MyIA.AI.Notebooks/X/04-2-Alpha_en.ipynb"],
         merge(group_by_slot([A], SOURCE_BASE)), set(), ["exempt_sibling"]),
        ("FAUX POSITIF  slot libere par la revision elle-meme (retitle)",
         ["MyIA.AI.Notebooks/X/04-2-New-Title.ipynb"],
         merge(group_by_slot(["MyIA.AI.Notebooks/X/04-2-Old-Title.ipynb"], SOURCE_BASE)),
         {"MyIA.AI.Notebooks/X/04-2-Old-Title.ipynb"}, ["free"]),
        ("FAUX POSITIF  meme index, repertoire different",
         [A], merge(group_by_slot([OD], SOURCE_BASE)), set(), ["free"]),
        ("FAUX POSITIF  lettre d'accretion differente 2.8b vs 2.8c",
         ["m/02-ML/2.8c-Borne.ipynb"],
         merge(group_by_slot(["m/02-ML/2.8b-Theorie.ipynb"], SOURCE_BASE)), set(), ["free"]),
        ("FAUX POSITIF  cible sans index (prefixe alphabetique)",
         ["s/MGS-27-Forensic.ipynb"],
         merge(group_by_slot(["s/MGS-26-Equilibrium.ipynb"], SOURCE_BASE)), set(), ["no_slot"]),
        ("NEGATIF       slot reellement libre",
         [A], merge(group_by_slot(["MyIA.AI.Notebooks/X/04-1-Previous.ipynb"], SOURCE_BASE)),
         set(), ["free"]),
        # --- la source PR ouvertes ne reserve pas ce qu'une PR supprime ---
        # `gh pr list --json files` ne rend pas `changeType` : c'est
        # `additions == 0` qui distingue une suppression pure d'une ecriture.
        ("FAUX POSITIF  PR qui SUPPRIME un notebook ne reserve pas son slot",
         [A], pr_claims([{"number": 1, "files": [
             {"path": C, "additions": 0, "deletions": 12}]}]), set(), ["free"]),
        ("VRAI POSITIF  PR qui ECRIT un notebook reserve son slot",
         [A], pr_claims([{"number": 2, "files": [
             {"path": C, "additions": 8, "deletions": 2}]}]), set(), ["reserved_by_open_pr"]),
    ]

    print("")
    print("--- verdicts (controles positifs ET negatifs) ---")
    for label, targets, occupants, releases, want in scenarios:
        ok, got = _scenario(targets, occupants, releases, want)
        ko += 0 if ok else 1
        print("  %-4s %-62s -> %s (attendu %s)"
              % ("OK" if ok else "KO", label, got, list(want)))

    total = len(_SLOT_CASES) + len(scenarios)
    print("")
    print("%s : %d cas, %d echec(s)" % ("ECHEC" if ko else "SUCCES", total, ko))
    return 2 if ko else 0


# ---------------------------------------------------------------- main

def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Preflight de reservation de slot de notebook (#15489).")
    ap.add_argument("--base", default="origin/main", help="revision de base (defaut: origin/main)")
    ap.add_argument("--head", default="HEAD", help="revision examinee (defaut: HEAD)")
    ap.add_argument("--target", action="append", default=None,
                    help="cible a verifier AVANT edition (repetable) ; par defaut, "
                         "les cibles de la revision sont examinees")
    ap.add_argument("--reservations", default=str(DEFAULT_RESERVATIONS),
                    help="table de reservation publiee (defaut: slot_reservations.json)")
    ap.add_argument("--no-reservations", action="store_true",
                    help="ignorer la table publiee (source declaree vide)")
    ap.add_argument("--offline", action="store_true",
                    help="ne pas interroger les PRs ouvertes (sources arbre + revision + declarees)")
    ap.add_argument("--exclude-pr", type=int, default=None,
                    help="numero de PR a exclure de la source PR ouvertes (la sienne)")
    ap.add_argument("--limit", type=int, default=500,
                    help="plafond de PRs lues (defaut 500 ; le defaut de gh est 30)")
    ap.add_argument("--repo", default=None, help="override du depot pour gh")
    ap.add_argument("--json", action="store_true", help="sortie machine")
    ap.add_argument("--self-test", action="store_true", help="controles positifs et negatifs")
    a = ap.parse_args(argv)

    if a.self_test:
        return self_test()

    mode = "target" if a.target else "revision"
    status: dict[str, dict] = {}
    try:
        rev_added = added_notebooks(a.base, a.head)
        targets = list(a.target) if a.target else rev_added
        releases = set(removed_notebooks(a.base, a.head))
        base_files = notebooks_at(a.base)
    except RuntimeError as e:
        print("ERREUR git : %s" % e, file=sys.stderr)
        return 2

    # La source `revision` couvre les DEUX modes, et c'est elle qui ferme le trou
    # n.1 : en mode revision les cibles SONT les ajouts, donc deux ajouts du meme
    # slot se voient l'un l'autre (la cible se reconnait elle-meme et s'ecarte,
    # occ.path == target). En mode cible, elle repond a « ma branche prend-elle
    # deja ce slot sous un autre nom ? ».
    rev_occ = group_by_slot(rev_added, SOURCE_REVISION)
    status[SOURCE_REVISION] = {
        "status": "ok",
        "added": len(rev_added),
        "examined": len(targets),
        "released": len(releases),
    }
    status[SOURCE_BASE] = {"status": "ok", "notebooks": len(base_files),
                           "ref": a.base}

    occ = merge(group_by_slot(base_files, SOURCE_BASE), rev_occ,
                load_open_pr_claims(a.limit, a.repo, a.exclude_pr, a.offline, status),
                load_declared(None if a.no_reservations else a.reservations, status))

    verdicts = examine(targets, occ, releases)
    conflicts = [v for v in verdicts if v["verdict"] == "conflict"]

    if a.json:
        print(json.dumps({
            "base": a.base, "head": a.head, "mode": mode,
            "sources": status,
            "targets_examined": len(targets),
            "states": {s: sum(1 for v in verdicts if v["state"] == s)
                       for s in sorted({v["state"] for v in verdicts})},
            "verdicts": verdicts,
            "conflicts": len(conflicts),
        }, indent=2, ensure_ascii=False))
        return 1 if conflicts else 0

    # Le denombrement de CHAQUE source est imprime, y compris quand il vaut
    # zero : une source muette et une source absente ne sont pas la meme chose.
    print("sources interrogees :")
    print("  base      : %d notebooks (%s)" % (len(base_files), a.base))
    print("  revision  : %d cible(s) examinee(s), %d liberee(s)"
          % (len(targets), len(releases)))
    pr_status = status.get(SOURCE_OPEN_PRS, {})
    if pr_status.get("status") == "ok":
        print("  open_prs  : %d PR(s) ouverte(s)" % pr_status.get("prs", 0))
    else:
        print("  open_prs  : INDISPONIBLE (%s)" % pr_status.get("reason", "?"))
    dec_status = status.get(SOURCE_DECLARED, {})
    if dec_status.get("status") == "ok":
        print("  declared  : %d reservation(s) publiee(s)" % dec_status.get("reserved", 0))
    else:
        print("  declared  : %s" % dec_status.get("status", "?"))

    if not targets:
        print("")
        print("VERDICT: OK -- aucune cible a verifier (rien a examiner n'est pas "
              "la meme chose que rien a trouver).")
        return 0

    print("")
    # Le jeton d'etat est imprime A COTE de la phrase francaise : une sortie
    # lisible par un humain et une sortie verifiable par un test ne doivent pas
    # diverger (`free` / `libre` designent le meme fait, ecrit une seule fois).
    for v in verdicts:
        mark = {"free": "libre (free)",
                "exempt_sibling": "exempt (exempt_sibling -- rendu alternatif du meme item)",
                "no_slot": "sans slot (no_slot -- aucun index)"}.get(
                    v["state"], v["state"].upper())
        print("  %-58s slot=%-10s %s" % (v["target"], v["slot"] or "-", mark))
        for c in v["conflicts"]:
            print("      <- %s : %s %s" % (c["state"], c["path"], c["detail"]))

    if not conflicts:
        print("")
        print("VERDICT: OK -- aucun slot en conflit.")
        return 0

    print("")
    print("VERDICT: CONFLIT DE SLOT (%d cible(s))" % len(conflicts))
    print("")
    print("Un slot designe une position dans une serie, et deux notebooks ne peuvent pas")
    print("l'occuper. Choisir un index libre, OU -- si les deux traitent le meme sujet --")
    print("les reconcilier en un seul avant d'ouvrir la PR. Un slot tenu par une PR ouverte")
    print("n'est pas forcement perdu : lire cette PR avant de conclure, l'arbitrage reste au")
    print("coordinateur (cet organe ne reserve rien et ne bloque personne).")
    return 1


if __name__ == "__main__":
    sys.exit(main())
