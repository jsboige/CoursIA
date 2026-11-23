#!/usr/bin/env python3
"""Detecte la derive des jumeaux Python/C# depuis le registre de parite (#8057).

Pourquoi cet outil existe
-------------------------
La campagne de **jumeaux Python/C#** est devenue structurante (Search/CSP,
ML.NET + pendants Python, SemanticWeb, Planners, Z3/SMT : des dizaines de
paires). Une **parite de surface** peut masquer une derive silencieuse : un
notebook evolue (fix, enrichissement, re-exec) tandis que son jumeau reste a
l'etat anterieur, et les deux implimentations derivent separement sans que
personne ne re-audite la parite. Aujourd'hui la parite est **declarative**
(des notes eparses dans des READMEs) ; ce outil la rend **auditable**.

Le registre vit dans le repertoire `twin_pairs.d/` (a cote de ce script,
#8542 Option C) : **un fichier YAML par paire** + `_schema.yaml` (documentation).
Chaque entree decrit une paire : le chemin des deux notebooks, le `parity_level`
(surface | semantic | native-both), l'**enregistrement d'audit** (date, auteur,
et le **git blob SHA** de chaque notebook au moment de l'audit) et les
`known_differences` documentees. Le file-per-entry supprime a la source la
classe de conflit serie qui frappait l'ancien mono-fichier (recurrences
#8415/#8476/#8499/#8505/#8526/#8499).

L'enregistrement d'audit existe en deux formes (#9399 volet a) : le singleton
legacy `last_audit:` ou la liste **append-only** `audits:`. Le singleton etait
un aimant a collision (deux audits concurrents de la meme paire ecrivaient les
memes lignes -> CONFLICT ou ecrasement silencieux du plus recent, #9171/#9237/
#9245) ; la forme append-only fait que chaque audit ajoute une entree distincte
-> rien n'ecrase plus rien. La migration legacy -> audits: est paresseuse (a la
volee, sur le 1er drift reel) pour eviter qu'une reecriture massive des ~158
fichiers ne soit elle-meme un aimant a collision. Le reader `_latest_audit`
lit le dernier enregistrement quelle que soit la forme.

Comment ca marche
-----------------
Pour chaque paire du registre, on :
  1. lit le **git blob SHA courant** de chaque notebook via `git ls-tree HEAD`
     (le contenu versionne, pas le working tree — reproductible) ;
  2. compare le SHA courant au `{python,csharp}_sha` du **dernier
     enregistrement d'audit** (`last_audit` legacy ou `audits[-1]`, #9399) ;
  3. **DRIFT** si l'un des deux a change depuis le dernier audit -> la paire
     doit etre re-auditee (un cote a evolue, la parite n'est plus garantie) ;
  4. **NUMBERING-DRIFT** si les numeros de base des deux jumeaux declares
     divergent (renommage unilateral d'un seul cote, classe #5361 -- EPIC
     #12933 « parite des identifiants, liberte des contenus ») -> realigner
     les numeros OU documenter `numbering_exception: <raison>` au cas par cas ;
  5. **MISSING** si le chemin n'existe pas dans git (typo, deplacement, jumeau
     non cree) ;
  6. **OK** sinon (les deux cotes sont au SHA audite, parite tenue).

Le bouclage d'audit : apres avoir re-audite une paire firsthand, on rebaseline
avec `--update --pair "<nom>" --by "<lane>"`, qui reecrit les SHAs courants
comme nouvelle reference.

L'angle mort du registre (`--coverage`)
---------------------------------------
Tout ce qui precede ne voit que les paires **deja declarees**. Une paire jamais
enregistree ne derive jamais, n'echoue jamais, n'apparait jamais : `--check`
peut afficher `OK=136 DRIFT=0` pendant que des paires reelles ne sont
surveillees par personne. `--coverage` mesure cet angle mort en partant du
disque (`git ls-files`) plutot que du registre : pour chaque notebook C#
versionne non declare, il cherche un jumeau Python et distingue

  UNREGISTERED  jumeau present, paire absente du registre -> lacune reelle
  CSHARP-ONLY   aucun jumeau -> notebook C#-only legitime, informatif

Le predicat est objectif (« un jumeau existe-t-il dans git ? »), sans liste
d'exceptions a maintenir. `--coverage` ne modifie rien : il **designe** les
tranches a enregistrer. L'enregistrement lui-meme reste un audit de parite
firsthand, une tranche a la fois (#8057) -- jamais une inscription en masse,
qui fabriquerait un `last_audit` que personne n'a fait.

`--update` EXIGE un selecteur (`--pair`, `--family`, ou l'opt-in
`--yes-all-pairs`) : sans lui, il reecrirait le `last_audit` des 116 paires et
masquerait des DRIFTs legitimes (#8508, lecons L963/L974). `--by` horodate
l'audit a ton nom -- la date est toujours remise a aujourd'hui.

L'ecriture est CHIRURGICALE : seules les lignes `last_audit` des paires ciblees
changent (cf `surgical_rebaseline`). Le diff d'un rebaseline vaut donc les
lignes reellement modifiees, commentaires et formatage du registre intacts.

Cet outil lit seulement par defaut (git ls-tree). Le mode `--update` ecrit le
registre (curated YAML, pas un notebook -> pas de souci de re-exec C.2).

Usage
-----
    # verifier toutes les paires vs le registre
    python check_twin_parity.py
    # exit 1 si drift/missing (CI-ready, mode historique fleet-wide)
    python check_twin_parity.py --check
    # restreindre a une famille
    python check_twin_parity.py --family SMT/Z3-API
    # une seule paire (ne parcourt que celle-ci ; nom inconnu = rc 2, #20197)
    python check_twin_parity.py --check --pair "SW-9 JSON-LD"
    # rebaseline apres audit firsthand (ecrit les SHAs courants).
    # --pair + --by obligatoires en pratique : le selecteur evite de rebaseliner
    # les 116 paires, --by evite d'heriter de l'auteur de l'audit precedent.
    python check_twin_parity.py --update --pair "Probas-4 Bayesian-Networks" \
        --by "myia-po-2024:CoursIA-2"
    # ORDRE (#8957) : --update ecrit le git blob SHA courant du notebook ; toute
    # mutation POSTERIEURE (strip_probe_banner.py --apply, strip_machine_paths.py,
    # scrub_papermill_paths.py) deplace ce blob et invalide l'attestation. Donc
    # --update va EN DERNIER, apres toute normalisation outillee. Inverser
    # l'ordre (attester PUIS stripper) laisse le gate --per-pair sortir DRIFT-INTRO
    # sur une parite pourtant vraie.
    # sortie machine
    python check_twin_parity.py --json
    # recenser les paires reelles absentes du registre (angle mort)
    python check_twin_parity.py --coverage
    # ... et en faire un gate, une fois les lacunes resorbees
    python check_twin_parity.py --coverage --check
    # mode per-pair : ne FAIL que sur le drift INTRODUIT par la PR en cours
    # (paire OK au base-ref mais DRIFT au HEAD). Necessite --base <ref>.
    # Compare le registre+blobs au base-ref (avant la PR) vs au HEAD (apres la PR).
    # Le drift pre-existant (deja present au base-ref) n'est PAS comptabilise ici
    # -- il releve d'une PR de rebaseline dediee (cf #8264 batch precedent).
    # Verdict STALE_BRANCH (#22920) : paire DEPLACEE sur la branche base apres le
    # fork (registre de la tete declare encore l'ancien chemin). Le rebaseline
    # --update y serait FAUX (il attesterait un chemin que main a abandonne) --
    # le remede est `gh pr update-branch`. Compteur dedie `stale_branch`, jamais
    # compte dans `drift_introduced`.
    python check_twin_parity.py --check --per-pair --base origin/main
    python check_twin_parity.py --check --per-pair --base HEAD~1
    # en CI sur une PR, `auto` est la base juste : actions/checkout extrait le
    # merge ref de GitHub, dont le premier parent est le main de l'evenement.
    # Comparer a `origin/main` (refetch au demarrage du job) classe en
    # DRIFT_INTRODUCED les paires rebaselinees sur main pendant l'attente en
    # file (#22292).
    python check_twin_parity.py --check --per-pair --base auto
    # mode CI cron (volet b #9399) : fleet-wide SANS base ref, breakdown 4 categories.
    # Distinct du check historique : rouge sur N'IMPORTE QUEL drift (legacy ou content),
    # pas seulement DRIFT_or_MISSING. Utilise par .github/workflows/twin-parity-cron.yml.
    python check_twin_parity.py --ci-strict --check --json
    python check_twin_parity.py --ci-strict --check          # sortie human-readable

Exit codes
----------
    0 -- toutes les paires OK (ou mode non --check), ou zero nouveau drift en --per-pair
         OU zero drift toutes categories (mode --ci-strict --check)
    1 -- un ou plusieurs DRIFT / MISSING (mode --check fleet-wide)
         OU nouveau(s) DRIFT introduit(s) par la PR (mode --check --per-pair)
         OU paire(s) STALE_BRANCH : deplacee(s) sur la branche base apres le
         fork (#22920) -- le remede est `gh pr update-branch`, pas un rebaseline
         OU un ou plusieurs drift legacy/content/missing en --ci-strict --check
    2 -- erreur (registre illisible, pas un depot git, paire ou famille inconnue
         pour --check / --verify-recorded-sha)
    3 -- mesure interrompue : un appel git a depasse sa borne (`_GIT_TIMEOUT_S`,
         ou `_GIT_HISTORY_TIMEOUT_S` pour le parcours d'historique) (#20197).
         Aucun verdict n'est rendu : ni vert, ni drift.

Voir aussi
----------
- twin_pairs.d/ (registre curated file-per-entry, a cote de ce script)
- twin_pairs.d/_schema.yaml (schema + vocabulaire parity_level + historique des tranches)
- Issue #8057 (metadonnee de parite des jumeaux Python/C#)
- Issue #8264 (batch rebaseline precedent -- pattern DRIFT pre-existant)
- Issue #4208 (parent : open-courseware fiabilise/publie)
"""
from __future__ import annotations

import datetime as _dt
import errno
import hashlib
import json
import re
import subprocess
import sys
import time
from pathlib import Path

try:
    import yaml
except ImportError:  # pragma: no cover
    yaml = None

# L'organe des revendications d'ordinal portees par les PRs ouvertes vit a cote
# de ce fichier (`twin_open_claims.py`) : on l'**importe**, on ne le
# reimplemente pas (#22299, constat du coordinateur du 2026-11-09 22:50Z).
sys.path.insert(0, str(Path(__file__).resolve().parent))
from twin_open_claims import GhError as OpenClaimsError  # noqa: E402
from twin_open_claims import collect_open_claims, repo_slug  # noqa: E402

# Tranche T7 (#26364) : la couche CLI et les corps de modes de `_main`
# vivent dans des modules freres, charges par le meme sys.path que
# twin_open_claims ci-dessus. Ils n'importent PAS cet organe (injection
# en parametre) : aucun cycle d'import, aucune double identite.
import twin_parity_attest  # noqa: E402
import twin_parity_census  # noqa: E402
import twin_parity_cli  # noqa: E402

# --- pression de fork (#16111) ----------------------------------------------
# Un `BlockingIOError` (EAGAIN, errno 11) au fork/clone n'est pas une erreur de
# git : c'est le noyau qui refuse un processus de plus, table de processus
# pleine. Sur la CI, les organes co-tenants tournent dans UN seul job
# (`Always-on guards -- N organes, 1 checkout`), donc dans une seule table : le
# premier fork d'un organe tardif tombe quand elle est deja saturee, et l'organe
# meurt avant d'avoir lu quoi que ce soit. `EAGAIN` est *temporaire* par
# definition -- echouer au premier refus transforme une contention transitoire
# en rouge de base. On retente donc un nombre borne de fois, sans jamais
# masquer une erreur d'une autre nature.
_EAGAIN_ATTEMPTS = 3
_EAGAIN_BACKOFF = (0.05, 0.15)  # avant les 2e et 3e tentatives


def _is_fork_pressure(exc: OSError) -> bool:
    """Vrai si l'OS a refuse de creer un processus (EAGAIN au fork/clone)."""
    return exc.errno in (errno.EAGAIN, errno.EWOULDBLOCK)


# --- borne de delai par appel git (#20197) -----------------------------------
# Sans borne, un appel git bloque lit comme un gel de l'organe. Au-dela de la
# borne, la mesure est interrompue et AUCUN verdict n'est rendu (ni vert, ni
# drift) : un resultat vide se lirait « rien a signaler ».
# Calibrage mesure : `ls-tree` / `show` durent de quelques ms a ~3 s (fetch
# paresseux sur clone partiel, po-2024). `rev-list --objects HEAD`
# (`_blob_ancestor_in`) parcourt tout l'historique et a depasse 60 s sous charge
# (load ~7 sur 4 coeurs, clone de 722 packs) : une borne de 60 s la prenait pour
# un blocage. 300 s laisse passer cet appel legitime et rend tout de meme un
# blocage reel visible en rc 3 au lieu d'un silence.
_GIT_TIMEOUT_S = 300
# Le parcours d'historique (`rev-list --objects HEAD`) a sa propre borne : sur
# le runner CI (clone `filter: blob:none`, fetch paresseux), ce seul appel a
# depasse 300 s, alors que l'etape `--check --verify-recorded-sha` entiere dure
# 3 min 54 a 6 min sur `main` sans borne (jobs 115585251354 et 115570972974).
# 1800 s couvre ces mesures avec une marge d'un facteur 5 et reste tres en deca
# du delai de job GitHub (6 h) : un vrai blocage sort toujours en rc 3.
_GIT_HISTORY_TIMEOUT_S = 1800


class GitTimeoutError(RuntimeError):
    """Un appel git a depasse sa borne de delai : la mesure est interrompue."""


def _run_git(args: list[str], *, cwd=None, text: bool = True,
             timeout: float | None = None) -> subprocess.CompletedProcess:
    """`subprocess.run` de git, avec repli borne sur la pression de fork.

    Seul `EAGAIN` est retente ; toute autre `OSError` remonte inchangee, pour
    qu'une panne reelle reste visible au lieu d'etre diluee en trois essais.
    Un appel qui depasse sa borne (`timeout`, `_GIT_TIMEOUT_S` par defaut) leve
    `GitTimeoutError` (jamais avale, jamais retente : un remote lent ne se
    repare pas en relancant).
    """
    borne = _GIT_TIMEOUT_S if timeout is None else timeout
    last_exc = None
    for attempt in range(_EAGAIN_ATTEMPTS):
        if attempt:
            time.sleep(_EAGAIN_BACKOFF[attempt - 1])
        options = {"encoding": "utf-8", "errors": "replace"} if text else {}
        try:
            return subprocess.run(args, cwd=cwd, capture_output=True, text=text,
                                  timeout=borne, **options)
        except subprocess.TimeoutExpired as exc:
            raise GitTimeoutError(
                f"mesure interrompue : `{' '.join(args)}` n'a pas repondu en "
                f"{borne:g} s (remote lent ou fetch paresseux bloque). "
                f"Aucun verdict n'est rendu pour ce controle."
            ) from exc
        except OSError as exc:
            if not _is_fork_pressure(exc):
                raise
            last_exc = exc
    raise last_exc

# Le registre vit desormais en un fichier par paire sous `twin_pairs.d/`
# (#8542 Option C). Un fichier = une entree = plus rien a fusionner en serie
# (la classe de conflit recurrente #8415/#8476/#8499/#8505/#8526/#8492 est
# supprimee a la source, pas seulement mitiguee). Le loader agrgege le
# repertoire ; l'ecriture chirurgicale (#8570) s'applique desormais a UN fichier
# d'une entree -- triviale, mais meme code, memes garanties (seules les lignes
# `last_audit` changent, commentaires du fichier preserves).
DEFAULT_REGISTRY = Path(__file__).resolve().parent / "twin_pairs.d"

# Verdict de bridge SOTA (#10439). Orthogonal a `parity_level` (qui decrit la
# correspondance des jumeaux) : ce champ decrit si un moteur SOTA est
# branchable/branche du cote .NET, pour qu'un verdict INTRINSIC deja rendu en
# prose cesse d'etre invisible aux detecteurs et de re-signaler la paire a
# chaque scan. Enumeration = les 5 verdicts de sota-not-workaround.md.
BRIDGE_VERDICTS = frozenset({
    "SOTA-OK",
    "RECOVERABLE-LOCAL",
    "RECOVERABLE-MACHINE",
    "RECOVERABLE-USER-HAND",
    "INTRINSIC",
})


def validate_pair_fields(pair: dict) -> list[str]:
    """Valide les champs structurels d'une paire. Retourne une liste d'erreurs
    (vide = OK). Fail-loud sur `bridge_verdict` hors enum, ou `bridge_verdict:
    INTRINSIC` sans `bridge_verdict_reason` (#10439), ou `numbering_exception`
    mal forme (#12933 -- doit etre une raison textuelle non vide).

    Les champs `bridge_verdict` et `bridge_verdict_reason` sont OPTIONNELS : la
    plupart des paires n'en portent pas (le verdict par defaut est "non-rompt",
    la paire reste actionnable). Un INTRINSIC sans reason est interdit car le
    verdict sans le raisonnement ne vaut rien (cf _schema.yaml + #10439).

    Scope : ne valide QUE bridge_verdict (#10439) et numbering_exception
    (#12933). `parity_level` n'est pas valide ici -- des fixtures de test
    utilisent des valeurs placeholders (ex. 'full') et l'enumeration reelle
    (surface/semantic/native-both) est deja enforcee par revue + _schema.yaml.
    """
    errs: list[str] = []
    name = pair.get("name", "?")
    bv = pair.get("bridge_verdict")
    if bv is not None:
        if bv not in BRIDGE_VERDICTS:
            errs.append(
                f"{name}: bridge_verdict={bv!r} hors enum {sorted(BRIDGE_VERDICTS)}"
            )
        elif bv == "INTRINSIC" and not str(pair.get("bridge_verdict_reason", "")).strip():
            errs.append(
                f"{name}: bridge_verdict=INTRINSIC requiert bridge_verdict_reason "
                f"(le verdict sans le raisonnement ne vaut rien, #10439)"
            )
    ne = pair.get("numbering_exception")
    if ne is not None and (not isinstance(ne, str) or not ne.strip()):
        # Un booleen (numbering_exception: true) ou un champ vide dirait QU'ON
        # sort de la convention sans dire POURQUOI -- exactement le defaut que
        # le pattern bridge_verdict_reason (#10439) interdit pour INTRINSIC.
        # Cote check_pair, un non-string n'est PAS non plus accepte comme
        # exception valide (isinstance str) : les deux organes sont coherents.
        errs.append(
            f"{name}: numbering_exception doit etre une raison textuelle NON VIDE "
            f"(booleen/entier/champ vide refuses) -- documenter POURQUOI la paire "
            f"sort de la convention de numerotation, ou supprimer le champ (#12933)"
        )
    return errs


def _slug(name: str) -> str:
    """Slug stable et deterministe du `name` d'une paire -> nom de fichier.

    Invariant : deux noms distincts produisent deux slugs distincts (verifie sur
    les 116 paires a la migration #8542, 0 collision). Permet de retomber sur le
    fichier d'une paire depuis son `name` sans index supplementaire.
    """
    s = str(name).lower()
    s = re.sub(r"[^a-z0-9]+", "-", s).strip("-")
    return s


def _pair_file(registry_dir: Path, name: str) -> Path:
    """Chemin du fichier d'une paire dans le registre file-per-entry."""
    return registry_dir / f"{_slug(name)}.yaml"


def _audit_dir(registry_dir: Path, slug: str) -> Path:
    """Repertoire des audits file-per-audit d'une paire (nouvelle forme #14911).

    Nouvelle forme : `twin_pairs.d/<slug>/` contient UN fichier par audit
    (`<date>-<lane>.yaml`). Retourne le chemin, meme si le repertoire n'existe
    pas encore (la migration avance a la volee).
    """
    return registry_dir / slug


# Windows MAX_PATH = 260 : le prefixe fixe (repo + twin_pairs.d/<pair-slug>/ +
# `<idx:04d>-<date>-`) consomme deja ~100 chars, et la CI windows-latest fait un
# `git checkout` sans `core.longpaths` -> un slug de lane non borne casse le
# checkout (incident 2026-09-07 : `by` narratif de 250+ chars -> fichier de 308).
_AUDIT_LANE_SLUG_MAX = 48


def _audit_lane_slug(by: str | None) -> str:
    """Slug d'une identite de lane (`myia-po-2024:CoursIA-2`) -> nom de fichier
    (safe : pas de `:` ni de `/`). Vide -> 'manual'.

    Borne a `_AUDIT_LANE_SLUG_MAX` : le champ `by` accepte une justification
    libre apres l'id de lane, mais seul le debut survit dans le nom de fichier
    (le contenu YAML garde le texte integral). Les collisions de troncature
    entre lanes differentes sont deja couvertes par le suffixe `-2`/`-3` de
    `_write_audit_file` et par l'index zero-padded unique par paire.
    """
    s = re.sub(r"[^a-z0-9A-Z]+", "-", str(by or "manual")).strip("-")
    if len(s) > _AUDIT_LANE_SLUG_MAX:
        s = s[:_AUDIT_LANE_SLUG_MAX].rstrip("-")
    return s or "manual"


def _audit_filename(date: str, by: str | None, index: int = 0) -> str:
    """Nom de fichier d'un audit : `<idx:04d>-<date ISO>-<slug de lane>.yaml`.

    Le prefixe sequentiel zero-padded N'EST PAS un luxe : il preserve l'ordre
    d'append de la liste `audits:` d'origine. Un simple `<date>-<lane>.yaml`
    trie mal les audits qui partagent la meme date ET la meme lane (#14911 :
    70 paires exposees, cf tests) -- la collision serait resolue par suffixe
    `-2` qui se trie AVANT le fichier de base (`-` < `.` en ASCII), inversant
    l'ordre et faussant `_latest_audit` (audits[-1]). Le prefixe d'index fait
    que le tri par nom == ordre d'append.
    """
    name = f"{date}-{_audit_lane_slug(by)}.yaml"
    return f"{index:04d}-{name}"


def _load_audits_from_files(registry_dir: Path, slug: str) -> list[dict]:
    """Reconstitue la liste `audits:` depuis les fichiers d'audit separes.

    Nouvelle forme (#14911) : `twin_pairs.d/<slug>/<idx>-<date>-<lane>.yaml`,
    un fichier par audit. Le tri par nom de fichier (index zero-padded en tete)
    restitue l'ordre d'append de la liste `audits:` d'origine, donc `_latest_audit`
    (audits[-1]) designe le MEME audit qu'en forme inline. Rerto-compat : si le
    repertoire n'existe pas, retourne [] (le `audits:`/`last_audit:` du fichier
    de paire est alors la source, comme avant).
    """
    d = _audit_dir(registry_dir, slug)
    if not d.is_dir():
        return []
    audits: list[dict] = []
    for f in sorted(d.glob("*.yaml")):
        data = yaml.safe_load(f.read_text(encoding="utf-8"))
        if isinstance(data, dict):
            audits.append(data)
        elif isinstance(data, list):
            audits.extend(data)
    return audits


def _twin_base_number(rel_path: str) -> str | None:
    """Numero de base d'un jumeau depuis son chemin DECLARE (EPIC #12933).

    Premier groupe de chiffres du basename. Convention du depot : deux jumeaux
    d'une meme paire partagent ce numero (App-N / SW-N / <Prefixe>-N) ; le
    suffixe lettre minuscule qui peut suivre (ex. App-10b) designe un compagnon
    legitime (3e notebook de la serie) et N'EST PAS extrait -- seule la partie
    numerique compte, un compagnon 10b cote C# face a un 10 cote Python n'est
    donc PAS une derive de numerotation.

    Retourne None si le basename n'a aucun chiffre (on ne compare pas ce qu'on
    ne peut pas numeroter). Evalue le chemin tel que DECLARE dans le registre,
    pas le disque : un renommage unilateral reste visible meme si les deux
    fichiers existent par ailleurs.
    """
    base = str(rel_path).replace("\\", "/").rsplit("/", 1)[-1]
    m = re.search(r"\d+", base)
    return m.group(0) if m else None


_CSHARP_TOKEN = re.compile(r"[-_][Cc][Ss]harp")


def python_twin_candidates(csharp_path: str, known_paths: set[str]) -> list[str]:
    """Jumeaux Python plausibles d'un notebook C#, parmi `known_paths`.

    Le depot porte TROIS conventions de nommage, et un scan qui n'en teste
    qu'une classe a tort en « C#-only » tout ce qui suit les deux autres :

        Tweety-10-MLN-CSharp.ipynb      <-> Tweety-10-MLN-Python.ipynb          (suffixe retire)
        Sudoku-07-Norvig-CSharp.ipynb    <-> Sudoku-07-Norvig-Python.ipynb (suffixe substitue)
        SW-10-RDFStar-CSharp.ipynb      <-> SW-10-RDFStar-Python.ipynb   (position mediale)

    Fonction pure : `known_paths` est l'univers des chemins connus (typiquement
    la sortie de `git ls-files`), pas un acces disque -- testable sans depot.
    Le meme repertoire est prefere ; a defaut on accepte un stem identique
    ailleurs dans l'arbre.
    """
    p = Path(csharp_path)
    stem = p.stem
    variants = [
        _CSHARP_TOKEN.sub("", stem),
        _CSHARP_TOKEN.sub("-Python", stem),
        re.sub(r"([-_])[Cc][Ss]harp([-_])", r"\1Python\2", stem),
    ]
    out: list[str] = []
    seen: set[str] = set()
    for v in variants:
        if not v or v == stem or v in seen:
            continue
        seen.add(v)
        same_dir = (p.parent / f"{v}.ipynb").as_posix()
        if same_dir in known_paths:
            out.append(same_dir)
        else:
            out.extend(sorted(q for q in known_paths if Path(q).stem == v))
    return out


def scan_coverage(repo_root: Path, pairs: list) -> dict:
    """Recense les notebooks C# versionnes NON couverts par le registre.

    Le registre ne sait detecter la derive que des paires qu'il declare deja :
    une paire jamais enregistree ne derive jamais, n'echoue jamais, n'apparait
    jamais. `--check` peut donc afficher `OK=136 DRIFT=0` alors que des paires
    reelles ne sont surveillees par personne. Ce scan rend cet angle mort
    mesurable.

    Verdicts, sur la seule base d'un predicat objectif (« un jumeau Python
    existe-t-il dans git ? ») :

      UNREGISTERED  jumeau present, paire absente du registre -> lacune reelle
      CSHARP-ONLY   aucun jumeau -> notebook C#-only legitime, informatif

    Les `*_output.ipynb` (artefacts d'execution) sont exclus des deux cotes.
    """
    r = _run_git(["git", "ls-files", "--", "*.ipynb"], cwd=repo_root)
    if r.returncode != 0:
        raise SystemExit("Erreur : `git ls-files` a echoue (depot inaccessible ?).")

    tracked = {
        line.replace("\\", "/")
        for line in r.stdout.splitlines()
        if line and not Path(line).stem.endswith("_output")
    }
    registered = {
        str(pp.get("csharp", "")).replace("\\", "/")
        for pp in pairs
        if pp.get("csharp")
    }

    unregistered, csharp_only = [], []
    for cs in sorted(p for p in tracked if _CSHARP_TOKEN.search(Path(p).name)):
        if cs in registered:
            continue
        cands = python_twin_candidates(cs, tracked)
        (unregistered if cands else csharp_only).append(
            {"csharp": cs, "python_candidates": cands}
        )

    n_cs = sum(1 for p in tracked if _CSHARP_TOKEN.search(Path(p).name))
    return {
        "csharp_tracked": n_cs,
        "registered": n_cs - len(unregistered) - len(csharp_only),
        "unregistered": unregistered,
        "csharp_only": csharp_only,
    }


def _git_blob_sha(repo_root: Path, rel_path: str, git_ref: str = "HEAD") -> str | None:
    """Git blob SHA d'un fichier versionne a `git_ref` (defaut: HEAD, None si absent).

    Accepte un ref arbitraire (HEAD, origin/main, HEAD~1, <sha>, ...) -- permet de
    lire l'etat du depot a un instant donne sans modifier le working tree.
    """
    r = _run_git(["git", "ls-tree", git_ref, "--", rel_path], cwd=str(repo_root))
    if r.returncode != 0 or not r.stdout.strip():
        return None
    # format : "<mode> <type> <blob_sha>\t<path>"
    parts = r.stdout.split()
    if len(parts) >= 3:
        return parts[2]
    return None


_REACHABLE_OBJECTS: dict[tuple[str, str], set[str]] = {}


def _blob_ancestor_in(repo_root: Path, blob_sha: str, ref: str = "HEAD") -> bool:
    """Vrai si `blob_sha` est accessible depuis `ref` (= un commit ancetre le reference).

    Discrimination cle du fix #11919 : un squash-merge peut re-hasher le git
    blob SHA d'un notebook sans toucher le contenu didactique. Le recorded
    `python_sha`/`csharp_sha` pointe alors sur un blob qui n'est PLUS ancre
    d'aucun commit accessible (orphelin par squash). Mais un cas
    distinct -- metadata-only drift (Sudoku-08/14 BDD, design-gate #9399
    critere 2) -- produit lui aussi un recorded blob SHA divergent de HEAD
    (le `_git_blob_sha` actuel change quand `nb["metadata"]` change, meme si
    `content_*_sha` est preserve). Les deux cas ont la MEME signature sur
    `rec_X != cur_X`, mais le deuxieme n'est PAS un orphelin : son blob
    reste accessible (il est reference par un commit ancetre de HEAD, juste
    pas le commit HEAD lui-meme).

    La discrimination : `git rev-list --objects <ref>` enumere tous les blobs
    reference par les commits accessibles depuis `<ref>`. Si `blob_sha` y
    figure, c'est un metadata-only drift (pas un orphelin). Sinon, c'est un
    orphelin par squash : le rebaseline doit le corriger.

    Cout : `rev-list --objects HEAD` parcourt tout l'historique (~4 s sur
    CoursIA). Le parcours ne depend que du commit resolu, et la fonction est
    appelee jusqu'a trois fois par paire : il est donc memorise par
    (depot, commit).

    Clone partiel : les workflows font leur checkout avec `filter: blob:none`.
    Sans option, `rev-list --objects` y rapatrie un par un chaque blob absent
    de l'historique (mesure du 2026-10-14 : 8 slots sur 10 bloques de 45 min a
    4 h dans ce seul appel). `--missing=print` liste ces blobs sous la forme
    `?<sha>` sans les telecharger ; l'appartenance se lit de la meme facon.
    """
    if not blob_sha or len(blob_sha) != 40:
        return False
    head = _run_git(["git", "rev-parse", "--verify", "--quiet", f"{ref}^{{commit}}"],
                    cwd=str(repo_root))
    if head.returncode != 0:
        return False
    key = (str(repo_root), head.stdout.strip())
    reachable = _REACHABLE_OBJECTS.get(key)
    if reachable is None:
        r = _run_git(["git", "rev-list", "--objects", "--missing=print", key[1]],
                     cwd=str(repo_root), timeout=_GIT_HISTORY_TIMEOUT_S)
        if r.returncode != 0:
            return False
        # Chaque ligne est "<sha>", "<sha> <chemin>" ou, pour un objet absent
        # du clone partiel, "?<sha>".
        reachable = {line.lstrip("?").split(" ", 1)[0] for line in r.stdout.splitlines()}
        _REACHABLE_OBJECTS[key] = reachable
    return blob_sha in reachable


def _content_sha(repo_root: Path, rel_path: str, git_ref: str = "HEAD") -> str | None:
    """SHA-256 canonique du notebook SANS sa metadonnee de niveau carnet (#9399 volet c).

    Hache le contenu pedagogique (cellules + leurs outputs) en excluant
    `nb["metadata"]` (cost, papermill, kernelspec, language_info) : un tampon
    `metadata.cost` seul ne porte aucune divergence pedagogique et ne doit PAS
    faire rougir le gate (les 2 faux positifs Sudoku-08/14 BDD du 2026-08-04,
    ou seul le bloc cost a bouge). Les cellules (et leur `metadata` cellulaire)
    restent hachees : un fix de prose (cellule markdown) ou une re-exec (output
    change) continuent de produire un DRIFT (vrais positifs, critere
    d'acceptation ai-01 : la correction de prose de #9413 rougit toujours).

    Canonique : `json.dumps(sort_keys=True, separators=(",",":"))` -- le SHA
    est stable d'une machine a l'autre et independant du formatage du fichier.
    """
    content = _git_show_file(repo_root, git_ref, rel_path)
    if content is None:
        return None
    try:
        nb = json.loads(content)
    except (ValueError, TypeError):
        return None
    stripped = {k: v for k, v in nb.items() if k != "metadata"}
    canonical = json.dumps(stripped, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def _git_show_file(repo_root: Path, git_ref: str, rel_path: str) -> str | None:
    """Contenu d'un fichier versionne a `git_ref` (None si absent).

    Utilise `git show <ref>:<path>` (mode stream), evite de checkout le working tree.
    Necessaire pour lire le registre YAML au base-ref sans polluer le workspace CI.
    """
    r = _run_git(["git", "show", f"{git_ref}:{rel_path}"], cwd=str(repo_root), text=False)
    if r.returncode != 0:
        return None
    return r.stdout.decode("utf-8", errors="replace")


def _load_registry_at_ref(repo_root: Path, git_ref: str, reg_path: Path,
                          names: set[str] | None = None) -> list:
    """Charge le registre a un ref git arbitraire (HEAD, origin/main, <sha>...).

    Robuste a la frontiere de migration #8542 : le base-ref peut etre l'ANCIEN
    mono-fichier `twin_pairs.yaml` (liste) tandis que le HEAD est le nouveau
    repertoire `twin_pairs.d/` (file-per-entry). On essaie le repertoire d'abord,
    puis on retombe sur le fichier legacy.

    Indispensable au mode `--per-pair --base origin/main` en CI : sur la PR de
    migration elle-meme, origin/main porte encore l'ancien format.

    `names` (#21972) : quand un selecteur `--pair`/`--family` est pose, on ne
    `git show` que les fichiers des paires visees (et leurs audits), pas les
    2374 fichiers du registre. `names=None` (mode plein, sans selecteur) ne
    filtre rien : le parcours integral reste strictement identique.
    """
    if yaml is None:
        raise SystemExit("PyYAML requis pour --per-pair.")
    try:
        reg_rel = reg_path.resolve().relative_to(repo_root).as_posix()
    except ValueError:
        reg_rel = Path(reg_path.name).as_posix()

    # (1) Le ref porte-t-il le REPERTOIRE file-per-entry ?
    r_ls = _run_git(
        ["git", "ls-tree", "-r", "--name-only", git_ref, "--", f"{reg_rel}/"],
        cwd=str(repo_root),
    )
    entries: list = []
    if r_ls.returncode == 0 and r_ls.stdout.strip():
        # Separe les fichiers de paire (profondeur 1 : `<reg_rel>/<slug>.yaml`)
        # des fichiers d'audit (profondeur 2 : `<reg_rel>/<slug>/<date>-<lane>.yaml`,
        # nouvelle forme #14911). La liste `git ls-tree -r` aplatit les deux ;
        # sans cette separation, un fichier d'audit serait lu comme une "paire".
        pair_lines: list[tuple[str, str]] = []   # (slug, ligne git)
        audit_lines: dict[str, list[str]] = {}   # slug -> [lignes git]
        prefix = f"{reg_rel}/"
        for line in r_ls.stdout.splitlines():
            sub = line[len(prefix):] if line.startswith(prefix) else line
            parts = sub.split("/")
            if len(parts) == 1:
                fname = parts[0]
                if fname.endswith(".yaml") and not fname.startswith("_"):
                    pair_lines.append((fname[:-5], line))
            elif len(parts) == 2 and parts[1].endswith(".yaml"):
                audit_lines.setdefault(parts[0], []).append(line)
        # Filtre AVANT lecture (#21972) : avec un selecteur, ne `git show` que
        # les fichiers de paire des noms demandes (+ leurs audits), pas les 2374
        # fichiers du registre. Le slug d'un fichier de paire EST `_slug(name)`
        # (un fichier = une paire, #8542), donc le filtre sur slug == sur name.
        had_pair_files = bool(pair_lines)
        if names is not None:
            wanted_slugs = {_slug(n) for n in names}
            pair_lines = [(s, l) for (s, l) in pair_lines if s in wanted_slugs]
            if had_pair_files and not pair_lines:
                # #28093 : le selecteur a vide la liste = les paires demandees
                # sont ABSENTES du base-ref (cas normal d'une PR qui ajoute une
                # paire). Base vide, pas de repli legacy : celui-ci finirait en
                # « Le registre au base-ref n'est pas une liste » apres avoir
                # `git show` le REPERTOIRE du registre (listing d'arbre, rc=0).
                print(
                    f"[twin-parity] paire(s) absente(s) du base-ref {git_ref} : "
                    f"{', '.join(sorted(wanted_slugs))} -> base vide pour la comparaison",
                    file=sys.stderr,
                )
                return []
        for slug, line in sorted(pair_lines):
            txt = _git_show_file(repo_root, git_ref, line)
            if txt is None:
                continue
            data = yaml.safe_load(txt)
            if isinstance(data, dict):
                audits = []
                for aline in sorted(audit_lines.get(slug, [])):
                    atxt = _git_show_file(repo_root, git_ref, aline)
                    if atxt is None:
                        continue
                    ad = yaml.safe_load(atxt)
                    if isinstance(ad, dict):
                        audits.append(ad)
                    elif isinstance(ad, list):
                        audits.extend(ad)
                if audits:
                    data = dict(data)
                    data["audits"] = audits
                    data.pop("last_audit", None)
                entries.append(data)
            elif isinstance(data, list):
                # Forme liste d'un dict : reconstitue AUSSI les audits
                # file-per-audit (#14911) depuis `<slug>/` (le `slug` de la
                # ligne git = le nom de fichier de paire, cf separation plus haut).
                for item in data:
                    if not isinstance(item, dict):
                        continue
                    audits = []
                    for aline in sorted(audit_lines.get(slug, [])):
                        atxt = _git_show_file(repo_root, git_ref, aline)
                        if atxt is None:
                            continue
                        ad = yaml.safe_load(atxt)
                        if isinstance(ad, dict):
                            audits.append(ad)
                        elif isinstance(ad, list):
                            audits.extend(ad)
                    if audits:
                        item = dict(item)
                        item["audits"] = audits
                        item.pop("last_audit", None)
                    entries.append(item)
        if entries:
            return entries
        # repertoire present mais vide de paires -> on continue vers le legacy

    # (2) Retombe sur l'ancien mono-fichier `twin_pairs.yaml` (a cote du script).
    legacy_rel = "scripts/notebook_tools/twin_pairs.yaml"
    reg_text_base = _git_show_file(repo_root, git_ref, legacy_rel)
    if reg_text_base is None and reg_rel.endswith(".yaml"):
        # tente aussi le chemin fourni en --registry, mais SEULEMENT si c'est un
        # chemin de FICHIER .yaml (#28093) : `git show <ref>:<repertoire>` rend
        # rc=0 avec un listing d'arbre, que yaml.safe_load ne parse pas en
        # liste -- d'ou le message trompeur « n'est pas une liste ».
        reg_text_base = _git_show_file(repo_root, git_ref, reg_rel)
    if reg_text_base is None:
        raise SystemExit(
            f"Impossible de lire le registre au base-ref '{git_ref}' "
            f"(ni repertoire {reg_rel}/ ni fichier legacy twin_pairs.yaml)."
        )
    data_base = yaml.safe_load(reg_text_base)
    if not isinstance(data_base, list):
        raise SystemExit("Le registre au base-ref n'est pas une liste.")
    return data_base


def _repo_root() -> Path:
    """Racine du depot contenant le cwd -- **sans fork**.

    `git rev-parse --show-toplevel` se reduit a une remontee de parents jusqu'a un
    `.git` : faite en pur Python, elle ne coute aucun processus. C'est exactement
    le fork qui mourait sous pression (#16111) : l'organe echouait ici, avant
    d'avoir lu une seule paire, et un organe qui ne demarre pas ne rapporte rien.
    Repli sur git si la remontee ne trouve rien (depot nu, `GIT_DIR` explicite) --
    soit les cas ou l'ancien code forkait de toute facon.
    """
    cwd = Path.cwd()
    for parent in (cwd, *cwd.parents):
        if (parent / ".git").exists():
            return parent
    r = _run_git(["git", "rev-parse", "--show-toplevel"])
    if r.returncode != 0:
        raise SystemExit("Erreur : pas un depot git (impossible de trouver la racine).")
    return Path(r.stdout.strip())


def load_registry(path: Path) -> list:
    """Charge le registre. `path` = un répertoire file-per-entry (`twin_pairs.d/`)
    ou un fichier YAML mono-liste (override `--registry`, ou ancien format).

    En mode répertoire (#8542 Option C), chaque `*.yaml` ne commençant pas par
    `_` est un fichier d'UNE paire (un dict, ou une liste d'un dict — tranches
    verbatim de l'ancien mono-fichier). Les fichiers `_`-préfixés (`_schema.yaml`)
    sont de la documentation, ignorée.
    """
    if path is None or not path.exists():
        raise SystemExit(f"Erreur : registre introuvable : {path}")
    if yaml is None:
        raise SystemExit("Erreur : PyYAML requis (pip install pyyaml).")
    if path.is_dir():
        entries: list = []
        for f in sorted(path.glob("*.yaml")):
            if f.name.startswith("_"):
                continue
            data = yaml.safe_load(f.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                # Nouvelle forme file-per-audit (#14911) : si un sous-repertoire
                # `<slug>/` porte des fichiers d'audit, reconstitue `audits:` et
                # retombe sur le `last_audit` legacy si present. Le reste du
                # script (check_pair, _latest_audit, verify, per-pair) consomme
                # ainsi `pair["audits"]` sans changement.
                audits = _load_audits_from_files(path, f.stem)
                if audits:
                    data = dict(data)
                    data["audits"] = audits
                    data.pop("last_audit", None)
                entries.append(data)
            elif isinstance(data, list):
                # Forme liste d'un dict (tranches verbatim de l'ancien
                # mono-fichier). On reconstitue AUSSI les audits file-per-audit
                # (#14911) : un fichier de paire sous forme `<slug>/<date>-<lane>.yaml`
                # porte desormais les audits, et `audits:`/`last_audit:` a ete
                # retire du fichier d'intention. Sans cette reconstitution pour la
                # forme liste, un registre migre renverrait des paires SANS audits
                # -> check_pair/_latest_audit/verify sortiraient NO_AUDIT.
                for item in data:
                    if not isinstance(item, dict):
                        continue
                    audits = _load_audits_from_files(path, f.stem)
                    if audits:
                        item = dict(item)
                        item["audits"] = audits
                        item.pop("last_audit", None)
                    entries.append(item)
            # None (fichier de commentaires) ou autre type -> ignore
        return entries
    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(data, list):
        raise SystemExit("Erreur : le registre (fichier) doit etre une liste de paires.")
    return data


def check_pair(repo_root: Path, pair: dict, git_ref: str = "HEAD") -> dict:
    """Verifie une paire. Retourne {name, python, csharp, status, details}.

    status in {OK, DRIFT, NUMBERING-DRIFT, MISSING}. details = liste de chaines
    explicatives. `git_ref` permet de checker a un instant arbitraire (HEAD,
    origin/main, <sha>...).

    `drift_sides` (#23020) = les COTES en drift a cette ref ("python" /
    "csharp"), sous forme de liste triee. Le `status` agrege ne dit pas quel
    jumeau a bouge : sans ce detail par cote, un drift AJOUTE par la PR sur
    un jumeau pouvait etre classe "pre-existant" des lors que la paire etait
    deja en drift sur l'AUTRE jumeau.
    """
    name = pair.get("name", "?")
    py = pair["python"]
    cs = pair["csharp"]
    # Cote rust OPTIONNEL (#27098 organe 1, decision coordinateur 22/11) : un
    # triplet porte la cle `rust:` ; une paire binaire ne la porte pas et son
    # comportement est BYTE-IDENTIQUE a avant (retro-compatibilite stricte des
    # ~158 paires existantes -- aucune ne declare rust: aujourd'hui, les ports
    # Rust vivent en prose known_differences en attendant la migration).
    ru = pair.get("rust")
    audit = _latest_audit(pair)
    rec_py = audit.get("python_sha")
    rec_cs = audit.get("csharp_sha")
    rec_ru = audit.get("rust_sha")

    cur_py = _git_blob_sha(repo_root, py, git_ref)
    cur_cs = _git_blob_sha(repo_root, cs, git_ref)
    cur_ru = _git_blob_sha(repo_root, ru, git_ref) if ru else None

    details = []
    status = "OK"
    # #23020 : ensemble des COTES en drift a cette ref. Le `status` agrege ne
    # dit pas QUEL jumeau a bouge -- c'est ce qui faisait classer "pre-existant"
    # un drift AJOUTE par la PR sur l'autre jumeau.
    drift_sides: set[str] = set()
    py_drift = False
    cs_drift = False
    ru_drift = False
    no_baseline = False

    if cur_py is None:
        details.append(f"Python MANQUANT dans git : {py}")
        status = "MISSING"
        drift_sides.add("python")
    if cur_cs is None:
        details.append(f"C# MANQUANT dans git : {cs}")
        status = "MISSING"
        drift_sides.add("csharp")
    if ru and cur_ru is None:
        details.append(f"Rust MANQUANT dans git : {ru}")
        status = "MISSING"
        drift_sides.add("rust")

    # Verdict NUMBERING-DRIFT (EPIC #12933) : numeros de base distincts entre
    # les jumeaux DECLARES. Evalue AVANT la comparaison de SHAs : si la
    # numerotation a diverge, la paire est cassee a un niveau plus fondamental
    # que l'empreinte de contenu -- realigner les numeros (rename) changera de
    # toute facon les chemins et rendra la comparaison SHA courante caduque.
    # MISSING garde la priorite (fichier absent = le cas le plus severe ; le
    # detail de numerotation reste alors seulement informatif, non emis).
    num_py = _twin_base_number(py)
    num_cs = _twin_base_number(cs)
    if status == "OK" and num_py is not None and num_cs is not None and num_py != num_cs:
        ne_raw = pair.get("numbering_exception")
        ne = ne_raw.strip() if isinstance(ne_raw, str) else ""
        if ne:
            details.append(
                f"Numerotation divergente documentee : python base={num_py} vs "
                f"csharp base={num_cs} -- exception : {ne}"
            )
        else:
            details.append(
                f"Numero de base divergent : python={num_py} ({py}) vs "
                f"csharp={num_cs} ({cs}) -- renommage unilateral (classe #5361) ou "
                f"declaration erronee. Realigner les numeros, OU documenter la "
                f"divergence via `numbering_exception: <raison>` dans l'entree du "
                f"registre (#12933)."
            )
            status = "NUMBERING-DRIFT"

    # Numbering du cote rust optionnel (#27098 organe 1) : meme principe
    # « parite des identifiants » que le bloc py/cs ci-dessus, aligne sur le
    # numero du jumeau PYTHON (reference du triplet). Bloc SEPARE pour ne pas
    # toucher aux messages py/cs que les tests pinnet -- le triplet partage le
    # meme numbering_exception que la paire.
    num_ru = _twin_base_number(ru) if ru else None
    if status == "OK" and ru and num_ru is not None and num_py is not None \
            and num_ru != num_py:
        ne_raw = pair.get("numbering_exception")
        ne = ne_raw.strip() if isinstance(ne_raw, str) else ""
        if ne:
            details.append(
                f"Numerotation divergente documentee : rust base={num_ru} vs "
                f"python base={num_py} -- exception : {ne}"
            )
        else:
            details.append(
                f"Numero de base divergent : rust={num_ru} ({ru}) vs "
                f"python={num_py} ({py}) -- renommage unilateral (classe #5361) "
                "ou declaration erronee. Realigner les numeros, OU documenter la "
                "divergence via `numbering_exception: <raison>` dans l'entree du "
                "registre (#12933)."
            )
            status = "NUMBERING-DRIFT"

    # content_*_sha (#9399 volet c) : metadata-immune. Calcules LAZILY -- UNIQUEMENT
    # quand l'audit les a enregistrees. Les paires legacy (aucune content_*_sha
    # enregistree) tombent sur les git blob SHA sans payer le surcout d'un git show
    # + json.loads par carnet ; ainsi la flotte actuelle (entierement legacy) garde
    # sa perf d'avant volet (c). Seules les paires --update'ees (rollout progressif)
    # declenchent le calcul metadata-immune.
    use_content = (audit.get("content_python_sha") is not None
                   and audit.get("content_csharp_sha") is not None)
    cur_cpy = _content_sha(repo_root, py, git_ref) if use_content else None
    cur_ccs = _content_sha(repo_root, cs, git_ref) if use_content else None
    # Cote rust : meme regle lazy que py/cs -- le content_rust_sha ne se
    # calcule que si l'audit l'a enregistre (#27098 organe 1).
    use_content_ru = ru and audit.get("content_rust_sha") is not None
    cur_cru = _content_sha(repo_root, ru, git_ref) if use_content_ru else None

    if status != "MISSING":
        # Verdict DRIFT : preferer les content_*_sha (metadata-immunes) quand
        # l'audit les enregistre ; sinon retomber sur les git blob SHA (legacy).
        # Un tampon metadata.cost seul -> content inchange -> PAS de DRIFT
        # (faux positif). Un fix de prose / re-exec -> content change -> DRIFT
        # (vrai positif, critere d'acceptation ai-01 #9399).
        #
        # #23020 (review du 2026-11-02, point 1) : la comparaison des SHAs est
        # evaluee AUSSI sous NUMBERING-DRIFT. Le garde `status == "OK"`
        # d'avant laissait `drift_sides` VIDE sur ce chemin : une PR qui
        # introduisait un drift de contenu sous couvert d'une divergence de
        # numerotation etait alors classee "pre-existant" (gate VERT), parce
        # que l'ensemble vide est contenu dans n'importe quel ensemble. Le
        # statut AGREGE reste NUMBERING-DRIFT (la numerotation est un niveau
        # plus fondamental que l'empreinte) -- ce qui change, c'est que les
        # COTES en drift sont desormais populatees, et le verdict per-pair
        # peut les comparer.
        rec_cpy, rec_ccs = _cmp_pair_shas(audit)
        if use_content:
            py_drift = (cur_cpy is not None and cur_cpy != rec_cpy)
            cs_drift = (cur_ccs is not None and cur_ccs != rec_ccs)
            no_baseline = (cur_cpy is None or cur_ccs is None)
            if py_drift:
                details.append(f"Python a drift (content) : {str(rec_cpy)[:8]} -> {cur_cpy[:8]}")
            if cs_drift:
                details.append(f"C# a drift (content) : {str(rec_ccs)[:8]} -> {cur_ccs[:8]}")
        else:
            py_drift = (rec_py is not None and cur_py != rec_py)
            cs_drift = (rec_cs is not None and cur_cs != rec_cs)
            no_baseline = (rec_py is None or rec_cs is None)
            if py_drift:
                details.append(f"Python a drift : {rec_py[:8]} -> {cur_py[:8]}")
            if cs_drift:
                details.append(f"C# a drift : {rec_cs[:8]} -> {cur_cs[:8]}")
        if no_baseline:
            details.append("Pas de last_audit_sha enregistre (--update requis)")
        # Cote rust optionnel (#27098 organe 1) : DRIFT sur le cote Rust, meme
        # semantique que py/cs -- content_rust_sha (metadata-immune) quand
        # l'audit l'enregistre, sinon le git blob SHA. Un cote rust DECLARE
        # sans empreinte attestee est un no_baseline rust : declarer le
        # troisieme jumeau sans l'attester dans le meme geste laisserait le
        # triplet hors discipline d'audit (cf update_pair, qui enregistre les
        # deux empreintes quand la paire porte la cle).
        if ru:
            if use_content_ru:
                ru_drift = (cur_cru is not None
                            and cur_cru != audit.get("content_rust_sha"))
            else:
                ru_drift = (rec_ru is not None and cur_ru != rec_ru)
            if ru_drift:
                drift_sides.add("rust")
                if use_content_ru:
                    details.append(
                        f"Rust a drift (content) : "
                        f"{str(audit.get('content_rust_sha'))[:8]} -> {cur_cru[:8]}")
                else:
                    details.append(f"Rust a drift : {rec_ru[:8]} -> {cur_ru[:8]}")
            if rec_ru is None and audit.get("content_rust_sha") is None:
                details.append("Pas de rust_sha enregistre (--update requis)")
                no_baseline = True
        if py_drift:
            drift_sides.add("python")
        if cs_drift:
            drift_sides.add("csharp")
        if ru_drift:
            drift_sides.add("rust")
        if status == "OK" and (py_drift or cs_drift or ru_drift or no_baseline):
            status = "DRIFT"

    return {
        "name": name,
        "family": pair.get("family", "?"),
        "python": py,
        "csharp": cs,
        "rust": ru,
        "parity_level": pair.get("parity_level", "?"),
        "bridge_verdict": pair.get("bridge_verdict"),
        "status": status,
        "drift_sides": sorted(drift_sides),
        # #23020 : la paire n'a AUCUNE reference (audit absent ou sans sha
        # enregistre). Differencie du drift : un ensemble de cotes vide n'est
        # PAS la preuve qu'aucun jumeau n'a bouge -- c'est l'absence de
        # reference, que la PR peut elle-meme introduire (voir le garde
        # `no_baseline` de `_classify_per_pair`).
        "no_baseline": no_baseline,
        "current_python_sha": cur_py,
        "current_csharp_sha": cur_cs,
        "current_rust_sha": cur_ru,
        "current_content_python_sha": cur_cpy,
        "current_content_csharp_sha": cur_ccs,
        "current_content_rust_sha": cur_cru,
        "recorded_python_sha": rec_py,
        "recorded_csharp_sha": rec_cs,
        "recorded_rust_sha": rec_ru,
        "last_audit_date": audit.get("date"),
        "last_audit_by": audit.get("by"),
        "details": details,
    }


def update_pair(
    repo_root: Path, pair: dict, by: str | None = None, date: str | None = None
) -> tuple[dict, str | None, bool]:
    """Rebaseline une paire : enregistre les SHAs courants comme nouvelle ref.

    `by` / `date` horodatent l'audit. Ils sont OBLIGATOIREMENT rafraichis :
    un rebaseline qui conserverait le `by`/`date` de l'audit precedent ferait
    affirmer a l'entree « auditee par <l'auditeur d'avant> le <la date d'avant> »
    alors que les SHAs sont ceux d'aujourd'hui -- la tracabilite mentirait, ce
    que le registre existe precisement pour empecher (cf #8570).

    Retourne (audit_dict, sha_utilise_pour_python ou None si missing, is_noop).
    Le 3e element `is_noop` est True ssi les SHAs de comparaison (content_sha si
    disponible, sinon git blob SHA, cf `_shas_match`) du nouveau audit sont
    identiques a ceux de `_latest_audit(pair)` -- c.-a-d. **rien n'a change
    pedagogiquement** depuis le dernier audit. Le caller peut alors refuser
    d'ecrire (faux audit = dater une attestation identique, design-gate #9399
    critere 2) ou laisser `--force` outrepasser.

    Pas de rebaseline silencieux sur metadata-only : un tampon `metadata.cost`
    seul deplace le git blob SHA mais preserve le content_sha (_shas_match
    compare via content_sha d'abord). C'est precisement la classe de drift
    pre-existante Sudoku-08/14 BDD/9 GraphColoring que ai-01 design-gate a
    designee comme devant etre ignoree par le rebaseline (cf commentaire
    ai-01 2026-08-04T23:23Z sur #9399 : « ne les rebaselinez pas avec
    --update ; deux disparaitront d'eux-memes avec volet (c) »).
    """
    py = pair["python"]
    cs = pair["csharp"]
    ru = pair.get("rust")  # cote optionnel #27098 organe 1
    cur_py = _git_blob_sha(repo_root, py)
    cur_cs = _git_blob_sha(repo_root, cs)
    cur_ru = _git_blob_sha(repo_root, ru) if ru else None
    # content_*_sha (#9399 volet c) : SHA-256 du notebook sans nb["metadata"].
    cur_cpy = _content_sha(repo_root, py)
    cur_ccs = _content_sha(repo_root, cs)
    cur_cru = _content_sha(repo_root, ru) if ru else None
    audit = {
        "date": date or _dt.date.today().isoformat(),
        "by": by or _latest_audit(pair).get("by", "manual"),
        "python_sha": cur_py,
        "csharp_sha": cur_cs,
        "content_python_sha": cur_cpy,
        "content_csharp_sha": cur_ccs,
    }
    # Empreintes du cote rust SEULEMENT si la paire le declare : les audits des
    # paires binaires P/C restent byte-identiques (pas de cle rust parasite
    # dans les ~158 fichiers existants au premier --update).
    if ru:
        audit["rust_sha"] = cur_ru
        audit["content_rust_sha"] = cur_cru
    # No-op detection : si les SHAs de comparaison (content_sha d'abord, puis
    # git blob SHA en fallback legacy) sont identiques au `_latest_audit`
    # actuel, le rebaseline n'apporterait aucune information nouvelle -- c'est
    # un faux audit au sens du design-gate #9399 critere 2.
    latest = _latest_audit(pair)
    is_noop = bool(latest) and _shas_match(latest, audit)
    # Cas d'orphelin par squash (#11919) : un squash-merge peut re-hasher le
    # blob sans toucher le contenu du notebook. Les `python_sha`/`csharp_sha`
    # (git blob, legacy) enregistres ne sont alors PLUS ancetres de main, mais
    # les `content_*_sha` sont identiques (le contenu est intact). Le no-op
    # detection ci-dessus verrait « rien n'a change pedagogiquement » -- mais
    # `--verify-recorded-sha` detecterait un MISMATCH sur le git blob SHA, et
    # laisser cette paire en orphelin signifierait qu'aucun `--update` ne peut
    # la ressoumettre au HEAD courant (le rebaseline necessaire est uniquement
    # sur les git blob SHA, pas sur le contenu).
    #
    # Discrimination : sur un no-op, demander a git si le recorded blob SHA
    # est accessible depuis HEAD (`_blob_ancestor_in`). Un vrai orphelin
    # (squash) N'EST PAS accessible ; un metadata-only drift l'est (le blob
    # est reference par un commit ancetre de HEAD, juste pas HEAD lui-meme).
    # C'est la cle qui distingue les deux cas ayant pourtant la meme
    # signature `rec_X != cur_X` -- sans cette discrimination, le fix
    # violerait le design-gate #9399 critere 2 (metadata-only drift DOIT
    # rester no-op, Sudoku-08/14 BDD du 2026-08-04).
    if is_noop and latest:
        rec_py = latest.get("python_sha")
        rec_cs = latest.get("csharp_sha")
        rec_ru = latest.get("rust_sha")
        py_orphan = rec_py is not None and not _blob_ancestor_in(repo_root, rec_py)
        cs_orphan = rec_cs is not None and not _blob_ancestor_in(repo_root, rec_cs)
        # Orphelin par squash du cote rust : meme discrimination (#27098).
        ru_orphan = (ru and rec_ru is not None
                     and not _blob_ancestor_in(repo_root, rec_ru))
        if py_orphan or cs_orphan or ru_orphan:
            is_noop = False
    return audit, cur_py, is_noop


def verify_recorded_sha(repo_root: Path, pair: dict) -> dict:
    """Verifie que les SHA enregistres dans le YAML correspondent aux SHA
    calcules a HEAD (#9399 volet b).

    Cible l'acceptance verbatim du design-gate (#9399 c.1205) :
    « La CI calcule python_sha / csharp_sha / content_*_sha et echoue si le
    YAML committé diverge ». Detecte un SHA invente / stale / corrompu en
    comparant ce que `last_audit:` (legacy) ou `audits[-1]` (append-only)
    declare au SHA reel du carnet a HEAD.

    Distinction avec `check_pair` (mode --per-pair) :
      - check_pair compare HEAD vs base-ref, et tolere DRIFT_PRE_EXISTING
        (un rebaseline historique peut dater d'un main anterieur) ;
      - verify_recorded_sha compare YAML-enregistre vs HEAD-calcule -- une
        valeur recorded egale a la valeur courante est legit, une valeur
        recorded divergente = MISMATCH (le sha a ete ecrit a la main, pas via
        --update, ou le carnet a bouge sans rebaseline).

    Tolerance metadata-only (#20228) : un blob SHA qui a bouge sans que le
    contenu (cellules + outputs) ait bouge -- tampon `nb["metadata"]` pose ou
    retire -- n'est PAS rapporte. `--update` refuse ce cas comme no-op par
    design (#9399 critere 2), donc le rapporter rendait l'avertissement
    inextinguible : les deux modes du meme outil se contredisaient. Le side
    concerne est liste dans `metadata_only_sha` (tracable, non bloquant).

    Migration progressive : les paires non encore re-auditees post-volet-(c)
    ont `content_*_sha: None` ; on les SAUTE (pas un mismatch, juste
    « pas encore migre »). Meme politique que les tests rename-aware (#9473).

    Sortie : dict avec `status` ("OK" / "MISMATCH" / "NO_AUDIT"), `mismatches`
    (liste de chaines courtes), `name` (utile au mode --json).
    """
    py = pair["python"]
    cs = pair["csharp"]
    audit = _latest_audit(pair)
    if not audit:
        return {
            "name": pair.get("name", "?"),
            "status": "NO_AUDIT",
            "mismatches": [],
        }

    # SHA calcules a HEAD (jamais lus a la main -- re-calcules systematiquement).
    ru = pair.get("rust")  # cote optionnel #27098 organe 1
    cur_py = _git_blob_sha(repo_root, py)
    cur_cs = _git_blob_sha(repo_root, cs)
    cur_ru = _git_blob_sha(repo_root, ru) if ru else None
    cur_cpy = _content_sha(repo_root, py)
    cur_ccs = _content_sha(repo_root, cs)
    cur_cru = _content_sha(repo_root, ru) if ru else None

    # SHA enregistres dans le YAML (forme append-only ou legacy, _latest_audit
    # normalise les deux).
    rec_py = audit.get("python_sha")
    rec_cs = audit.get("csharp_sha")
    rec_ru = audit.get("rust_sha")
    rec_cpy = audit.get("content_python_sha")
    rec_ccs = audit.get("content_csharp_sha")
    rec_cru = audit.get("content_rust_sha")

    # Drift metadata-only (#20228) : le blob SHA a bouge -- un tampon
    # `nb["metadata"]` (kernelspec, cost, papermill) pose ou retire -- sans que
    # le contenu pedagogique (cellules + outputs) ait bouge. Le design exige que
    # ce cas NE fasse PAS rougir le gate (#9399 critere 2 ; cf docstring de
    # `_content_sha` : « un tampon `metadata.cost` seul ne porte aucune
    # divergence pedagogique et ne doit PAS faire rougir le gate », faux
    # positifs Sudoku-08/14 BDD du 2026-08-04). Coherence avec `--update`, qui
    # le refuse deja comme no-op : sans cette tolerance, les deux modes se
    # contredisaient -- `verify` disait « incoherent » quand `update` disait
    # « rien a faire », et AUCUN geste ne pouvait eteindre l'avertissement.
    #
    # Un orphelin par squash reste rapporte : son blob n'est plus accessible
    # depuis HEAD, il n'est donc pas un drift metadata-only et il EST
    # rebaselinable (#11919).
    def _metadata_only(rec_content, cur_content, rec_blob):
        return (rec_content is not None and rec_content == cur_content
                and rec_blob is not None
                and _blob_ancestor_in(repo_root, rec_blob))

    py_meta_only = _metadata_only(rec_cpy, cur_cpy, rec_py)
    cs_meta_only = _metadata_only(rec_ccs, cur_ccs, rec_cs)
    ru_meta_only = _metadata_only(rec_cru, cur_cru, rec_ru)

    mismatches = []
    metadata_only_sha = []
    # Comparaison sur les blob SHA : compares stricte, sauf drift metadata-only.
    if rec_py is not None and rec_py != cur_py:
        if py_meta_only:
            metadata_only_sha.append("python_sha")
        else:
            mismatches.append(
                f"python_sha: recorded={rec_py[:12]} calculated={cur_py[:12]}"
            )
    if rec_cs is not None and rec_cs != cur_cs:
        if cs_meta_only:
            metadata_only_sha.append("csharp_sha")
        else:
            mismatches.append(
                f"csharp_sha: recorded={rec_cs[:12]} calculated={cur_cs[:12]}"
            )
    # Comparaison sur les content_sha : on SKIP si recorded=None (migration
    # progressive post-volet-(c) ; les paires legacy n'ont pas encore ces
    # champs). Une comparaison `None != cur_cpy` serait un faux positif de
    # masse (cf doctrine rename-aware #9473 -- tolerer les absences
    # transitoires sur les champs ajoutes apres coup).
    if rec_cpy is not None and rec_cpy != cur_cpy:
        mismatches.append(
            f"content_python_sha: recorded={rec_cpy[:12]} calculated={cur_cpy[:12]}"
        )
    if rec_ccs is not None and rec_ccs != cur_ccs:
        mismatches.append(
            f"content_csharp_sha: recorded={rec_ccs[:12]} calculated={cur_ccs[:12]}"
        )
    # Cote rust optionnel (#27098 organe 1) : memes comparaisons, seulement si
    # la paire declare le troisieme jumeau ET que l'audit l'a attesté (rec non
    # None) -- une paire `rust:` dont l'audit n'a pas d'empreinte rust reste
    # du ressort de check_pair (no_baseline), pas un mismatch de valeur.
    if ru and rec_ru is not None and rec_ru != cur_ru:
        if ru_meta_only:
            metadata_only_sha.append("rust_sha")
        else:
            mismatches.append(
                f"rust_sha: recorded={rec_ru[:12]} calculated={cur_ru[:12]}"
            )
    if ru and rec_cru is not None and rec_cru != cur_cru:
        mismatches.append(
            f"content_rust_sha: recorded={rec_cru[:12]} calculated={cur_cru[:12]}"
        )

    return {
        "name": pair.get("name", "?"),
        "family": pair.get("family", "?"),
        "parity_level": pair.get("parity_level", "?"),
        "status": "MISMATCH" if mismatches else "OK",
        "mismatches": mismatches,
        "metadata_only_sha": metadata_only_sha,
        "current_python_sha": cur_py,
        "current_csharp_sha": cur_cs,
        "current_rust_sha": cur_ru,
        "current_content_python_sha": cur_cpy,
        "current_content_csharp_sha": cur_ccs,
        "current_content_rust_sha": cur_cru,
        "recorded_python_sha": rec_py,
        "recorded_csharp_sha": rec_cs,
        "recorded_rust_sha": rec_ru,
        "recorded_content_python_sha": rec_cpy,
        "recorded_content_csharp_sha": rec_ccs,
        "recorded_content_rust_sha": rec_cru,
    }


# Cles scalaires d'un enregistrement d'audit (forme append-only ET legacy).
# Partagees par le singleton `last_audit:` (legacy) et chaque element de la
# liste `audits:` (append-only, #9399).
_AUDIT_KEYS = (
    "date", "by", "python_sha", "csharp_sha",
    # content_*_sha (#9399 volet c) : SHA-256 du notebook sans nb["metadata"].
    # metadata-immune : un tampon cost seul ne fait plus rougir le gate ni
    # declencher un faux audit au --update. Ajoutes a cote (anti-regression :
    # les blob SHA python_sha/csharp_sha restent enregistres pour inspection).
    "content_python_sha", "content_csharp_sha",
    # Cote rust optionnel (#27098 organe 1) : empreintes du troisieme jumeau,
    # enregistrees par --update UNIQUEMENT quand la paire declare `rust:` (les
    # paires binaires n'emettent jamais ces cles -- pas de diff parasite).
    "rust_sha", "content_rust_sha",
)


def _latest_audit(pair: dict) -> dict:
    """Retourne le dernier enregistrement d'audit d'une paire.

    Supporte les deux formes du registre (#9399) :
      - append-only : `audits:` est une liste d'enregistrements (date/by/shas) ;
        le plus recent est le dernier element. Deux audits concurrents sur la
        meme paire ecrivent alors des entrees distinctes -> git les fusionne
        seul (fin de la collision mecanique du singleton legacy).
      - legacy : `last_audit:` singleton (forme historique des ~158 fichiers).

    Priorite a `audits:` (nouvelle forme) si present et non vide, sinon fallback
    sur `last_audit:`. Renvoie `{}` si ni l'un ni l'autre (paire non encore
    auditee -> DRIFT au prochain --check, comme avant).

    Cette retro-compatibilite permet une migration **a la volee** (chaque
    `--update` migre sa paire vers la forme append-only) plutot qu'une
    reecriture massive des 158 fichiers en un coup, qui serait elle-meme un
    aimant a collision (#9399 critere d'acceptation : preserve l'historique).
    """
    audits = pair.get("audits")
    if isinstance(audits, list) and audits:
        # Les enregistrements legacy peuvent omettre `by`/`date` ; tolerer.
        last = audits[-1]
        if isinstance(last, dict):
            return last
    return pair.get("last_audit") or {}


def _fmt_audit_value(key: str, value) -> str:
    """Rend une valeur de `last_audit` dans le style du registre.

    `date` est quotee (comme les 116 entrees existantes), le reste est nu.
    """
    if value is None:
        return "null"
    return f'"{value}"' if key == "date" else str(value)


def write_registry_text(path: Path, text: str) -> None:
    """Ecrit un fichier de registre en preservant ses fins de ligne LF.

    `Path.write_text(..., encoding="utf-8")` ouvre le fichier avec
    `newline=None`, ce qui traduit chaque `\\n` en `os.linesep` -- donc en
    `\\r\\n` sous Windows. La moitie de la flotte tourne sous Windows : un
    rebaseline y reecrivait silencieusement **toutes** les lignes du fichier en
    CRLF, y compris celles que `surgical_rebaseline` venait de laisser
    intactes. Le diff annonce (« exactement les lignes changees ») devenait un
    diff de fichier entier, et la ligne qu'un relecteur doit examiner -- le SHA
    -- se retrouvait noyee dans le bruit.

    `newline=""` desactive toute traduction : le texte est ecrit tel quel.

    Incident : PR #8709 et #8713, deux rebaselines d'une seule paire chacun,
    affichant `+23/-16` et `+24/-16` la ou le changement reel valait deux
    lignes.
    """
    with path.open("w", encoding="utf-8", newline="") as fh:
        fh.write(text)


def _parse_flat_audit(body_lines):
    """Paires (cle, valeur_textuelle) d'un bloc `last_audit:` legacy (mapping plat).

    Preserve l'ordre du fichier : `reason` est optionnel et libre (texte long de
    justification d'audit), on ne PEUT PAS se restreindre a `_AUDIT_KEYS` sous
    peine de jeter l'historique d'audit (#9399 critere 4, anti-regression).
    """
    items = []
    for ln in body_lines:
        m = re.match(r"^\s+(\w+):\s*(.*)$", ln)
        if m:
            items.append((m.group(1), m.group(2).strip().strip("\"'")))
    return items


def _parse_latest_audit_entry(body_lines):
    """Dernier element de liste d'un bloc `audits:` -> dict des cles scalaires.

    Sert au no-op check : si la derniere entree enregistre deja les SHAs
    courants, on n'ajoute pas de doublon (evite la croissance infinie de la
    liste sur des `--update` successifs sans changement reel).
    """
    latest = {}
    for ln in body_lines:
        m_item = re.match(r"^\s+-\s+(\w+):\s*(.*)$", ln)
        m_kv = re.match(r"^\s{2,}(\w+):\s*(.*)$", ln)
        if m_item:
            latest = {m_item.group(1): m_item.group(2).strip().strip("\"'")}
        elif m_kv:
            latest[m_kv.group(1)] = m_kv.group(2).strip().strip("\"'")
    return latest


def _cmp_pair_shas(d: dict) -> tuple:
    """SHAs de comparaison (no-op / drift) extraits d'un enregistrement d'audit.

    Prefer les `content_*_sha` (metadata-immunes, #9399 volet c) quand l'audit
    les porte ; sinon retombe sur les `python_sha`/`csharp_sha` (git blob SHA,
    legacy pre-content_sha). Centralise la regle de preference afin que
    `_shas_match` (no-op au --update) et `verify_pair` (DRIFT au --check)
    appliquent la MEME definition de « rien n'a change ».
    """
    cp = d.get("content_python_sha")
    cc = d.get("content_csharp_sha")
    if cp is not None and cc is not None:
        return cp, cc
    return d.get("python_sha"), d.get("csharp_sha")


def _cmp_rust_sha(d: dict) -> str | None:
    """SHA de comparaison du cote rust optionnel (#27098 organe 1).

    Meme regle de preference que `_cmp_pair_shas` : `content_rust_sha`
    (metadata-immune) quand l'enregistrement le porte, sinon `rust_sha`
    (git blob SHA). None = cote rust absent de l'enregistrement (paire
    binaire, ou attestation rust pas encore migree).
    """
    cr = d.get("content_rust_sha")
    if cr is not None:
        return cr
    return d.get("rust_sha")


def _shas_match(record: dict, new_entry: dict) -> bool:
    """True ssi `record` et `new_entry` partagent les memes SHAs de comparaison (no-op).

    Un changement **metadata-only** (ex: tampon `metadata.cost`) change les git
    blob SHAs mais PAS les `content_*_sha` : via `_cmp_pair_shas` cela devient un
    no-op, donc le `--update` n'APPEND PAS de nouvelle entree d'audit pour un
    changement qui n'est pas pedagogique (faux audit, cf ai-01 design-gate #9399).

    Cote rust (#27098 organe 1) : la contrainte est CONDITIONNELLE -- une
    `new_entry` sans empreinte rust (paire binaire) n'en impose aucune ; une
    `new_entry` qui en porte une (paire `rust:`) exige que `record` porte la
    meme. Une premiere attestation rust (record sans empreinte) n'est donc
    JAMAIS un no-op : declarer le troisieme jumeau append une entree reelle.
    """
    rec_py, rec_cs = _cmp_pair_shas(record)
    new_py, new_cs = _cmp_pair_shas(new_entry)
    if new_py is None or new_cs is None:
        return False
    if str(rec_py) != str(new_py) or str(rec_cs) != str(new_cs):
        return False
    new_ru = _cmp_rust_sha(new_entry)
    if new_ru is not None and str(_cmp_rust_sha(record)) != str(new_ru):
        return False
    return True


def _attestation_identical(record: dict, new_entry: dict) -> bool:
    """True ssi une nouvelle entree serait STRICTEMENT identique a `record`.

    Difference avec `_shas_match` (no-op, content-only) : on exige EN PLUS que
    les git blob SHAs soient egaux. C'est la discrimination du cas orphelin par
    squash (#11919 / #13100) : `update_pair` a deja tranche is_noop=False quand
    le recorded blob n'est pas ancre de HEAD, puis recalcule une entree dont le
    content_sha est PRESERVE (le squash a re-hashe le blob sans toucher au
    contenu). Si la couche d'ecriture re-verifiait un `_shas_match` content-only,
    elle REFUSERait cet ecrit legitime et `surgical_rebaseline` renvoyait
    touched=0 -> message trompeur « aucun bloc d'audit reconnu » sur un bloc
    2/4/6 parfaitement canonique. Seule une attestation identique au sens strict
    (content ET blobs) est un faux audit a rejeter sans --force.
    """
    if not _shas_match(record, new_entry):
        return False
    for key in ("python_sha", "csharp_sha", "rust_sha"):
        rec_val = record.get(key)
        new_val = new_entry.get(key)
        if rec_val is not None and new_val is not None and rec_val != new_val:
            return False
    return True


def _legacy_body_as_list_item(body_lines):
    """Convertit un body legacy (mapping plat indent 4) en 1er item de `audits:`.

    Mecanique pure : la 1re ligne recoit `- ` apres son indentation, les
    suivantes +2 espaces (alignement sous la 1re cle). La VALEUR (quotes
    comprises) est preservee byte-faithful -- crucial pour `reason` (texte libre
    long) : on ne re-quotationne pas, on deplace juste la marge.
    """
    out = []
    for idx, ln in enumerate(body_lines):
        m = re.match(r"^(\s+)(\S.*?)(\r?\n)?$", ln)
        if not m:
            out.append(ln)
            continue
        indent, content, eol = m.group(1), m.group(2), m.group(3) or "\n"
        if idx == 0:
            out.append(f"{indent}- {content}{eol}")
        else:
            out.append(f"  {indent}{content}{eol}")
    return out


def _render_new_audit_entry(entry: dict, item_indent: str = "    ") -> list[str]:
    """Rendre une nouvelle entree en preservant la marge de la liste `audits:`."""
    lines = []
    keys = [k for k in _AUDIT_KEYS if entry.get(k) is not None]
    field_indent = f"{item_indent}  "
    for idx, key in enumerate(keys):
        val = _fmt_audit_value(key, entry[key])
        if idx == 0:
            lines.append(f"{item_indent}- {key}: {val}\n")
        else:
            lines.append(f"{field_indent}{key}: {val}\n")
    return lines


def _audit_item_indent(block: list[str]) -> str:
    """Detecte la marge des items existants, ou derive le style par defaut.

    YAML autorise une sequence indentationless : l'item peut etre au meme niveau
    que la cle ``audits:``. D'autres registres utilisent une marge de deux espaces
    supplementaires. Melanger les deux styles dans un meme bloc rend le YAML
    invalide ; l'append doit donc suivre le premier item existant.
    """
    for line in block[1:]:
        match = re.match(r"^(\s*)-\s+", line)
        if match:
            return match.group(1)

    header = re.match(r"^(\s*)audits:\s*$", block[0])
    header_indent = header.group(1) if header else "  "
    return f"{header_indent}  "


def _transform_audit_block(form: str, block: list[str], new_entry: dict, force: bool = False) -> tuple[list[str], bool]:
    """Transforme un bloc d'audit (header + body) pour une paire ciblee.

    form = "last_audit" (legacy singleton) ou "audits" (liste append-only).
    Retourne (nouvelles_lignes_du_bloc, a_change).

    Semantique append-only (#9399) :
      - audits: + SHAs inchanges -> no-op (pas de doublon) SAUF si force=True
        (opt-in explicite --force : ecriture malgre l'identite, design-gate
        #9399 critere 2).
      - audits: + SHAs changes   -> APPEND d'une nouvelle entree.
      - last_audit: + SHAs inchanges -> no-op (on reste legacy ; migration
        paresseuse a la volee, uniquement quand la paire drift reelement)
        SAUF si force=True.
      - last_audit: + SHAs changes   -> MIGRATION vers audits: [ancien, nouveau]
        (l'ancien enregistrement, `reason` compris, devient item[0]).
    """
    body = block[1:]
    if form == "audits":
        latest = _parse_latest_audit_entry(body)
        if _attestation_identical(latest, new_entry) and not force:
            return block, False
        # force=True OU SHAs differents : APPEND une nouvelle entree
        # (avec --force c'est le faux audit designe par ai-01 -- averti sur stderr).
        item_indent = _audit_item_indent(block)
        return block + _render_new_audit_entry(new_entry, item_indent), True

    # form == "last_audit" -> migration vers la forme append-only
    old_pairs = _parse_flat_audit(body)
    if _shas_match(dict(old_pairs), new_entry) and not force:
        return block, False
    new_block = ["  audits:\n"]
    if old_pairs:
        new_block += _legacy_body_as_list_item(body)
    new_block += _render_new_audit_entry(new_entry)
    return new_block, True


def surgical_rebaseline(raw: str, updates: dict[str, dict], force: bool = False) -> tuple[str, int]:
    """Reecrit UNIQUEMENT le bloc d'audit des paires ciblees (forme append-only).

    Pourquoi ne pas re-serialiser via `yaml.safe_dump` (comportement d'avant
    #8570) : un dump complet detruit **tout** le fichier autour des donnees.
    Mesure firsthand sur le registre a 116 paires -- un rebaseline d'UNE paire
    produisait `1108 insertions(+), 658 deletions(-)` et supprimait les **67
    lignes de commentaire**, dont l'en-tete de 15 lignes qui documente le
    schema et le vocabulaire `parity_level`. Le vrai changement devenait
    irreviewable, et la documentation du registre disparaissait sans que
    personne ne l'ait demande.

    L'edition ligne-a-ligne ci-dessous preserve commentaires, ordre, quoting et
    espacement : le diff d'un rebaseline vaut exactement les lignes changees.

    Depuis #9399 (volet a), l'ecriture est **append-only** : le singleton
    `last_audit:` est un aimant a collision (deux audits concurrents de la meme
    paire visent les memes lignes -> CONFLICT ou ecrasement silencieux du plus
    recent par le plus ancien, cf #9171/#9237/#9245). La forme cible est une
    liste `audits:` ou chaque audit ajoute une entree distincte -> git fusionne
    sans intervention, et rien n'ecrase plus un enregistrement plus recent.
    La migration legacy -> audits: est **paresseuse** (a la volee, sur le 1er
    drift reel) pour eviter qu'une reecriture massive des ~158 fichiers ne soit
    elle-meme un aimant a collision.

    Args:
        raw: contenu texte du registre YAML.
        updates: {nom_de_paire: {"date":.., "by":.., "python_sha":.., "csharp_sha":..}}
        force: bool -- si True, outrepasse la detection no-op au niveau
            `_transform_audit_block` (cf design-gate #9399 critere 2 ; permet
            un rebaseline explicite d'un audit identique au precedent, designe
            par ai-01 comme "faux audit" mais parfois legitime pour forcer une
            nouvelle attestation datee).

    Returns:
        (nouveau_texte, nombre_de_paires_effectivement_touchees)
    """
    lines = raw.splitlines(keepends=True)
    out: list[str] = []
    current: str | None = None
    touched: set[str] = set()

    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        m_entry = re.match(r"^-\s+name:\s*(.+?)\s*$", line)
        if m_entry:
            current = m_entry.group(1).strip().strip("\"'")
            out.append(line)
            i += 1
            continue

        # Quantificateur \s{2,} (pas \s{2} exact) + coupure RELATIVE a
        # l'indentation de la cle (#10430) : un fichier a indentation native 4
        # (ex. app-10-portfolio.yaml, `audits:` a 4 espaces) voyait son en-tete
        # reste invisible avec \s{2} exact -> surgical_rebaseline renvoyait
        # touched=0 SANS erreur (header introuvable = no-op silencieux).
        m_hdr = re.match(r"^(\s{2,})(last_audit|audits):\s*$", line)
        if m_hdr and current in updates:
            hdr_indent = len(m_hdr.group(1))
            form = m_hdr.group(2)
            # Corps du bloc : coupure RELATIVE (pas le seuil absolu \s{4,}
            # d'avant, qui etrangle la cle sibling `known_differences:` quand
            # `audits:` est a indent 4). Continuation = strictement plus indent
            # que la cle, OU un item de sequence `-` a indent >= cle (YAML
            # autorise un block sequence a la meme indent que sa cle parent).
            block = [line]
            j = i + 1
            while j < n:
                nxt = lines[j]
                if not nxt.strip():
                    break
                lead = len(nxt) - len(nxt.lstrip(" "))
                is_seq = nxt.lstrip(" ").startswith("-")
                if lead > hdr_indent or (is_seq and lead >= hdr_indent):
                    block.append(nxt)
                    j += 1
                else:
                    break
            new_block, did = _transform_audit_block(form, block, updates[current], force=force)
            if did:
                touched.add(current)
            out.extend(new_block)
            i = j
            continue

        out.append(line)
        i += 1

    return "".join(out), len(touched)


def _strip_audits_from_yaml(raw: str) -> str:
    """Retire le bloc `audits:` / `last_audit:` d'un fichier de paire.

    Nouvelle forme file-per-audit (#14911) : le fichier `<pair>.yaml` ne porte
    plus la liste d'audits (desormais un fichier par audit dans `<pair>/`).
    Ce complement de `surgical_rebaseline` supprime LA liste en preservant
    commentaires, ordre, quoting et espacement des autres cles (meme heuristique
    de detection du bloc : continuation = strictement plus indente que la cle,
    OU un item de sequence a indent >= cle).

    Retourne le texte sans le bloc audits (si present, sinon inchange).
    """
    lines = raw.splitlines(keepends=True)
    out: list[str] = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        m_hdr = re.match(r"^(\s{2,})(last_audit|audits):\s*$", line)
        if m_hdr:
            hdr_indent = len(m_hdr.group(1))
            j = i + 1
            while j < n:
                nxt = lines[j]
                if not nxt.strip():
                    break
                lead = len(nxt) - len(nxt.lstrip(" "))
                is_seq = nxt.lstrip(" ").startswith("-")
                if lead > hdr_indent or (is_seq and lead >= hdr_indent):
                    j += 1
                else:
                    break
            i = j  # saute tout le bloc audits
            continue
        out.append(line)
        i += 1
    return "".join(out)


def _inline_audits_of(raw: str) -> list[dict]:
    """Extrait les audits inline (`audits:`/`last_audit:`) d'un fichier de paire.

    Utilise par le mode directory de `--update` (#14911) pour migrer les audits
    encore inline d'une paire NON migree avant d'appender le nouvel audit --
    sinon `_strip_audits_from_yaml` retirerait la liste entiere et les audits
    existants seraient perdus (anti-regression).
    """
    data = yaml.safe_load(raw)
    if isinstance(data, list):
        data = data[0] if data and isinstance(data[0], dict) else {}
    if not isinstance(data, dict):
        return []
    audits = list(data.get("audits") or [])
    la = data.get("last_audit")
    if la and isinstance(la, dict):
        audits.append(la)
    return audits


def _dump_audit_yaml(audit: dict) -> str:
    """Serie un dict d'audit au style du registre (date quotee, SHA nus).

    Un fichier d'audit separe (#14911) est un NOUVEAU fichier, donc un dump
    propre est acceptable (pas de commentaires a preserver). On reproduit le
    style des entrees existantes : `date: "2026-09-06"`, `by: myia-...:CoursIA`,
    SHAs hex nus, `null` explicite.
    """
    # Normalise les dates non-str (un `date: 2026-08-04` non quote se charge en
    # datetime.date) vers l'ISO string, pour que le fichier porte
    # `date: "2026-08-04"` et se re-charge en str (le schema du registre attend
    # une str ; un datetime.date casserait les lectures et egalites de cles).
    normalized = {}
    for k, v in audit.items():
        if isinstance(v, _dt.date) and not isinstance(v, _dt.datetime):
            normalized[k] = v.isoformat()
        else:
            normalized[k] = v
    try:
        # safe_dump gere l'echappement (un `reason` contenant `"`, `:`, `\n`,
        # ou un `[` de tete serait casse par une citation naive `"..."`).
        # sort_keys=False preserve l'ordre de la source (date, by, shas, reason).
        return yaml.safe_dump(
            normalized, allow_unicode=True, sort_keys=False, default_flow_style=False
        )
    except Exception:
        # Repli minimal si un type non-serialisable (ex. `content_sha` absent
        # ou un type exotique) : on aplatit en str sans echappement exotique.
        lines: list[str] = []
        for k, v in normalized.items():
            if v is None:
                lines.append(f"{k}: null")
            else:
                lines.append(f"{k}: {v}")
        return "\n".join(lines) + "\n"


def _write_audit_file(registry_dir: Path, name: str, audit: dict,
                      used_names: set[str] | None = None,
                      index: int | None = None,
                      floor: int = 0) -> Path:
    """Ecrit un audit dans un fichier separe `<pair>/<idx>-<date>-<lane>.yaml`.

    Nouvelle forme (#14911). `index` (optionnel) place l'audit dans l'ordre
    d'append : a la migration on passe l'index d'origine (1-base), a l'ajout
    d'un nouvel audit (`--update`) il prend `max(indexes existants)+1` pour
    trier en derniere position (= plus recent). `used_names` suit les noms
    deja pris pour suffixer `-2`, `-3`... en secours si un index venait a
    collider. Retourne le chemin.

    `floor` (#22299) est le plus grand index deja PUBLIE pour la paire sur la
    ref d'integration : l'index alloue reste strictement au-dessus. Le max
    local ne suffit pas -- deux branches issues du meme `main` lisent le meme
    disque, calculent le meme max et emettent le meme `NNNN`.
    """
    slug = _slug(name)
    d = _audit_dir(registry_dir, slug)
    d.mkdir(parents=True, exist_ok=True)
    date = str(audit.get("date") or _dt.date.today().isoformat())
    by = audit.get("by")
    if index is None:
        index = max(_next_audit_index(d), floor + 1)
    base = _audit_filename(date, by, index)
    stem = base[:-5]  # retire ".yaml"
    used = used_names if used_names is not None else set()
    cand = base
    k = 2
    while cand in used:
        cand = f"{stem}-{k}.yaml"
        k += 1
    # Course entre branches (incident gametheory-4c : deux 0009 emis par deux
    # lanes depuis des checkouts differents) : ne JAMAIS ecraser un fichier
    # existant -- prendre l'index libre suivant. Le suffixe -2 ci-dessus garde
    # le meme prefixe NNNN, que test_audit_index_unique interdit aujourd'hui ;
    # il ne reste legitime que pour la migration inline (repertoire vierge).
    while (d / cand).exists():
        index += 1
        cand = _audit_filename(date, by, index)
    used.add(cand)
    path = d / cand
    path.write_text(_dump_audit_yaml(audit), encoding="utf-8", newline="")
    return path


def audit_index(filename: str) -> str:
    """Cle de tri d'un fichier d'audit : le prefixe ``NNNN`` avant le premier
    tiret (``0007-2026-09-08-myia-po-2024-CoursIA.yaml`` -> ``0007``).

    C'EST LA GRANDEUR QUE LE GARDE D'INTEGRITE TESTE : `idx = name.split("-",
    1)[0]`, unicite par paire (`test_twin_registry_integrity.py`,
    `test_audit_index_unique_and_no_identical_duplicates_per_pair`). Toute
    lecture qui doit predire ce verdict passe par ICI -- une derivation
    reecrite ailleurs finit par diverger de la definition testee, et un
    instrument qui mesure une autre grandeur que le garde rend un vert faux.
    """
    return str(filename).split("-", 1)[0]


def _next_audit_index(d: Path) -> int:
    """Max des index NNNN existants + 1 -- jamais len()+1 : un trou ou un
    doublon herite ferait re-emettre un index deja pris (l'index est la cle
    de tri du journal, #14911/#15345)."""
    idxs = [int(audit_index(f.name)) for f in d.glob("*.yaml")
            if audit_index(f.name).isdigit()]
    return max(idxs, default=0) + 1


def _audit_indexes_at_ref(repo_root: Path, git_ref: str, registry_dir: Path,
                          name: str) -> set[int]:
    """Index `NNNN` deja publies pour cette paire sur `git_ref` (#22299).

    `_next_audit_index` ne lit que le disque local : deux branches issues du
    meme `main` calculent le meme max, donc le meme prefixe, et le garde
    d'integrite les refuse apres merge (5 paires mesurees le 2026-10-24). Ce
    plancher lit la ref d'integration pour qu'une branche qui re-atteste
    APRES que la ref a gagne un audit n'emette jamais un `NNNN` deja pris.

    Un ref illisible, un repertoire absent ou un `registry_dir` hors depot
    rendent l'ensemble VIDE : c'est un plancher, pas une mesure -- ne rien
    trouver ne doit jamais bloquer une ecriture.
    """
    slug = _slug(name)
    try:
        reg_rel = registry_dir.resolve().relative_to(repo_root.resolve()).as_posix()
    except ValueError:
        return set()
    try:
        r = _run_git(
            ["git", "ls-tree", "-r", "--name-only", git_ref, "--",
             f"{reg_rel}/{slug}/"],
            cwd=str(repo_root),
        )
    except GitTimeoutError:
        # Un ls-tree qui expire degrade comme une ref illisible : un garde
        # ne doit jamais transformer un remote lent en ecriture refusee.
        return set()
    if r.returncode != 0:
        return set()
    out: set[int] = set()
    for line in (r.stdout or "").splitlines():
        idx = audit_index(line.rsplit("/", 1)[-1])
        if idx.isdigit():
            out.add(int(idx))
    return out


def _audit_floor(repo_root: Path, registry_dir: Path, name: str,
                 ref: str | None) -> int:
    """Plus grand index deja publie pour la paire sur `ref` (0 si inutilisable)."""
    if not ref:
        return 0
    return max(_audit_indexes_at_ref(repo_root, ref, registry_dir, name), default=0)


def _open_claim_floors(repo_root: Path) -> dict[str, int]:
    """Ordinals revendiques par les PRs ouvertes, par paire (dossier).

    Le plancher d'allocation lisait jusqu'ici la **seule** ref d'integration
    (`origin/main`). Mesure du 2026-11-09 (constat du coordinateur) : une PR
    ouverte peut ** deja tenir l'ordinal propose -- l'ordinal `0018` de
    `tweety-11-causal` etait tenu par #25037, et `0013`/`0021` ont ete
    proposes pour deux autres paires alors que la collision n'etait visible
    qu'apres le push. Le plancher de la ref ne voit pas une PR encore
    ouverte : il faut aussi lire les **revendications** des PRs ouvertes.

    L'organe natif de cette lecture est `twin_open_claims.py` : on l'appelle,
    on ne reimplemente ni le parsing du nom de fichier ni le controle de
    troncature. Rend `{<dossier de paire>: <ordinal le plus haut revendique>}`.

    **Lecture impossible -> plancher vide, jamais une ecriture refusee.** Le
    plancher d'allocation est un garde, pas une mesure : un `gh` absent, un
    reseau coupe ou une liste tronquee ne doivent pas bloquer une
    attestation. L'ecart est dit sur stderr, et la porte d'index reste
    l'organe unique du verdict au push.

    **Depot sans remote GitHub -> plancher vide, SANS avertissement.** Le
    plancher n'est pas *applicable* la (copie locale, bac a sable) : ce n'est
    pas une lecture ratee, il n'y a rien a mesurer. Un avertissement dans ce
    cas polluerait la sortie d'un outil qui fonctionne.
    """
    try:
        slug = repo_slug(repo_root)
    except (OpenClaimsError, OSError):
        # Depot sans remote GitHub (copie locale, bac a sable, tests) ou
        # `gh` absent : le plancher des PRs ouvertes n'est pas **applicable**
        # ici -- ce n'est pas une lecture ratee, il n'y a rien a mesurer.
        # Aucun avertissement : la ligne resterait dans la sortie d'un
        # outil qui fonctionne.
        return {}
    try:
        data = collect_open_claims(slug, cwd=repo_root)
    except OpenClaimsError as exc:
        print(f"AVERTISSEMENT : lecture des PRs ouvertes impossible ({exc}) -- "
              "le plancher d'allocation ne couvre que la ref d'integration ; "
              "une collision d'ordinal reste possible (la porte d'index la "
              "verra au push).", file=sys.stderr)
        return {}
    except Exception as exc:  # pragma: no cover -- garde-fou d'import
        print(f"AVERTISSEMENT : lecture des PRs ouvertes impossible ({exc!r}) -- "
              "le plancher d'allocation ne couvre que la ref d'integration.",
              file=sys.stderr)
        return {}
    floors: dict[str, int] = {}
    for claims in (data.get("prs") or {}).values():
        for claim in claims or []:
            pair = str(claim.get("pair") or "")
            index = str(claim.get("index") or "")
            if not pair or not index.isdigit():
                continue
            floors[pair] = max(floors.get(pair, 0), int(index))
    return floors


def _refresh_allocate_ref(repo_root: Path, ref: str | None) -> None:
    """Rafraichit `<remote>/<branche>` avant la lecture du plancher (#22547).

    `ls-tree` lit la ref LOCALE : sans ce fetch, `origin/main` designe ce que
    le clone connaissait a son dernier fetch, et la collision que le plancher
    doit fermer reste atteignable des qu'un autre worker a pousse depuis
    (reproduction Hermes : worker B clone avant le push de C, sans fetch ->
    floor 5, prefixe 0006 deja pris par C ; apres fetch -> floor 8).

    Bornee (_GIT_TIMEOUT_S via `_run_git`, EAGAIN borne) et **jamais
    bloquante** : toute erreur (remote absent, ref non remote, hors ligne,
    timeout) retombe silencieusement sur la ref locale -- meme philosophie
    que le plancher lui-meme, un garde ne bloque jamais une ecriture. Les
    refs non `<remote>/<branche>` (ex. `main`, SHA) ne sont pas fetchees.
    """
    if not ref or "/" not in ref:
        return
    remote, branch = ref.split("/", 1)
    try:
        _run_git(["git", "fetch", "--quiet", remote, branch],
                 cwd=str(repo_root))
    except Exception:
        # Repli sur la ref locale : un plancher perime reste preferable a
        # une ecriture refusee.
        return


def migrate_registry_files_per_audit(registry_dir: Path,
                                     names: set[str] | None = None) -> dict:
    """Migre le registre vers la forme file-per-audit (#14911).

    Pour chaque paire (optionnellement restreinte a `names`) : extrait `audits:`
    (ou `last_audit:` legacy), ecrit un fichier d'audit separe dans `<pair>/`,
    puis retire la liste du fichier d'intention `<pair>.yaml`. Les
    commentaires/ordre des autres cles sont preserves par `_strip_audits_from_yaml`.
    Retourne {migrated, audits_moved} ; les fichiers sont ecrits sur disque
    (le caller commit).
    """
    if yaml is None:
        raise SystemExit("PyYAML requis pour --migrate-audits.")
    migrated = 0
    audits_moved = 0
    for f in sorted(registry_dir.glob("*.yaml")):
        if f.name.startswith("_"):
            continue
        raw = f.read_text(encoding="utf-8")
        data = yaml.safe_load(raw)
        # Les fichiers de paire sont soit un dict, soit une liste d'un dict
        # (tranches verbatim de l'ancien mono-fichier). On normalise a l'entree.
        if isinstance(data, list):
            if not data or not isinstance(data[0], dict):
                continue
            data = data[0]
        if not isinstance(data, dict):
            continue
        audits = data.get("audits") or []
        la = data.get("last_audit")
        if la and isinstance(la, dict):
            audits = list(audits) + [la]
        if not audits:
            continue
        name = data.get("name", f.stem)
        if names is not None and name not in names:
            continue
        used: set[str] = set()
        for idx, a in enumerate(audits, start=1):
            _write_audit_file(registry_dir, name, a, used_names=used, index=idx)
            audits_moved += 1
        new_raw = _strip_audits_from_yaml(raw)
        if new_raw != raw:
            write_registry_text(f, new_raw)
        migrated += 1
    return {"migrated": migrated, "audits_moved": audits_moved}


def _classify_per_pair(base_status: str, head_status: str,
                       base_drift: set[str] | None = None,
                       head_drift: set[str] | None = None,
                       base_no_baseline: bool | None = None,
                       head_no_baseline: bool | None = None) -> str:
    """Verdict per-pair pour le mode --per-pair (compare HEAD vs base-ref).

    Retourne un de : OK / DRIFT_INTRODUCED / DRIFT_RESOLVED / DRIFT_PRE_EXISTING.
    Le gate (--check --per-pair) ne FAIL que sur DRIFT_INTRODUCED.

    Cas special : une paire AJOUTEE par la PR (base_status="MISSING", absente au
    base-ref). Pour une paire nouvelle, il n'y a PAS d'etat pre-existant -- son etat
    au HEAD est exactement ce que la PR introduit. Donc ajoutee+OK -> OK, ajoutee+
    DRIFT -> DRIFT_INTRODUCED. (Avant le fix, le 'else' classait MISSING+DRIFT en
    DRIFT_PRE_EXISTING, qui ne fail pas le gate -- contredisait le comment inline et
    laissait passer une paire ajoutee driftante. Forensic po-2026 c.709.)

    NUMBERING-DRIFT (#12933) suit la meme semantique que DRIFT : introduit par la
    PR (base OK -> head NUMBERING-DRIFT, ex. renommage unilateral dans cette PR) =
    DRIFT_INTRODUCED, gate ROUGE ; resolu par la PR (renommage realigne, OU
    divergence documentee via numbering_exception au HEAD) = DRIFT_RESOLVED.

    #23020 -- le verdict "pre-existant" exige que le drift du HEAD soit un
    SOUS-ENSEMBLE du drift du base. Les deux entrees `base_drift` /
    `head_drift` portent les COTES en drift (voir `check_pair`). Sans eux, le
    statut AGREGE decide seul : une paire deja en drift sur python au base,
    dont la PR touche le jumeau C#, donnait DRIFT -> DRIFT (donc
    DRIFT_PRE_EXISTING, gate VERT) alors que la PR INTRODUISAIT le drift C#.
    Les ensembles sont optionnels : sans eux, la semantique historique est
    conservee (les appelants qui n'ont pas le detail par cote ne changent
    pas de verdict).

    `base_no_baseline` / `head_no_baseline` (#23020, review du 2026-11-02,
    point 2) disent si la paire a une REFERENCE a cette ref. Un ensemble de
    cotes vide n'est pas la preuve qu'aucun jumeau n'a bouge : c'est
    l'absence de reference, que la PR peut elle-meme introduire en
    supprimant une attestation. Une paire qui PERD sa reference au HEAD est
    donc DRIFT_INTRODUCED (les attestations sont append-only) ; une paire
    sans reference des deux cotes reste PRE_EXISTING (rien n'a ete change).
    """
    if base_status == "MISSING":
        return "OK" if head_status == "OK" else "DRIFT_INTRODUCED"
    if base_status == "OK" and head_status == "OK":
        return "OK"
    if base_status == "OK" and head_status in ("DRIFT", "MISSING", "NUMBERING-DRIFT"):
        return "DRIFT_INTRODUCED"
    if base_status in ("DRIFT", "NUMBERING-DRIFT") and head_status == "OK":
        return "DRIFT_RESOLVED"
    # #23020 (review du 2026-11-02, point 2) : une paire PERDANT sa reference
    # au HEAD n'est pas classable "pre-existant". Au base la paire avait une
    # attestation (donc un etat CONNU), au HEAD elle n'en a plus : l'ensemble
    # de cotes du HEAD est vide, et l'ensemble vide est contenu dans
    # n'importe quel ensemble -- la regle de sous-ensemble classait donc
    # "pre-existant" (gate VERT) une PR qui SUPPRIME l'attestation. Les
    # attestations sont append-only : la perte d'une reference est un
    # changement introduit par la PR, donc DRIFT_INTRODUCED. Le cas
    # symetrique (les DEUX cotes sans reference) reste PRE_EXISTING : rien
    # n'a ete change par la PR.
    if head_no_baseline and not base_no_baseline:
        return "DRIFT_INTRODUCED"
    if base_drift is not None and head_drift is not None:
        if set(head_drift) - set(base_drift):
            return "DRIFT_INTRODUCED"
    return "DRIFT_PRE_EXISTING"


def _pair_paths_diverge(base_pp: dict, head_pp: dict) -> bool:
    """True si la paire est declaree avec des chemins differents aux deux refs (#22920).

    Test PUR (aucun appel git) : sert de garde de cout -- les sondes croisees et
    le merge-base ne se paient que sur les paires qui divergent.
    """
    for side in ("python", "csharp", "rust"):
        b = base_pp.get(side)
        h = head_pp.get(side)
        if isinstance(b, str) and isinstance(h, str) and b != h:
            return True
    return False


def _merge_base_ref(repo_root: Path, base_ref: str) -> str | None:
    """Point de fork (merge-base) entre HEAD et `base_ref` ; None si indeterminable.

    Sert uniquement a ORIENTER le verdict STALE_BRANCH (#22920) : savoir de quel
    cote (base ou tete) vient le deplacement d'une paire exige une ref
    ANTERIEURE aux deux. Les arbres base/tete seuls ne le peuvent pas -- les
    scenarios « paire deplacee par main, branche en retard » et « paire renommee
    par la PR » y sont des images miroir exactes (meme jeu d'observations :
    chemin du base present au base / absent de la tete, chemin de la tete
    present a la tete / absent du base). Un echec (histoires disjointes, ref
    inconnue) degrade vers le comportement existant : pas de verdict STALE_BRANCH.
    """
    r = _run_git(["git", "merge-base", "HEAD", base_ref], cwd=str(repo_root))
    if r.returncode != 0 or not r.stdout.strip():
        return None
    return r.stdout.strip()


def _stale_branch_probe(repo_root: Path, base_pp: dict, head_pp: dict,
                        base_ref: str, merge_base: str | None) -> dict | None:
    """Detecte une paire DEPLACEE par la branche base apres le fork (#22920).

    Contexte : `main` deplace une paire (O -> N) APRES le fork de la branche de
    PR. Le registre au base-ref declare N ; le registre de la tete declare
    encore O. `_classify_per_pair` ne recoit que deux STATUTS : ce cas lui est
    indiscernable d'une vraie derive, et le rebaseline `--update` prescrit sur
    ce malentendu attesterait un chemin que main a deja abandonne -- une
    attestation qui REGRESSE le registre au merge.

    Conditions (toutes requises, par cote python/csharp divergent) :

      1. chemins divergents (`_pair_paths_diverge`, deja garanti par l'appelant) ;
      2. sonde croisee : le chemin declare au BASE est absent de l'arbre de la
         TETE, OU le chemin declare par la TETE est absent du BASE (le
         deplacement fait par main a supprime l'ancien chemin) ;
      3. orientation (merge-base) : le chemin declare par la TETE existait au
         point de fork ET le chemin declare au BASE n'y existait PAS -- le
         deplacement est l'oeuvre de la branche base, pas de la PR.

    La condition 3 est le discriminateur que les sondes croisees de la condition
    2 ne peuvent pas fournir (cf `_merge_base_ref` : symetrie exacte des deux
    scenarios). Sans elle, un rename LEGITIME introduit par la PR serait
    qualifie STALE_BRANCH a tort. Un rename par la PR echoue la condition 3 :
    son nouveau chemin n'existe pas au point de fork.

    Retourne None si le cas n'est pas etabli (comportement per-pair existant) ;
    sinon {"paths_base": {...}, "paths_head": {...}} pour le rapport JSON.
    """
    for side in ("python", "csharp", "rust"):
        base_path = base_pp.get(side)
        head_path = head_pp.get(side)
        if not (isinstance(base_path, str) and isinstance(head_path, str)
                and base_path != head_path):
            continue
        # Sondes croisees (existence seulement) : la tete est-elle en retard ?
        base_path_in_head = _git_blob_sha(repo_root, base_path, "HEAD") is not None
        head_path_in_base = _git_blob_sha(repo_root, head_path, base_ref) is not None
        if base_path_in_head and head_path_in_base:
            continue  # les deux chemins existent aux deux refs : pas un deplacement
        # Orientation : le deplacement vient-il de la branche base ?
        if merge_base is None:
            continue  # point de fork inconnu -> verdict non etabli (degradation safe)
        head_path_at_fork = _git_blob_sha(repo_root, head_path, merge_base) is not None
        base_path_at_fork = _git_blob_sha(repo_root, base_path, merge_base) is not None
        if head_path_at_fork and not base_path_at_fork:
            return {
                "paths_base": {"python": base_pp.get("python"),
                               "csharp": base_pp.get("csharp")},
                "paths_head": {"python": head_pp.get("python"),
                               "csharp": head_pp.get("csharp")},
            }
    return None


# Gabarit de la commande de rebaseline : --update atteste une empreinte de
# contenu, il ne RESTAURE pas un fichier supprime (cf split_introduced_pairs).
REBASELINE_TEMPLATE = (
    'python scripts/notebook_tools/check_twin_parity.py --update --pair '
    '"%s" --by "<machine:workspace>"'
)


def split_introduced_pairs(pairs: list) -> tuple[list, list]:
    """Separe les paires DRIFT_INTRODUCED selon la remediation applicable.

    Le verdict per-pair (`_classify_per_pair`) dit que la PR a casse la parite ;
    il ne dit pas COMMENT la reparer -- et les deux remediations n'ont rien a
    voir. Le discriminant est deja dans la donnee : `head_status`, le statut de
    la paire au HEAD produit par `check_pair` (vocabulaire
    `OK / DRIFT / NUMBERING-DRIFT / MISSING`).

      - `head_status == "MISSING"` : un carnet de la paire est absent au HEAD.
        Un rebaseline (`--update --pair`) atteste une empreinte de contenu ; il
        ne restaure pas un fichier supprime -- la commande echoue ou fait un
        no-op et envoie l'agent sur une piste morte. Le lot « missing » porte
        donc le constat de suppression et les deux corrections possibles.
      - tout le reste (`DRIFT`, `NUMBERING-DRIFT`) : derive de contenu, les deux
        carnets existent et leur blob SHA a bouge -> rebaseline apres re-audit
        firsthand (comportement historique, inchange).

    Retourne `(drift, missing)` : deux listes des dicts de paire, dans l'ordre du
    rapport. Seules les paires `verdict == "DRIFT_INTRODUCED"` sont considerees
    -- c'est exactement ce que le gate rougit ; une paire pre-existante
    (`DRIFT_PRE_EXISTING`, y compris un carnet deja absent au base-ref) n'entre
    dans aucun des deux lots.
    """
    drift: list = []
    missing: list = []
    for p in pairs or []:
        if p.get("verdict") != "DRIFT_INTRODUCED":
            continue
        if p.get("head_status") == "MISSING":
            missing.append(p)
        else:
            drift.append(p)
    return drift, missing


def _missing_remediation_line(pair: dict) -> str:
    """Ligne de remediation d'une paire dont un carnet est absent au HEAD."""
    name = pair.get("name", "?")
    if pair.get("base_status") == "MISSING":
        fix = ("entree ajoutee par cette PR mais carnet absent au HEAD -- cree le "
               "carnet, ou retire l'entree du registre "
               "scripts/notebook_tools/twin_pairs.d/")
    else:
        fix = ("carnet absent au HEAD alors qu'il existait au base-ref -- SUPPRIME "
               "par cette PR : restaure le carnet dans cette PR, ou retire l'entree "
               "du registre scripts/notebook_tools/twin_pairs.d/ si la suppression "
               "est voulue")
    details = " ; ".join(pair.get("head_details") or [])
    suffix = f" ({details})" if details else ""
    return f'  [MISSING] "{name}" : {fix}.{suffix}'


def split_stale_pairs(pairs: list) -> list:
    """Paires STALE_BRANCH du rapport `--per-pair` (#22920), dans l'ordre du rapport.

    Ces paires ne sont JAMAIS comptees dans `drift_introduced` (compteur dedie
    `stale_branch`) : la derive n'est pas l'oeuvre de la PR, elle est le
    deplacement d'une paire par la branche base APRES le fork. Fonction separee
    de `split_introduced_pairs` (qui ne voit que les DRIFT_INTRODUCED) pour ne
    pas en changer l'arite -- le contrat des tests du lot missing est preserved.
    """
    return [p for p in pairs or [] if p.get("verdict") == "STALE_BRANCH"]


def _stale_remediation_line(pair: dict) -> str:
    """Ligne de remediation d'une paire deplacee par la branche base (#22920).

    Le remede est `gh pr update-branch` (reprendre le deplacement), JAMAIS un
    rebaseline : la ligne ne doit contenir NI `--update` NI `--pair` -- un
    rebaseline sur les anciens chemins ecraserait au merge la declaration a
    jour du registre de main (regression du registre, cf #22920).
    """
    name = pair.get("name", "?")
    pb = pair.get("paths_base") or {}
    ph = pair.get("paths_head") or {}
    return (
        f'  [STALE-BRANCH] "{name}" : paire DEPLACEE sur la branche base apres '
        f"le fork -- la tete declare python={ph.get('python', '?')} / "
        f"csharp={ph.get('csharp', '?')}, le base declare "
        f"python={pb.get('python', '?')} / csharp={pb.get('csharp', '?')}. "
        f"Remede : gh pr update-branch, puis rejoue le travail et l attestation "
        f"sur les NOUVEAUX chemins du base. Un rebaseline sur les anciens "
        f"chemins regresserait le registre au merge (#22920)."
    )


def render_introduced_remediation(pairs: list) -> list:
    """Lignes de remediation du gate, dans l'ordre des trois lots.

    Consomme le rapport JSON `--per-pair` (`d["pairs"]`) et rend le texte que le
    workflow imprime dans le log ET dans l'annotation ::error :

      - derive de contenu -> la commande de rebaseline, inchangee ;
      - carnet supprime  -> le constat de suppression et les deux corrections
        possibles, SANS commande de rebaseline (elle ne restaure rien) ;
      - branche perimee (#22920) -> `gh pr update-branch` + rejouer le travail
        sur les nouveaux chemins, SANS rebaseline (il attesterait un chemin que
        main a abandonne).

    Aucun lot (rapport sans paire DRIFT_INTRODUCED ni STALE_BRANCH) -> la
    commande generique historique, a nom exact a completer.
    """
    drift, missing = split_introduced_pairs(pairs)
    stale = split_stale_pairs(pairs)
    lines: list = []
    if drift:
        lines.append("Derive de contenu (rebaseline APRES re-audit firsthand) :")
        for p in drift:
            lines.append(REBASELINE_TEMPLATE % p.get("name", "?"))
    if missing:
        lines.append("Carnet SUPPRIME (aucun rebaseline ne restaure un fichier "
                     "supprime) :")
        for p in missing:
            lines.append(_missing_remediation_line(p))
    if stale:
        lines.append("Branche PERIMEE (paire deplacee sur la branche base apres "
                     "le fork -- le rebaseline y serait faux, #22920) :")
        for p in stale:
            lines.append(_stale_remediation_line(p))
    if not drift and not missing and not stale:
        lines.append(REBASELINE_TEMPLATE % "<nom exact de l entree>")
    return lines


def _paire_inconnue(nom: str, pairs: list) -> None:
    """Message d'erreur pour un `--pair` qui ne nomme aucune paire (#20197)."""
    names = sorted({pp.get("name", "?") for pp in pairs})
    print(
        f"Aucune paire nommee '{nom}'. "
        f"Noms connus : {', '.join(names[:10])}{'...' if len(names) > 10 else ''}",
        file=sys.stderr,
    )


# --- base de comparaison lue a l'execution (#22292) --------------------------
# En CI, `actions/checkout` extrait `refs/pull/N/merge` : un commit de fusion
# dont le PREMIER parent est le `main` tel qu'il etait a l'evenement, le second
# etant la tete de la PR. `origin/main` est refetch au demarrage du job. Sous
# famine de runners, `main` avance entre les deux lectures : toute paire
# rebaselinee dans l'intervalle est DRIFT au merge ref et OK a `origin/main`,
# donc classee DRIFT_INTRODUCED sur une PR qui ne la touche pas (instance
# mesuree : #22218, 11 paires dont aucune n'etait touchee ; 22 des 256 PRs
# ouvertes portaient ce rouge a leur tete).
#
# `--base auto` repond a la question que ce gate pose vraiment -- « qu'a
# introduit CETTE PR ? » -- en comparant au main dont le merge ref est issu :
# le choix ne depend plus du temps d'attente en file.
_AUTO_BASE = "auto"
# Sujet exact du commit de fusion fabrique par GitHub :
#   Merge 1ad73da1e3 into e0964ecf4a
# Le motif est un DISCRIMINANT, pas une dependance : s'il ne matche pas (sujet
# reecrit, commit de fusion pousse par l'auteur sur sa branche), on retombe sur
# `origin/main`, c'est-a-dire le comportement d'avant ce fix -- jamais une base
# plus fausse que l'ancienne.
_GITHUB_MERGE_SUBJECT = re.compile(r"^Merge [0-9a-f]{7,40} into [0-9a-f]{7,40}")


def resolve_base_ref(repo_root: Path, base: str) -> str:
    """Resout la sentinelle `auto` en une ref git reelle (#22292).

    `HEAD^1` quand `HEAD` est un commit de fusion GitHub (`refs/pull/N/merge`),
    `origin/main` sinon. Toute autre valeur est rendue inchangee : cette
    fonction n'interprete que la sentinelle.

    Un `HEAD` d'un seul parent (branche ordinaire), ou dont le sujet n'a pas la
    forme `Merge <sha> into <sha>`, n'est pas un merge ref : la base reste
    `origin/main`, soit exactement le comportement anterieur au fix.
    """
    if base != _AUTO_BASE:
        return base
    # `rev-list --parents -n 1 HEAD` : le commit puis ses parents. Deux parents
    # ou plus -> commit de fusion. Aucune exception n'est avalee ici : une pause
    # git (`GitTimeoutError`) doit interrompre la mesure en rc 3, pas se
    # deguiser en base par defaut.
    parents = _run_git(
        ["git", "rev-list", "--parents", "-n", "1", "HEAD"], cwd=repo_root
    ).stdout.split()
    if len(parents) < 3:
        return "origin/main"
    subject = _run_git(
        ["git", "log", "-1", "--format=%s", "HEAD"], cwd=repo_root
    ).stdout.strip()
    if _GITHUB_MERGE_SUBJECT.match(subject):
        return "HEAD^1"
    return "origin/main"


def main(argv=None) -> int:
    """Point d'entree CLI. Un appel git qui depasse sa borne de delai interrompt la
    mesure : message explicite sur stderr et rc 3 (distinct de 1 = drift et de
    2 = erreur de registre ou d'usage), jamais une trace brute ni un verdict vide."""
    try:
        return _main(argv)
    except GitTimeoutError as exc:
        print(f"ERREUR : {exc}", file=sys.stderr)
        return 3


def _self():
    """L'organe vu comme namespace, pour l'injection dans les modules
    freres (T7) : fonctionne quelle que soit l'identite d'import de cet
    organe -- script direct, module de package, ou importlib par chemin
    sans registration dans sys.modules (cas des tests)."""
    import types
    return types.SimpleNamespace(**globals())


def _main(argv=None) -> int:
    p = twin_parity_cli.build_parser(DEFAULT_REGISTRY, __doc__.split("\n\n")[0])
    args = twin_parity_cli.parse_and_validate(p, argv, organ=_self())

    repo_root = Path(args.repo_root) if args.repo_root else _repo_root()
    reg_path = Path(args.registry)

    # #22292 : la base du mode --per-pair se resout a l'execution. `--base` exige
    # deja `--per-pair` (validation ci-dessus), donc la sentinelle ne peut pas
    # s'inviter dans un mode qui n'en fait rien.
    if args.base == _AUTO_BASE:
        args.base = resolve_base_ref(repo_root, args.base)
        origine = ("merge ref GitHub : comparaison au main dont il est issu"
                   if args.base == "HEAD^1"
                   else "HEAD n'est pas un merge ref GitHub")
        print(f"--base auto -> '{args.base}' ({origine}, #22292)", file=sys.stderr)

    # --- Mode --summary-by-verdict (#10439) : denominateur actionnable sans
    # soustraction manuelle. Compte les paires par bridge_verdict ; les paires
    # SANS verdict sont les 'actionnables' (ni INTRINSIC ni SOTA-OK declare). ---
    if args.summary_by_verdict:
        return twin_parity_census.run_summary_by_verdict(args, organ=_self(), reg_path=reg_path)

    # --- Mode --coverage : angle mort du registre (paires jamais declarees) ---
    if args.coverage:
        return twin_parity_census.run_coverage(args, organ=_self(), reg_path=reg_path, repo_root=repo_root)

    # --- Mode --per-pair : comparaison HEAD vs base-ref ---
    if args.per_pair:
        return twin_parity_census.run_per_pair(args, organ=_self(), reg_path=reg_path, repo_root=repo_root)

    # --- Mode historique (fleet-wide) ---
    pairs = load_registry(reg_path)

    # Validation schema (#10439) : fail-loud sur bridge_verdict/parity_level
    # invalide. Une valeur hors enum ignorée silencieusement est precisement le
    # defaut que le champ structurel vient corriger (verdict invisible aux
    # detecteurs). S'applique aux modes check ET update (un update n'ecrit pas
    # non plus par-dessus un schema error).
    schema_errs = [e for pp in pairs for e in validate_pair_fields(pp)]
    if schema_errs:
        for e in schema_errs:
            print(f"SCHEMA ERROR: {e}", file=sys.stderr)
        return 2

    if args.family:
        pairs = [pp for pp in pairs if pp.get("family") == args.family]
        if not pairs:
            print(f"Aucune paire pour la famille '{args.family}'.", file=sys.stderr)

    if args.update:
        return twin_parity_attest.run_update(args, organ=_self(), reg_path=reg_path, repo_root=repo_root)

    # --- Mode --migrate-audits : reecriture file-per-audit (#14911) ---
    if args.migrate_audits:
        return twin_parity_attest.run_migrate_audits(args, p, organ=_self(), reg_path=reg_path)

    # --- Mode --verify-recorded-sha : gate CI (#9399 volet b) ---
    if args.verify_recorded_sha:
        return twin_parity_attest.run_verify_recorded_sha(args, organ=_self(), reg_path=reg_path, repo_root=repo_root, pairs=pairs)

    # --pair (#20197) : restreint --check a la paire nommee. Avant ce correctif il
    # etait accepte puis ignore : les 157 paires etaient parcourues (628 appels git
    # pour le controle d'une seule). Un nom inconnu echoue en nommant les noms
    # connus, jamais en retombant sur le registre entier.
    if args.pair is not None:
        selection = [pp for pp in pairs if pp.get("name") == args.pair]
        if not selection:
            _paire_inconnue(args.pair, pairs)
            return 2
        pairs = selection
    # Selecteur sans paire (--family inconnue, deja signalee plus haut) : rien a
    # mesurer. C'est une erreur d'usage, jamais un succes sur zero paire (#20197).
    if not pairs and (args.pair is not None or args.family):
        return 2
    results = [check_pair(repo_root, pp) for pp in pairs]
    n_ok = sum(1 for r in results if r["status"] == "OK")
    n_drift = sum(1 for r in results if r["status"] == "DRIFT")
    n_missing = sum(1 for r in results if r["status"] == "MISSING")
    n_numbering = sum(1 for r in results if r["status"] == "NUMBERING-DRIFT")

    # --- Mode --ci-strict (#9399 volet b) ---
    # Verdict dur : pour chaque paire, on detaillé le verdict legacy vs content_sha.
    # Une paire legacy (sans content_*_sha) a son blob SHA comme seule signature
    # -> un strip outille deplace le blob et fait DRIFT (faux positif du gate per-PR,
    # parce que le gate per-PR ignore le drift PRE-EXISTANT ; ici on est en fleet-wide
    # sans base-ref, on voit TOUT).
    # Une paire avec content_*_sha (volet c) -> tampon cost seul ne fait PAS DRIFT,
    # mais fix de prose / re-exec font DRIFT (verdict sincere).
    # Le cron fleet-wide survole les DEUX : utile pour detecter un worker qui a oublie
    # --update apres un strip, ou un depot SHA declare a la main devenu faux.
    if args.ci_strict:
        return twin_parity_census.run_ci_strict(args, organ=_self(), results=results, pairs=pairs, reg_path=reg_path, n_ok=n_ok, n_drift=n_drift, n_missing=n_missing)

    if args.json:
        out = {
            "registry": str(reg_path),
            "total": len(results),
            "ok": n_ok,
            "drift": n_drift,
            "missing": n_missing,
            "numbering_drift": n_numbering,
            "pairs": results,
        }
        print(json.dumps(out, ensure_ascii=False, indent=2))
    else:
        for r in results:
            tag = {"OK": "OK", "DRIFT": "DRIFT", "MISSING": "MISSING",
                   "NUMBERING-DRIFT": "NUMBERING-DRIFT"}[r["status"]]
            print(f"[{tag}] {r['name']} ({r['family']}, {r['parity_level']})")
            if r["status"] != "OK":
                for d in r["details"]:
                    print(f"       - {d}")
        print(f"\nTotal : {len(results)} paire(s) | OK={n_ok} DRIFT={n_drift} "
              f"MISSING={n_missing} NUMBERING-DRIFT={n_numbering}")

    if args.check and (n_drift > 0 or n_missing > 0 or n_numbering > 0):
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
