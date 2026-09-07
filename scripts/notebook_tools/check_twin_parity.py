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
    python check_twin_parity.py --check --per-pair --base origin/main
    python check_twin_parity.py --check --per-pair --base HEAD~1
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
         OU un ou plusieurs drift legacy/content/missing en --ci-strict --check
    2 -- erreur (registre illisible, pas un depot git)

Voir aussi
----------
- twin_pairs.d/ (registre curated file-per-entry, a cote de ce script)
- twin_pairs.d/_schema.yaml (schema + vocabulaire parity_level + historique des tranches)
- Issue #8057 (metadonnee de parite des jumeaux Python/C#)
- Issue #8264 (batch rebaseline precedent -- pattern DRIFT pre-existant)
- Issue #4208 (parent : open-courseware fiabilise/publie)
"""
from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

try:
    import yaml
except ImportError:  # pragma: no cover
    yaml = None

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


def _audit_lane_slug(by: str | None) -> str:
    """Slug d'une identite de lane (`myia-po-2024:CoursIA-2`) -> nom de fichier
    (safe : pas de `:` ni de `/`). Vide -> 'manual'."""
    s = re.sub(r"[^a-z0-9A-Z]+", "-", str(by or "manual")).strip("-")
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

        Tweety-10-MLN-Csharp.ipynb      <-> Tweety-10-MLN.ipynb          (suffixe retire)
        Sudoku-07-Norvig-Csharp.ipynb    <-> Sudoku-07-Norvig-Python.ipynb (suffixe substitue)
        SW-10-CSharp-RDFStar.ipynb      <-> SW-10-Python-RDFStar.ipynb   (position mediale)

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
    r = subprocess.run(
        ["git", "ls-files", "--", "*.ipynb"],
        cwd=repo_root, capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
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
    r = subprocess.run(
        ["git", "ls-tree", git_ref, "--", rel_path],
        capture_output=True, text=True, encoding="utf-8", errors="replace", cwd=str(repo_root),
    )
    if r.returncode != 0 or not r.stdout.strip():
        return None
    # format : "<mode> <type> <blob_sha>\t<path>"
    parts = r.stdout.split()
    if len(parts) >= 3:
        return parts[2]
    return None


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

    Cout : `rev-list --objects HEAD` parcourt tout l'historique ; le defacto
    full scan reste borne par la taille du depot (~5-10s sur CoursIA). Pour
    un seul test is_noop par paire, c'est acceptable. Une optimisation
    ulterieure (cache par ref+blob) n'est pas justifiee a c.409.
    """
    if not blob_sha or len(blob_sha) != 40:
        return False
    r = subprocess.run(
        ["git", "rev-list", "--objects", ref],
        capture_output=True, text=True, encoding="utf-8", errors="replace", cwd=str(repo_root),
    )
    if r.returncode != 0:
        return False
    # Chaque ligne de `rev-list --objects` est soit "<commit_sha>" soit
    # "<commit_sha> <blob_sha>". On grep simplement le blob SHA sur la sortie.
    return blob_sha in r.stdout


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
    r = subprocess.run(
        ["git", "show", f"{git_ref}:{rel_path}"],
        capture_output=True, cwd=str(repo_root),
    )
    if r.returncode != 0:
        return None
    return r.stdout.decode("utf-8", errors="replace")


def _load_registry_at_ref(repo_root: Path, git_ref: str, reg_path: Path) -> list:
    """Charge le registre a un ref git arbitraire (HEAD, origin/main, <sha>...).

    Robuste a la frontiere de migration #8542 : le base-ref peut etre l'ANCIEN
    mono-fichier `twin_pairs.yaml` (liste) tandis que le HEAD est le nouveau
    repertoire `twin_pairs.d/` (file-per-entry). On essaie le repertoire d'abord,
    puis on retombe sur le fichier legacy.

    Indispensable au mode `--per-pair --base origin/main` en CI : sur la PR de
    migration elle-meme, origin/main porte encore l'ancien format.
    """
    if yaml is None:
        raise SystemExit("PyYAML requis pour --per-pair.")
    try:
        reg_rel = reg_path.resolve().relative_to(repo_root).as_posix()
    except ValueError:
        reg_rel = Path(reg_path.name).as_posix()

    # (1) Le ref porte-t-il le REPERTOIRE file-per-entry ?
    r_ls = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", git_ref, "--", f"{reg_rel}/"],
        capture_output=True, text=True, encoding="utf-8", errors="replace", cwd=str(repo_root),
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
    if reg_text_base is None:
        # tente aussi le chemin absolu fourni en --registry (si c'etait un fichier)
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
    r = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
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
    """
    name = pair.get("name", "?")
    py = pair["python"]
    cs = pair["csharp"]
    audit = _latest_audit(pair)
    rec_py = audit.get("python_sha")
    rec_cs = audit.get("csharp_sha")

    cur_py = _git_blob_sha(repo_root, py, git_ref)
    cur_cs = _git_blob_sha(repo_root, cs, git_ref)

    details = []
    status = "OK"

    if cur_py is None:
        details.append(f"Python MANQUANT dans git : {py}")
        status = "MISSING"
    if cur_cs is None:
        details.append(f"C# MANQUANT dans git : {cs}")
        status = "MISSING"

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

    if status == "OK":
        # Verdict DRIFT : preferer les content_*_sha (metadata-immunes) quand
        # l'audit les enregistre ; sinon retomber sur les git blob SHA (legacy).
        # Un tampon metadata.cost seul -> content inchange -> PAS de DRIFT
        # (faux positif). Un fix de prose / re-exec -> content change -> DRIFT
        # (vrai positif, critere d'acceptation ai-01 #9399).
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
        if py_drift or cs_drift or no_baseline:
            status = "DRIFT"

    return {
        "name": name,
        "family": pair.get("family", "?"),
        "python": py,
        "csharp": cs,
        "parity_level": pair.get("parity_level", "?"),
        "bridge_verdict": pair.get("bridge_verdict"),
        "status": status,
        "current_python_sha": cur_py,
        "current_csharp_sha": cur_cs,
        "current_content_python_sha": cur_cpy,
        "current_content_csharp_sha": cur_ccs,
        "recorded_python_sha": rec_py,
        "recorded_csharp_sha": rec_cs,
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
    cur_py = _git_blob_sha(repo_root, py)
    cur_cs = _git_blob_sha(repo_root, cs)
    # content_*_sha (#9399 volet c) : SHA-256 du notebook sans nb["metadata"].
    cur_cpy = _content_sha(repo_root, py)
    cur_ccs = _content_sha(repo_root, cs)
    audit = {
        "date": date or _dt.date.today().isoformat(),
        "by": by or _latest_audit(pair).get("by", "manual"),
        "python_sha": cur_py,
        "csharp_sha": cur_cs,
        "content_python_sha": cur_cpy,
        "content_csharp_sha": cur_ccs,
    }
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
        py_orphan = rec_py is not None and not _blob_ancestor_in(repo_root, rec_py)
        cs_orphan = rec_cs is not None and not _blob_ancestor_in(repo_root, rec_cs)
        if py_orphan or cs_orphan:
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
    cur_py = _git_blob_sha(repo_root, py)
    cur_cs = _git_blob_sha(repo_root, cs)
    cur_cpy = _content_sha(repo_root, py)
    cur_ccs = _content_sha(repo_root, cs)

    # SHA enregistres dans le YAML (forme append-only ou legacy, _latest_audit
    # normalise les deux).
    rec_py = audit.get("python_sha")
    rec_cs = audit.get("csharp_sha")
    rec_cpy = audit.get("content_python_sha")
    rec_ccs = audit.get("content_csharp_sha")

    mismatches = []
    # Comparaison sur les blob SHA : compares stricte.
    if rec_py is not None and rec_py != cur_py:
        mismatches.append(
            f"python_sha: recorded={rec_py[:12]} calculated={cur_py[:12]}"
        )
    if rec_cs is not None and rec_cs != cur_cs:
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

    return {
        "name": pair.get("name", "?"),
        "family": pair.get("family", "?"),
        "parity_level": pair.get("parity_level", "?"),
        "status": "MISMATCH" if mismatches else "OK",
        "mismatches": mismatches,
        "current_python_sha": cur_py,
        "current_csharp_sha": cur_cs,
        "current_content_python_sha": cur_cpy,
        "current_content_csharp_sha": cur_ccs,
        "recorded_python_sha": rec_py,
        "recorded_csharp_sha": rec_cs,
        "recorded_content_python_sha": rec_cpy,
        "recorded_content_csharp_sha": rec_ccs,
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


def _shas_match(record: dict, new_entry: dict) -> bool:
    """True ssi `record` et `new_entry` partagent les memes SHAs de comparaison (no-op).

    Un changement **metadata-only** (ex: tampon `metadata.cost`) change les git
    blob SHAs mais PAS les `content_*_sha` : via `_cmp_pair_shas` cela devient un
    no-op, donc le `--update` n'APPEND PAS de nouvelle entree d'audit pour un
    changement qui n'est pas pedagogique (faux audit, cf ai-01 design-gate #9399).
    """
    rec_py, rec_cs = _cmp_pair_shas(record)
    new_py, new_cs = _cmp_pair_shas(new_entry)
    if new_py is None or new_cs is None:
        return False
    return str(rec_py) == str(new_py) and str(rec_cs) == str(new_cs)


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
    for key in ("python_sha", "csharp_sha"):
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
                      index: int | None = None) -> Path:
    """Ecrit un audit dans un fichier separe `<pair>/<idx>-<date>-<lane>.yaml`.

    Nouvelle forme (#14911). `index` (optionnel) place l'audit dans l'ordre
    d'append : a la migration on passe l'index d'origine (1-base), a l'ajout
    d'un nouvel audit (`--update`) il prend `count+1` pour trier en derniere
    position (= plus recent). `used_names` suit les noms deja pris pour suffixer
    `-2`, `-3`... en secours si un index venait a collider. Retourne le chemin.
    """
    slug = _slug(name)
    d = _audit_dir(registry_dir, slug)
    d.mkdir(parents=True, exist_ok=True)
    date = str(audit.get("date") or _dt.date.today().isoformat())
    by = audit.get("by")
    if index is None:
        index = len(list(d.glob("*.yaml"))) + 1
    base = _audit_filename(date, by, index)
    stem = base[:-5]  # retire ".yaml"
    used = used_names if used_names is not None else set()
    cand = base
    k = 2
    while cand in used:
        cand = f"{stem}-{k}.yaml"
        k += 1
    used.add(cand)
    path = d / cand
    path.write_text(_dump_audit_yaml(audit), encoding="utf-8", newline="")
    return path


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


def _classify_per_pair(base_status: str, head_status: str) -> str:
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
    """
    if base_status == "MISSING":
        return "OK" if head_status == "OK" else "DRIFT_INTRODUCED"
    if base_status == "OK" and head_status == "OK":
        return "OK"
    if base_status == "OK" and head_status in ("DRIFT", "MISSING", "NUMBERING-DRIFT"):
        return "DRIFT_INTRODUCED"
    if base_status in ("DRIFT", "NUMBERING-DRIFT") and head_status == "OK":
        return "DRIFT_RESOLVED"
    return "DRIFT_PRE_EXISTING"


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("--registry", default=str(DEFAULT_REGISTRY),
                   help=f"Chemin du registre YAML (defaut: {DEFAULT_REGISTRY.name})")
    p.add_argument("--repo-root", default=None,
                   help="Racine du depot git (defaut: detectee via `git rev-parse "
                        "--show-toplevel`). Utile pour les tests (mini-depot tmp_path) "
                        "et le cron CI qui pointe sur le checkout explicite.")
    p.add_argument("--family", default=None,
                   help="Restreindre a une famille (ex. SMT/Z3-API)")
    p.add_argument("--check", action="store_true",
                   help="Exit 1 si DRIFT/MISSING/NUMBERING-DRIFT detecte (CI-ready)")
    p.add_argument("--update", action="store_true",
                   help="Rebaseline : ecrit les SHAs courants comme nouveau last_audit "
                        "(a lancer APRES une audit firsthand d'une paire, ET EN DERNIER : "
                        "toute normalisation outillee ulterieure -- strip_probe_banner.py, "
                        "strip_machine_paths.py, scrub_papermill_paths.py -- deplace le "
                        "blob SHA sans toucher le contenu calcule et invaliderait cette "
                        "attestation, cf #8957). Depuis #9399 critere 2, --update "
                        "REFUSE par defaut d'ecrire une nouvelle entree d'audit si "
                        "les SHAs de comparaison sont identiques au `_latest_audit` "
                        "(no-op = faux audit, --update devient facultatif). "
                        "Utilisez --force pour outrepasser avec un avertissement.")
    p.add_argument("--json", action="store_true", help="Sortie machine JSON")
    p.add_argument("--summary-by-verdict", action="store_true",
                   help="Compte les paires par `bridge_verdict` (#10439) : SOTA-OK / "
                        "RECOVERABLE-* / INTRINSIC / (non-rompu = actionnable). "
                        "Le point du champ structurel : soustraire les verdicts "
                        "INTRINSIC/SOTA-OK du denominateur 'actionnable' SANS "
                        "intervention manuelle. Incompatible avec --update/--per-pair.")
    p.add_argument("--coverage", action="store_true",
                   help="Recense les notebooks C# versionnes NON couverts par le "
                        "registre (jumeau Python present mais paire non declaree). "
                        "Avec --check, sort 1 s'il reste des paires non enregistrees.")
    p.add_argument("--per-pair", action="store_true",
                   help="Mode per-pair : compare HEAD vs --base <ref>. Ne FAIL que "
                        "le drift INTRODUIT par la PR, jamais le drift pre-existant.")
    p.add_argument("--base", default=None,
                   help="Ref git de base pour le mode --per-pair (ex. origin/main, HEAD~1).")
    p.add_argument("--ci-strict", action="store_true",
                   help="Mode CI cron (#9399 volet b) : check fleet-wide SANS base ref, "
                        "avec breakdown 4 categories (ok_legacy / ok_content / drift_blob / "
                        "drift_content / drift_legacy_after_content / missing_python / "
                        "missing_csharp / no_audit). Combine avec --check pour FAIL sur N'IMPORTE "
                        "QUEL drift (vs la semantique 'DRIFT_or_MISSING only' historique). "
                        "Distingue erreur d'outil vs constat de drift (cf L948/L949, c.1240).")
    p.add_argument("--pair", default=None,
                   help="Restreindre --update a une paire nommee (ex. 'Search-9-LP'). "
                        "Impossible a combiner avec --family.")
    p.add_argument("--yes-all-pairs", action="store_true",
                   help="Opt-in explicite pour rebaseline TOUTES les paires du registre "
                        "avec --update. Sans ce flag (ou --family/--pair), --update refuse.")
    p.add_argument("--by", default=None,
                   help="Auteur de l'audit inscrit dans last_audit.by (ex. "
                        "'myia-po-2024:CoursIA-2'). Avec --update, la date est "
                        "TOUJOURS mise a aujourd'hui : sans --by, l'entree garderait "
                        "l'auteur de l'audit precedent alors que les SHAs sont neufs.")
    p.add_argument("--force", action="store_true",
                   help="Avec --update : outrepasser la detection no-op (cf #9399 "
                        "critere 2). Par defaut, --update REFUSE d'ecrire une "
                        "nouvelle entree d'audit si les SHAs de comparaison sont "
                        "identiques au `_latest_audit` (--update devient "
                        "facultatif : la CI derive elle-meme les SHAs depuis "
                        "volet b, un rebaseline manuel identique n'apporte aucune "
                        "information nouvelle et serait un faux audit). --force "
                        "est l'opt-in explicite pour forcer la nouvelle entree "
                        "malgre le no-op, avec un avertissement explicite sur "
                        "stdout. Sans effet sur les modes non --update.")
    p.add_argument("--verify-recorded-sha", action="store_true",
                   help="Gate CI #9399 volet b : verifie que les SHA enregistres "
                        "dans le YAML (last_audit legacy OU audits[-1] append-only) "
                        "correspondent aux SHA recalcules a HEAD (git ls-tree + "
                        "SHA-256 metadata-immune). Exit 1 si MISMATCH sur au moins "
                        "une paire (avec --check). Mode read-only : n'ecrit rien.")
    p.add_argument("--migrate-audits", action="store_true",
                   help="Reecrit le registre en forme file-per-audit (#14911) : "
                        "chaque audit migre vers `twin_pairs.d/<pair>/<date>-<lane>.yaml` "
                        "et la liste `audits:`/`last_audit:` est retiree du fichier "
                        "d'intention. Exige un selecteur (--pair / --family / "
                        "--yes-all-pairs) pour eviter une invocation nue qui "
                        "reecrirait les 157 paires (cf #8508).")
    args = p.parse_args(argv)

    # Cross-validation : --per-pair <-> --base
    if args.coverage and (args.update or args.per_pair or args.base or args.verify_recorded_sha):
        p.error("--coverage est un mode de recensement seul : incompatible avec "
                "--update / --per-pair / --base / --verify-recorded-sha.")
    if args.summary_by_verdict and (args.update or args.per_pair or args.base
                                    or args.verify_recorded_sha or args.coverage):
        p.error("--summary-by-verdict est un mode de recensement seul : incompatible "
                "avec --update / --per-pair / --base / --verify-recorded-sha / --coverage.")
    if args.per_pair and not args.base:
        p.error("--per-pair necessite --base <ref>")
    if args.base and not args.per_pair:
        p.error("--base necessite --per-pair")
    if args.update and (args.per_pair or args.base or args.verify_recorded_sha):
        p.error("--update est incompatible avec --per-pair/--base/--verify-recorded-sha")
    if args.verify_recorded_sha and (args.per_pair or args.base or args.update):
        p.error("--verify-recorded-sha est read-only : incompatible avec "
                "--update/--per-pair/--base.")
    # --update exige un selecteur (anti-corruption silencieuse du registre, cf #8508)
    if args.update and not (args.family or args.pair or args.yes_all_pairs):
        p.error("--update exige un selecteur explicite : --family <f>, --pair <name>, "
                "OU --yes-all-pairs. Le defaut '--update' seul reecrirait le last_audit "
                "de TOUTES les paires du registre, ce qui masque des DRIFTs legitimes "
                "(cf issue #8508 + lecons L963/L974).")
    # --migrate-audits est un mode de reecriture structurelle exclusive (#14911) :
    # le selecteur est deja obligatoire (bloc d'execution), et il est incompatible
    # avec les autres modes d'ecriture/conservation.
    if args.migrate_audits and (args.update or args.per_pair or args.base
                                or args.verify_recorded_sha or args.coverage
                                or args.summary_by_verdict or args.ci_strict):
        p.error("--migrate-audits est un mode exclusif : incompatible avec "
                "--update / --per-pair / --base / --verify-recorded-sha / "
                "--coverage / --summary-by-verdict / --ci-strict.")
    # Garde anti-derive MERGE_HEAD / REBASE_HEAD (#11732) : pendant un merge non
    # commite, `git ls-tree HEAD` lit l'ANCIENNE tete de branche (pas le resultat
    # du merge). --update atteste alors des blob SHAs qui ne refletent pas l'etat
    # final du notebook -- au commit du merge, les notebooks obtiennent de
    # nouveaux blobs, et l'attestation fraichement ecrite est deja DRIFT avant
    # meme que la CI ne la voie. Variante operationnelle de #8957 (« attester
    # en DERNIER ») : le commit du merge lui-meme deplace le blob apres
    # attestation. Refus : on commit d'abord, puis on re-atteste.
    if args.update:
        try:
            if args.repo_root:
                repo_root_for_state = Path(args.repo_root)
            else:
                repo_root_for_state = _repo_root()
        except SystemExit:
            repo_root_for_state = None
        if repo_root_for_state is not None:
            # git rev-parse -q --verify MERGE_HEAD/REBASE_HEAD : rc=0 si le
            # depot est en cours de merge/rebase interactif. Le check precede
            # `_repo_root()` final pour economiser un subprocess en cas d'erreur
            # deja connue (mais apres args.repo_root parse, qui peut etre override
            # dans les tests --repo-root sur tmp_path).
            for state_file, label in (("MERGE_HEAD", "merge"), ("REBASE_HEAD", "rebase")):
                r = subprocess.run(
                    ["git", "rev-parse", "-q", "--verify", state_file],
                    capture_output=True, text=True, encoding="utf-8", errors="replace", cwd=str(repo_root_for_state),
                )
                if r.returncode == 0:
                    p.error(f"--update pendant un {label} non committe : HEAD ne contient pas "
                            f"le resultat du {label}. Commitez d'abord, puis re-attestez "
                            f"(cf #11732, variante operationnelle de #8957).")
    if args.pair and args.family:
        p.error("--pair et --family sont mutuellement exclusifs avec --update.")
    if args.ci_strict and args.per_pair:
        p.error("--ci-strict est un mode fleet-wide SANS base ref : incompatible avec --per-pair.")
    if args.ci_strict and args.update:
        p.error("--ci-strict est un mode read-only : incompatible avec --update.")
    # Cross-validation --ci-strict x --verify-recorded-sha (#9481, post-rebase c.984) :
    # les deux sont des modes fleet-wide read-only avec des sorties JSON disjointes
    # (breakdown 4 categories vs recorded-vs-HEAD mismatch). Les coupler en CLI
    # melange deux verdicts dans la meme invocation, ce qui rend le choix du
    # categoriel d'echec ambigu pour le mainteneur. Le cron les lance separement
    # (twin-parity-cron.yml pour --ci-strict, twin-parity-sha-mismatch du
    # twin-parity.yml #9481 pour --verify-recorded-sha). Mutuellement exclusifs.
    if args.ci_strict and args.verify_recorded_sha:
        p.error("--ci-strict et --verify-recorded-sha sont deux modes fleet-wide "
                "read-only avec des sorties JSON disjointes : incompatibles. "
                "Lancer l'un ou l'autre, pas les deux (le cron les dispatch separement).")

    repo_root = Path(args.repo_root) if args.repo_root else _repo_root()
    reg_path = Path(args.registry)

    # --- Mode --summary-by-verdict (#10439) : denominateur actionnable sans
    # soustraction manuelle. Compte les paires par bridge_verdict ; les paires
    # SANS verdict sont les 'actionnables' (ni INTRINSIC ni SOTA-OK declare). ---
    if args.summary_by_verdict:
        pairs = load_registry(reg_path)
        # Fail-loud sur un bridge_verdict invalide avant de resumer : un resume
        # qui ignore silencieusement une valeur hors enum est le defaut meme
        # que #10439 vient corriger.
        schema_errs = [e for pp in pairs for e in validate_pair_fields(pp)]
        if schema_errs:
            for e in schema_errs:
                print(f"SCHEMA ERROR: {e}", file=sys.stderr)
            return 2
        counts: dict = {}
        names_by: dict = {}
        for pp in pairs:
            bv = pp.get("bridge_verdict", "(non-rompu)")
            counts[bv] = counts.get(bv, 0) + 1
            names_by.setdefault(bv, []).append(pp.get("name", "?"))
        actionable = sum(c for k, c in counts.items()
                         if k not in ("INTRINSIC", "SOTA-OK"))
        if args.json:
            print(json.dumps({
                "mode": "summary_by_verdict",
                "registry": str(reg_path),
                "total": len(pairs),
                "counts": counts,
                "actionable": actionable,
            }, ensure_ascii=False, indent=2))
        else:
            order = ["(non-rompu)", "SOTA-OK", "RECOVERABLE-LOCAL",
                     "RECOVERABLE-MACHINE", "RECOVERABLE-USER-HAND", "INTRINSIC"]
            shown = [k for k in order if k in counts] + sorted(set(counts) - set(order))
            print(f"Summary by bridge_verdict ({len(pairs)} paires) :")
            for k in shown:
                tag = " ACTIONNABLE" if k not in ("INTRINSIC", "SOTA-OK") else ""
                print(f"  {k:<22} {counts[k]:>3}{tag}")
            print(f"  {'actionnables (a bridger)':<22} {actionable:>3}"
                  f"  = total - INTRINSIC - SOTA-OK")
        return 0

    # --- Mode --coverage : angle mort du registre (paires jamais declarees) ---
    if args.coverage:
        cov = scan_coverage(repo_root, load_registry(reg_path))
        n_unreg, n_only = len(cov["unregistered"]), len(cov["csharp_only"])
        if args.json:
            print(json.dumps(cov, ensure_ascii=False, indent=2))
        else:
            for e in cov["unregistered"]:
                print(f"[UNREGISTERED] {e['csharp']}")
                for c in e["python_candidates"]:
                    print(f"        <-> {c}")
            for e in cov["csharp_only"]:
                print(f"[CSHARP-ONLY]  {e['csharp']}")
            print(
                f"\nNotebooks C# versionnes : {cov['csharp_tracked']} | "
                f"enregistres={cov['registered']} "
                f"NON-ENREGISTRES={n_unreg} C#-only={n_only}"
            )
            if n_unreg:
                print(
                    f"\n{n_unreg} paire(s) reelle(s) hors registre : invisibles au "
                    f"gate de derive tant qu'elles n'y sont pas declarees.\n"
                    f"Enregistrer par tranche APRES audit de parite firsthand "
                    f"(cf #8057), jamais en masse."
                )
        return 1 if (args.check and n_unreg) else 0

    # --- Mode --per-pair : comparaison HEAD vs base-ref ---
    if args.per_pair:
        # Charge le registre a HEAD (working tree) et au base-ref (git show).
        # Le base-ref peut porter l'ancien mono-fichier (frontiere de migration
        # #8542) -> _load_registry_at_ref essaie le repertoire puis retombe sur
        # le fichier legacy.
        pairs_head = load_registry(reg_path)
        pairs_base = _load_registry_at_ref(repo_root, args.base, reg_path)
        # Index par nom (au cas ou l'ordre ou les ajouts/suppressions different)
        base_by_name = {pp.get("name", "?"): pp for pp in pairs_base}

        if args.family:
            pairs_head = [pp for pp in pairs_head if pp.get("family") == args.family]
            if not pairs_head:
                print(f"Aucune paire pour la famille '{args.family}'.", file=sys.stderr)

        results = []
        for pp in pairs_head:
            name = pp.get("name", "?")
            head_state = check_pair(repo_root, pp, git_ref="HEAD")
            base_pp = base_by_name.get(name)
            if base_pp is None:
                # Paire ajoutee par la PR -> si elle n'est PAS OK au HEAD, c'est du drift introduit
                base_status = "MISSING"
                base_details = [f"Paire '{name}' absente du registre au base-ref '{args.base}' (ajoutee par la PR)"]
            else:
                base_check = check_pair(repo_root, base_pp, git_ref=args.base)
                base_status = base_check["status"]
                base_details = base_check["details"]

            head_status = head_state["status"]
            # Classification per-pair (cf _classify_per_pair -- le cas paire ajoutee
            # est special : pas d'etat pre-existant, l'etat HEAD = ce que la PR introduit).
            verdict = _classify_per_pair(base_status, head_status)

            results.append({
                "name": name,
                "family": pp.get("family", "?"),
                "parity_level": pp.get("parity_level", "?"),
                "base_ref": args.base,
                "base_status": base_status,
                "head_status": head_status,
                "verdict": verdict,
                "base_details": base_details,
                "head_details": head_state["details"],
            })

        n_ok = sum(1 for r in results if r["verdict"] == "OK")
        n_introduced = sum(1 for r in results if r["verdict"] == "DRIFT_INTRODUCED")
        n_resolved = sum(1 for r in results if r["verdict"] == "DRIFT_RESOLVED")
        n_pre_existing = sum(1 for r in results if r["verdict"] == "DRIFT_PRE_EXISTING")

        if args.json:
            out = {
                "mode": "per_pair",
                "registry": str(reg_path),
                "base_ref": args.base,
                "total": len(results),
                "ok": n_ok,
                "drift_introduced": n_introduced,
                "drift_resolved": n_resolved,
                "drift_pre_existing": n_pre_existing,
                "pairs": results,
            }
            print(json.dumps(out, ensure_ascii=False, indent=2))
        else:
            tag_map = {
                "OK": "OK",
                "DRIFT_INTRODUCED": "DRIFT-INTRO",
                "DRIFT_RESOLVED": "DRIFT-FIXED",
                "DRIFT_PRE_EXISTING": "DRIFT-PRE",
            }
            for r in results:
                tag = tag_map[r["verdict"]]
                print(f"[{tag}] {r['name']} ({r['family']}, {r['parity_level']}) "
                      f"base={r['base_status']} head={r['head_status']}")
                if r["verdict"] != "OK":
                    for d in r["head_details"]:
                        print(f"       HEAD: {d}")
            print(f"\nTotal : {len(results)} paire(s) | "
                  f"OK={n_ok} INTRO={n_introduced} FIXED={n_resolved} PRE={n_pre_existing}")

        if args.check and n_introduced > 0:
            if args.per_pair:
                # Le DRIFT d'une normalisation outillee (strip_probe_banner.py --apply,
                # strip_machine_paths.py, scrub_papermill_paths.py) deplace le blob SHA
                # SANS toucher le contenu calcule : la parite est vraie, c'est son
                # empreinte qui a bouge. Dans ce cas le rebaseline --update va EN DERNIER,
                # apres ces strips, sinon l'attestation est invalidee par le strip qui suit
                # (piege naturel, #8957).
                #
                # Ce rappel est un DIAGNOSTIC destine a l'humain : il va sur stderr, pas stdout.
                # En mode --json, stdout est un contrat machine (un unique objet JSON consomme
                # par le workflow CI via json.load) ; imprimer ce rappel sur stdout apres le
                # JSON -> json.load levait "Extra data" et faisait tomber le gate en raw
                # traceback (PRs #9097/#9098, exit 1 sur drift introduit). stderr reste visible
                # dans les logs CI sans corrompre le rapport.
                print(
                    "\nRappel : si le DRIFT vient d'une normalisation outillee qui "
                    "deplace le blob SHA (strip_probe_banner.py --apply, "
                    "strip_machine_paths.py, scrub_papermill_paths.py), le rebaseline "
                    "--update va EN DERNIER, apres ces strips -- attester PUIS "
                    "stripper invalide l'attestation (#8957).",
                    file=sys.stderr,
                )
            return 1
        return 0

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
        # Selecteur obligatoire depuis c.909 (#8508) : --family OU --pair OU
        # --yes-all-pairs. Sans lui, --update rebaselinerait les 116 paires et
        # masquerait des DRIFTs legitimes.
        all_pairs = load_registry(reg_path)
        if args.pair:
            target = [pp for pp in all_pairs if pp.get("name") == args.pair]
            if not target:
                names = sorted({pp.get("name", "?") for pp in all_pairs})
                print(
                    f"Aucune paire nommee '{args.pair}'. "
                    f"Noms connus : {', '.join(names[:10])}{'...' if len(names) > 10 else ''}",
                    file=sys.stderr,
                )
                return 1
        elif args.family:
            target = [pp for pp in all_pairs if pp.get("family") == args.family]
            if not target:
                print(f"Aucune paire pour la famille '{args.family}'.", file=sys.stderr)
        else:
            # --yes-all-pairs (filet anti-corruption silencieuse, cf #8508)
            target = all_pairs
        updates: dict[str, dict] = {}
        skipped: list[str] = []
        # No-op detection (#9399 critere 2) : un rebaseline qui n'apporte
        # aucune information nouvelle (SHAs de comparaison identiques au
        # `_latest_audit`) est un "faux audit" -- dater une attestation
        # identique. On les distingue pour les compter separement et (sans
        # --force) refuser de les ecrire.
        no_op: list[str] = []
        forced_no_op: list[str] = []
        for pp in target:
            audit, cur_py, is_noop = update_pair(repo_root, pp, by=args.by)
            if cur_py is None:
                skipped.append(pp.get("name", "?"))
                continue
            if is_noop and not args.force:
                # Refuse par defaut : message comprehensible + n'ecrit rien.
                # Le worker peut relancer avec --force s'il a une raison
                # explicite de re-attester (rare, mais legitime).
                no_op.append(pp.get("name", "?"))
                continue
            if is_noop and args.force:
                forced_no_op.append(pp.get("name", "?"))
            updates[pp["name"]] = audit
        # Rebaseline CHIRURGICAL (#8570) : seules les lignes d'audit des paires
        # ciblees changent. En mode file-per-entry (#8542) + file-per-audit
        # (#14911), on ecrit CHAQUE audit dans son propre fichier
        # `<pair>/<idx>-<date>-<lane>.yaml` (un ajout, pas un remplacement
        # d'historique) et on retire la liste `audits:` du fichier d'intention.
        # Pour le mono-fichier legacy, on conserve `surgical_rebaseline`
        # (append chirurgical au bloc d'audit inline).
        if reg_path.is_dir():
            written = 0
            for name, audit in updates.items():
                pfile = _pair_file(reg_path, name)
                if not pfile.exists():
                    print(f"Aucun fichier pour la paire '{name}' "
                          f"(attendu : {pfile.name}).", file=sys.stderr)
                    continue
                # Nouvelle forme file-per-audit (#14911) : on ecrit chaque audit
                # dans un fichier separe `<pair>/<idx>-<date>-<lane>.yaml`, puis
                # on retire la liste `audits:`/`last_audit:` du fichier
                # d'intention `<pair>.yaml` (le lecteur reconstitue `audits:`
                # depuis les fichiers separes -- voir `load_registry`).
                #
                # Anti-regression (paire non encore migree) : si le fichier
                # d'intention porte ENCORE des audits inline, on les migre
                # d'abord vers des fichiers (indices 1..N) AVANT d'appender le
                # nouvel audit (sinon `_strip_audits_from_yaml` les perdrait :
                # seuls les fichiers restants seraient relus). Sur une paire deja
                # migree (intention sans audits), `_write_audit_file` appende au
                # prochain slot (index=None -> count+1).
                raw = pfile.read_text(encoding="utf-8")
                inline = _inline_audits_of(raw)
                if inline:
                    used: set[str] = set()
                    # Migre les audits inline existants (1..len(inline)).
                    for idx, a in enumerate(inline, start=1):
                        _write_audit_file(reg_path, name, a,
                                          used_names=used, index=idx)
                    _write_audit_file(reg_path, name, audit,
                                      used_names=used, index=len(inline) + 1)
                else:
                    _write_audit_file(reg_path, name, audit)
                new_raw = _strip_audits_from_yaml(raw)
                if new_raw != raw:
                    write_registry_text(pfile, new_raw)
                written += 1
            updated = written
        else:
            # mono-fichier legacy (--registry <file.yaml>)
            raw = reg_path.read_text(encoding="utf-8")
            new_raw, updated = surgical_rebaseline(raw, updates, force=args.force)
            write_registry_text(reg_path, new_raw)
            if updated < len(updates):
                print(
                    f"AVERTISSEMENT : {len(updates) - updated} paire(s) a "
                    f"rebaseliner sans bloc d'audit reconnu dans {reg_path.name} "
                    f"-- rebaseline IGNORE pour elles (header introuvable).",
                    file=sys.stderr,
                )
        if skipped:
            print(
                f"Ignorees (notebook absent de git) : {', '.join(skipped)}",
                file=sys.stderr,
            )
        # Bilan no-op vs reelles (#9399 critere 2) -- informe le worker de
        # la portee reelle de sa commande. Sans --force, les paires no-op ne
        # sont PAS ecrites ; le worker voit la liste et peut relancer --force
        # s'il a une raison explicite de re-attester.
        if no_op:
            print(
                f"Refusees (no-op, --update facultatif post-volet-b : les SHAs "
                f"enregistres sont deja ceux du carnet a HEAD) : "
                f"{', '.join(no_op)}",
                file=sys.stderr,
            )
        if forced_no_op:
            print(
                f"ATTENTION --force : {len(forced_no_op)} paire(s) no-op "
                f"ecrite(s) avec une nouvelle entree d'audit identique au "
                f"_latest_audit precedent : {', '.join(forced_no_op)}. "
                f"Cela produit un faux audit au sens du design-gate #9399 "
                f"critere 2 (dater une attestation sans information nouvelle). "
                f"Verifiez que c'est bien votre intention.",
                file=sys.stderr,
            )
        msg = f"Registre rebaseline : {updated} paire(s) mise(s) a jour -> {reg_path}"
        print(msg)
        # Rappel d'ordre (#8957) : ce rebaseline est l'attestation des SHAs courants.
        # Il va EN DERNIER -- si un strip outille (strip_probe_banner.py --apply,
        # strip_machine_paths.py, scrub_papermill_paths.py) edite le notebook APRES
        # ce point, le blob SHA deplace et le gate --per-pair sortira DRIFT-INTRO
        # sur la prochaine PR (la parite est vraie, c'est son empreinte qui a bouge).
        print(
            "Rappel : cette attestation est celle du notebook TEL QU'IL EST MAINTENANT. "
            "Tout strip outille ulterieur deplace le blob SHA -- si vous devez "
            "normaliser (strip_probe_banner / strip_machine_paths / scrub_papermill), "
            "refaites --update en dernier, apres (cf #8957)."
        )
        # Exit code (#10430 acceptance) :
        #   0 = ecrit OK (peut inclure des no_op informes sur stderr)
        #   1 = au moins une paire DEMANDEE n'a pas pu etre ecrite parce que
        #       son bloc d'audit etait introuvable / indentation non reconnue.
        #       L'AVERTISSEMENT ci-dessus a deja liste les paires concernees ;
        #       l'exit non-zero est le signal que le worker doit inspecter
        #       l'indentation et relancer --update (ou investiguer le fichier).
        #   2 = aucun nom de paire trouve (path `Aucune paire nommee` plus haut).
        # Le commentaire historique qui disait « 0 meme si toutes les cibles
        # etaient no-op » est REVOQUE ici : un worker qui voit exit=0 et 0
        # ligne ecrite conclut legitimement « rien a faire ». Si le probleme
        # reel est que le scanner est aveugle (entrees manquees), c'est
        # INVISIBLE. L'exit 1 ferme la boucle.
        # Garder la garde sur les paires skippees (`notebook absent de git`)
        # en dehors de cette logique : ce n'est PAS un failed-rebaseline, juste
        # une mise en garde environnementale.
        # #10430 exit 1 : un rebaseline IGNORE (header d'audit introuvable /
        # indentation non reconnue) ne doit pas laisser le worker conclure
        # « rien a faire ». Ce mode d'echec est propre au mono-fichier legacy :
        # en mode file-per-audit (#14911) il n'existe plus de header inline a
        # manquer -- les audits sont des fichiers (glob, jamais aveugles).
        if not reg_path.is_dir() and updated < len(updates):
            return 1
        return 0

    # --- Mode --migrate-audits : reecriture file-per-audit (#14911) ---
    if args.migrate_audits:
        # Selecteur obligatoire (replique la politique --update, cf #8508) :
        # une invocation nue reecrirait les 157 paires du registre. L'invocation
        # --pair / --family / --yes-all-pairs borne la migration (migrer une
        # tranche est utile pour tester la forme sur une seule famille avant
        # de committer l'ensemble).
        if not (args.family or args.pair or args.yes_all_pairs):
            p.error("--migrate-audits exige un selecteur explicite : --family <f>, "
                    "--pair <name>, OU --yes-all-pairs. Une invocation nue "
                    "reecrirait les 157 paires (cf #8508).")
        if reg_path is None or not reg_path.is_dir():
            p.error("--migrate-audits ne s'applique qu'au registre en forme "
                    "file-per-entry (--registry <dir> avec twin_pairs.d/) ; "
                    "le mono-fichier legacy n'a pas de sous-repertoires.")
        all_pairs = load_registry(reg_path)
        if args.pair:
            target = [pp for pp in all_pairs if pp.get("name") == args.pair]
            if not target:
                names = sorted({pp.get("name", "?") for pp in all_pairs})
                print(
                    f"Aucune paire nommee '{args.pair}'. "
                    f"Noms connus : {', '.join(names[:10])}{'...' if len(names) > 10 else ''}",
                    file=sys.stderr,
                )
                return 1
            sel_names = {args.pair}
        elif args.family:
            target = [pp for pp in all_pairs if pp.get("family") == args.family]
            if not target:
                print(f"Aucune paire pour la famille '{args.family}'.", file=sys.stderr)
                return 1
            sel_names = {pp.get("name") for pp in target}
        else:
            target = all_pairs
            sel_names = None
        result = migrate_registry_files_per_audit(reg_path, names=sel_names)
        print(
            f"Registre migre vers file-per-audit (#14911) : "
            f"{result['migrated']} paire(s) traitee(s), "
            f"{result['audits_moved']} audit(s) deplace(s) vers "
            f"{reg_path}/<pair>/<date>-<lane>.yaml."
        )
        return 0

    # --- Mode --verify-recorded-sha : gate CI (#9399 volet b) ---
    if args.verify_recorded_sha:
        # Accepte --family comme selecteur (replique la politique --update) :
        # en CI on cible generalement tout le registre, mais un audit local peut
        # vouloir borner a une famille.
        target_pairs = pairs
        if args.family:
            target_pairs = [pp for pp in target_pairs if pp.get("family") == args.family]
            if not target_pairs:
                print(
                    f"Aucune paire pour la famille '{args.family}'.",
                    file=sys.stderr,
                )
                # En --check ce serait un gate casse ; ici on retourne 2
                # (distinct de 1=MISMATCH, 0=clean) pour discriminer le cas.
                return 2

        results = [verify_recorded_sha(repo_root, pp) for pp in target_pairs]
        n_ok = sum(1 for r in results if r["status"] == "OK")
        n_mismatch = sum(1 for r in results if r["status"] == "MISMATCH")
        n_no_audit = sum(1 for r in results if r["status"] == "NO_AUDIT")

        if args.json:
            out = {
                "mode": "verify_recorded_sha",
                "registry": str(reg_path),
                "total": len(results),
                "ok": n_ok,
                "mismatch": n_mismatch,
                "no_audit": n_no_audit,
                "pairs": results,
            }
            print(json.dumps(out, ensure_ascii=False, indent=2))
        else:
            tag_map = {"OK": "OK", "MISMATCH": "MISMATCH", "NO_AUDIT": "NO_AUDIT"}
            for r in results:
                if r["status"] == "OK":
                    continue  # ne pas bruiter les OK en sortie humaine
                tag = tag_map[r["status"]]
                print(f"[{tag}] {r['name']} ({r.get('family','?')})")
                for m in r.get("mismatches", []):
                    print(f"       - {m}")
            print(
                f"\nTotal : {len(results)} paire(s) | "
                f"OK={n_ok} MISMATCH={n_mismatch} NO_AUDIT={n_no_audit}"
            )

        if args.check and n_mismatch > 0:
            # Gate CI : un seul mismatch = RED. Message d'erreur oriente
            # l'auteur vers --update (le seul moyen legitime de resoudre :
            # l'audit firsthand + rebaseline, cf #8508 selector policy).
            print(
                f"::error title=Twin parity SHA mismatch (#9399 volet b)::"
                f"{n_mismatch} paire(s) ont un SHA enregistre dans le YAML qui ne "
                f"correspond pas au SHA reel du carnet a HEAD. L'integrite du "
                f"registre est corrompue (sha invente / stale / modifie a la "
                f"main). Remediation : lancer "
                f"`python scripts/notebook_tools/check_twin_parity.py --update "
                f"--pair \"<nom>\" --by \"<machine:workspace>\"` APRES audit "
                f"firsthand de la parite. Le selecteur --pair est obligatoire "
                f"(cf #8508).",
                file=sys.stderr,
            )
            return 1
        return 0

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
        # Breakdown par categorie : legacy vs content vs missing vs ok
        cat = {
            "n_ok_legacy": 0,             # blob SHA match, pas de content_sha enregistre
            "n_ok_content": 0,            # content_sha match (volet c)
            "n_drift_blob": 0,            # legacy blob SHA mismatch
            "n_drift_content": 0,         # content_sha mismatch
            "n_drift_legacy_after_content": 0,  # legacy blob drift mais content_sha OK
                                             # = strip outille detecte
            "n_missing_python": 0,
            "n_missing_csharp": 0,
            "n_no_audit": 0,              # paire sans audits ni last_audit
            "n_numbering_drift": 0,       # numeros de base distincts (#12933)
        }
        ci_results = []
        for pp, r in zip(pairs, results):
            audit = _latest_audit(pp)
            rec_py = audit.get("python_sha")
            rec_cs = audit.get("csharp_sha")
            rec_cpy = audit.get("content_python_sha")
            rec_ccs = audit.get("content_csharp_sha")
            cur_py = r["current_python_sha"]
            cur_cs = r["current_csharp_sha"]
            cur_cpy = r["current_content_python_sha"]
            cur_ccs = r["current_content_csharp_sha"]

            entry_ci = {
                "name": r["name"],
                "family": r["family"],
                "parity_level": r["parity_level"],
                "status": r["status"],
                "details": list(r["details"]),
                "has_content_sha_audit": bool(rec_cpy and rec_ccs),
            }

            # NUMBERING-DRIFT (#12933) : compte dans SA categorie, sans
            # re-classer la paire dans les buckets SHA (blob/content) -- une
            # paire renumerotee unilateralement est rouge pour une raison qui
            # n'a rien a voir avec l'attestation d'empreinte, et la double
            # comptabilisation (ex. no_audit en plus) fausserait chaque
            # categorie.
            if r["status"] == "NUMBERING-DRIFT":
                cat["n_numbering_drift"] += 1
                ci_results.append(entry_ci)
                continue

            if not audit:
                cat["n_no_audit"] += 1
                ci_results.append(entry_ci)
                continue

            py_missing = (cur_py is None)
            cs_missing = (cur_cs is None)
            if py_missing:
                cat["n_missing_python"] += 1
            if cs_missing:
                cat["n_missing_csharp"] += 1

            blob_py_drift = (not py_missing and rec_py and cur_py != rec_py)
            blob_cs_drift = (not cs_missing and rec_cs and cur_cs != rec_cs)
            content_py_drift = (rec_cpy and cur_cpy and cur_cpy != rec_cpy)
            content_cs_drift = (rec_ccs and cur_ccs and cur_ccs != rec_ccs)

            if entry_ci["has_content_sha_audit"]:
                if content_py_drift or content_cs_drift:
                    cat["n_drift_content"] += 1
                elif blob_py_drift or blob_cs_drift:
                    # Churn metadata-only carnet : INFORMATIF, jamais bloquant.
                    # `_content_sha` hache les cellules ET leurs outputs, en
                    # n'excluant que `nb["metadata"]` (cost / papermill /
                    # kernelspec / language_info). Donc « blob bouge, content
                    # identique » ne peut signifier QUE du churn de metadata
                    # carnet -- exactement le faux positif que le volet c a ete
                    # construit pour tuer (cf docstring de `_content_sha`).
                    # Rougir ici le re-fabriquerait au niveau du cron : incident
                    # du 2026-08-07, cron rouge sur main pour Sudoku-08/14 BDD --
                    # les 2 paires nommees dans cette meme docstring -- avec un
                    # `::error ...::<none>` qui ne designait aucune paire (leur
                    # `status` reste OK, donc `_cron_extract_drift` n'en listait
                    # aucune). Et le remede prescrit (`--update`) est un NO-OP
                    # par design puisque `_shas_match` compare les content_sha :
                    # un gate que son propre remede ne peut pas eteindre.
                    cat["n_drift_legacy_after_content"] += 1
                    entry_ci["metadata_only_blob_drift"] = True
                    entry_ci["details"].append(
                        "blob SHA drift MAIS content_sha OK : churn metadata-only "
                        "(metadata.cost / papermill / kernelspec) -- aucune divergence "
                        "pedagogique. INFORMATIF : ne fait pas rougir le gate. "
                        "`--update` est un no-op par design ici (il compare les "
                        "content_sha) ; re-tamponner le blob SHA exigerait --force et "
                        "n'apporterait aucune information nouvelle (cf #9399 critere 2)."
                    )
                else:
                    cat["n_ok_content"] += 1
            else:
                if blob_py_drift or blob_cs_drift:
                    cat["n_drift_blob"] += 1
                else:
                    cat["n_ok_legacy"] += 1

            ci_results.append(entry_ci)

        # Anomalies BLOQUANTES (celles qui font rougir le gate).
        # `n_drift_legacy_after_content` en est volontairement EXCLU : blob
        # bouge + content identique == churn metadata-only, informatif (cf la
        # classification ci-dessus). `n_total_drift` reste le total de TOUTES
        # les anomalies, pour le reporting.
        n_blocking_drift = (cat["n_drift_blob"] + cat["n_drift_content"]
                            + cat["n_missing_python"] + cat["n_missing_csharp"]
                            + cat["n_no_audit"] + cat["n_numbering_drift"])
        n_total_drift = n_blocking_drift + cat["n_drift_legacy_after_content"]

        if args.json:
            out = {
                "mode": "ci_strict",
                "registry": str(reg_path),
                "total": len(ci_results),
                "ok_total": n_ok,
                "drift_total": n_drift,
                "missing_total": n_missing,
                "ci_strict": cat,
                "n_total_drift": n_total_drift,
                "n_blocking_drift": n_blocking_drift,
                "pairs": ci_results,
            }
            print(json.dumps(out, ensure_ascii=False, indent=2))
        else:
            print(f"[CI-STRICT] {len(ci_results)} paire(s) | "
                  f"ok_legacy={cat['n_ok_legacy']} ok_content={cat['n_ok_content']} "
                  f"drift_blob={cat['n_drift_blob']} drift_content={cat['n_drift_content']} "
                  f"drift_legacy_after_content={cat['n_drift_legacy_after_content']} "
                  f"missing_py={cat['n_missing_python']} missing_cs={cat['n_missing_csharp']} "
                  f"no_audit={cat['n_no_audit']} numbering_drift={cat['n_numbering_drift']}")
            for r in ci_results:
                if r["status"] != "OK":
                    print(f"  [{r['status']}] {r['name']} ({r['family']}, {r['parity_level']})")
                    for d in r["details"]:
                        print(f"       - {d}")
            # Les paires en churn metadata-only gardent `status == OK` (aucune
            # divergence pedagogique) : sans cette boucle elles ne seraient
            # nommees NULLE PART, et un compteur non nul sans nom n'est pas
            # actionnable (c'est le `::error ...::<none>` du 2026-08-07).
            for r in ci_results:
                if r.get("metadata_only_blob_drift"):
                    print(f"  [INFO metadata-only] {r['name']} "
                          f"({r['family']}, {r['parity_level']})")
                    for d in r["details"]:
                        print(f"       - {d}")

        # CI gate : rouge sur les anomalies BLOQUANTES uniquement (le but du
        # cron fleet-wide). Le churn metadata-only est compte et nomme, mais
        # ne rougit pas -- sinon on re-fabrique le faux positif que le volet c
        # a elimine, et sur un gate dont le remede prescrit est un no-op.
        if args.check and n_blocking_drift > 0:
            return 1
        return 0

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
