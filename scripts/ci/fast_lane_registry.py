"""Registre de la voie rapide -- donnees chargees depuis fast_lane_registry.d/.

Historiquement ce module portait les ~100 gardes en dur (5098 lignes, #28117).
Depuis #28117 les entrees vivent dans un fichier YAML par groupe
(``fast_lane_registry.d/<groupe>.yaml``) ; ce module garde la mecanique :
dataclass ``Guard``, constantes et le chargeur qui valide le schema. Le
dataclass ``Commenter`` et les gabarits de commentaires viennent du module
voisin ``fast_lane_commenters`` (#27572), comme sur le monolithe.

Contrat d'identite : le registre charge est identique, entree pour entree, a
l'ancien module monolithique (temoin gele :
``scripts/tests/fixtures/fast_lane_registry_snapshot.json``).

Ajouter une porte a un groupe existant = une entree YAML, aucun fichier .py.
Ajouter un groupe = nouvelle ligne dans ``_REQUIRED_GROUPS`` + assignment
module (changement de schema, review coordinateur).
"""

from __future__ import annotations

import json

import sys

from dataclasses import dataclass, field

from pathlib import Path

# Les corps des commentaires consultatifs vivent dans un module voisin
# (#27572, cliquet de taille des scripts) : le registre porte la DONNEE de
# garde, le module porte les CORPS affiches dans le commentaire de la PR.
_CI_DIR = Path(__file__).resolve().parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

from fast_lane_commenters import (  # noqa: E402
    Commenter,
    _body_claims_output,
    _body_factual_mislabel,
    _body_listing_coherence,
    _body_md_hierarchy,
    _body_organ_duplication,
    _body_outputs_required,
    _body_stale_claim,
)

REPO_ROOT = Path(__file__).resolve().parents[2]

LIVE_READ_REGISTRY = REPO_ROOT / "scripts" / "notebook_tools" / "live_read_registry.json"

LIVE_READ_WILDCARD = "MyIA.AI.Notebooks/**/*.ipynb"

def live_read_source_paths(registry_path: Path | None = None) -> list[str]:
    """Chemins des fichiers LUS par les cellules live-read, d'apres le registre.

    Une cellule live-read lit un fichier du depot et en committent la sortie
    (compte de lignes, citations ``L<n>``). Si la source change, la sortie
    committée devient un temoignage du passe -- et le garde qui le verifie
    doit etre SELECTIONNE par la revision qui touche la source. Jusque-là
    (avant #22001), les `paths` du garde ne portaient que ``**.ipynb`` et ses
    propres fichiers : une PR qui ne touchait que la source ne declenchait
    rien, et la revision #21899 (`Pillars.lean` 364 -> 414 lignes) a ete
    mergee verte.

    Les sources sont donc lues dans le registre, jamais recopiees : ajouter
    une entree au registre suffit a elargir le declencheur.

    Fail-closed : un registre illisible ou une entree sans `source` leve
    plutot que de rendre un garde muet (un garde eteint en silence est le
    defaut que ce correctif vient corriger). Les `paths` du garde passent par
    `live_read_guard_paths()`, qui LOCALISE cette panne (cf sa docstring).
    """
    path = Path(registry_path) if registry_path is not None else LIVE_READ_REGISTRY
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise RuntimeError(f"registre live-read illisible : {path} ({exc})") from exc
    sources: list[str] = []
    for cell in data.get("cells", []):
        source = cell.get("source")
        if not source:
            raise RuntimeError(
                f"registre live-read : entree sans champ 'source' : {cell}")
        if cell.get("source_kind", "repo") == "external":
            # La source d'une lecture EXTERNE (clone Lake amont epingle par un
            # tag) n'est PAS un fichier du depot : la revision qui peut
            # invalider la declaration est celle qui touche le CARNET -- la
            # sortie commitee y vit -- et non celle du fichier amont, que
            # personne ne peut modifier ici. Declarer le chemin amont comme
            # declencheur rendrait le garde eteint en silence sur ce carnet.
            notebook = cell.get("notebook")
            if not notebook:
                raise RuntimeError(
                    f"registre live-read : entree externe sans champ "
                    f"'notebook' : {cell}")
            sources.append(notebook)
            continue
        sources.append(source)
    return sources

def live_read_guard_paths() -> list[str]:
    """`paths` du garde Live-read, sans emporter le registre entier en cas de panne.

    `TRANCHE20` porte ces chemins au CHARGEMENT du module : une exception
    laissee filer rendrait `fast_lane_registry` inimportable, donc les 30+
    gardes avec lui (mesure #22041 : registre absent -> `python scripts/ci/
    fast_lane.py` meurt sur `RuntimeError` a l'import, aucun check-run n'est
    emis). La panne est donc LOCALISEE au garde concerne : on retombe sur un
    motif large -- tous les carnets -- qui reste un SUPERSET des sources
    declarees. Le garde reste ainsi SELECTIONNE, et son propre argv
    (`check_live_read_freshness.py`) rend le rouge en lisant le registre
    manquant : bruyamment, jamais en silence.
    """
    try:
        return live_read_source_paths()
    except RuntimeError as exc:
        print(
            f"[fast-lane] registre live-read illisible : {exc} -- le garde "
            f"Live-read reste selectionne sur {LIVE_READ_WILDCARD} au lieu de "
            "rendre tout le registre inimportable (#22041).",
            file=sys.stderr,
        )
        return [LIVE_READ_WILDCARD]

@dataclass(frozen=True)
class Guard:
    """Un garde de la voie rapide.

    name        Nom EXACT du check-run emis. En phase pilote il est prefixe
                par `shadow_prefix` (cf fast_lane.py) pour cohabiter avec le
                workflow d'origine sans lui voler son nom.
    paths       Globs (syntaxe fnmatch, evaluee sur des chemins POSIX
                relatifs a la racine). Vide = le garde tourne toujours.
                Reproduit le bloc `paths:` du workflow d'origine -- la
                difference est qu'ici c'est du code, donc testable.
                Si `iterates_paths=True`, le garde recoit la liste des
                fichiers qui matchent ces globs et est execute UNE FOIS PAR
                fichier (le placeholder `{changed_paths}` dans `argv` est
                alors substitue par un chemin a la fois).
    argv        Commande a executer, deja decoupee (pas de shell : un shell
                introduirait une seconde couche de quoting sur des chemins
                qui viennent du diff).
    blocking    True  -> un echec doit rougir la PR (conclusion `failure`).
                False -> advisory : le verdict est publie, jamais bloquant
                (conclusion `neutral`), conformement au caractere annonce du
                workflow d'origine. Neutraliser un advisory en `success`
                effacerait le signal ; le rendre `failure` mentirait sur son
                statut.
    needs_base  Le garde compare HEAD a la base : le runner lui garantit que
                `origin/<base_ref>` est joignable.
    diff_bounded  Le verdict du garde est un DELTA (comparaison base/head, ou
                lignes ajoutees par la PR) : un rouge corrobore ne peut pas
                heriter de `main`. Lu par le picker (`_diff_bounded_check_names`,
                #19645) -- la declaration est EXPLICITE et distincte de
                `needs_base`, parce que l'information de bornage peut manquer
                a l'argv absorbe (cas `check-nav-chain`/`check-navlinks`,
                suite c.1503 du 2026-10-09 : leur workflow d'origine scopait
                au diff via `git diff $BASE...HEAD`, l'argv absorbe dit
                seulement `--check`) et que les ~20 gardes `needs_base` ne
                sont PAS un delta borne au diff par defaut.
    delta_argv  Present => le garde est un DELTA en trois temps : `argv` est
                execute sur HEAD (sa sortie standard est capturee comme
                `head.json`), puis sur l'arbre bascule a la base
                (`base.json`), puis `delta_argv` compare les deux. Le
                placeholder `{base_json}` / `{head_json}` y est substitue.
    swap_paths  Sous-arbres a basculer a la base pour la phase 2. Le
                basculement est MUTANT : c'est le seul danger propre a la
                mutualisation d'un job, puisqu'un garde pourrait lire l'arbre
                d'un autre. Le runner y repond par trois mesures -- les
                gardes non-mutants passent tous AVANT, la bascule est faite
                UNE fois pour tous les gardes delta (au lieu d'une par garde
                aujourd'hui), et la restauration est **verifiee** avant de
                rendre le moindre verdict.
    source      Workflow d'origine, pour que la correspondance reste tracable
                quand on retirera le workflow unitaire.
    """

    name: str
    argv: list[str]
    source: str
    paths: list[str] = field(default_factory=list)
    blocking: bool = True
    needs_base: bool = False
    # #19645 suite c.1503 : verdict DELTA lu par le picker (voir la docstring
    # du champ). Declare sur les gardes dont l'argv absorbe a perdu
    # l'information de bornage -- une heuristique d'argv ne peut pas la voir.
    diff_bounded: bool = False
    delta_argv: list[str] = field(default_factory=list)
    swap_paths: list[str] = field(default_factory=list)
    iterates_paths: bool = False  # voir `run_iter` dans fast_lane.py
    absorbed: bool = False  # tranche d'absorption #12567 : nom canonique + conclusion reelle, meme en lane ombre
    # Motif d'ombre DECLARE (#19168). Un garde `blocking=True` qui n'est pas
    # absorbe n'est pas compte par `blocking_failed` et emet sous
    # `fast-lane (ombre): ` avec une conclusion neutre : son `blocking=True`
    # est alors une declaration sans effet. Deux etats sont legitimes --
    # absorbe (il bloque vraiment), ou volontairement en ombre, et dans ce
    # second cas le motif ET le critere de bascule s'ecrivent ICI. Sans cette
    # declaration, la classe entiere est invisible : `test_fast_lane.py`
    # rougit des qu'un garde bloquant n'est ni absorbe ni declare.
    shadow_reason: str = ""
    # Codes de retour traites comme SUCCES au-dela de 0. Les detecteurs de
    # la serie figure/texte rendent rc=1 sur defaut et rc=2 sur fichier
    # INTROUVABLE (mesure firsthand : un JSON corrompu rend rc=0 avec une
    # NOTE "unreadable"). Leur workflow d'origine ne voit jamais ce cas --
    # il saute les fichiers supprimes (`[ -f "$nb" ] || continue`) -- et le
    # moteur reproduit ce skip ; `warn_rc` est la seconde defense si un
    # chemin echappe au filtre (checkout partiel). Sans lui, la lane serait
    # PLUS stricte que le workflow qu'elle absorbe.
    warn_rc: tuple[int, ...] = ()
    # Anti-auto-desarmement AGREGE (clause #8655/#8656) : si CHAQUE fichier
    # examine rend un rc de `warn_rc`, le garde n'a RIEN analyse et ne peut
    # pas certifier -- on fail loud (rc=1) au lieu de produire un quitus
    # aveugle. Sans ce flag, `warn_rc` lisserait la panne en succes. Reserved
    # a `iterates_paths` ; par defaut desarme (un garde sans clause d'origine
    # ne devient jamais plus strict).
    fail_on_all_warn: bool = False
    # Globs EXCLUSIFS d'iteration quand `iterates_paths=True` : seuls les
    # fichiers qui matchent sont passes au detecteur. Distinct de `paths` (le
    # declencheur via `guard_applies`), parce que le workflow d'origine SEPARE
    # les deux : `on.pull_request.paths` inclut le detecteur + le workflow
    # (pour que la garde reparte quand ils changent), mais sa boucle interne
    # itere UNIQUEMENT le glob d'actifs (`MyIA.AI.Notebooks/**/*.ipynb`).
    # Mettre le detecteur/workflow dans le meme sac que l'iter-set ferait
    # passer un `.yml`/`.py` au detecteur de notebooks -> rc=2 -> faux echec
    # (incident #13220 : la PR qui ajoute la garde echouait dessus). Vide =
    # fallback sur `paths` (comportement pre-change pour les gardes sans
    # distinction trigger/iter).
    iterate_paths: list[str] = field(default_factory=list)
    # Commande de PRE-CONTROLE executee avant `argv` (phase 1). Un rc non
    # nul devient le verdict du garde et `argv` n'est PAS execute. Cas
    # d'usage : le self-test du ratchet output-failure, qui dans son
    # workflow d'origine etait un step distinct AVANT le scan -- un
    # detecteur qui ne peut pas prouver qu'il tire est indiscernable d'un
    # detecteur debranche (lecon #11685/#12817). Pas de `bash -c ... &&` :
    # le shell n'est pas resolu pareil selon l'hote (127 mesuré en local
    # Windows) et le registre interdit la seconde couche de quoting.
    pre_argv: list[str] = field(default_factory=list)
    # Effets de bord PR du garde (#22209 tranche 1b). Vide = le garde n'ecrit
    # que son check-run, comme les tranches precedentes. Non vide = le job
    # `Always-on commenters` execute le garde et pose ses commentaires
    # stickies + ses artefacts ; le job `Always-on guards` l'EXCLUT
    # (`--no-effects`), sinon les deux emettraient le meme verdict ET le meme
    # commentaire. Le type `Commenter` est declare apres cette dataclass.
    commenters: tuple = ()

FAST_LANE_NATIVE = "(garde natif de la voie rapide : aucun workflow d'origine)"

PILOT_LOT_NAME = "PILOT"

TRANCHE_ALIGNMENT_EN_COURS = frozenset()

NOTEBOOK_GLOBS = ["**/*.ipynb"]

PILOT_SHADOW_SANS_EMETTEUR = (
    "phase pilote #11835, aucun autre emetteur : le workflow d'origine ne "
    "declenche pas sur `pull_request`. Critere de bascule : absorber, ou retirer "
    "la garde.")

PILOT_SHADOW_NATIF = (
    "phase pilote #11835, garde natif : aucun workflow d'origine, donc aucun autre "
    "emetteur du nom de check-run. Critere de bascule : absorber (convention des "
    "tranches depuis TRANCHE8).")

_COMMENTS_OUT_GLOB = "**/*.ipynb"

# ---------------------------------------------------------------------------
# Chargeur des donnees (#28117). Fail-closed : groupe inconnu, marqueur
# inconnu, champ requis manquant ou groupe absent = erreur a l'import, la CI
# ne passe pas sur un registre incoherent.
# ---------------------------------------------------------------------------
from dataclasses import fields as _dc_fields

_GUARD_FIELDS = frozenset(f.name for f in _dc_fields(Guard))
_COMMENTER_FIELDS = frozenset(f.name for f in _dc_fields(Commenter))

_REGISTRY_DIR = Path(__file__).resolve().parent / "fast_lane_registry.d"

_REQUIRED_GROUPS = (
    "PILOT",
    "TRANCHE1",
    "TRANCHE2",
    "TRANCHE3",
    "TRANCHE4",
    "TRANCHE5",
    "TRANCHE6",
    "TRANCHE7",
    "TRANCHE8",
    "TRANCHE9",
    "TRANCHE10",
    "TRANCHE11",
    "TRANCHE13",
    "TRANCHE12",
    "TRANCHE14",
    "TRANCHE15",
    "TRANCHE16",
    "TRANCHE17",
    "TRANCHE19",
    "TRANCHE18",
    "TRANCHE20",
    "TRANCHE21",
    "TRANCHE22",
    "TRANCHE23",
    "TRANCHE24",
    "TRANCHE25",
    "TRANCHE26",
    "TRANCHE27",
    "TRANCHE33",
    "TRANCHE28",
    "TRANCHE31",
    "TRANCHE29",
    "TRANCHE30",
    "TRANCHE32",
    "TRANCHE37",
    "TRANCHE34",
    "TRANCHE35",
    "TRANCHE36",
    "TRANCHE38",
    "TRANCHE41",
    "TRANCHE39",
    "TRANCHE40",
    "TRANCHE42",
    "TRANCHE43",
    "TRANCHE44",
    "TRANCHE45",
    "TRANCHE46",
    "TRANCHE47",
    "TRANCHE48",
    "TRANCHE53",
    "TRANCHE51",
    "TRANCHE49",
    "TRANCHE50",
    "TOPLEVEL_SERIES_GUARDS",
    "RISK_KERNEL_GUARDS",
    "TRANCHE52",
    "TRANCHE54",
    "TRANCHE55",
)

# Marqueurs du YAML -> objets reels du module.
_SOURCE_MARKERS = {"native": FAST_LANE_NATIVE}
_SHADOW_MARKERS = {
    "$pilot_shadow_natif": PILOT_SHADOW_NATIF,
    "$pilot_shadow_sans_emetteur": PILOT_SHADOW_SANS_EMETTEUR,
}
_COMMENTER_BODY_FNS = {
    "claims_output": _body_claims_output,
    "stale_claim": _body_stale_claim,
    "factual_mislabel": _body_factual_mislabel,
    "listing_coherence": _body_listing_coherence,
    "organ_duplication": _body_organ_duplication,
    "md_hierarchy": _body_md_hierarchy,
    "outputs_required": _body_outputs_required,
}


class RegistryDataError(Exception):
    """Donnees de registre invalides (YAML malforme, schema incoherent)."""


def _resolve_string(value, field, rel):
    if not isinstance(value, str):
        return value
    if value in _SOURCE_MARKERS and field == "source":
        return _SOURCE_MARKERS[value]
    if value in _SHADOW_MARKERS and field == "shadow_reason":
        return _SHADOW_MARKERS[value]
    return value


def _resolve_paths(items, rel):
    out = []
    for item in items:
        if item == "$notebook_globs":
            out.extend(NOTEBOOK_GLOBS)
        elif item == "$live_read_guard_paths":
            out.extend(live_read_guard_paths())
        else:
            out.append(item)
    return out


def _build_commenter(entry, rel):
    if not isinstance(entry, dict):
        raise RegistryDataError(f"{rel}: un commenter doit etre un mapping")
    unknown = set(entry) - _COMMENTER_FIELDS
    if unknown:
        raise RegistryDataError(f"{rel}: champs commenter inconnus {sorted(unknown)}")
    body_name = entry.get("body")
    if body_name not in _COMMENTER_BODY_FNS:
        raise RegistryDataError(
            f"{rel}: body de commenter inconnu {body_name!r} "
            f"(connus: {sorted(_COMMENTER_BODY_FNS)})")
    kw = dict(entry)
    kw["body"] = _COMMENTER_BODY_FNS[body_name]
    # Les types du monolithe, que le dataclass annonce : `paths` liste,
    # `fatal_rc` tuple. Le temoin JSON ecrit les deux sous la meme forme,
    # il ne voit donc pas un type servi a l'envers (test epingle).
    if "paths" in kw:
        kw["paths"] = list(kw["paths"])
    if "fatal_rc" in kw:
        kw["fatal_rc"] = tuple(kw["fatal_rc"])
    return Commenter(**kw)


def _build_guard(entry, rel):
    if not isinstance(entry, dict):
        raise RegistryDataError(f"{rel}: une porte doit etre un mapping")
    unknown = set(entry) - _GUARD_FIELDS
    if unknown:
        raise RegistryDataError(f"{rel}: champs inconnus {sorted(unknown)}")
    for req in ("name", "argv", "source"):
        if req not in entry:
            raise RegistryDataError(f"{rel}: champ requis manquant {req!r}")
    kw = {}
    for field, value in entry.items():
        if field == "source":
            kw[field] = _resolve_string(value, field, rel)
        elif field == "shadow_reason":
            kw[field] = _resolve_string(value, field, rel)
        elif field in ("paths", "delta_argv", "swap_paths", "pre_argv"):
            kw[field] = list(value)
        elif field in ("warn_rc",):
            kw[field] = tuple(value)
        elif field == "commenters":
            kw[field] = tuple(
                _build_commenter(c, f"{rel}[commenter {i}]")
                for i, c in enumerate(value))
        else:
            kw[field] = value
    if "paths" in kw:
        kw["paths"] = _resolve_paths(kw["paths"], rel)
    return Guard(**kw)


def _load_registry(data_dir=None):
    import yaml

    root = Path(data_dir) if data_dir else _REGISTRY_DIR
    if not root.is_dir():
        raise RegistryDataError(f"repertoire de donnees absent: {root}")
    loaded = {}
    for path in sorted(root.glob("*.yaml")):
        rel = path.relative_to(root).as_posix()
        try:
            doc = yaml.safe_load(path.read_text(encoding="utf-8"))
        except yaml.YAMLError as exc:
            raise RegistryDataError(f"{rel}: YAML malforme ({exc})") from exc
        if not isinstance(doc, dict) or "group" not in doc or "guards" not in doc:
            raise RegistryDataError(
                f"{rel}: attendu un mapping group:/guards:")
        group = doc["group"]
        if group not in _REQUIRED_GROUPS:
            raise RegistryDataError(
                f"{rel}: groupe inconnu {group!r} (schema: _REQUIRED_GROUPS)")
        if group in loaded:
            raise RegistryDataError(f"{rel}: groupe duplique {group}")
        if not isinstance(doc["guards"], list):
            raise RegistryDataError(f"{rel}: guards doit etre une liste")
        loaded[group] = [
            _build_guard(e, f"{rel}[{i}]")
            for i, e in enumerate(doc["guards"])
        ]
    missing = [g for g in _REQUIRED_GROUPS if g not in loaded]
    if missing:
        raise RegistryDataError(f"groupes absents des donnees: {missing}")
    return loaded


# Assignments module : les noms d'attributs ne changent PAS (consommateurs :
# fast_lane.py, check_absorbed_*). Un groupe absent du YAML fait echouer
# l'import (fail-closed).
_LOADED = _load_registry()
PILOT: list[Guard] = _LOADED["PILOT"]
TRANCHE1: list[Guard] = _LOADED["TRANCHE1"]
TRANCHE2: list[Guard] = _LOADED["TRANCHE2"]
TRANCHE3: list[Guard] = _LOADED["TRANCHE3"]
TRANCHE4: list[Guard] = _LOADED["TRANCHE4"]
TRANCHE5: list[Guard] = _LOADED["TRANCHE5"]
TRANCHE6: list[Guard] = _LOADED["TRANCHE6"]
TRANCHE7: list[Guard] = _LOADED["TRANCHE7"]
TRANCHE8: list[Guard] = _LOADED["TRANCHE8"]
TRANCHE9: list[Guard] = _LOADED["TRANCHE9"]
TRANCHE10: list[Guard] = _LOADED["TRANCHE10"]
TRANCHE11: list[Guard] = _LOADED["TRANCHE11"]
TRANCHE13: list[Guard] = _LOADED["TRANCHE13"]
TRANCHE12: list[Guard] = _LOADED["TRANCHE12"]
TRANCHE14: list[Guard] = _LOADED["TRANCHE14"]
TRANCHE15: list[Guard] = _LOADED["TRANCHE15"]
TRANCHE16: list[Guard] = _LOADED["TRANCHE16"]
TRANCHE17: list[Guard] = _LOADED["TRANCHE17"]
TRANCHE19: list[Guard] = _LOADED["TRANCHE19"]
TRANCHE18: list[Guard] = _LOADED["TRANCHE18"]
TRANCHE20: list[Guard] = _LOADED["TRANCHE20"]
TRANCHE21: list[Guard] = _LOADED["TRANCHE21"]
TRANCHE22: list[Guard] = _LOADED["TRANCHE22"]
TRANCHE23: list[Guard] = _LOADED["TRANCHE23"]
TRANCHE24: list[Guard] = _LOADED["TRANCHE24"]
TRANCHE25: list[Guard] = _LOADED["TRANCHE25"]
TRANCHE26: list[Guard] = _LOADED["TRANCHE26"]
TRANCHE27: list[Guard] = _LOADED["TRANCHE27"]
TRANCHE33: list[Guard] = _LOADED["TRANCHE33"]
TRANCHE28: list[Guard] = _LOADED["TRANCHE28"]
TRANCHE31: list[Guard] = _LOADED["TRANCHE31"]
TRANCHE29: list[Guard] = _LOADED["TRANCHE29"]
TRANCHE30: list[Guard] = _LOADED["TRANCHE30"]
TRANCHE32: list[Guard] = _LOADED["TRANCHE32"]
TRANCHE37: list[Guard] = _LOADED["TRANCHE37"]
TRANCHE34: list[Guard] = _LOADED["TRANCHE34"]
TRANCHE35: list[Guard] = _LOADED["TRANCHE35"]
TRANCHE36: list[Guard] = _LOADED["TRANCHE36"]
TRANCHE38: list[Guard] = _LOADED["TRANCHE38"]
TRANCHE41: list[Guard] = _LOADED["TRANCHE41"]
TRANCHE39: list[Guard] = _LOADED["TRANCHE39"]
TRANCHE40: list[Guard] = _LOADED["TRANCHE40"]
TRANCHE42: list[Guard] = _LOADED["TRANCHE42"]
TRANCHE43: list[Guard] = _LOADED["TRANCHE43"]
TRANCHE44: list[Guard] = _LOADED["TRANCHE44"]
TRANCHE45: list[Guard] = _LOADED["TRANCHE45"]
TRANCHE46: list[Guard] = _LOADED["TRANCHE46"]
TRANCHE47: list[Guard] = _LOADED["TRANCHE47"]
TRANCHE48: list[Guard] = _LOADED["TRANCHE48"]
TRANCHE53: list[Guard] = _LOADED["TRANCHE53"]
TRANCHE51: list[Guard] = _LOADED["TRANCHE51"]
TRANCHE49: list[Guard] = _LOADED["TRANCHE49"]
TRANCHE50: list[Guard] = _LOADED["TRANCHE50"]
TOPLEVEL_SERIES_GUARDS: list[Guard] = _LOADED["TOPLEVEL_SERIES_GUARDS"]
RISK_KERNEL_GUARDS: list[Guard] = _LOADED["RISK_KERNEL_GUARDS"]
TRANCHE52: list[Guard] = _LOADED["TRANCHE52"]
TRANCHE54: list[Guard] = _LOADED["TRANCHE54"]
TRANCHE55: list[Guard] = _LOADED["TRANCHE55"]

