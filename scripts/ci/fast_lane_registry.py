"""Registre de la voie rapide -- donnees chargees depuis fast_lane_registry.d/.

Historiquement ce module portait les ~100 gardes en dur (5098 lignes, #28117).
Depuis #28117 les entrees vivent dans un fichier YAML par groupe
(``fast_lane_registry.d/<groupe>.yaml``) ; ce module garde la mecanique :
dataclasses ``Guard``/``Commenter``, constantes, gabarits de commentaires et
le chargeur qui valide le schema.

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

@dataclass
class Commenter:
    """Un effet de bord PR d'un garde absorbe.

    header      En-tete de la section dans le commentaire consultatif unique
                (organe `advisory_sticky`, #24514). Il DOIT rester un nom
                d'organe valide (`[A-Za-z0-9._-]+`) : les six en-tetes
                historiques marocchino le sont deja, et le dossier de
                prevalidation les lit dans `_BOT_STICKY_ADVISORY_HEADERS`.
    argv        Detecteur. Sa sortie standard est le rapport : elle part dans
                l'artefact quand `artifact_name` est renseigne, et dans le
                corps du commentaire quand `body` la consomme.
    body        (rc, payload, ctx) -> corps de la section. Rend une chaine
                vide quand le verdict est VERT : la section est alors RETIREE
                (et rien n'est ecrit sur une PR qui n'en portait pas) -- le
                succes ne parle pas (#24514).
    artifact_name / artifact_file
                Nom d'artefact et nom de fichier, copies tels quels du
                workflow source (`actions/upload-artifact` garde son nom
                public). Vide = pas d'artefact.
    paths       Globs des fichiers passes au detecteur via `{changed_paths}`,
                en UNE invocation (les trois detecteurs de prose rendent un
                document JSON unique pour N carnets ; un appel par fichier
                casserait le JSON). Vide = le detecteur ne recoit aucun
                chemin (`{changed_paths}` n'est pas substitue).
    max_paths   Borne du nombre de chemins passes (0 = pas de borne). Les
                detecteurs de prose bornent a 50 dans leur workflow d'origine
                et DISENT la couverture partielle -- on reproduit les deux.
    needs_pr_body
                Le detecteur lit le corps de la PR (`--body-file`) : la valeur
                vient de `FAST_LANE_PR_BODY` et est ecrite dans un temporaire.
                Un corps absent fait ABSTENIR le commentaire plutot que de
                juger sur un corps vide.
    fatal_rc    rc qui sont une PANNE du detecteur et non un constat. Le
                workflow d'origine rougit sur ces codes (scan_md_hierarchy :
                rc=1 = baseline illisible ou scan vide) ; l'emetteur les
                propage au job, sans quoi un detecteur casse rendrait un
                commentaire vert. Les rc de constat (rc=1 des detecteurs de
                prose, rc=2 du drift) ne sont PAS fatals.
    """

    header: str
    argv: list[str]
    body: "Callable[[int, str, dict], str]"
    artifact_name: str = ""
    artifact_file: str = ""
    paths: list[str] = field(default_factory=list)
    max_paths: int = 0
    needs_pr_body: bool = False
    fatal_rc: tuple[int, ...] = ()

_CLAIMS_ABSTAIN = (
    "⚠️ Detector abstained (merge-base introuvable, shallow fetch or "
    "unanchored branch)."
)

_CLAIMS_WARN = (
    "⚠️ Prose/output review needed in the notebooks this PR changed: a "
    "numeric value is not anchored, an explicit relation is contradicted, "
    "or its evidence is missing. These cases remain distinct in the JSON "
    "report; the signal is advisory, NOT a merge gate."
)

_CLAIMS_TRAILER = (
    "Scope = notebooks CHANGED in this PR, not the whole corpus. Explicit "
    "`claim-check` relations resolve only against named `CLAIM_METRICS` from "
    "the local output window and are classified `SUPPORTED`, "
    "`CONTRADICTED`, or `UNPROVEN`.\n"
    "The `markdown-claims-output-report` run artifact contains the "
    "structured JSON report. See `python "
    "scripts/check_markdown_claims_output.py --help` for re-running "
    "locally.\n"
    "Detector rationale: c.290 / c.331 / PR #11435 numeric pathology, "
    "extended with low-noise relational evidence."
)

_STALE_ABSTAIN = (
    "⚠️ Stale-claim detector abstained (merge-base introuvable, shallow "
    "fetch or unanchored branch)."
)

_STALE_WARN = (
    "⚠️ Stale-claim review needed: a markdown cell claims a measurement "
    "value that appears in NO committed output of the notebook. Advisory, "
    "NOT a merge gate — triage against the JSON artifact."
)

_STALE_TRAILER = (
    "Scope = notebooks CHANGED in this PR, not the whole corpus. The "
    "`stale-claim-report` run artifact holds the structured JSON.\n"
    "Rationale: the sibling detector above only compares a claim to the "
    "outputs of the cells that PRECEDE it; a claim written in a cell that "
    "precedes its code (App-05-Timetabling-Python c.2/c.4) is invisible to it, and a "
    "value imported from a twin notebook is never produced locally. See "
    "`python scripts/check_stale_claims.py --help`."
)

_MISLABEL_ABSTAIN = (
    "⚠️ Factual-mislabel detector abstained (merge-base introuvable, "
    "shallow fetch or unanchored branch)."
)

_MISLABEL_WARN = (
    "⚠️ Factual-mislabel review needed: a markdown cell states an entity "
    "count or tuple formula that CONTRADICTS the committed stream of the "
    "code cell it describes (typically copied from a twin notebook with "
    "different data). Advisory, NOT a merge gate — triage against the JSON "
    "artifact."
)

_MISLABEL_TRAILER = (
    "Scope = notebooks CHANGED in this PR, not the whole corpus. The "
    "`factual-mislabel-report` run artifact holds the structured JSON.\n"
    "Rationale: pure ABSENCE of a claimed value is the sibling stale-claim "
    "detector's job; this one only reports CONTRADICTIONS between an "
    "adjacent code cell's stream and the markdown that describes it. See "
    "`python scripts/check_factual_mislabel.py --help`."
)

_LISTING_ABSTAIN = (
    "⚠️ Listing-coherence detector abstained (merge-base introuvable, "
    "shallow fetch or unanchored branch)."
)

_LISTING_WARN = (
    "⚠️ Listing-coherence review needed: a markdown table announces a total "
    "but lists only a CONTIGUOUS PREFIX of the identifiers a nearby code "
    "cell's stream prints — the signature of a table left behind when the "
    "series grew. Advisory, NOT a merge gate — triage against the JSON "
    "artifact."
)

_LISTING_FATAL = (
    "⚠️ Listing-coherence n'a PAS conclu : le detecteur a rendu un code "
    "d'erreur d'usage (entree illisible ou chemin absent), pas un constat sur "
    "cette PR. Ne lire ni comme un vert ni comme une troncature — voir le log "
    "du job."
)

_LISTING_UNREAD = (
    "{n} carnet(s) n'ont pas pu etre lus (JSON corrompu ou encodage non "
    "UTF-8) : les findings ne portent que sur les carnets lus."
)

_LISTING_OK_UNREAD = (
    "⚠️ Listing-coherence PARTIEL : aucun tableau tronque sur les carnets "
    "lus, mais {n} carnet(s) n'ont pas pu etre lus (JSON corrompu ou encodage "
    "non UTF-8) — le vert n'est pas rendu."
)

_LISTING_TRAILER = (
    "Scope = notebooks CHANGED in this PR, not the whole corpus. The "
    "`listing-coherence-report` run artifact holds the structured JSON.\n"
    "Rationale: this compares identifier SETS, not counts — a count "
    "comparison cannot see a table truncated from `08` while the stream "
    "lists up to `15`. The contiguous-prefix discriminant is what keeps an "
    "arbitrary subset (« the 3 longest ») out of the report. See "
    "`python scripts/check_listing_coherence.py --help`."
)

_CLAIMS_FATAL = (
    "⚠️ Markdown-claims n'a PAS conclu : le detecteur a rendu un code "
    "d'erreur d'usage, pas un constat sur cette PR. Voir le log du job."
)

_STALE_FATAL = (
    "⚠️ Stale-claim n'a PAS conclu : le detecteur a rendu un code d'erreur "
    "d'usage, pas un constat sur cette PR. Voir le log du job."
)

_MISLABEL_FATAL = (
    "⚠️ Factual-mislabel n'a PAS conclu : le detecteur a rendu un code "
    "d'erreur d'usage, pas un constat sur cette PR. Voir le log du job."
)

_ORGAN_EXEMPTED = (
    "Organ duplication DETECTED but EXEMPTED: the PR body declares a "
    "pedagogical copy. The organ-first rule (5 questions) is satisfied by "
    "construction. If this copy grows (several consumer notebooks), ask the "
    "source series for an extraction instead."
)

_ORGAN_ABSTAIN = (
    "Organ-duplication detector ABSTAINS: merge-base unresolved or "
    "structural error -- no verdict. See workflow log."
)

_ORGAN_WARN = (
    "WARNING: added symbol(s) collide with another series organ API "
    "(organ-first rule, .claude/rules/organ-first-implementation.md). "
    "Answer the 5 questions in the PR body, or declare the pedagogical copy "
    "(« copie pedagogique declaree, motif : ... ») which whitens it. See "
    "the workflow log for the full collision list (demanding series -> "
    "bypassed organ -> symbol). Advisory, NOT a merge gate."
)

_ORGAN_TRAILER = (
    "Detector: `python scripts/audit/detect_organ_duplication.py --base "
    "<merge-base> --body-file <pr body>`\n"
    "Rationale: `#16776` / `#13564` (rule merged in `#16778`)."
)

def _with_note(sentence: str, ctx: dict) -> str:
    """Phrase d'etat + note de couverture partielle quand elle existe.

    Le workflow d'origine ecrit cette note sur sa propre ligne, vide quand la
    PR tient sous la borne (`steps.run.outputs.trunc_note`) : la ligne vide
    disparait a l'affichage markdown, donc la coller en fin de phrase rend le
    meme commentaire.
    """
    note = (ctx.get("trunc_note") or "").strip()
    return f"{sentence} {note}".strip() if note else sentence

def _exit_state(rc: int, ctx: dict, fatal_rc: tuple[int, ...] = (2,)) -> str:
    # L'abstention des trois detecteurs de prose porte sur le MERGE-BASE, pas
    # sur `base_sha` : c'est lui qui manque sur une branche non ancree, et
    # c'est lui que les workflows sources testent avant de lancer le
    # detecteur (#11754 : « rien regarde » et « rien trouve » doivent rester
    # distinguables).
    if not ctx.get("merge_base"):
        return "abstain"
    # `rc=2` est l'erreur d'USAGE des quatre detecteurs de cette famille
    # (entree illisible, chemin absent) : la rendre « warn » postait une
    # accusation de troncature sur un lot que l'organe n'avait pas pu lire,
    # et un `rc=2` suffisait a la provoquer (#23394, reserve 3 -- defaut
    # herite des trois freres, corrige ici sur les quatre).
    if rc in fatal_rc:
        return "fatal"
    return "ok" if rc == 0 else "warn"

def _body_claims_output(rc: int, payload: str, ctx: dict) -> str:
    state = _exit_state(rc, ctx)
    if state == "ok":
        # #24514 : le succes ne parle pas -- le vert vit dans le check-run.
        # Vert TRONQUE : ce n'est pas un vert integral (borne 50 carnets),
        # la note de couverture se conserve seule, sinon un lot > borne
        # passe pour un vert complet (WARN adjoint 2026-11-10 sur #25286).
        return _with_note("", ctx)
    sentence = {"abstain": _CLAIMS_ABSTAIN,
                "fatal": _CLAIMS_FATAL}.get(state, _CLAIMS_WARN)
    return f"{_with_note(sentence, ctx)}\n\n{_CLAIMS_TRAILER}"

def _body_stale_claim(rc: int, payload: str, ctx: dict) -> str:
    state = _exit_state(rc, ctx)
    if state == "ok":
        # Vert tronque : meme regle que claims (note seule, cf. #24514).
        return _with_note("", ctx)
    sentence = {"abstain": _STALE_ABSTAIN,
                "fatal": _STALE_FATAL}.get(state, _STALE_WARN)
    return f"{_with_note(sentence, ctx)}\n\n{_STALE_TRAILER}"

def _body_factual_mislabel(rc: int, payload: str, ctx: dict) -> str:
    state = _exit_state(rc, ctx)
    if state == "ok":
        # Vert tronque : meme regle que claims (note seule, cf. #24514).
        return _with_note("", ctx)
    sentence = {"abstain": _MISLABEL_ABSTAIN,
                "fatal": _MISLABEL_FATAL}.get(state, _MISLABEL_WARN)
    return f"{_with_note(sentence, ctx)}\n\n{_MISLABEL_TRAILER}"

def _payload_count(payload: str, key: str) -> int:
    """Compte entier d'un rapport JSON, 0 si le rapport est illisible.

    Un rapport qu'on ne sait pas lire ne doit pas se lire comme un zero :
    l'appelant ne s'en sert que pour AJOUTER une phrase d'incompletude.
    """
    try:
        data = json.loads(payload)
    except (ValueError, TypeError):
        return 0
    valeur = data.get(key) if isinstance(data, dict) else None
    return valeur if isinstance(valeur, int) else 0

def _body_listing_coherence(rc: int, payload: str, ctx: dict) -> str:
    state = _exit_state(rc, ctx)
    non_lus = _payload_count(payload, "non_lus")
    if state == "ok" and not non_lus:
        # #24514 : le succes ne parle pas -- SAUF le vert PARTIEL, qui n'est
        # pas un vert (carnets jamais lus, #23394 reserve 1) et parle. Le
        # vert TRONQUE garde, lui, la note de couverture seule (borne 50).
        return _with_note("", ctx)
    sentence = {"ok": _LISTING_OK_UNREAD.format(n=non_lus),
                "abstain": _LISTING_ABSTAIN,
                "fatal": _LISTING_FATAL}.get(state, _LISTING_WARN)
    # `non_lus` porte les carnets que le detecteur n'a pas pu ouvrir : sans
    # cette phrase, un carnet illisible sortait en vert « aucun tableau
    # tronque » alors qu'il n'avait jamais ete lu (#23394, reserve 1).
    if non_lus and state not in ("ok", "abstain"):
        sentence = f"{sentence} {_LISTING_UNREAD.format(n=non_lus)}"
    return f"{_with_note(sentence, ctx)}\n\n{_LISTING_TRAILER}"

def _organ_status(payload: str) -> str:
    """Ordre du workflow source : BLOCKED, puis EXEMPTED, puis CLEAN."""
    for line in payload.splitlines():
        head = line.strip()
        if head.startswith("BLOCKED"):
            return "collision"
        if head.startswith("EXEMPTED"):
            return "exempted"
        if head.startswith("CLEAN"):
            return "clean"
    return "abstain"

def _body_organ_duplication(rc: int, payload: str, ctx: dict) -> str:
    state = _organ_status(payload)
    if state == "clean":
        # #24514 : le succes ne parle pas.
        return ""
    sentence = {
        "exempted": _ORGAN_EXEMPTED,
        "abstain": _ORGAN_ABSTAIN,
    }.get(state, _ORGAN_WARN)
    return f"{sentence}\n\n{_ORGAN_TRAILER}"

def _body_md_hierarchy(rc: int, payload: str, ctx: dict) -> str:
    """Commentaire du drift markdown, assemble comme dans le workflow source.

    Le workflow ne commente QUE sur rc=2 (derive) : rc=1 est une panne du
    scanner, pas un constat sur la PR, et rc=0 n'a rien a dire. La reference
    « avant » est la base de fusion re-scannee quand elle est connue ; sans
    elle le texte est ATTENUE (mode « derive du corpus »), exactement comme
    dans la source -- c'est la difference entre « cette PR a ajoute un
    defaut » et « le corpus en porte ».
    """
    if rc != 2:
        return ""
    base_short = (ctx.get("base_sha") or "")[:9]
    head_short = (ctx.get("head_sha") or "")[:9]
    lines = [f"## MD hierarchy drift -- {head_short}", ""]
    if base_short:
        lines += [
            "Cette PR augmente le compte de defauts de rendu markdown",
            f"par rapport a la base de fusion {base_short} re-scannee.",
            "Nouveaux defauts imputables au diff :",
        ]
    else:
        lines += [
            "Drift vs la baseline stockee (mode dispatch, sans base de",
            "fusion) -- derive du corpus, pas d'imputation stricte a ce",
            "diff. Details :",
        ]
    lines += ["", "```", payload.strip(), "```", ""]
    if base_short:
        lines.append(
            "Corriger (ex. `- # Indice : ...` -> `- **Indice :** ...`). "
            "See #11831.")
    else:
        lines.append(
            "Si la regle scanner change dans CETTE PR, re-seeder la baseline")
        lines.append("dans le meme commit : `--update-baseline`. See #11831.")
    return "\n".join(lines)

def _body_outputs_required(rc: int, payload: str, ctx: dict) -> str:
    """Recapitulatif du garde `outputs-required` (#25510, tranche T-A).

    Le corps est celui du workflow source, mot pour mot : c'est la section
    que les reviewers lisent depuis le 2026-09-11 (`## Notebook
    outputs-required (H.4 schema): ...`), et le dossier de prevalidation en
    reconnait le prefixe (`_BOT_ONLY_PREFIX_MARKERS`). Le workflow source
    ecrivait cette section dans le resume de job PUIS la collait (ou la
    retirait) ; ici elle n'est plus ecrite que dans le commentaire.

    Le SUCCES RETIRE la section (#15511 : le succes ne parle plus) -- c'est
    exactement ce que faisait le workflow (`--clear` sur un run vert).
    """
    data: dict = {}
    if payload.strip():
        try:
            data = json.loads(payload)
        except (json.JSONDecodeError, ValueError):
            data = {}
    if not isinstance(data, dict):
        data = {}
    total = data.get("occurrences") or 0
    notebooks = data.get("notebooks") or []
    errors = data.get("errors") or []
    if total > 0:
        lines = [
            f"## Notebook outputs-required (H.4 schema): **FAIL** ({total} "
            f"defective cell(s) in {len(notebooks)} notebook(s))",
            "",
        ]
        for entry in notebooks:
            lines.append(f"### {entry.get('notebook', '')}")
            lines.append("")
            for defect in entry.get("defects") or []:
                lines.append(
                    f"- cell#{defect.get('cell_index')} "
                    f"id={defect.get('cell_id')}: {defect.get('reason', '')}"
                )
            lines.append("")
        lines += [
            "### How to fix",
            "",
            "A code cell without an `outputs` key violates the nbformat 5.10.4 "
            "strict schema:",
            "",
            "```python",
            "# Option 1: re-execute the notebook so Papermill fills outputs",
            "python scripts/notebook_tools/notebook_tools.py execute <path>",
            "",
            "# Option 2: add an empty outputs list explicitly (stub cells)",
            "# Find cells missing the key in the .ipynb JSON and add:",
            '#   "outputs": [],',
            '# immediately after the "source" entry.',
            "```",
            "",
            "See Hermes Concern on PR #15631 (2026-09-11T19:06:00Z) for the "
            "founding incident.",
            "",
        ]
        return "\n".join(lines)
    if errors:
        lines = [
            f"## Notebook outputs-required (H.4 schema): **ERROR** "
            f"({len(errors)} unreadable notebook(s))",
            "",
        ]
        for entry in errors:
            lines.append(
                f"- {entry.get('notebook', '')}: {entry.get('error', '')}"
            )
        lines.append("")
        return "\n".join(lines)
    # PASS : la section est RETIREE ; le verdict vit dans le check-run du
    # garde bloquant (TRANCHE10), qui porte le detail.
    return ""

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

