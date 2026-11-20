"""Corps des commentaires consultatifs de la voie rapide (#27572).

Scission du 21/11 (cliquet de taille des scripts, #26364) : le registre
`fast_lane_registry.py` depassait son plafond epingle. Les CORPS des
commentaires consultatifs -- les textes affiches dans le commentaire unique
d'une PR -- sont des donnees de presentation, pas des donnees de garde :
elles vivent dans ce module, et le registre les importe.

Les phrases sont copiees MOT POUR MOT des workflows sources : une
reformulation silencieuse changerait le signal d'une PR a l'autre pour la
meme mesure. Seul l'emballage change (le heredoc shell disparait).
"""
from __future__ import annotations

import json
from dataclasses import dataclass, field


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


# --- Corps des commentaires -------------------------------------------------
#
# Les phrases sont copiees MOT POUR MOT des workflows sources : ce sont les
# textes que des reviewers et des bots lisent depuis des mois, et une
# reformulation silencieuse changerait le signal d'une PR a l'autre pour la
# meme mesure. Seul l'emballage change (le heredoc shell disparait).
#
# #24514 (famille #15511) : le succes ne parle plus. Il n'y a plus de phrase
# OK -- un corps vide rendu par un builder fait RETIRER la section advisory
# (ou n'ecrit rien sur une PR saine) ; le vert vit dans le check-run nomme.
# Les phrases qui restent portent toutes un SIGNAL : abstention, panne
# d'usage, constat, exemption ou vert PARTIEL (carnets non lus).

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

# Echec d'usage (rc=2) des trois detecteurs de prose freres : ni un constat,
# ni un quitus. Voir `_exit_state` (#23394, reserve 3).
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


