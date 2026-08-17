#!/usr/bin/env python3
"""Gate pre-merge : aucun nit de review non leve ne doit survivre a un merge.

Pourquoi cet organe existe
--------------------------
Le champ `reviews[].state` est **structurellement aveugle** aux deux canaux de
review qui comptent le plus sur ce depot :

1. Le **user** poste ses nits comme *issue comments* (pas de review formelle) :
   il n'y a donc AUCUN `state` a lire — ni `CHANGES_REQUESTED`, ni meme une
   entree dans `reviews[]`.
2. **Hermes** (bot reviewer) poste ses reserves avec `state: COMMENTED` et le
   verdict en **prefixe de body** (`[Hermes] COMMENT_WITH_CONCERNS`) : lire
   l'etat renvoie `COMMENTED`, qui ne bloque rien.
3. Les **commentaires inline** de review vivent dans `reviewThreads` (GraphQL),
   une 3e surface absente de `gh pr view --json comments,reviews`.

Incident fondateur : PR #10761, mergee 2026-08-14T04:15Z malgre 2 nits user du
2026-08-13T11:07 (~17 h avant) et une review Hermes COMMENT_WITH_CONCERNS
confirmant les 2 nits + 3 points neufs dont « second reviewer obligatoire non
fourni ». `mergeStateStatus: CLEAN`, `reviews[].state: COMMENTED` : les deux
champs qu'un merge-gate lit d'ordinaire etaient verts.

Usage
-----
    python scripts/check_unaddressed_nits.py <PR>          # gate : exit 1 si bloque
    python scripts/check_unaddressed_nits.py <PR> --json   # sortie machine
    python scripts/check_unaddressed_nits.py --audit --limit 400   # audit retro

Ce qui leve un nit — et ce qui ne le leve PAS
---------------------------------------------
**Ce qui leve une remarque est une phrase, pas un SHA.** Un nit n'est considere
**leve** que si, entre son horodatage et le merge, on trouve au moins un de :
  - une **reponse ecrite** capable de repondre (cf `can_lift` : ni bot de CI,
    ni tag de protocole nu) ;
  - pour un thread inline : `isResolved: true` ou `isOutdated: true`.

Ne levent RIEN :
  - **un commit pousse apres le nit** : un push muet est indiscernable d'un push
    qui repond (sur #10761, le « traitement » etait un rebase qui n'adressait
    aucun des deux nits). Il est reporte comme contexte (`code_pushed_after`) ;
  - **un commentaire poste apres le merge** : c'est l'annonce de merge, pas une
    reponse — sans cette borne, le gate ratait son propre incident fondateur ;
  - **un commentaire de bot CI ou un tag de protocole nu** : ils ne repondent a
    rien, et sur ce depot ils sont postes a chaque push (defaut signale par
    Hermes en review de cet organe meme, cf `can_lift`).

Limite honnete de l'heuristique HUMAN
-------------------------------------
Le compte `jsboige` est utilise **a la fois** par le user et par les agents. Le
discriminant retenu est le **CRLF** : un commentaire redige dans l'UI web GitHub
porte `\r\n`, un commentaire poste via `gh` CLI porte `\n`. C'est fiable en
pratique sur ce depot mais ce n'est pas une preuve d'identite : un nit user
poste via `gh` serait manque (faux negatif), un agent collant du CRLF serait
signale a tort (faux positif). Le gate signale, l'humain tranche.

Limite honnete du CONDITIONAL_LIFT (#11201)
-------------------------------------------
La regex neutralise le marqueur « je merge » au niveau du BODY ENTIER : un
commentaire contenant a la fois une annonce vraie (« c'est bon, je merge ») et
une construction conditionnelle (« corrige X et je merge ») est integralement
de-leve — l'annonce vraie y perd son effet (faux positif possible). La branche
« des » peut aussi matcher « je merge des PRs » (pluriel direct, pas « dès »).
Choix assume : le cout d'un faux positif (un flag a trier) est inferieur au
cout du faux negatif corrige ici (un nit invisible fondu dans sa propre
condition). Toute passe `--audit` lancee avant le 2026-08-16 a sous-compte :
elle est a rejouer.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import unicodedata
from datetime import datetime, timezone

REPO = "jsboige/CoursIA"

BOT_LOGINS = {"github-actions", "codecov", "dependabot", "copilot-pull-request-reviewer"}

# Prefixes de tags utilises par les agents du cluster (protocole dashboard/PR).
AGENT_PREFIXES = (
    "[PART-OF-EPIC", "[GRAIN", "[CLAIMED", "[DONE", "[INFO", "[DISPATCH",
    "[ACK", "[RELEASED", "[OVERRIDE", "[MERGED", "[WARN", "[ERROR", "[ASK",
    "[REPLY", "[PROPOSAL", "[BLOCKED", "[ESCALATION",
)

# Marqueurs de reserve d'un reviewer bot (le verdict est dans le body, pas l'etat).
CONCERN_MARKERS = (
    "COMMENT_WITH_CONCERNS", "CHANGES_REQUESTED", "NEEDS_CHANGES", "CONCERNS",
    "SUSPECT_", "STRUCTURAL_ONLY", "SCOPE FLAG", "scope mismatch",
    "avant merge", "avant de merger", "il va falloir", "a nuancer", "à nuancer",
    # Miroir anglais de « avant merge » : fenetre 04-23..04-30 (triage po-2023,
    # #11044) — 2 faux negatifs mesures, PRs mergees sans aucune levee :
    # #594 « issues that should be addressed before merge » et #590
    # « CRITICAL — Must fix before merge ». Une seule addition couvre les deux.
    "before merge",
    # Fenetre 2026-08-16 (#11201) : le registre naturel d'un nit redige a la main.
    # Le commentaire 03:22:28Z de #11190 disait « Une seule chose a changer —
    # une ligne » sans AUCUN marqueur ci-dessus : une fois le faux negatif
    # « et je merge » neutralise (CONDITIONAL_LIFT), classify() le rendait
    # encore None. `_unaccent` fait matcher « a changer » et « à changer ».
    # Garde-fou FP : « rien a changer » nie le nit — le citer « rien »
    # (CITERS, ci-dessous) rend l'occurrence citee.
    "a changer",
)

# Un commentaire qui ANNONCE la levee ou le merge n'est pas un nit — il en est
# la resolution. Sans ce filtre, chaque « CHANGES_REQUESTED levée » est compte
# comme une reserve ouverte (faux positif massif, mesure sur 400 PRs).
LIFT_MARKERS = (
    "levée", "levee", "LGTM", "Mergé", "Merged", "je merge", "Merge.",
    "est adressé", "sont adressés", "sont levées", "est levée",
    "Je lève", "Je leve", "Levée de", "Levee de",
)

# Un LIFT en construction CONDITIONNELLE (« corrige X et je merge », « je merge
# quand… ») n'est pas une levee : c'est l'enonce de la condition bloquante
# (#11201). Le marqueur « je merge » couvre en effet deux sens opposes —
# « c'est bon, je merge » (annonce, levant) et « Change la ligne 19 et je
# merge » (condition, bloquant) — et le test LIFT_MARKERS passait AVANT toute
# recherche de reserve : le nit devenait invisible par la clause meme qui le
# rendait bloquant. On ne RETIRE pas le marqueur : sur les 7 occurrences
# conditionnelles mesurees dans les 60 dernieres PRs mergees, 4 etaient de
# vraies annonces (le retrait produirait des faux positifs). On annule son
# effet quand la construction est conditionnelle.
CONDITIONAL_LIFT = re.compile(
    r"(et je merge|puis je merge|ensuite je merge"
    r"|je merge (?:dès|des|une fois|quand|après|apres|si\b))", re.I)

# #11246 — use vs mention : CONDITIONAL_LIFT lisait les exemples CITES du motif
# comme des usages. Une review qui explique « corrige X et je merge » se
# flaggait elle-meme (2/15 findings de l'audit --limit 400 : les 2 seules
# reviews du corpus qui PARLENT du gate), et son annonce de merge reelle
# (« **Mergée.** ») etait annulee. On neutralise les segments cites AVANT la
# recherche de la construction conditionnelle — guillemets typographiques
# (« … »), backticks inline (`…`), blocs de code (``` … ```) — comme pour tout
# parseur qui ne doit pas lire ses propres exemples. La construction
# conditionnelle EMPLOYEE (« corrige la ligne 19 et je merge ») reste bloquante
# (#11201) : elle ne porte aucun de ces delimiteurs.
_QUOTED_RANGES = re.compile(r"```.*?```|«.*?»|`[^`]*`", re.DOTALL)


def _strip_quoted(body: str) -> str:
    """Retire les segments cites (guillemets typo, backtick, bloc code)."""
    return _QUOTED_RANGES.sub(" ", body)

# NOTE — proposition ecartee (triage 07-15..07-31, retiree au rebase 2026-08-16).
# Un `NO_CONCERN_TAIL_MARKERS` dechargeant tout body dont les 300 derniers chars
# portent « ne bloque pas » / « Safe to merge » a ete propose puis RETIRE : il
# rouvre le failure mode fondateur de B.0. Sur #10761, Hermes a emis
# COMMENT_WITH_CONCERNS et la PR a ete mergee sans reponse ecrite ; si ce meme
# body s'etait conclu par « ne bloque pas », un tel filtre l'aurait efface — et
# l'organe aurait manque precisement l'incident qui l'a fait naitre. Une reserve
# emise se leve par une PHRASE de reponse, jamais par la conclusion de celui qui
# l'a emise. `POSITIVE_MARKERS` ci-dessous fait le travail voisin, mais lui ne
# decharge QUE s'il ne reste aucune reserve vivante — c'est la difference.

# Verdict structurel POSITIF : l'emporte sur toute prose du body, y compris un
# decompte de CONCERNS passe en revue (« NanoClaw a relevé 2 CONCERNS... Verdict
# : COMMENT_WITHOUT_CONCERNS » #7583). C'est le miroir exact de
# COMMENT_WITH_CONCERNS : quand le verdict formel est rendu, il decide.
VERDICT_POSITIVE = "COMMENT_WITHOUT_CONCERNS"

# Approbations SOUPES : ne rescussitent un commentaire que s'il ne porte AUCUNE
# reserve vivante. Une review mixte (« [COMMENT_WITH_CONCERNS] — 2 concerns...
# Safe to merge » #6849/#6852/#7704, gate vision « [avant merge] » #6698) garde
# ses reserves — le « Safe to merge » y est une conclusion nuancee, pas un
# verdict.
POSITIVE_MARKERS = (
    "SAFE for merge", "Safe to merge",
    "Verdict** : OK", "Verdict : OK",
)

# Mots qui, DEVANT une occurrence de marqueur, la rendent CITEE et non emise :
# negation (« No CHANGES_REQUESTED », « COMMENT_WITHOUT_CONCERNS »), article
# defini narratif (« the CHANGES_REQUESTED reflects a pre-fix state » #6699),
# modal hypothesique (« would `CHANGES_REQUESTED` a probeAddresses strip »
# #7248). L'occurrence fait reference au verdict d'un autre sans l'emettre.
# Fenetre courte (30 chars avant l'occurrence) : une citation a distance
# (autre phrase) ne desactive rien.
CITERS = (
    "no", "not", "pas de", "pas d'", "sans", "without", "aucun", "aucune",
    "zero", "jamais", "the", "would", "could", "might", "aurait",
    # « Previous CHANGES_REQUESTED was incorrect... Revised verdict: APPROVE »
    # (#748, 10 s avant le merge) : le reviewer RETRACTE sa propre reserve.
    # On ne peut pas demander « previous » — le mot ne peut que narrer.
    "previous",
    # Fenetre 05-08..05-14 (triage po-2023, #11044) — trois narrations mesurees :
    # « **COMMENTED** (pas CHANGES_REQUESTED) » (#860) : negation francaise
    # sans « de » — « pas de » ci-dessus ne couvrait pas la forme nue.
    "pas",
    # « rien a changer » (#11201) : negation totale du nit — le marqueur
    # « a changer » y est cite, pas emis.
    "rien",
    # « pending dismissal of stale CHANGES_REQUESTED » (#977) : comme
    # « previous », le mot ne peut que narrer une reserve passee.
    "stale",
    # « CONFLICTING — needs rebase before merge » (#887, recidive de #729
    # fenetre 05-01..05-07) : demande procedurelle satisfaite par le merge
    # lui-meme — git n'autorise pas le merge d'une branche en conflit.
    "needs rebase",
    # « Si Static validation rouge → CHANGES_REQUESTED + diagnostic » (#1247,
    # fenetre 05-15..05-21) : verdict CONDITIONNEL futur, jamais emis. Une
    # fleche devant le marqueur est une derivation, pas une emission — les
    # verdicts reels s'ecrivent « Verdict : X » ou dans le state de la review.
    # Traite hors CITERS (voir _is_cited) car la fleche n'est pas un mot.
    # Fenetre 05-22..05-28 (triage po-2023, #11044) — la RETRACTION narree :
    # « my earlier CHANGES_REQUESTED was a FALSE POSITIVE (retracted) » puis
    # « Supersedes my earlier false-positive CHANGES_REQUESTED » (#1458), et
    # « supersedes my CHANGES_REQUESTED of 03:21 » (#1442). Comme « previous »,
    # ces mots ne peuvent que narrer un verdict passe ; une emission s'ecrit
    # « CHANGES_REQUESTED: » ou passe par le state de la review. « supersedes
    # my » en deux mots (pas « my » nu : « my CONCERN is... » est une vraie
    # emission).
    "earlier",
    "false-positive",
    "supersedes my",
    # « **Retracting CHANGES_REQUESTED → approving.** » (#1458, meme
    # commentaire) : le gerondif de retraction ne peut qu'annuler sa propre
    # reserve passee.
    "retracting",
    # Fenetre 05-29..06-04 (triage po-2023, #11044) — la REPONSE QUI NOMME.
    # « ## Re: CONCERNS ... **Fixed.** » (#1839) : « Re: » est un en-tete de
    # reponse — le marqueur cite est le SUJET auquel on repond, jamais une
    # nouvelle emission. (Forme nue « re » : le normalisateur retire la
    # ponctuation de fin de fenetre, deux-points compris.)
    "re",
    # « Per ai-01 CHANGES_REQUESTED: ... » (#2363) : « per X » = « selon X »,
    # attribution d'une reserve passee dans un rapport de fix. Idem « du
    # precedent review (CHANGES_REQUESTED ... » (#1958, 2e review APPROVED).
    # Ces deux-la agissent via la regle du mot d'attribution dans _is_cited.
    "per",
    "precedent",
)


def _unaccent(text: str) -> str:
    """« sont adressés » et « sont adresses » disent la meme chose.

    Les agents du cluster ecrivent massivement sans accents (les fichiers de
    regles eux-memes le font) tandis que les marqueurs ci-dessus sont accentues.
    Comparer les formes brutes rend le filtre orthographique — un nit deja leve
    serait re-signale (faux positif) sur la seule foi d'un accent absent. La
    casse, elle, est PRESERVEE : elle porte du sens (« Merge. »), et l'ignorer
    elargirait le filet au point de manquer de vrais nits.
    """
    return "".join(
        c for c in unicodedata.normalize("NFD", text)
        if unicodedata.category(c) != "Mn"
    )


def has_marker(body: str, markers: tuple[str, ...]) -> bool:
    normalised = _unaccent(body)
    return any(_unaccent(m) in normalised for m in markers)


def _excerpt(body: str) -> str:
    """Tete + queue : le verdict d'un reviewer vit en QUEUE de body.

    Les 280 premiers chars seuls coupaient la conclusion (mesure triage
    07-15..07-31 : le verdict final tombait hors excerpt sur les PRs longues,
    et l'audit lisait la position du titre au lieu de la conclusion).

    Note : ceci concerne l'AFFICHAGE de l'audit, pas la classification. Voir
    `classify` — la conclusion en queue n'y decharge rien.
    """
    snippet = " ".join(body.split())
    if len(snippet) <= 400:
        return snippet[:280]
    return snippet[:200] + " [...] " + snippet[-200:]


def _is_cited(window: str) -> bool:
    """La fenetre avant l'occurrence se termine-t-elle sur un mot de citation ?

    Le mot doit etre delimite : le caractere qui le precede est non-alphanumerique
    (espace, newline, ponctuation) ou le debut de la fenetre. Sans frontiere,
    « xxxtechno » matcherait « no ».
    """
    w = window
    # Fleche immediatement devant le marqueur : derivation conditionnelle
    # (« Si X → CHANGES_REQUESTED », #1247), pas une emission de verdict.
    stripped = w.rstrip()
    if stripped.endswith(("→", "->", "=>")):
        return True
    while w and not w[-1].isalnum():
        w = w[:-1]
    w = w.lower()
    for c in CITERS:
        c = c.rstrip("'’")
        if w == c or (w.endswith(c) and not w[-len(c) - 1].isalnum()):
            return True
    # Fenetre 05-29..06-04 (#11044) — le mot d'ATTRIBUTION entre le citer et
    # le marqueur : « Per ai-01 CHANGES_REQUESTED » (#2363), « Stale Hermes
    # CHANGES_REQUESTED was purely... » (#2006), « du precedent review
    # (CHANGES_REQUESTED sur commit... » (#1958). Un citer suivi d'UN seul
    # mot reste une narration — le nom d'agent n'y change rien. Une emission
    # ne le traverse jamais : elle s'ecrit « MARKER: » nue ou passe par le
    # state de la review (« [Hermes] — CHANGES_REQUESTED » n'a pas de citer
    # devant l'agent, donc reste live).
    parts = w.rsplit(None, 1)
    head = parts[0] if len(parts) == 2 else ""
    if head:
        for c in CITERS:
            c = c.rstrip("'’")
            if head == c or (head.endswith(c) and not head[-len(c) - 1].isalnum()):
                return True
    return False


def has_live_marker(body: str, markers: tuple[str, ...]) -> bool:
    """Marqueur present avec au moins une occurrence NON citee.

    `has_marker` traite le body comme un sac de mots : « No CHANGES_REQUESTED
    from this review » contient « CHANGES_REQUESTED » donc compte comme une
    reserve. C'est la source dominante de faux positifs de l'organe (11/64
    signaux flagges sur la fenetre 07-14..07-20, triage po-2024:CoursIA-2) :
    des reviews d'approbation qui citent le verdict qu'elles n'emettent pas —
    negation (« No », « Pas de », « without »), narration d'une review
    pre-fix (« the CHANGES_REQUESTED reflects a pre-fix state » #6699), ou
    modal hypothesique (« would CHANGES_REQUESTED » #7248). On verifie donc
    chaque occurrence : si un mot de citation touche le debut du marqueur
    (fenetre de 30 caracteres, le « WITHOUT_ » de COMMENT_WITHOUT_CONCERNS
    compris), l'occurrence est morte ; le marqueur ne vit que si au moins une
    occurrence survit.
    """
    normalised = _unaccent(body)
    for marker in markers:
        m = _unaccent(marker)
        start = 0
        while (i := normalised.find(m, start)) != -1:
            if not _is_cited(normalised[max(0, i - 30):i]):
                return True
            start = i + 1
    return False


def ts(value: str | None) -> datetime | None:
    if not value:
        return None
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def gh_json(args: list[str]) -> object:
    out = subprocess.run(
        ["gh", *args], capture_output=True, text=True, encoding="utf-8", check=True
    ).stdout
    return json.loads(out)


def can_lift(comment: dict) -> bool:
    """Ce commentaire est-il capable de LEVER un nit qui le precede ?

    Seule une reponse d'un humain ou d'un agent, qui dit quelque chose, peut
    lever une remarque. Sont exclus :
      - les bots de CI (`github-actions` & co) : ils postent a chaque push et
        n'ont aucun compte a rendre sur une remarque de review ;
      - les tags de protocole nus (`[ACK]`, `[DISPATCH...]`, `[CLAIMED]`) :
        ils ne nomment aucun nit.

    Sans ce filtre, l'organe reproduit exactement le defaut qu'il traque :
    n'importe quel bruit poste entre le nit et le merge eteint le nit. Sur ce
    depot ou les bots commentent a chaque push, ce failure mode est la regle,
    pas l'exception (defaut trouve par Hermes en review de #11045).

    Limite connue et assumee : on ne verifie pas que la reponse *nomme* la
    remarque — cela demanderait du NLP. Un commentaire humain hors-sujet leve
    donc encore un nit (faux negatif residuel). Auteur + protocole eliminent le
    gros du bruit sans pretendre lire le sens.
    """
    login = (comment.get("author") or {}).get("login", "")
    if login in BOT_LOGINS:
        return False
    body = (comment.get("body") or "").lstrip()
    if not body:
        return False
    if body.startswith(AGENT_PREFIXES) and not has_marker(body, LIFT_MARKERS):
        return False
    return True


def classify(author: str, body: str) -> str | None:
    """'HUMAN' (nit user, UI web) | 'BOT-CONCERN' (reviewer avec reserves) | None."""
    if author in BOT_LOGINS or not body:
        return None
    stripped = body.lstrip()
    if has_marker(body, LIFT_MARKERS) and not CONDITIONAL_LIFT.search(_strip_quoted(body)):
        return None  # annonce de levee / de merge : resolution, pas reserve
    # (construction conditionnelle « et je merge » : voir CONDITIONAL_LIFT —
    # l'annonce conditionnee n'est pas une levee, le commentaire continue)
    if has_live_marker(body, (VERDICT_POSITIVE,)):
        return None  # verdict structurel positif rendu : il decide, la prose ne compte plus
    live_concern = has_live_marker(body, CONCERN_MARKERS)
    if not live_concern and has_live_marker(body, POSITIVE_MARKERS):
        return None  # approbation sans reserve vivante : la review conclut, ne reserve pas
    if stripped.startswith(AGENT_PREFIXES):
        # Tag de protocole agent : informatif, pas un nit — sauf s'il porte une reserve.
        return "BOT-CONCERN" if live_concern else None
    if "\r\n" in body:
        return "HUMAN"
    if live_concern:
        return "BOT-CONCERN"
    return None


def review_threads(pr: int) -> list[dict]:
    """Threads inline (3e surface, absente de `gh pr view --json`)."""
    query = """
    query($owner:String!,$repo:String!,$n:Int!){
      repository(owner:$owner,name:$repo){
        pullRequest(number:$n){
          reviewThreads(first:100){nodes{
            isResolved isOutdated path line
            comments(first:1){nodes{author{login} body createdAt}}
          }}
        }
      }
    }"""
    owner, name = REPO.split("/")
    data = gh_json([
        "api", "graphql", "-f", f"query={query}",
        "-F", f"owner={owner}", "-F", f"repo={name}", "-F", f"n={pr}",
    ])
    nodes = data["data"]["repository"]["pullRequest"]["reviewThreads"]["nodes"]
    # Pas de pagination : au-dela de 100 threads inline, les suivants seraient
    # invisibles. Plutot que de tronquer en silence — le mode d'echec que ce
    # script existe pour combattre — on le DIT. Theorique sur ce depot ; si le
    # message apparait, paginer devient necessaire, pas optionnel.
    if len(nodes) == 100:
        print(f"  [!] PR #{pr}: 100 threads inline retournes (plafond `first:100`) "
              "— d'eventuels threads supplementaires ne sont PAS analyses.",
              file=sys.stderr)
    out = []
    for t in nodes:
        first = (t.get("comments") or {}).get("nodes") or [{}]
        c = first[0]
        out.append({
            "resolved": bool(t.get("isResolved")),
            "outdated": bool(t.get("isOutdated")),
            "path": t.get("path"),
            "line": t.get("line"),
            "author": (c.get("author") or {}).get("login", "?"),
            "body": c.get("body", ""),
            "createdAt": c.get("createdAt"),
        })
    return out


def analyse(pr_data: dict, threads: list[dict], cutoff: datetime) -> dict:
    """cutoff = mergedAt (audit retro) ou now (gate pre-merge)."""
    commits = [ts(c.get("committedDate")) for c in (pr_data.get("commits") or [])]
    commits = [c for c in commits if c]
    last_commit = max(commits) if commits else None

    # Seuls les commentaires capables de LEVER comptent (cf can_lift) : un
    # commentaire de bot CI ou un tag de protocole nu n'a jamais repondu a rien.
    comment_times = [
        ts(c["createdAt"]) for c in (pr_data.get("comments") or []) if can_lift(c)
    ]
    comment_times = [t for t in comment_times if t]

    # Fenetre 05-29..06-04 (#1958) : la RE-REVIEW APPROVED. Le reviewer qui
    # revient approuver apres sa demande de changements A dit que la reserve
    # est levee — le state GitHub natif porte plus de sens que le body (une
    # re-review Hermes narre l'ancien verdict en le citant, sans mot de
    # levee). Seul APPROVED compte : une re-review COMMENTED qui re-emet une
    # reserve (« NOT FIXED », #2298) ne doit rien eteindre, et l'agent
    # d'exclusion can_lift ne s'applique pas — un state APPROVED n'est pas du
    # bruit de protocole, meme depuis un reviewer bot.
    approved_rereviews = [
        (ts(r.get("submittedAt")), (r.get("author") or {}).get("login", ""))
        for r in (pr_data.get("reviews") or [])
        if r.get("state") == "APPROVED"
        and (r.get("author") or {}).get("login", "") not in BOT_LOGINS
    ]
    approved_rereviews = [(t, a) for (t, a) in approved_rereviews if t]
    comment_times += [t for (t, _) in approved_rereviews]

    # Fenetre 2026-08-16 (#11222) : les temps plats ne suffisent pas pour un
    # CHANGES_REQUESTED. Une PHRASE explicite de levee (LIFT_MARKER non
    # conditionnel) dans un commentaire qui peut lever reste une levee pour
    # l'etat de review — c'est la reponse ecrite que B.0 exige. On garde
    # l'auteur pour la branche dedicated ci-dessous.
    explicit_lifts = [
        (ts(c["createdAt"]), (c.get("author") or {}).get("login", ""),
         c.get("body", ""))
        for c in (pr_data.get("comments") or [])
        if can_lift(c)
        and has_marker(c.get("body", ""), LIFT_MARKERS)
        and not CONDITIONAL_LIFT.search(_strip_quoted(c.get("body", "")))
    ]
    explicit_lifts = [x for x in explicit_lifts if x[0] is not None]

    signals: list[tuple] = []
    for c in pr_data.get("comments") or []:
        login = (c.get("author") or {}).get("login", "")
        kind = classify(login, c.get("body", ""))
        if kind:
            signals.append((ts(c["createdAt"]), kind, login, c.get("body", ""), "comment"))
    for r in pr_data.get("reviews") or []:
        login = (r.get("author") or {}).get("login", "")
        body = r.get("body", "")
        if r.get("state") == "DISMISSED":
            # Une dismissal GitHub n'est possible que par l'auteur de la review
            # (ou un admin) : la reserve est formellement RETIREE par son
            # emetteur — pas un signal (#11222, levée (b)).
            continue
        kind = classify(login, body)
        if r.get("state") == "CHANGES_REQUESTED":
            kind = "BOT-CONCERN" if kind is None else kind
        if kind:
            signals.append((ts(r.get("submittedAt")), kind, login, body,
                            f"review:{r.get('state')}"))

    blocking = []
    for (when, kind, login, body, src) in signals:
        if when is None or when >= cutoff:
            continue
        # Un commentaire posté APRÈS le merge ne peut pas avoir levé le nit :
        # c'est l'annonce de merge, pas une réponse. Sans cette borne, le gate
        # rate son propre incident fondateur (#10761, où mon commentaire de
        # merge « éteignait » rétroactivement le nit user posté 17 h plus tôt).
        if src == "review:CHANGES_REQUESTED":
            # Fenetre 2026-08-16 (#11222) : un CHANGES_REQUESTED est un ETAT
            # GitHub natif, pas une remarque en prose — un commentaire
            # posterieur quelconque ne l'eteint pas. Sur #11215, la review de
            # 08:34:39 etait eteinte par le commentaire 08:36:23 de son
            # PROPRE auteur (« Ma remarque de review sur le fond est
            # inchangee ») : le gate rendait EXIT=0. Le principe du state
            # natif (deja applique a la LEVEE par la re-review APPROVED
            # ci-dessus) est honore dans l'autre sens : l'etat ne se retire
            # que par son AUTEUR (re-review APPROVED ; la dismissal est
            # eliminee des la collecte), ou par une PHRASE explicite de levee
            # (B.0 : ce qui leve une remarque est une phrase). Les nits portes
            # par un COMMENTAIRE gardent le regime general ci-dessous — limite
            # NLP documentee dans can_lift.
            lifted = any(
                when < t < cutoff and author == login
                for (t, author) in approved_rereviews
            ) or any(
                when < t < cutoff
                for (t, _, _) in explicit_lifts
            )
            if lifted:
                continue
        elif any(when < t < cutoff for t in comment_times):
            continue  # discute/refuse explicitement apres le nit, avant le merge
        # Un commit poussé après le nit ne le lève PAS à lui seul : sur #10761,
        # le « traitement » était un rebase à 19:41 qui n'adressait aucun des
        # deux nits de 11:07. Le push est reporté comme contexte, pas comme levée
        # — seule une réponse écrite (ou un thread résolu) lève une remarque.
        pushed_after = last_commit is not None and last_commit > when
        blocking.append({
            "kind": kind, "author": login, "src": src,
            "at": when.isoformat(),
            "gap_hours": round((cutoff - when).total_seconds() / 3600.0, 1),
            "code_pushed_after": pushed_after,
            "excerpt": _excerpt(body),
        })

    for t in threads:
        if t["resolved"] or t["outdated"]:
            continue
        blocking.append({
            "kind": "INLINE-UNRESOLVED", "author": t["author"], "src": "reviewThread",
            "at": t.get("createdAt") or "?",
            "where": f"{t.get('path')}:{t.get('line')}",
            "excerpt": _excerpt(t.get("body") or ""),
        })

    return {
        "pr": pr_data.get("number"),
        "title": (pr_data.get("title") or "")[:110],
        "blocking": blocking,
        "blocked": bool(blocking),
    }


FIELDS = "number,title,mergedAt,author,comments,reviews,commits,url,state"

# `commits` porte une connection `authors` par commit : sur un `gh pr list` large,
# GraphQL depasse son plafond de 500 000 noeuds. L'audit retro liste donc SANS
# `commits`, puis ne les recupere que pour les PRs reellement candidates.
LIST_FIELDS = "number,title,mergedAt,url,comments,reviews"


def gate(pr: int, as_json: bool) -> int:
    data = gh_json(["pr", "view", str(pr), "--repo", REPO, "--json", FIELDS])
    merged = ts(data.get("mergedAt"))
    cutoff = merged or datetime.now(timezone.utc)
    result = analyse(data, review_threads(pr), cutoff)
    if as_json:
        print(json.dumps(result, indent=1, ensure_ascii=False))
    elif not result["blocked"]:
        print(f"OK  PR #{pr} — aucun nit non leve.")
    else:
        print(f"BLOCKED  PR #{pr} — {len(result['blocking'])} nit(s) non leve(s) :\n")
        for b in result["blocking"]:
            where = b.get("where", "")
            gap = f" (+{b['gap_hours']}h avant merge)" if "gap_hours" in b else ""
            print(f"  [{b['kind']}] {b['author']} via {b['src']}{where}{gap}")
            print(f"      {b['excerpt']}\n")
        print("Lever chaque nit (commit, reponse explicite, ou issue de suivi nommee)")
        print("avant `gh pr merge`. Cf CLAUDE.md section B.0.")
    return 1 if result["blocked"] else 0


def audit(limit: int, search: str | None = None) -> int:
    cmd = ["pr", "list", "--repo", REPO, "--state", "merged",
           "--limit", str(limit), "--json", LIST_FIELDS]
    if search:
        # Partitionnement de l'historique entre lanes, ex :
        #   --search "merged:2026-07-01..2026-07-15"
        cmd += ["--search", search]
    prs = gh_json(cmd)
    findings = []
    for p in prs:
        merged = ts(p.get("mergedAt"))
        if not merged:
            continue
        # Pre-filtre sans `commits` : si rien ne ressort deja, inutile de payer
        # un appel de plus (les commits ne peuvent que LEVER un nit, jamais en creer).
        if not analyse(p, [], merged)["blocked"]:
            continue
        try:
            p["commits"] = gh_json(
                ["pr", "view", str(p["number"]), "--repo", REPO, "--json", "commits"]
            )["commits"]
        except subprocess.CalledProcessError:
            p["commits"] = []
        # Ce 2e passage rend le MEME verdict `blocked` que le pre-filtre — un
        # commit ne leve rien (c'est le principe de B.0). Il n'est pas pour le
        # verdict : il renseigne `code_pushed_after`, dont la Phase 2 de #11044
        # a besoin pour trier (« du code a bouge apres le nit » = aller lire le
        # diff avant de conclure). Information de triage, pas critere.
        # Audit retro : on n'interroge pas les threads inline (1 appel GraphQL/PR).
        res = analyse(p, [], merged)
        if res["blocked"]:
            res["url"] = p.get("url")
            res["merged_at"] = p["mergedAt"]
            findings.append(res)
    findings.sort(key=lambda f: f["pr"], reverse=True)
    print(json.dumps({
        "scanned": len(prs),
        "search": search,
        "oldest_merged": min((p["mergedAt"] for p in prs if p.get("mergedAt")), default=None),
        "newest_merged": max((p["mergedAt"] for p in prs if p.get("mergedAt")), default=None),
        "flagged": len(findings),
        "findings": findings,
    }, indent=1, ensure_ascii=False))
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pr", nargs="?", type=int, help="numero de PR (mode gate)")
    ap.add_argument("--audit", action="store_true", help="audit retro des PRs mergees")
    ap.add_argument("--limit", type=int, default=200, help="taille de l'audit retro")
    ap.add_argument("--search", help="filtre gh (ex: 'merged:2026-07-01..2026-07-15')")
    ap.add_argument("--json", action="store_true", help="sortie machine (mode gate)")
    args = ap.parse_args()
    if args.audit:
        return audit(args.limit, args.search)
    if args.pr is None:
        ap.error("fournir un numero de PR, ou --audit")
    return gate(args.pr, args.json)


if __name__ == "__main__":
    sys.exit(main())
