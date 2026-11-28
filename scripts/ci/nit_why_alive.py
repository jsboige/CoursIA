"""Pourquoi une reserve de B.0 survit : le DIAGNOSTIC de l'organe, extrait.

#28924 -- l'organe (`scripts/check_unaddressed_nits.py`) annoncait un nit non
leve par une seule ligne : « BLOCKED -- 1 nit(s) non leve(s) », puis l'auteur
et l'extrait de la reserve. Rien ne disait POURQUOI les reponses deja postees
ne l'avaient pas levee. Mesure fondatrice sur #28876, entre la deuxieme et la
troisieme reponse de la lane : la deuxieme portait une phrase de levee vive
mais son prefixe `[ACTION]` etait lu comme un prefixe de ROLE (une levee
portee par un role ne leve pas une reserve en voix nue, #14850) ; la premiere
ne portait aucune phrase reconnue, et son `[ACTION]` aurait bute sur la meme
porte. Ces refus vivaient dans `_lift_eligible` sous forme de `return False`
muets, et la lane n'a trouve la cause qu'en lisant le code.

Deux roles, aucun verdict :

* `refusal` -- le LIBELLE de chaque refus de `_lift_eligible`. L'organe garde
  l'evaluation des conditions et n'appelle que `_refuse(key, *args)` ; la
  phrase imprimee vit ici, avec le reste du rapport (cliquet de taille,
  cible T5 : « separer la grammaire des marqueurs, l'evaluation et le
  rapport »).
* `explain` -- les deux cles ADDITIVES d'une entree de `blocking` :
  `reserve_nature` (la nature de la reserve, telle que `_lift_eligible` la
  lit) et `why_alive` (une ligne par reponse candidate, avec les conditions
  qu'elle a echouees). Il ne tourne qu'APRES qu'une entree de `blocking` a
  ete decidee ; aucun booleen de l'organe ne lit ces cles.

Une reponse est expliquee par TOUTES les conditions qu'elle echoue, pas par
la seule premiere : chacune suffit a elle seule a laisser la reserve vivante,
et une lane qui n'en corrige qu'une rebute au tour suivant.

Collaborateurs : les fonctions et constantes de l'organe sont lues AU MOMENT
DE L'APPEL a travers un proxy LIVE de ses globales (meme montage que le funnel
`scripts/ci/b0_funnel.py`, #27319) -- les monkeypatchs des tests
(`mod.has_live_lift`, `mod.can_lift`, ...) sont donc honores, et deux
instances de l'organe chargees dans un meme processus ne se croisent pas.
`_lift_eligible` fait exception : imbriquee dans `analyse`, elle voyage dans
le contexte (`ctx["lift_eligible"]`).

Trois surfaces de levee, celles que les trois branches de l'organe consultent,
relues ici dans l'ordre et avec les bornes de l'organe : les phrases de levee
(`explicit_lifts`, apres le crible SHA), les re-reviews APPROVED
(`approved_rereviews`) et les renvois a une issue de suivi ouverte
(`followup_lifts`).
"""
from __future__ import annotations

import re
from typing import Callable

#: Le libelle de la condition « phrase de levee », partage par le pre-filtre
#: des phrases et par la chute de `_lift_eligible` : les deux disent la meme
#: chose d'une reponse qui n'en porte aucune.
AUCUNE_LEVEE = (
    "aucune phrase de levée reconnue : ni marqueur explicite de "
    "`EXPLICIT_LIFT_MARKERS` (« Je lève », « Levée de », « Lève la »), "
    "ni forme du jeu large `LIFT_MARKERS`")

#: Nombre de reponses imprimees en mode texte (les plus recentes). La sortie
#: `--json` les porte toutes : un couperet d'affichage n'est pas une mesure.
MAX_TEXT = 6

_REVIEW_CHANGES_REQUESTED = "review:CHANGES_REQUESTED"


def shown_prefix(match) -> str:
    """Le prefixe entre crochets d'un matche, tel qu'il figure dans le corps.

    « [ACTION] » pour un prefixe de role, « [Hermes] » pour une persona ; le
    texte nu quand le matche n'a pas de crochets (forme gras en tete de
    paragraphe, par exemple).
    """
    bracketed = re.search(r"\[[^\]]*\]", match.group(0))
    return bracketed.group(0) if bracketed else match.group(0).strip()


#: La cause d'un thread inline non resolue : l'organe ne retient qu'un thread
#: qui n'est NI resolu sur GitHub, NI devenu obsolete apres un push (la boucle
#: `for t in threads` saute les deux autres).
INLINE_NATURE = (
    "thread de review inline non résolu : il sort du rouge en le résolvant sur "
    "GitHub, ou par un push qui rend sa ligne obsolète")


def explain_inline() -> dict:
    """Les deux cles d'un thread inline non resolue (#28924).

    Un thread ne se leve par aucune des trois surfaces relues par `explain`
    (phrase, re-review, renvoi) : sa cause est son etat meme.
    """
    return {"reserve_nature": INLINE_NATURE, "why_alive": []}


def _nature(nits, body: str) -> str:
    """La nature de la reserve, lue par les memes patrons que `_lift_eligible`.

    Un blocage est nomme le premier, avec son marqueur (`[BLOCAGE] lane X`,
    `[BLOCK] lane X`, `[HOLD] lane X`) : ses voies de levee sont plus etroites
    que celles d'une reserve (#13083), et le marqueur `[BLOCAGE]` lu comme un
    simple prefixe de role ne le disait pas.
    """
    stripped = nits._strip_quoted(body or "")
    m = nits.BLOCAGE_LANE.search(nits._unaccent(stripped))
    if m:
        return f"blocage « {m.group(0).strip()} »"
    if nits._block_emitted(body or ""):
        return "blocage (verdict posé en tête du corps)"
    for pattern, label in ((nits._PERSONA_MARKERS_RE, "de persona"),
                           (nits._ROLE_PREFIX_RE, "de rôle"),
                           (nits._CROSS_LANE_LIFT_RE, "de lane")):
        m = pattern.search(stripped)
        if m:
            return f"réserve {label} {shown_prefix(m)}"
    return "réserve en voix nue"


def _reply_candidates(nits, pr_data: dict):
    """Les reponses candidates : commentaires et reviews COMMENTED levables.

    `can_lift` fait foi (bots, tags de protocole nus et corps-pointeurs
    ecartes) : ce sont exactement les lignes que l'organe consulte comme
    phrases de levee possibles.
    """
    for c in pr_data.get("comments") or ():
        if not nits.can_lift(c):
            continue
        yield (nits.ts(c.get("createdAt")), nits._author_login(c),
               c.get("body") or "", "comment")
    for r in pr_data.get("reviews") or ():
        if r.get("state") != "COMMENTED" or not nits.can_lift(r):
            continue
        yield (nits.ts(r.get("submittedAt")), nits._author_login(r),
               r.get("body") or "", "review")


def _voided_detail(ctx: dict, t, author: str) -> str:
    """Le motif du crible SHA (#13639, #15556), tel que `voided_lifts` le porte."""
    at = t.isoformat()
    v = next((x for x in ctx["voided_lifts"]
              if x.get("at") == at and x.get("author") == author), None)
    if not v:
        return ("la réponse cite un commit absent des commits de la PR : elle "
                "n'a pas été retenue comme levée (#13639)")
    if v.get("tree_differs"):
        return (f"la réponse cite {v.get('sha')}, rembobiné par un push "
                "ultérieur : la preuve ne pointe plus l'arbre de la tête "
                "(#13639, #15556)")
    return (f"la réponse cite {v.get('sha')}, absent des commits de la PR et "
            "non rattaché à elle : la preuve n'est pas vérifiable (#13639)")


def _reply_rows(nits, ctx: dict, reserve: tuple) -> list[dict]:
    """Une ligne par reponse candidate posterieure a la reserve.

    Conditions relues dans l'ordre de l'organe : la comprehension
    `explicit_lifts` (phrase vive, levee non annulee, reponse qui n'est pas
    elle-meme une reserve), le crible SHA, puis `_lift_eligible`, puis la
    borne de blocage #13083. Les conditions de portee de `_lift_eligible` ont
    la propriete de ne dependre ni de la phrase ni du SHA : elles sont donc
    relirees aussi pour une reponse sans phrase, pour dire d'un coup les deux
    gestes a faire (ecrire la phrase, et sans prefixe de role).
    """
    when, kind, login, body, src = reserve
    rows: list[dict] = []
    for (t, author, rbody, channel) in _reply_candidates(nits, ctx["pr_data"]):
        if t is None or not (when < t < ctx["cutoff"]):
            continue
        pairs: list[tuple[str, str]] = []

        def add(tag: str, detail: str = "") -> None:
            if tag not in [seen for seen, _ in pairs]:
                pairs.append((tag, detail))

        live = bool(nits.has_live_lift(nits._strip_adjoint_dossier(rbody)))
        if not live:
            add("AUCUNE-LEVEE", AUCUNE_LEVEE)
        cancelled = bool(nits._lift_cancelled(nits._strip_quoted(rbody)))
        if live and cancelled:
            add("LEVEE-ANNULEE",
                "la réponse annule sa propre levée (formulation conditionnelle "
                "ou rétractation) : elle ne lève pas (#12074)")
        if nits.classify(author, rbody) is not None:
            add("EST-RESERVE",
                "la réponse est elle-même lue comme une réserve : une réserve "
                "ne lève rien")
            rows.append({"at": t.isoformat(), "author": author,
                         "channel": channel, "surface": "phrase", "pairs": pairs})
            continue
        in_lifts = (t, author, rbody) in ctx["explicit_lifts"]
        if live and not cancelled and not in_lifts:
            add("SHA-REMBOBINE", _voided_detail(ctx, t, author))
        why: list[tuple[str, str]] = []
        eligible = bool(ctx["lift_eligible"](author, login, rbody, body,
                                              _why=why))
        for tag, detail in why:
            add(tag, detail)
        if eligible and in_lifts:
            # Les trois branches consultent cette levee : si la reserve
            # survit, c'est que la borne de blocage #13083 a parle.
            guard_fails = (kind == "BLOCK"
                           and src != _REVIEW_CHANGES_REQUESTED
                           and author == ctx["pr_author"]
                           and not nits.OVERRIDE_LANE.search(rbody))
            add("AUTEUR" if guard_fails else "A-EXAMINER", _BLOCK_GUARD_DETAIL
                if guard_fails else _UNMODELLED_DETAIL)
        rows.append({"at": t.isoformat(), "author": author,
                     "channel": channel, "surface": "phrase", "pairs": pairs})
    return rows


def _approval_rows(nits, ctx: dict, reserve: tuple) -> list[dict]:
    """Une ligne par re-review APPROVED posterieure a la reserve.

    Miroir de `_approved_lifts_reserve` : la borne est « posterieure a la
    reserve », sans coupure -- c'est celle que l'organe applique ici.
    """
    when, _kind, login, _body, _src = reserve
    rows: list[dict] = []
    for (t, author, abody) in ctx["approved_rereviews"]:
        if t is None or t <= when:
            continue
        pairs: list[tuple[str, str]] = []
        if author == login:
            if login == ctx["pr_author"]:
                pairs.append((
                    "AUTO-APPROBATION",
                    "re-review APPROVED de l'auteur de la réserve, qui est "
                    "aussi l'auteur de la PR : une auto-approbation ne lève "
                    "rien (#12319)"))
        elif author == ctx["pr_author"]:
            pairs.append((
                "AUTEUR",
                "l'auteur de la PR approuve : son approbation ne remplace pas "
                "la levée de l'auteur de la réserve (#13399)"))
        elif not nits._names_author(abody, login):
            pairs.append((
                "APPROVAL-SANS-NOM",
                f"approbation de `{author}` qui ne nomme pas la réserve : une "
                "approbation générique n'identifie aucune réserve (#13399)"))
        if not pairs:
            pairs.append(("A-EXAMINER", _UNMODELLED_DETAIL))
        rows.append({"at": t.isoformat(), "author": author,
                     "channel": "review", "surface": "approval",
                     "pairs": pairs})
    return rows


def _short(text: str, limit: int = 60) -> str:
    text = " ".join((text or "").split())
    return text if len(text) <= limit else text[:limit - 1] + "…"


def _followup_rows(nits, ctx: dict, reserve: tuple) -> list[dict]:
    """Une ligne par renvoi a une issue de suivi posterieur a la reserve.

    Miroir des trois `any(...)` de l'organe, conditions 1 a 6 de
    `collect_followup_lifts` (#13495, #14218).
    """
    when, _kind, login, _body, _src = reserve
    rows: list[dict] = []
    for (t, namer, info) in ctx["followup_lifts"]:
        if t is None or not (when < t < ctx["cutoff"]):
            continue
        pairs: list[tuple[str, str]] = []
        # Trois conditions independantes : chacune suffit a laisser la reserve
        # vivante, chacune est donc nommee.
        if (namer not in (login, ctx["pr_author"])
                and namer not in nits.LIFT_OVERRIDE_LOGINS):
            pairs.append((
                "AUTEUR",
                f"`{namer}` n'est ni l'auteur de la réserve, ni l'auteur de la "
                "PR, ni le coordinateur : son renvoi ne lève pas (#13495)"))
        if info.created_at is not None and not (when < info.created_at):
            pairs.append((
                "SUIVI-ANTERIEUR",
                f"l'issue de suivi nommée (« {_short(info.title)} ») est "
                "antérieure à la réserve : elle ne peut pas la reporter "
                "(#14218)"))
        if not nits._issue_references_pr(info, ctx["pr_number"]):
            pairs.append((
                "SUIVI-SANS-LIEN",
                f"l'issue de suivi nommée (« {_short(info.title)} ») ne "
                "référence pas cette PR : le lien report / réserve n'est pas "
                "établi (#14218)"))
        if not pairs:
            pairs.append(("A-EXAMINER", _UNMODELLED_DETAIL))
        rows.append({"at": t.isoformat(), "author": namer,
                     "channel": "comment", "surface": "followup",
                     "pairs": pairs})
    return rows


def _merge(rows: list[dict]) -> list[dict]:
    """Fusionner les lignes d'une meme reponse (phrase + renvoi, par exemple)."""
    merged: dict[tuple, dict] = {}
    for r in rows:
        key = (r["at"], r["author"])
        if key not in merged:
            merged[key] = {"at": r["at"], "author": r["author"],
                           "channel": r["channel"],
                           "surfaces": [r["surface"]],
                           "pairs": list(r["pairs"])}
            continue
        m = merged[key]
        if r["surface"] not in m["surfaces"]:
            m["surfaces"].append(r["surface"])
        seen = [tag for tag, _ in m["pairs"]]
        for pair in r["pairs"]:
            if pair[0] not in seen:
                m["pairs"].append(pair)
                seen.append(pair[0])
    return list(merged.values())


_BLOCK_GUARD_DETAIL = (
    "la levée est recevable, mais un blocage ne se lève ni par l'auteur de la "
    "PR ni par un compte qui en est à la fois l'auteur et l'émetteur sans "
    "`[OVERRIDE] lane` (#13083)")

#: Une reponse qui satisfait toutes les conditions relues ici alors que la
#: reserve survit : le diagnostic ne modelise pas une condition de l'organe. Il
#: le DIT -- un diagnostic muet sur un cas qu'il ne comprend pas est le defaut
#: meme que #28924 repare.
_UNMODELLED_DETAIL = (
    "cette réponse satisfait toutes les conditions que ce diagnostic relit, et "
    "la réserve survit pourtant : une condition de l'organe n'est pas "
    "modélisée ici -- à remonter sur #28924")


def explain(nits, ctx: dict, reserve: tuple) -> dict:
    """Les deux cles ADDITIVES d'une entree de `blocking` (#28924).

    `nits` est le proxy live des globales de l'organe ; `ctx` porte les
    surfaces deja calculees par `analyse` et la fermeture `_lift_eligible` ;
    `reserve` est le signal survivant (`when`, `kind`, `login`, `body`, `src`).

    Le contrat est « la sortie ajoute la cause, elle ne change aucun
    verdict » : une erreur du diagnostic ne remonte donc JAMAIS dans l'organe.
    Elle est ecrite dans l'entree, visible, et rien d'autre.
    """
    # TOUTE erreur est ici, dans `explain` : ce qui sort vers l'organe est
    # toujours le couple de cles, jamais une exception.
    try:
        return _explain(nits, ctx, reserve)
    except Exception as exc:  # diagnostic : le verdict ne doit jamais en dependre
        return {"reserve_nature": None, "why_alive": [{
            "at": "", "author": "", "channel": "", "surfaces": [],
            "failed": ["DIAGNOSTIC-INDISPONIBLE"],
            "detail": [f"le diagnostic de survie n'a pas pu être calculé "
                       f"({type(exc).__name__}) -- à remonter sur #28924"]}]}


def _explain(nits, ctx: dict, reserve: tuple) -> dict:
    rows = _merge(_reply_rows(nits, ctx, reserve)
                  + _approval_rows(nits, ctx, reserve)
                  + _followup_rows(nits, ctx, reserve))
    rows.sort(key=lambda r: (r["at"], r["author"]))
    why = [{"at": r["at"], "author": r["author"], "channel": r["channel"],
            "surfaces": r["surfaces"],
            "failed": [tag for tag, _ in r["pairs"]],
            "detail": [d for _, d in r["pairs"] if d]}
           for r in rows if r["pairs"]]
    return {"reserve_nature": _nature(nits, reserve[3]), "why_alive": why}


# ----------------------------------------------------------------------
# Les libelles des refus de `_lift_eligible`, par cle. La cle nomme la
# CONDITION evaluee dans l'organe ; le premier element est le tag imprime
# (la famille : PERSONA, LANE, ROLE, AUTEUR, OVERRIDE, ...).
# ----------------------------------------------------------------------

_REFUSALS: dict[str, tuple[str, Callable]] = {
    "PERSONA-SCOPE": (
        "PERSONA",
        lambda persona: (
            f"portée de persona {persona} : une levée signée d'une persona ne "
            "lève pas une réserve en voix nue (#14850)")),
    "PERSONA-LANE": (
        "PERSONA",
        lambda: (
            "marqueur de persona posé par la lane de la PR : la voie persona "
            "est réservée au dialogue `clusterManager-Myia` <-> self-bot "
            "`jsboige` (#18149)")),
    "LANE-SCOPE": (
        "LANE",
        lambda lane: (
            f"portée de lane « {lane} » : une levée signée d'une lane ne lève "
            "que les réserves de cette lane (#14850)")),
    "ROLE-DIFFERENT": (
        "ROLE",
        lambda lift_role, nit_role: (
            f"rôles différents : la levée est signée « {lift_role} », la "
            f"réserve « {nit_role} » (#18937)")),
    "ROLE-SCOPE": (
        "ROLE",
        lambda role, nit_has_persona, nit_has_lane: (
            f"portée de rôle « {role} » : une levée préfixée d'un rôle ne lève "
            "pas " + ("une réserve de persona" if nit_has_persona
                      else "une réserve de lane" if nit_has_lane
                      else "une réserve en voix nue") + " (#14850)")),
    "NU-SUR-PERSONA": (
        "NU-SUR-PERSONA",
        lambda: (
            "levée en voix nue sous `jsboige` d'une réserve de persona : elle "
            "exige un close-the-loop nommé (« mon concern », « ma review »), "
            "une levée signée de la persona, un override nommé ou une re-review "
            "(#17507)")),
    "AUCUNE-LEVEE": ("AUCUNE-LEVEE", lambda: AUCUNE_LEVEE),
    "AUTEUR-PR": (
        "AUTEUR",
        lambda: (
            "la réponse vient de l'auteur de la PR, qui n'est pas l'auteur de "
            "la réserve : une réponse documente le traitement, elle ne "
            "remplace pas la levée de l'auteur (#11145, #13495)")),
    "AUTEUR-TIERS": (
        "AUTEUR",
        lambda lift_author, nit_author: (
            f"`{lift_author}` n'est ni l'auteur de la réserve "
            f"(`{nit_author}`), ni un compte de levée nommé (coordinateur, "
            "adjoint, persona) : une tierce partie documente, elle ne lève "
            "pas (#11145)")),
    "OVERRIDE-ADJOINT-TETE": (
        "OVERRIDE",
        lambda: (
            "voix adjointe sans tête `[OVERRIDE] lane` : la levée de "
            "l'adjoint exige cette forme en tête de ligne (Q185)")),
    "OVERRIDE-ADJOINT-PERIMETRE": (
        "OVERRIDE",
        lambda nit_author: (
            f"voix adjointe sur une réserve hors de son périmètre (auteur "
            f"`{nit_author}`) : elle ne lève que les réserves de bot, jamais "
            "celles du coordinateur, du user, d'une autre lane ou d'un humain "
            "(Q185)")),
    "OVERRIDE-SANS-NOM": (
        "OVERRIDE",
        lambda: (
            "l'override ne nomme pas nommément cette réserve : il ne lève que "
            "les réserves de son auteur (#14216)")),
}


def refusal(key: str, *args) -> tuple[str, str]:
    """Le couple `(tag, detail)` d'un refus de `_lift_eligible` (#28924)."""
    family, build = _REFUSALS[key]
    return family, build(*args)


def _stamp(iso: str) -> str:
    """`2026-11-27T19:27:10+00:00` -> `2026-11-27T19:27:10Z` (UTC explicite)."""
    return iso.replace("+00:00", "Z")


def print_notes(entry: dict) -> None:
    """Imprimer la cause de survie d'un nit, sous son extrait (mode texte)."""
    nature = entry.get("reserve_nature")
    rows = entry.get("why_alive") or []
    if not nature and not rows:
        return
    label = nature or "nature de la réserve non lue"
    if not rows:
        # Un thread inline n'a pas de reponse candidate a relire : sa cause
        # est complete telle quelle.
        tail = "" if nature == INLINE_NATURE else " — aucune réponse candidate après elle."
        print(f"      cause : {label}{tail}")
        return
    print(f"      cause : {label} — {len(rows)} réponse(s) candidate(s), "
          "aucune retenue :")
    shown = rows[-MAX_TEXT:]
    omitted = len(rows) - len(shown)
    if omitted:
        print(f"        (+{omitted} plus ancienne(s), même objet — voir --json)")
    for r in shown:
        surfaces = r.get("surfaces") or []
        via = "" if surfaces == ["phrase"] else f" ({'/'.join(surfaces)})"
        who = " ".join(x for x in (_stamp(r.get("at") or ""),
                                   r.get("author") or "",
                                   f"via {r['channel']}" if r.get("channel") else "")
                       if x)
        print(f"        {who}{via} — {', '.join(r.get('failed') or [])}")
        for detail in r.get("detail") or ():
            print(f"            {detail}")
