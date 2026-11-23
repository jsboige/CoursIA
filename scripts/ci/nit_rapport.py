"""Le RAPPORT de l'organe B.0, extrait de `scripts/check_unaddressed_nits.py`.

#27874 — comme #27881 (la grammaire des marqueurs, `nit_markers.py`), le bloc
de rapport est extrait pour que l'organe ne grossisse pas : le cliquet de
taille (`scripts/ci/script_size_ceilings.json`) est epingle, et la cible T5
declaree dans la note du plafond — « separer la grammaire des marqueurs,
l'evaluation et le rapport » — est atteinte ici.

Le contrat est **byte-pour-byte** : les trois fonctions impriment exactement
ce qu'elles imprimaient avant l'extraction. Une seule dependance change de
forme : `_BLOB_UNCOMPARABLE` (constante du module d'origine) est passee en
argument, pour que l'organe reste l'unique proprietaire de la constante et
que `mod._BLOB_UNCOMPARABLE` reste lisible par les tests existants.

Aucun import reseau ici : ce module est pur (formatage + print).
"""

BLOB_UNCOMPARABLE = "uncomparable"


def ok_line(pr: int, result: dict) -> str:
    """La ligne de verdict, avec sa reserve DANS la ligne (#13512, #13779).

    `OK -- aucun nit non leve` repond « aucune phrase de levee ne manque », et
    RIEN D'AUTRE : un commentaire que `classify` n'a pas su lire n'est pas un
    commentaire absent. `print_unevaluated` le dit -- mais il le dit SOUS la
    ligne, et c'est la LIGNE qui circule : un agent qui rapporte « organe OK
    sur #N » cite le verdict, pas le bloc. Un `OK` cite sans sa reserve
    certifie alors exactement le silence que cet organe refuse de certifier,
    et la promesse de #13779 (« cesser de certifier le silence ») s'arrete a la
    frontiere du stdout.

    Mesure fondatrice (2026-09-21, arbitrage ai-01) : `check_unaddressed_nits.py`
    rendait `rc=0` -- et sa ligne `OK` a ete citee -- sur deux PRs dont les
    reserves vivaient dans le bloc « NON EVALUE(S) ». Un `rc=0` n'est pas une
    dispense de lecture, mais rien ne le rappelait la ou le verdict se lit.

    Le compte qui voyage est le TOTAL non evalue, jamais le sous-ensemble
    affiche -- meme regle que l'en-tete de `print_unevaluated`. Quand il n'y a
    rien a relire, la ligne reste celle d'avant, octet pour octet.
    """
    total = result.get("unevaluated_total") or 0
    if not total:
        return f"OK  PR #{pr} — aucun nit non leve."
    return (
        f"OK  PR #{pr} — aucun nit non leve parmi les commentaires evalues ; "
        f"{total} commentaire(s) NON EVALUE(S) — lire le bloc A RELIRE ci-dessous."
    )


def print_unevaluated(result: dict) -> None:
    """Imprimer verbatim ce que l'organe n'a pas evalue (#13512).

    La ligne de verdict porte desormais le compte (`ok_line`) ; ce bloc reste
    le detail -- le propos est le meme : ce que l'organe n'a pas su classer, il
    l'imprime.
    """
    rows = result.get("unevaluated") or []
    if not rows:
        return
    # #13779 : le compte imprime est celui du TOTAL non evalue, pas celui des
    # lignes affichees -- un organe dont tout le propos est de ne pas certifier
    # son propre silence ne peut pas sous-declarer ce qu'il n'a pas lu.
    total = result.get("unevaluated_total") or len(rows)
    omitted = total - len(rows)
    after = sum(1 for r in rows if r["after_last_commit"])
    tail = f", dont {after} posterieur(s) au dernier commit" if after else ""
    cut = f" — {len(rows)} affiche(s), {omitted} plus ancien(s) omis" if omitted > 0 else ""
    print()
    print(f"  --- A RELIRE : {total} commentaire(s) NON EVALUE(S) par cet organe{tail}{cut} ---")
    print("  Le verdict ci-dessus ne porte QUE sur les phrases de levee. Ces")
    print("  commentaires n'ont pas ete classes : les lire avant `gh pr merge`.")
    for r in rows:
        mark = " [APRES LE DERNIER COMMIT]" if r["after_last_commit"] else ""
        print()
        print(f"  * {r['author']} — {r['at']}{mark}")
        lines = r["body"].split("\n")
        for line in lines[:8]:
            print(f"      {line[:160]}")
        if len(lines) > 8:
            print(f"      ... (+{len(lines) - 8} ligne(s))")
    print()


def print_sha_notes(result: dict, blob_uncomparable: str = BLOB_UNCOMPARABLE) -> None:
    """#13639 : nommer les levees dont la preuve citee manque de la PR.

    #15556 : distinguer l'ARTEFACT du vrai defaut -- un push muet
    (wake-commit, amend de message) ne change pas l'arbre, la preuve citee
    reste byte-pour-byte vraie ; seul le SHA a change. Les deux cas ne
    demandent pas le meme geste au lecteur, et l'artefact ne bloque pas.

    `blob_uncomparable` est la constante `_BLOB_UNCOMPARABLE` de l'organe,
    passee en argument : le module reste pur et ne possede pas la constante.
    """
    for a in result.get("rewind_artifacts") or []:
        if a["reason"] == "same_tree":
            why = "arbre identique à la tête"
        elif a["reason"] == "rebase_preserved":
            why = "rebase sur base avancée, blobs identiques par chemin"
        elif a["reason"] == "symbols_survive":
            # #20066 piste 2 : le blob a bougé (la PR a continué de
            # travailler), mais la SUBSTANCE de la levée est mesurée
            # présente -- chaque def/class introduit par le commit cité
            # existe encore à la tête.
            why = ("blobs modifiés mais symboles introduits par la levée "
                   "tous présents à la tête")
        else:
            why = "fichiers de la PR inchangés"
        print(f"  [i] levee de {a['author']} à {a['at']} cite {a['sha']} "
              f"rembobiné par un push muet ({why}) — preuve conservée, "
              f"non bloquant")
    for v in result.get("voided_lifts") or []:
        # #20066 -- `tree_differs` dit que les deux arbres sont connus et
        # differents ; il ne dit pas qu'un BLOB a ete compare. Quand
        # `sha_files` est vide (pas d'entree pour ce SHA), ou la carte de la
        # tete vide, `_rebase_blob_state` rend `uncomparable` : le refus est
        # le meme, le libelle doit dire qu'aucun blob n'a ete regarde.
        if not v.get("tree_differs"):
            detail = " — arbre non comparable, refus conservateur"
        elif v.get("blob_state") == blob_uncomparable:
            detail = (" — l'arbre DIFFÈRE de la tête : aucun blob comparable, "
                      "refus conservateur")
        elif (v.get("symbols") or {}).get("verdict") == "missing":
            # #20066 piste 2 : le fond a ÉTÉ mesuré, et il manque -- c'est
            # la seule formule qui ait le droit de parler de réserve, car
            # elle nomme ce qui a disparu.
            absents = ", ".join((v["symbols"].get("missing") or [])[:5])
            detail = (f" — l'arbre DIFFÈRE de la tête : blob modifié et "
                      f"symbole(s) introduit(s) par la levée ABSENT(s) de "
                      f"la tête ({absents})")
        else:
            detail = (" — l'arbre DIFFÈRE de la tête : blob modifié depuis la levée, fond non vérifié")
        print(f"  [!] NON LEVE — levee de {v['author']} à {v['at']} : cite "
              f"{v['sha']}, absent des commits de la PR (résolu côté serveur, "
              f"mais rembobiné par un push ultérieur){detail}")
    for w in result.get("absent_sha_warnings") or ():
        print(f"  [i] levee de {w['author']} à {w['at']} cite {w['sha']} "
              f"(absent des commits, non rattaché à cette PR) — non bloquant")
