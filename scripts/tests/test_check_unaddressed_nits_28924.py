"""Tests #28924 -- la cause d'un nit non levé, livrée par l'organe B.0.

Contrat (coordinateur, DM `msg-20261127T202318-uwp35x`) : la sortie du gate
`scripts/check_unaddressed_nits.py` AJOUTE, pour chaque nit non levé, la
condition qui a échoué -- voix nue, portée de rôle `[ACTION]`, marqueur
explicite absent de `EXPLICIT_LIFT_MARKERS`, auteur non habilité -- et ne
change AUCUN verdict.

Cas fondateur : PR #28876. Entre sa deuxième et sa troisième réponse, la lane
a relu le code de l'organe pour comprendre pourquoi le gate restait rouge :

  * la première réponse (`[ACTION] Densité restaurée -- ...`) ne portait
    aucune phrase de levée reconnue ;
  * la deuxième (`[ACTION] Réserve de densité levée -- ...`) en portait une,
    mais son préfixe `[ACTION]` est lu comme un préfixe de RÔLE : une levée
    signée d'un rôle ne lève pas une réserve en voix nue (#14850) ;
  * la troisième (`Levée de la réserve de densité ...`), sans préfixe, lève.

Les quatre corps ci-dessous sont ceux de la PR, réduits à leurs deux premiers
paragraphes (la suite est la liste du contenu ré-ajouté, sans marqueur de
levée).

Acceptance :
  1. une entrée de `blocking` porte deux clés additives, `reserve_nature` et
     `why_alive`, et rien d'autre ne change ;
  2. chaque réponse candidate postérieure à la réserve est expliquée par
     TOUTES les conditions qu'elle échoue ;
  3. le mode texte imprime la cause sous l'extrait du nit ;
  4. une erreur du diagnostic s'écrit dans l'entrée, jamais dans le verdict.
"""
import importlib.util
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"

spec = importlib.util.spec_from_file_location(
    "check_unaddressed_nits_28924", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits_28924"] = mod
spec.loader.exec_module(mod)
why = mod.nit_why_alive


def utc(year: int, month: int, day: int, hour: int, minute: int = 0) -> datetime:
    return datetime(year, month, day, hour, minute, tzinfo=timezone.utc)


def at(hour: int, day: str = "2026-09-05") -> str:
    return f"{day}T{hour:02d}:00:00Z"


def comment(login: str, hour: int, body: str, day: str = "2026-09-05") -> dict:
    return {"author": {"login": login}, "createdAt": at(hour, day), "body": body}


def run(comments: list, cutoff: datetime, reviews: list = None, threads: list = None,
        pr_author: str = "jsboige", number: int = 0, commits: list = None,
        data_extra: dict = None, **analyse_kwargs) -> dict:
    """`analyse()` sur une PR montée de toutes pièces."""
    data = {
        "number": number, "title": "t", "author": {"login": pr_author},
        "comments": comments, "reviews": reviews or [],
        "commits": COMMIT_TEMOIN if commits is None else commits,
    }
    data.update(data_extra or {})
    return mod.analyse(data, threads or [], cutoff, **analyse_kwargs)


def lines(result: dict, index: int = 0) -> list:
    """`(conditions échouées, détails)` de chaque ligne de `why_alive`."""
    return [(tuple(w["failed"]), w["detail"])
            for w in result["blocking"][index]["why_alive"]]


def unique(result: dict, index: int = 0) -> dict:
    """La seule ligne de `why_alive` d'une entrée qui n'admet qu'une réponse."""
    rows = result["blocking"][index]["why_alive"]
    assert len(rows) == 1, rows
    return rows[0]


def failed(result: dict, index: int = 0) -> list:
    return [w["failed"] for w in result["blocking"][index]["why_alive"]]


COMMIT_TEMOIN = [{"oid": "abc" + "0" * 37, "committedDate": at(13)}]


def run_temoins(comments: list, cutoff: datetime = None, **kwargs) -> dict:
    return run(comments, cutoff or utc(2026, 9, 6, 18), **kwargs)


CLES_ORGAN = {"kind", "author", "src", "channel", "at", "gap_hours",
              "code_pushed_after", "excerpt"}
CLES_DIAGNOSTIC = {"reserve_nature", "why_alive"}

# --- Le cas #28876 : corps réels, réduits à leurs deux premiers paragraphes ------

JOUR = "2026-11-27"

#: Comment 7219843906 : la réserve du mainteneur, en voix nue.
NIT_28876 = comment("jsboige", 13, "", JOUR)
NIT_28876["createdAt"] = f"{JOUR}T13:42:31Z"
NIT_28876["body"] = ("Concern: Attention on a perdu en densité, il faudrait "
                     "développer un peu.")

#: Comment 7221094424 : un compte rendu d'action, sans phrase de levée.
ACTION_1 = comment("jsboige", 14, "", JOUR)
ACTION_1["createdAt"] = f"{JOUR}T14:41:08Z"
ACTION_1["body"] = (
    "[ACTION] Densité restaurée — commit `d1426d5bd3d`, le fichier passe de "
    "308 à 429 lignes, sans redevenir la copie de l'ancien.\n\n"
    "Ce qui a été ré-ajouté, dans la forme que demande "
    "`docs/reference/readme-series-gabarit.md` :")

#: Comment 7226540941 : une phrase de levée, sous le préfixe `[ACTION]`.
ACTION_2 = comment("jsboige", 19, "", JOUR)
ACTION_2["createdAt"] = f"{JOUR}T19:27:10Z"
ACTION_2["body"] = (
    "[ACTION] Réserve de densité levée — commit `5841dddff21` : le README passe "
    "de 428 à 504 lignes et retrouve le contenu carnet par carnet\n\n"
    "La mesure manquait dans ma réponse précédente : je comparais la tête à "
    "l'état antérieur de cette branche (308 → 429), pas à `main`.")

#: Comment 7226560379 : la même levée, en voix nue.
LEVEE_3 = comment("jsboige", 19, "", JOUR)
LEVEE_3["createdAt"] = f"{JOUR}T19:28:21Z"
LEVEE_3["body"] = (
    "Levée de la réserve de densité sur ce README — commit `5841dddff21` : "
    "428 → 504 lignes, le contenu carnet par carnet est rétabli\n\n"
    "La mesure manquait dans ma réponse précédente : je comparais la tête à "
    "l'état antérieur de cette branche (308 → 429), pas à `main`.")

COMMITS_28876 = [
    {"oid": "d1426d5bd3d" + "0" * 29, "committedDate": f"{JOUR}T14:40:00Z"},
    {"oid": "5841dddff21" + "0" * 29, "committedDate": f"{JOUR}T19:26:00Z"},
]

AVANT_REPONSE_3 = utc(2026, 11, 27, 19, 28)
APRES_TOUT = utc(2026, 11, 27, 20)
DETAIL_ROLE = ("portée de rôle « [ACTION] » : une levée préfixée d'un rôle ne "
               "lève pas une réserve en voix nue (#14850)")


def run_28876(comments: list, cutoff: datetime = AVANT_REPONSE_3) -> dict:
    return run(comments, cutoff, number=28876, commits=COMMITS_28876)


# --- Acceptance 1 + 2 : les deux cas de #28876 ----------------------------------


def test_28876_reponse_sans_phrase_de_levee():
    """Première réponse : elle n'est ni une levée, ni en voix nue. Les DEUX
    conditions sont nommées -- corriger la seule phrase fait buter au tour
    suivant sur le préfixe."""
    res = run_28876([NIT_28876, ACTION_1], cutoff=utc(2026, 11, 27, 19))
    assert res["blocked"] is True
    entry = res["blocking"][0]
    assert entry["reserve_nature"] == "réserve en voix nue"
    assert set(entry) == CLES_ORGAN | CLES_DIAGNOSTIC
    assert len(entry["why_alive"]) == 1
    ligne = entry["why_alive"][0]
    assert (ligne["at"], ligne["author"], ligne["channel"], ligne["surfaces"]) == (
        "2026-11-27T14:41:08+00:00", "jsboige", "comment", ["phrase"])
    assert ligne["failed"] == ["AUCUNE-LEVEE", "ROLE"]
    assert ligne["detail"] == [why.AUCUNE_LEVEE, DETAIL_ROLE]


def test_28876_levee_masquee_par_son_prefixe_action():
    """Deuxième réponse : la phrase de levée est vive et son SHA est celui d'un
    commit de la PR ; seule la portée de rôle la rejette."""
    res = run_28876([NIT_28876, ACTION_1, ACTION_2])
    assert res["blocked"] is True
    assert res["blocking"][0]["reserve_nature"] == "réserve en voix nue"
    assert [(w["at"], w["failed"]) for w in res["blocking"][0]["why_alive"]] == [
        ("2026-11-27T14:41:08+00:00", ["AUCUNE-LEVEE", "ROLE"]),
        ("2026-11-27T19:27:10+00:00", ["ROLE"]),
    ]
    assert res["blocking"][0]["why_alive"][1]["detail"] == [DETAIL_ROLE]


def test_28876_levee_en_voix_nue_leve():
    """Contrôle : la troisième réponse, sans préfixe, éteint la réserve -- le
    gate est vert et aucune entrée ne subsiste."""
    res = run_28876([NIT_28876, ACTION_1, ACTION_2, LEVEE_3], cutoff=APRES_TOUT)
    assert res["blocked"] is False
    assert res["blocking"] == []


def test_28876_la_cause_est_le_prefixe_pas_la_phrase():
    """La cause est le préfixe, rien d'autre : la deuxième réponse amputée de
    son `[ACTION]` lève la réserve."""
    sans_prefixe = dict(ACTION_2, body=ACTION_2["body"][len("[ACTION] "):])
    assert run_28876([NIT_28876, sans_prefixe])["blocked"] is False


def test_28876_reserve_sans_aucune_reponse(capsys):
    """Réponse 2 encore non postée : la réserve est seule, et le diagnostic le
    dit au lieu de se taire."""
    res = run_28876([NIT_28876], cutoff=utc(2026, 11, 27, 14))
    assert res["blocked"] is True
    entry = res["blocking"][0]
    assert entry["reserve_nature"] == "réserve en voix nue"
    assert entry["why_alive"] == []
    why.print_notes(entry)
    assert capsys.readouterr().out.splitlines() == [
        "      cause : réserve en voix nue — aucune réponse candidate après elle."]


def test_le_verdict_est_independant_du_diagnostic(monkeypatch):
    """Le contrat : sans diagnostic, même `blocked`, mêmes entrées."""
    cas = [
        [NIT_28876],
        [NIT_28876, ACTION_1],
        [NIT_28876, ACTION_1, ACTION_2],
        [NIT_28876, ACTION_1, ACTION_2, LEVEE_3],
    ]

    def cutoff_de(comments: list) -> datetime:
        return APRES_TOUT if LEVEE_3 in comments else AVANT_REPONSE_3

    attendus = []
    for comments in cas:
        res = run_28876(comments, cutoff_de(comments))
        attendus.append((res["blocked"],
                         [{k: b[k] for k in CLES_ORGAN} for b in res["blocking"]]))
    monkeypatch.setattr(why, "explain", lambda *a, **k: {})
    for comments, attendu in zip(cas, attendus):
        res = run_28876(comments, cutoff_de(comments))
        assert (res["blocked"],
                [{k: b[k] for k in CLES_ORGAN} for b in res["blocking"]]) == attendu
        assert all(set(b) == CLES_ORGAN for b in res["blocking"])


# --- Acceptance 3 : le mode texte -----------------------------------------------


def _gate(monkeypatch, comments: list, as_json: bool = False) -> int:
    """`gate()` sur les commentaires donnés, réseau et bundle remplacés."""
    data = {"number": 28876, "title": "t", "author": {"login": "jsboige"},
            "comments": comments, "reviews": [], "commits": COMMITS_28876,
            "mergedAt": "2026-11-27T19:28:00Z"}
    monkeypatch.setattr(mod, "_ensure_utf8_stdout", lambda: None)
    monkeypatch.setattr(mod, "gh_json", lambda args: dict(data))
    monkeypatch.setattr(mod, "_pr_review_bundle",
                        lambda pr: {"typed": {}, "threads": [], "author_of": {}})
    monkeypatch.setattr(mod, "_attach_absent_sha_context", lambda data: None)
    monkeypatch.setattr(mod, "improper_dismissals",
                        lambda pr, author_of=None: {})
    monkeypatch.setattr(mod, "gh_issue_info", lambda n: None)
    return mod.gate(28876, as_json=as_json)


def test_gate_texte_imprime_la_cause_sous_chaque_nit(monkeypatch, capsys):
    """Le texte du gate : l'extrait, puis la nature, puis une ligne par
    réponse candidate avec ses conditions échouées."""
    rc = _gate(monkeypatch, [NIT_28876, ACTION_1, ACTION_2])
    out = capsys.readouterr().out
    assert rc == 1
    assert ("      cause : réserve en voix nue — 2 réponse(s) candidate(s), "
            "aucune retenue :") in out
    assert "        2026-11-27T19:27:10Z jsboige via comment — ROLE" in out
    assert ("        2026-11-27T14:41:08Z jsboige via comment — "
            "AUCUNE-LEVEE, ROLE") in out
    assert "            portée de rôle « [ACTION] » :" in out
    # L'extrait du nit reste imprimé, au-dessus de sa cause.
    assert out.index("via comment") < out.index("cause : réserve en voix nue")
    # UTC explicite : l'heure porte `Z`, jamais le décalage d'`isoformat()`.
    assert "+00:00" not in out


def test_gate_json_porte_les_deux_cles(monkeypatch, capsys):
    """`--json` porte toutes les réponses (la borne d'affichage du mode texte
    n'est pas une mesure)."""
    rc = _gate(monkeypatch, [NIT_28876, ACTION_1, ACTION_2], as_json=True)
    res = json.loads(capsys.readouterr().out)
    assert rc == 1
    assert res["blocking"][0]["reserve_nature"] == "réserve en voix nue"
    assert failed(res) == [["AUCUNE-LEVEE", "ROLE"], ["ROLE"]]


def test_mode_texte_borne_l_affichage_pas_la_mesure(capsys):
    """Sept réponses d'un tiers : six lignes imprimées, la borne annoncée --
    et `why_alive` en porte toujours sept."""
    reserve = comment("jsboige", 10, "Concern: la densité du README.")
    tiers = [comment("myia-po-2024", 11 + i, f"Note {i} : je passe, rien de plus.")
             for i in range(7)]
    res = run_temoins([reserve] + tiers)
    entry = res["blocking"][0]
    assert len(entry["why_alive"]) == 7
    why.print_notes(entry)
    lignes = capsys.readouterr().out.splitlines()
    assert ("      cause : réserve en voix nue — 7 réponse(s) candidate(s), "
            "aucune retenue :") in lignes
    assert "        (+1 plus ancienne(s), même objet — voir --json)" in lignes
    assert sum(l.endswith("via comment — AUCUNE-LEVEE, AUTEUR") for l in lignes) == 6


# --- La nature de la réserve, telle que `_lift_eligible` la lit -----------------


@pytest.mark.parametrize("reserve, nature", [
    (comment("clusterManager-Myia", 10,
             "[Hermes] COMMENT_WITH_CONCERNS — 3 seeds manquants."),
     "réserve de persona [Hermes]"),
    (comment("jsboige", 10,
             "[myia-po-2024:CoursIA-2] Verdict : CHANGES_REQUESTED (substance) "
             "— sortie dégénérée en cell 3."),
     "réserve de lane [myia-po-2024:CoursIA-2]"),
    (comment("coursia-lane-po-2025[bot]", 10,
             "[ADJOINT] CONCERNS — le body ne porte pas le compte avant/après."),
     "réserve de rôle [ADJOINT]"),
    (comment("myia-ai-01", 10,
             "**BLOCAGE — le chemin est mauvais.** Il doit être levé par une phrase."),
     "blocage (verdict posé en tête du corps)"),
    (comment("myia-ai-01", 10, "## [HOLD G-VAR-2] Titre — budget LIGHT épuisé."),
     "blocage (verdict posé en tête du corps)"),
    (comment("jsboige", 10,
             "[BLOCAGE] lane myia-po-2024:CoursIA-2 — le chemin est mauvais."),
     "blocage « [BLOCAGE] lane myia-po-2024:CoursIA-2 »"),
], ids=["persona", "lane", "role", "blocage-verdict", "hold-etiquete",
        "blocage-lane"])
def test_nature_de_la_reserve(reserve: dict, nature: str):
    """La nature se lit avec les patrons de l'organe ; un blocage porte son
    marqueur (`[BLOCAGE]` n'est pas un préfixe de rôle comme un autre)."""
    res = run_temoins([reserve])
    assert res["blocked"] is True
    assert res["blocking"][0]["reserve_nature"] == nature


# --- Les autres conditions, une par famille -------------------------------------

NU = comment("jsboige", 10,
             "Concern: l'attribution est ambiguë, il faudrait la corriger.")


def test_levee_d_un_tiers_auteur_non_habilite():
    """Auteur non habilité : le libellé nomme les deux logins."""
    res = run_temoins([NU, comment("another-contributor", 12, "Je lève cette réserve.")])
    ligne = unique(res)
    assert ligne["failed"] == ["AUTEUR"]
    detail = ligne["detail"][0]
    assert "`another-contributor`" in detail and "(`jsboige`)" in detail
    assert "(#11145)" in detail


def test_levee_de_persona_sur_reserve_en_voix_nue():
    res = run_temoins([NU, comment(
        "jsboige", 12,
        "[Hermes] Je lève ma réserve d'attribution : lemme dédié ajouté.")])
    ligne = unique(res)
    assert ligne["failed"] == ["PERSONA"]
    assert "portée de persona [Hermes]" in ligne["detail"][0]


def test_levee_de_lane_sur_reserve_en_voix_nue():
    res = run_temoins([NU, comment(
        "jsboige", 12,
        "[myia-po-2024:CoursIA-2] Je lève la réserve d'attribution : tranche D2 livrée.")])
    ligne = unique(res)
    assert ligne["failed"] == ["LANE"]
    assert "portée de lane « [myia-po-2024:CoursIA-2] »" in ligne["detail"][0]


def test_reponse_de_l_auteur_de_la_pr_sur_un_changes_requested_natif():
    """La réserve est une review `CHANGES_REQUESTED` d'un tiers : la réponse de
    l'auteur de la PR documente le traitement, elle ne lève pas."""
    review = {"author": {"login": "po-2026"}, "state": "CHANGES_REQUESTED",
              "submittedAt": at(10), "body": "Sortie dégénérée en cell 3."}
    res = run_temoins(
        [comment("jsboige", 12, "[ACTION] Réserve de la cell 3 levée — ré-exécution 5/5.")],
        reviews=[review])
    assert res["blocked"] is True
    assert (res["blocking"][0]["src"], res["blocking"][0]["channel"]) == (
        "review:CHANGES_REQUESTED", "review")
    ligne = unique(res)
    assert ligne["failed"] == ["AUTEUR"]
    assert "l'auteur de la PR, qui n'est pas l'auteur de la réserve" in ligne["detail"][0]


def test_reponse_postee_comme_review_commented():
    """La surface « phrase » relit aussi les reviews `COMMENTED`."""
    review = {"author": {"login": "jsboige"}, "state": "COMMENTED",
              "submittedAt": at(12),
              "body": "[ACTION] Réserve de densité levée — commit abc000000000."}
    res = run_temoins([NU], reviews=[review])
    assert res["blocked"] is True
    ligne = res["blocking"][0]["why_alive"][0]
    assert (ligne["channel"], ligne["surfaces"], ligne["failed"]) == (
        "review", ["phrase"], ["ROLE"])


def test_reponse_qui_est_elle_meme_une_reserve():
    """Une réserve ne lève rien : les DEUX réserves survivent, et la seconde
    est expliquée comme réponse de la première."""
    res = run_temoins(
        [NU, comment("myia-ai-01", 12,
                     "Concern: la correction introduit une régression en cell 4.")])
    assert res["blocked"] is True and len(res["blocking"]) == 2
    assert lines(res) == [(("AUCUNE-LEVEE", "EST-RESERVE"),
                           [why.AUCUNE_LEVEE,
                            "la réponse est elle-même lue comme une réserve : une "
                            "réserve ne lève rien"])]


def test_levee_conditionnelle():
    """Marqueur générique + formulation conditionnelle, sans marqueur
    explicite avant : la réponse annule sa propre levée (#12074)."""
    res = run_temoins([NU, comment(
        "jsboige", 12, "Les 2 points sont adressés, et je merge dès que la CI est verte.")])
    assert lines(res) == [(("LEVEE-ANNULEE",),
                           ["la réponse annule sa propre levée (formulation "
                            "conditionnelle ou rétractation) : elle ne lève pas "
                            "(#12074)"])]


def test_levee_dont_la_preuve_est_rembobinee():
    """Le SHA cité n'est plus celui d'un arbre de la PR (#13639, #15556)."""
    reserve = comment("myia-ai-01", 10, "Concern: le chemin est mauvais.")
    levee = comment("myia-ai-01", 12,
                    "Je lève ma réserve : chemin corrigé au commit deadbeef000.")
    res = run_temoins(
        [reserve, levee],
        data_extra={"_absent_sha_messages": {"deadbeef000": "fix #0 : chemin corrigé"},
                    "_absent_sha_trees": {"deadbeef000": "tree-old"},
                    "_head_tree": "tree-new"})
    assert lines(res) == [(("SHA-REMBOBINE",),
                           ["la réponse cite deadbeef000, rembobiné par un push "
                            "ultérieur : la preuve ne pointe plus l'arbre de la "
                            "tête (#13639, #15556)"])]


# --- Surface « approval » --------------------------------------------------------

RESERVE_PO = comment("po-2026", 10, "Verdict : CHANGES_REQUESTED (substance) — "
                                    "sortie dégénérée en cell 3.")
CORRECTION = comment("jsboige", 12, "cell 3 corrigée, ré-exécution 5/5.")


def approval(login: str, body: str) -> dict:
    return {"author": {"login": login}, "state": "APPROVED",
            "submittedAt": at(15), "body": body}


def test_auto_approbation():
    """Réserve et auto-approbation de l'auteur de la PR (#12319)."""
    reserve = comment("jsboige", 10, "Verdict : CHANGES_REQUESTED (substance) — "
                                     "sortie dégénérée en cell 3.")
    res = run_temoins([reserve, CORRECTION], reviews=[approval("jsboige", "APPROVED.")])
    assert lines(res) == [
        (("AUCUNE-LEVEE",), [why.AUCUNE_LEVEE]),
        (("AUTO-APPROBATION",),
         ["re-review APPROVED de l'auteur de la réserve, qui est aussi l'auteur "
          "de la PR : une auto-approbation ne lève rien (#12319)"])]
    assert res["blocking"][0]["why_alive"][1]["surfaces"] == ["approval"]


def test_approbation_generique_d_un_tiers():
    """Une approbation qui ne nomme pas la réserve n'identifie aucune réserve
    (#13399)."""
    res = run_temoins(
        [RESERVE_PO, CORRECTION],
        reviews=[approval("ai-01", "APPROVED — le livrable est bon à merger.")])
    assert [c for c, _ in lines(res)] == [("AUCUNE-LEVEE", "AUTEUR"),
                                          ("APPROVAL-SANS-NOM",)]
    assert "approbation de `ai-01`" in lines(res)[1][1][0]


def test_approbation_de_l_auteur_de_la_pr():
    res = run_temoins(
        [RESERVE_PO],
        reviews=[approval("jsboige", "APPROVED — la réserve de po-2026 est traitée.")])
    assert lines(res) == [(("AUTEUR",),
                           ["l'auteur de la PR approuve : son approbation ne "
                            "remplace pas la levée de l'auteur de la réserve "
                            "(#13399)"])]


# --- La borne de blocage #13083 --------------------------------------------------


def test_blocage_leve_par_son_emetteur_qui_est_l_auteur_de_la_pr():
    """La levée est recevable pour une réserve ; sur un blocage, la borne
    d'auteur la refuse."""
    res = run_temoins([
        comment("jsboige", 10, "[BLOCAGE] lane myia-ai-01:CoursIA — chemin mauvais."),
        comment("jsboige", 12, "Les 2 points sont adressés : chemin corrigé.")])
    assert res["blocking"][0]["kind"] == "BLOCK"
    assert lines(res) == [(("AUTEUR",), [why._BLOCK_GUARD_DETAIL])]
    assert "(#13083)" in why._BLOCK_GUARD_DETAIL


# --- Surface « followup » : la voie 3 de B.0 -------------------------------------

JOUR_SUIVI = "2026-08-14"
NIT_SUIVI = comment("jsboige", 9, "Concern: l'attribution est fausse.", JOUR_SUIVI)
RAPPORT = comment("jsboige", 12,
                  "L'attribution est reportée sciemment sur l'issue #500.", JOUR_SUIVI)
COMMIT_SUIVI = [{"oid": "abc" + "0" * 37, "committedDate": at(8, JOUR_SUIVI)}]
MERGE_SUIVI = utc(2026, 8, 14, 20)


def suivi(created_at: datetime, title: str = "PR #0") -> dict:
    """Le rapport vers l'issue #500, ouverte, créée à `created_at`."""
    issue = mod.IssueInfo({
        "state": "open",
        "created_at": created_at.isoformat().replace("+00:00", "Z"),
        "title": title, "body": ""})
    return run([NIT_SUIVI, RAPPORT], cutoff=MERGE_SUIVI, commits=COMMIT_SUIVI,
               issue_info=lambda numero: issue if numero == 500 else None)


def test_rapport_vers_une_issue_anterieure_a_la_reserve_et_sans_lien():
    """Les conditions 5 (créée après la réserve) et 6 (référence la PR) sont
    indépendantes : l'issue #500 d'avant la réserve et sans lien échoue les
    deux, et le rapport est aussi une réponse sans phrase de levée."""
    res = suivi(utc(2026, 8, 14, 8), title="Autre sujet")
    assert res["blocked"] is True
    ligne = res["blocking"][0]["why_alive"][0]
    assert ligne["surfaces"] == ["phrase", "followup"]
    assert ligne["failed"] == ["AUCUNE-LEVEE", "SUIVI-ANTERIEUR", "SUIVI-SANS-LIEN"]
    assert ligne["detail"][1].startswith(
        "l'issue de suivi nommée (« Autre sujet ») est antérieure à la réserve")
    assert "(#14218)" in ligne["detail"][2]


def test_rapport_vers_une_issue_sans_lien_avec_la_pr():
    res = suivi(utc(2026, 8, 14, 11), title="Autre sujet")
    assert res["blocked"] is True
    assert failed(res) == [["AUCUNE-LEVEE", "SUIVI-SANS-LIEN"]]


def test_rapport_vers_une_issue_anterieure_mais_liee():
    res = suivi(utc(2026, 8, 14, 8))
    assert res["blocked"] is True
    assert failed(res) == [["AUCUNE-LEVEE", "SUIVI-ANTERIEUR"]]


def test_rapport_d_un_tiers():
    rapport = dict(RAPPORT, author={"login": "myia-po-2024"})
    issue = mod.IssueInfo({"state": "open", "created_at": "2026-08-14T11:00:00Z",
                           "title": "PR #0", "body": ""})
    res = run([NIT_SUIVI, rapport], cutoff=MERGE_SUIVI, commits=COMMIT_SUIVI,
              issue_info=lambda numero: issue if numero == 500 else None)
    assert res["blocked"] is True
    ligne = res["blocking"][0]["why_alive"][0]
    assert ligne["surfaces"] == ["phrase", "followup"]
    assert ligne["failed"] == ["AUCUNE-LEVEE", "AUTEUR"]
    assert "`myia-po-2024`" in ligne["detail"][1]


def test_rapport_qui_credite_ne_laisse_aucune_ligne():
    """Contrôle : issue ouverte après la réserve et liée à la PR -- la voie 3
    lève, le gate est vert."""
    assert suivi(utc(2026, 8, 14, 11))["blocked"] is False


# --- Thread inline ---------------------------------------------------------------


def test_thread_inline_non_resolu_porte_sa_cause(capsys):
    """Un thread ne se lève par aucune des trois surfaces : sa cause est son
    état, et le mode texte l'imprime."""
    thread = {"resolved": False, "outdated": False, "path": "a.py", "line": 12,
              "author": "jsboige", "body": "ce nom est trompeur",
              "createdAt": at(10)}
    res = run([], cutoff=utc(2026, 9, 6, 18), threads=[thread])
    assert res["blocked"] is True
    entry = res["blocking"][0]
    assert entry["kind"] == "INLINE-UNRESOLVED"
    assert (entry["reserve_nature"], entry["why_alive"]) == (why.INLINE_NATURE, [])
    why.print_notes(entry)
    assert capsys.readouterr().out.splitlines() == [f"      cause : {why.INLINE_NATURE}"]


# --- Acceptance 4 : une erreur du diagnostic ne remonte jamais -------------------


def test_une_erreur_du_diagnostic_s_ecrit_sans_toucher_le_verdict(monkeypatch):
    commentaires = [NU, comment("jsboige", 12, "[ACTION] Réserve d'attribution levée.")]
    reference = run_temoins(commentaires)

    def casse(*args, **kwargs):
        raise RuntimeError("sonde")

    monkeypatch.setattr(why, "_explain", casse)
    res = run_temoins(commentaires)
    assert res["blocked"] is reference["blocked"] is True
    entree, temoin = res["blocking"][0], reference["blocking"][0]
    assert {k: entree[k] for k in CLES_ORGAN} == {k: temoin[k] for k in CLES_ORGAN}
    assert entree["reserve_nature"] is None
    assert entree["why_alive"] == [{
        "at": "", "author": "", "channel": "", "surfaces": [],
        "failed": ["DIAGNOSTIC-INDISPONIBLE"],
        "detail": ["le diagnostic de survie n'a pas pu être calculé "
                   "(RuntimeError) -- à remonter sur #28924"]}]


# --- Le canal `_why` : un diagnostic, jamais une condition -----------------------


def test_le_canal_why_ne_change_aucun_booleen(monkeypatch):
    """`_lift_eligible` rend le même booléen avec ou sans canal `_why`."""
    vus = {}
    reel = why.explain

    def espion(nits, ctx, reserve):
        vus["eligible"], vus["corps_reserve"] = ctx["lift_eligible"], reserve[3]
        return reel(nits, ctx, reserve)

    monkeypatch.setattr(why, "explain", espion)
    bloque = [NU, comment("jsboige", 12, "[ACTION] Réserve d'attribution levée.")]
    assert run_temoins(bloque)["blocked"] is True
    eligible, corps_reserve = vus["eligible"], vus["corps_reserve"]

    canal = []
    assert eligible("jsboige", "jsboige", ACTION_2["body"], corps_reserve) is False
    assert eligible("jsboige", "jsboige", ACTION_2["body"], corps_reserve,
                    _why=canal) is False
    assert [tag for tag, _ in canal] == ["ROLE"]
    canal = []
    assert eligible("jsboige", "jsboige", LEVEE_3["body"], corps_reserve,
                    _why=canal) is True
    assert canal == []


def test_les_cles_sont_serialisables():
    """`gate --json` imprime l'entrée telle quelle."""
    res = run_28876([NIT_28876, ACTION_1, ACTION_2])
    assert json.loads(json.dumps(res["blocking"], ensure_ascii=False)) == res["blocking"]


def test_la_cause_fondatrice_est_lisible_dans_les_patrons_de_l_organe():
    """`[ACTION]` n'est ni un tag de protocole écarté par `can_lift`, ni un
    rôle exclu par `_ROLE_PREFIX_RE` : il est donc un préfixe de rôle."""
    assert mod.can_lift(ACTION_2)
    assert why.shown_prefix(mod._ROLE_PREFIX_RE.search(ACTION_2["body"])) == "[ACTION]"
    assert "EXPLICIT_LIFT_MARKERS" in why.AUCUNE_LEVEE
