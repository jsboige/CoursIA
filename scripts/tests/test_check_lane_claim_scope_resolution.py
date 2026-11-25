#!/usr/bin/env python3
"""Temoins du correctif #26657 -- le scope VIVANT d'un claim.

Le defaut : `check_lane_claim.py` decidait qu'un scope de claim etait MORT
quand le glob ne matchait aucun fichier suivi par `git ls-files`. Deux
situations rendent un scope reellement vivant que l'arbre local ne peut pas
voir :

  (A) les fichiers sont dans une PR OUVERTE -- le `[DELIVERED] ... PR #N`
      qui nomme le dossier cree par sa propre PR ;
  (B) les fichiers ont ete RENOMMES (descente de sous-serie) -- le registre
      `docs/reference/rename-ledger.tsv` le sait.

Mesure du 15/11 sur #20298 : `empty_scope` non vide sur des claims livres,
`locked: false` sur une livraison, `free_paths_size: 0`, et deux lanes en
epic-wide sur une issue entiere alors que leurs scopes etaient precis et
disjoints (verrou DEAD-SCOPE).

Ces tests sont les temoins : ils rougissent sur le code casse (un scope lu
mort) et restent verts sur le code corrige. Ils pignent AUSSI ce qui ne doit
PAS changer : un scope non resolvable reste mort (fail-CLOSED #10958), un
glob dont le repertoire parent n'existe pas n'est pas resolu (#21431 (c)),
un scope deja vivant n'est pas touche.

Run: python -m pytest scripts/tests/test_check_lane_claim_scope_resolution.py
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc  # noqa: E402


# --- helpers -----------------------------------------------------------------

def comment(body, created_at, author="jsboige", url=None):
    return {
        "body": body,
        "createdAt": created_at,
        "author": {"login": author},
        "url": url,
    }


def payload(*comments, number=20298, title="t", labels=None):
    d = {"number": number, "title": title, "comments": list(comments)}
    if labels is not None:
        d["labels"] = labels
    return d


def _summary(capsys):
    """Le JSON de synthese emis par `_run_check` (stdout)."""
    captured = capsys.readouterr()
    return json.loads(captured.out.split("\n\n", 1)[0]), captured.err


def _delivered(lane, pr_ref, paths, created="2026-11-15T00:00:00Z"):
    body = clc._DELIVERED_BODY_TMPL.format(
        lane=lane, pr_ref=pr_ref,
        paths_clause=clc._paths_clause(paths),
    )
    return comment(body, created)


# --- (A) le scope d'une PR OUVERTE est vivant -------------------------------


def test_le_scope_dune_pr_ouverte_est_vivant(capsys, monkeypatch):
    """POSITIF (cas A) -- le `[DELIVERED] ... PR #N` qui nomme le dossier
    cree par sa propre PR ouverte : le scope VERROUILLE les fichiers de la
    PR. Avant le correctif, `git ls-files` ne voyait pas ces fichiers, le
    scope etait lu MORT, `empty_scope` portait le glob entier, et le claim
    etait leve en epic-wide (verrou DEAD-SCOPE)."""
    monkeypatch.setattr(clc, "_git_tracked_files",
                        lambda: ["docs/series/README.md"])
    pr_files = {
        26415: [
            "series/ICT-13/ICT-13-AxelrodStrategicMorphodynamics.ipynb",
            "series/ICT-13/ICT-13b-DecroisementDynamique.ipynb",
        ],
    }
    p = payload(_delivered("A:CoursIA", 26415, ["series/ICT-13/**"]))

    rc = clc._run_check(
        p, "B:CoursIA",
        my_paths=["series/ICT-13/ICT-13-AxelrodStrategicMorphodynamics.ipynb"],
        pr_states={26415: "OPEN"}, pr_files=pr_files)
    summary, _err = _summary(capsys)

    claim = summary["active_claims"]["A:CoursIA"]
    assert claim["empty_scope"] == []
    assert claim["scope_intersection_size"] == 1
    # La resolution est journalisee : la lane voit ou son perimetre est.
    assert claim["scope_resolution"][0]["how"] == "pr-en-cours"
    assert claim["live_paths"] == pr_files[26415]
    # Le claim reste un bloqueur (la tranche est en vol) : le fix ne
    # debloque rien, il cesse seulement de verrouiller l'issue entiere.
    assert rc == 1


def test_le_scope_dune_pr_ouverte_n_est_plus_un_verrou_dissue_entiere(capsys,
                                                                       monkeypatch):
    """POSITIF (cas A, effet mesure) -- avant le correctif, deux claims
    dont le scope vit dans une PR ouverte etaient lus morts, donc leves en
    epic-wide : l'issue entiere etait bloquee et `free_paths` etait vide.
    Apres, les scopes sont disjoints et le tapis peut nommer un chemin
    libre."""
    monkeypatch.setattr(clc, "_git_tracked_files",
                        lambda: ["docs/series/README.md"])
    pr_files = {
        26415: ["series/ICT-13/ICT-13-Axelrod.ipynb"],
        26416: ["series/ICT-14/ICT-14-FreeEnergy.ipynb"],
    }
    p = payload(
        _delivered("A:CoursIA", 26415, ["series/ICT-13/**"]),
        _delivered("C:CoursIA", 26416, ["series/ICT-14/**"]),
    )

    rc = clc._run_check(p, "B:CoursIA", my_paths=["docs/series/README.md"],
                        pr_states={26415: "OPEN", 26416: "OPEN"},
                        pr_files=pr_files)
    summary, _err = _summary(capsys)

    assert summary["free_paths_size"] >= 1
    assert summary["blocking_lanes"] == []
    assert rc == 0


def test_le_scope_resolu_par_le_registre_est_vivant(capsys, monkeypatch):
    """POSITIF (cas B, registre) -- un glob de chemin RENOMME est resolu
    vers sa position vivante : le claim garde son perimetre au lieu d'etre
    lu mort et de bloquer l'issue entiere."""
    monkeypatch.setattr(clc, "_git_tracked_files", lambda: [
        "series/ICT-20-FeatureCatastrophes/ICT-20-FeatureCatastrophes.ipynb",
        "docs/series/README.md",
    ])
    monkeypatch.setattr(clc, "_rename_ledger_map", lambda repo_root=None: {
        "series/ICT-20-FeatureCatastrophes.ipynb":
            "series/ICT-20-FeatureCatastrophes/"
            "ICT-20-FeatureCatastrophes.ipynb",
    })
    body = clc._CLAIM_BODY_TMPL.format(
        lane="A:CoursIA", intention="tranche ICT-20",
        paths_clause=clc._paths_clause(
            ["series/ICT-20-FeatureCatastrophes.ipynb"]),
    )
    p = payload(comment(body, "2026-11-15T00:00:00Z"))

    rc = clc._run_check(p, "B:CoursIA", my_paths=["docs/series/README.md"])
    summary, _err = _summary(capsys)

    claim = summary["active_claims"]["A:CoursIA"]
    assert claim["empty_scope"] == []
    assert claim["scope_resolution"][0]["how"] == "rename-ledger"
    # Un claim dont le scope est disjoint ne bloque pas le caller.
    assert rc == 0


def test_le_scope_resolu_par_basename_unique_est_vivant(capsys, monkeypatch):
    """POSITIF (cas B, basename) -- le « did you mean » #13129 existait
    deja, mais en WARN seul : le scope restait lu mort. Il est desormais
    applique, en version STRICTE (basename unique)."""
    monkeypatch.setattr(clc, "_git_tracked_files", lambda: [
        "series/ICT-02/ICT-02-SelfSortingMorphogenesis.ipynb",
        "docs/series/README.md",
    ])
    body = clc._CLAIM_BODY_TMPL.format(
        lane="A:CoursIA", intention="tranche ICT-02",
        paths_clause=clc._paths_clause(
            ["series/ICT-02-SelfSortingMorphogenesis.ipynb"]),
    )
    p = payload(comment(body, "2026-11-15T00:00:00Z"))

    rc = clc._run_check(p, "B:CoursIA", my_paths=["docs/series/README.md"])
    summary, _err = _summary(capsys)

    claim = summary["active_claims"]["A:CoursIA"]
    assert claim["empty_scope"] == []
    assert claim["scope_resolution"][0]["how"] == "basename-unique"
    assert rc == 0


# --- ce qui ne doit PAS changer ---------------------------------------------


def test_un_basename_ambigu_n_est_pas_resolu(capsys, monkeypatch):
    """NEGATIF -- deux fichiers portent le meme basename : aucune resolution
    n'est prouvee, le scope reste MORT, et le fail-CLOSED #10958/#11098
    s'applique toujours (le claim est bloqueur de l'issue entiere)."""
    monkeypatch.setattr(clc, "_git_tracked_files", lambda: [
        "series/ICT-02/ICT-02-N.ipynb",
        "series/ICT-03/ICT-02-N.ipynb",
        "docs/series/README.md",
    ])
    body = clc._CLAIM_BODY_TMPL.format(
        lane="A:CoursIA", intention="tranche ICT-02",
        paths_clause=clc._paths_clause(["series/ICT-02-N.ipynb"]),
    )
    p = payload(comment(body, "2026-11-15T00:00:00Z"))

    clc._run_check(p, "B:CoursIA", my_paths=["docs/series/README.md"])
    summary, _err = _summary(capsys)

    claim = summary["active_claims"]["A:CoursIA"]
    assert claim["empty_scope"] == ["series/ICT-02-N.ipynb"]
    assert claim["scope_resolution"] == []


def test_un_glob_dont_le_parent_nexiste_pas_n_est_pas_resolu(capsys,
                                                             monkeypatch):
    """NEGATIF (#21431 (c)) -- le repertoire parent du glob n'existe pas :
    le glob est un typo, pas un chemin renomme. Aucune resolution, et le
    claim reste epic-wide (fail-CLOSED)."""
    monkeypatch.setattr(clc, "_git_tracked_files",
                        lambda: ["docs/series/README.md"])
    monkeypatch.setattr(clc, "_rename_ledger_map", lambda repo_root=None: {
        "serie-inexistante/carnet.ipynb":
            "docs/series/README.md",
    })
    body = clc._CLAIM_BODY_TMPL.format(
        lane="A:CoursIA", intention="tranche",
        paths_clause=clc._paths_clause(["serie-inexistante/carnet.ipynb"]),
    )
    p = payload(comment(body, "2026-11-15T00:00:00Z"))

    clc._run_check(p, "B:CoursIA", my_paths=["docs/series/README.md"])
    summary, _err = _summary(capsys)

    claim = summary["active_claims"]["A:CoursIA"]
    assert claim["empty_scope"] == ["serie-inexistante/carnet.ipynb"]
    assert claim["scope_resolution"] == []


def test_un_scope_deja_vivant_n_est_pas_touche(capsys, monkeypatch):
    """POSITIF (non-regression) -- un scope qui matche deja l'arbre suivi
    n'est ni resolu ni modifie : la resolution ne s'active que sur un glob
    MORT."""
    monkeypatch.setattr(clc, "_git_tracked_files",
                        lambda: ["docs/series/README.md"])
    body = clc._CLAIM_BODY_TMPL.format(
        lane="A:CoursIA", intention="tranche",
        paths_clause=clc._paths_clause(["docs/series/README.md"]),
    )
    p = payload(comment(body, "2026-11-15T00:00:00Z"))

    clc._run_check(p, "B:CoursIA", my_paths=["docs/series/README.md"])
    summary, _err = _summary(capsys)

    claim = summary["active_claims"]["A:CoursIA"]
    assert claim["empty_scope"] == []
    assert claim["scope_resolution"] == []
    assert claim["paths"] == ["docs/series/README.md"]


def test_une_chaine_de_renommages_est_suivie(monkeypatch):
    """POSITIF -- le registre est un HISTORIQUE : `A` -> `B` -> `C`. La
    resolution suit la chaine (3 sauts maximum) et aboutit au chemin
    vivant."""
    tracked = ["series/C/carnet.ipynb"]
    ledger = {
        "series/A/carnet.ipynb": "series/B/carnet.ipynb",
        "series/B/carnet.ipynb": "series/C/carnet.ipynb",
    }

    resolved = clc._resolve_ledger_scope("series/A/carnet.ipynb", tracked,
                                          ledger)

    assert resolved == ["series/C/carnet.ipynb"]


def test_une_chaine_trop_longue_n_est_pas_resolue(monkeypatch):
    """NEGATIF -- au-dela de trois sauts, la resolution n'est plus prouvee :
    le glob reste mort (fail-CLOSED)."""
    tracked = ["series/E/carnet.ipynb"]
    ledger = {
        "series/A/carnet.ipynb": "series/B/carnet.ipynb",
        "series/B/carnet.ipynb": "series/C/carnet.ipynb",
        "series/C/carnet.ipynb": "series/D/carnet.ipynb",
        "series/D/carnet.ipynb": "series/E/carnet.ipynb",
    }

    resolved = clc._resolve_ledger_scope("series/A/carnet.ipynb", tracked,
                                          ledger)

    assert resolved == []


def test_une_pr_fermee_n_apporte_aucun_fichier_vivant(monkeypatch):
    """NEGATIF -- seule une PR OUVERTE apporte des fichiers : une PR
    fermee sans merge n'apporte rien, une PR mergee a depose les siens sur
    `main` (l'arbre local les voit deja)."""
    monkeypatch.setattr(clc, "_fetch_pr_state", lambda ref: ("MERGED", None))

    assert clc._scope_pr_files([26415]) == {}


def test_une_pr_ouverte_apporte_ses_fichiers(monkeypatch):
    """POSITIF -- une PR ouverte livre ses fichiers a l'univers du scope."""
    monkeypatch.setattr(clc, "_fetch_pr_state", lambda ref: ("OPEN", None))
    monkeypatch.setattr(clc, "_fetch_pr_files",
                        lambda ref: ["series/ICT-13/a.ipynb"])

    assert clc._scope_pr_files([26415]) == {
        26415: ["series/ICT-13/a.ipynb"],
    }


def test_sans_injection_le_verdict_ne_change_pas(capsys, monkeypatch):
    """NEGATIF (contrat) -- sans `pr_files` injectes, l'univers des
    fichiers reste l'arbre local : aucun verdict ne change (le reseau est
    hors de l'organe)."""
    monkeypatch.setattr(clc, "_git_tracked_files",
                        lambda: ["docs/series/README.md"])
    body = clc._CLAIM_BODY_TMPL.format(
        lane="A:CoursIA", intention="tranche",
        paths_clause=clc._paths_clause(["series/ICT-13/**"]),
    )
    p = payload(comment(body, "2026-11-15T00:00:00Z"))

    clc._run_check(p, "B:CoursIA", my_paths=["docs/series/README.md"])
    summary, _err = _summary(capsys)

    claim = summary["active_claims"]["A:CoursIA"]
    assert claim["empty_scope"] == ["series/ICT-13/**"]
