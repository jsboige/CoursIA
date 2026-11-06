"""Tests de `twin_open_claims.py` et du verdict OPEN-PR de la porte.

La regle testee, en deux temps :

1. **Qui revendique un ordinal** : une PR qui AJOUTE ou RENOMME le fichier
   qui le porte. Une PR qui MODIFIE une attestation existante garde l'ordinal
   et n'en revendique pas un nouveau -- sinon le registre se signalerait
   lui-meme sur chaque retouche.

2. **Quand y a-t-il collision** : quand deux PRs distinctes revendiquent le
   meme (paire, ordinal). C'est le cas que la porte de base ne voit pas :
   elle juge une PR contre SA base au push, et deux PRs paralleles passent
   donc toutes les deux (mesure #22299 : #24010 vs #23832, `0024`-`0026`).

Le sens du refus est essential : la PR **creee en DERNIER** voit l'autre (une
PR existe des son push), c'est donc elle qui renumerote -- avant qu'aucune des
deux ne merge.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import twin_open_claims as toc  # noqa: E402
from check_twin_index_collisions import open_pr_reasons  # noqa: E402
from twin_open_claims import (  # noqa: E402
    claims_from_files,
    collisions_by_ordinal,
    parse_claim,
)

REPO = Path(__file__).resolve().parents[3]

PREFIX = "scripts/notebook_tools/twin_pairs.d"


def _path(index: str, lane: str = "myia-po-2025-CoursIA") -> str:
    return "%s/app/%s-2026-11-01-%s.yaml" % (PREFIX, index, lane)


# --- 1. qui revendique un ordinal -------------------------------------------


def test_un_chemin_du_registre_revendique_son_ordinal():
    claim = parse_claim(_path("0024"))
    assert claim == {
        "pair": "app",
        "index": "0024",
        "path": _path("0024"),
    }


def test_un_chemin_hors_registre_ne_revendique_rien():
    assert parse_claim("scripts/ci/fast_lane_registry.py") is None
    assert parse_claim("") is None


def test_un_ordinal_non_numerique_ne_revendique_rien():
    """Le nom du fichier porte l'index, pas l'inverse : un fichier du
    registre sans index numerique n'est pas une revendication d'ordinal."""
    assert parse_claim("%s/app/notes-2026-11-01-x.yaml" % PREFIX) is None


def test_seul_un_fichier_ajoute_ou_renomme_revendique_un_ordinal():
    files = [
        {"path": _path("0024"), "status": "added"},
        {"path": _path("0025"), "status": "renamed"},
        {"path": _path("0026"), "status": "modified"},
        {"path": _path("0027"), "status": "removed"},
    ]
    claims = claims_from_files(files)
    assert sorted(c["index"] for c in claims) == ["0024", "0025"]


def test_un_fichier_modifie_ne_revendique_pas_d_ordinal():
    """Une PR qui touche une attestation SANS la deplacer garde l'ordinal de
    la paire : le revendiquer ferait signaler le registre contre lui-meme."""
    assert claims_from_files([{"path": _path("0024"), "status": "modified"}]) == []


def test_un_fichier_sans_statut_ne_revendique_pas_d_ordinal():
    """Information absente != information negative : on ne bloque pas sur ce
    qu'on ne sait pas."""
    assert claims_from_files([{"path": _path("0024")}]) == []


# --- 2. quand y a-t-il collision --------------------------------------------


def test_deux_prs_qui_revendiquent_le_meme_ordinal_collisionnent():
    claims = {
        "23832": [{"pair": "app", "index": "0024", "path": _path("0024")}],
        "24010": [{"pair": "app", "index": "0024",
                   "path": _path("0024", "myia-po-2024-CoursIA")}],
    }
    collisions = collisions_by_ordinal(claims)
    assert len(collisions) == 1
    assert collisions[0]["pair"] == "app"
    assert collisions[0]["index"] == "0024"
    assert collisions[0]["prs"] == [23832, 24010]


def test_une_seule_pr_ne_collisionne_pas_avec_elle_meme():
    claims = {
        "23832": [
            {"pair": "app", "index": "0024", "path": _path("0024")},
            {"pair": "app", "index": "0024", "path": _path("0024")},
        ],
    }
    assert collisions_by_ordinal(claims) == []


def test_des_ordinals_de_paires_differentes_ne_collisionnent_pas():
    claims = {
        "23832": [{"pair": "app", "index": "0024", "path": _path("0024")}],
        "24010": [{"pair": "autre", "index": "0024",
                   "path": "%s/autre/0024-2026-11-01-x.yaml" % PREFIX}],
    }
    assert collisions_by_ordinal(claims) == []


def test_le_meme_nom_revendique_par_deux_prs_nest_pas_un_doublon():
    """Deux PRs qui ajoutent le MEME fichier ne produisent qu'un fichier sur
    `main` : git refuse le merge (`add/add`) et un humain tranche. C'est un
    conflit de merge, pas un doublon d'index -- la regle de l'organe
    historique l'exclut deja (le nom identique vu des deux cotes n'est pas une
    collision)."""
    claims = {
        "23832": [{"pair": "app", "index": "0024", "path": _path("0024")}],
        "24010": [{"pair": "app", "index": "0024", "path": _path("0024")}],
    }
    assert collisions_by_ordinal(claims) == []


# --- 3. le verdict de la porte ----------------------------------------------


def _claims(*pairs):
    """[(pr, pair, index, lane)] -> {'claims': [...]} au format de l'organe."""
    return {"claims": [
        {"pr": pr, "pair": pair, "index": index,
         "path": "%s/%s/%s-2026-11-01-%s.yaml" % (PREFIX, pair, index, lane)}
        for pr, pair, index, lane in pairs
    ]}


def test_la_porte_refuse_l_ordinal_revendique_par_une_autre_pr_ouverte():
    payload = _claims((24010, "app", "0024", "myia-po-2024-CoursIA"),
                      (23832, "app", "0024", "myia-po-2025-CoursIA"))
    by_pr: dict = {}
    for row in payload["claims"]:
        by_pr.setdefault(str(row["pr"]), []).append(row)
    reasons = open_pr_reasons(by_pr, head_pr=24010)
    assert len(reasons) == 1
    assert reasons[0]["kind"] == "open_pr"
    assert reasons[0]["pair"] == "app"
    assert reasons[0]["index"] == "0024"
    assert reasons[0]["prs"] == [23832, 24010]
    # le geste doit etre nommé : un `git mv` PUR, sans re-execution
    assert "git mv" in reasons[0]["gist"]
    assert "23832" in reasons[0]["gist"]


def test_la_porte_ne_juge_pas_une_collision_qui_ne_la_concerne_pas():
    payload = _claims((24010, "app", "0024", "myia-po-2024-CoursIA"),
                      (23832, "app", "0024", "myia-po-2025-CoursIA"))
    by_pr: dict = {}
    for row in payload["claims"]:
        by_pr.setdefault(str(row["pr"]), []).append(row)
    assert open_pr_reasons(by_pr, head_pr=12345) == []


def test_sans_numeros_de_pr_le_verdict_ne_se_prononce_pas():
    assert open_pr_reasons({}, head_pr=None) == []


# --- 4. le contrat de sortie de l'organe -------------------------------------


def _has_ref(ref: str) -> bool:
    return subprocess.run(
        ["git", "-C", str(REPO), "rev-parse", "--verify", "--quiet", ref],
        capture_output=True).returncode == 0


def test_la_porte_en_cli_refuse_le_verdict_open_pr(tmp_path):
    """Contrôle de bout en bout : la porte rend `gate_fail` a cause du SEUL
    verdict OPEN-PR -- la base et la tete ne portent aucune collision (le
    registre de la revision testee est propre). Sans ce controle, une
    integration qui nposerait pas le verdict OPEN-PR passerait quand meme."""
    if not (_has_ref("origin/main") and _has_ref("HEAD")):
        return
    claims = tmp_path / "claims.json"
    claims.write_text(json.dumps(_claims(
        (24010, "app", "0024", "myia-po-2024-CoursIA"),
        (23832, "app", "0024", "myia-po-2025-CoursIA"),
    )), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable,
         "scripts/notebook_tools/check_twin_index_collisions.py",
         "--repo", str(REPO), "--base", "origin/main", "--head", "HEAD",
         "--gate", "--json",
         "--open-claims", str(claims), "--head-pr", "24010"],
        cwd=str(REPO), capture_output=True, text=True, encoding="utf-8")
    report = json.loads(proc.stdout)
    assert report["gate_fail"] is True
    kinds = [r["kind"] for r in report["gate_reasons"]]
    assert "open_pr" in kinds
    assert proc.returncode == 1


# --- 5. la couverture de la lecture -----------------------------------------
#
# Mesure fondatrice (2026-11-04) : le parc comptait 241 PRs ouvertes et
# #24340 se situait au rang 204 -- soit **hors** du lot du plafond
# `--limit 200`. Sa revendication d'ordinal n'etait pas lue, et la couche
# OPEN-PR de la porte rendait un VERT. Un plafond fige est un plafond qui
# expire en silence.


def _stub_gh(monkeypatch, *, counts, rows):
    """Stub de `_gh` : comptes successifs (API search) + liste rendue.

    `counts` : la suite des `total_count` rendues par l'API search ;
    `rows`   : la liste rendue par `gh pr list`.

    Le stub honore `--limit` comme le fait `gh pr list` : c'est ce qui rend
    le scenario de l'index en retard fidele -- sans cela, le stub rendrait
    plus de lignes que demandees et la troncature ne se produirait jamais.
    """
    calls = []
    state = {"i": 0}

    def fake(args, *, cwd=None):
        calls.append(list(args))
        if args[0] == "api":
            idx = min(state["i"], len(counts) - 1)
            state["i"] += 1
            return json.dumps({"total_count": counts[idx]})
        limit = int(args[args.index("--limit") + 1])
        return json.dumps(rows[:limit])

    monkeypatch.setattr(toc, "_gh", fake)
    return calls


def _pr_rows(numbers, *, registry=False):
    out = []
    for number in numbers:
        path = _path("0024") if registry else "scripts/ci/other.py"
        out.append({"number": number, "files": [{"path": path,
                                                  "status": "added"}]})
    return out


def _limit_of(calls):
    """Le `--limit` passe a `gh pr list`."""
    for call in calls:
        if call[0] == "pr" and "--limit" in call:
            return int(call[call.index("--limit") + 1])
    return None


def test_le_plafond_de_lecture_vient_du_compte_exact_des_prs_ouvertes(monkeypatch):
    """Le plafond vaut le parc mesure **plus la marge**, pas une constante :
    241 PRs ouvertes imposent 241 + la marge, pas 200."""
    calls = _stub_gh(monkeypatch, counts=[241], rows=_pr_rows(range(1, 242)))
    toc.open_prs_touching_registry("jsboige/CoursIA")
    assert _limit_of(calls) == 241 + toc.READ_MARGIN


def test_un_plafond_explicite_ne_petit_jamais_la_lecture(monkeypatch):
    """Un `limit` passe en parametre est un PLANCHER, pas un plafond : il ne
    peut pas re-introduire la troncature qu'on vient de supprimer."""
    calls = _stub_gh(monkeypatch, counts=[241], rows=_pr_rows(range(1, 242)))
    toc.open_prs_touching_registry("jsboige/CoursIA", limit=10)
    assert _limit_of(calls) == 241 + toc.READ_MARGIN


def test_une_liste_tronquee_leve_une_erreur_au_lieu_de_rendre_un_vert(monkeypatch):
    """« je n'ai pas pu tout lire » n'est pas « c'est propre » : fail-closed."""
    _stub_gh(monkeypatch, counts=[500, 500], rows=_pr_rows(range(1, 201)))
    with pytest.raises(toc.GhError) as exc:
        toc.open_prs_touching_registry("jsboige/CoursIA")
    assert "tronquee" in str(exc.value)


def test_une_fermeture_survenue_entre_les_deux_appels_ne_leve_pas_d_erreur(monkeypatch):
    """L'ecart entre le compte et la liste peut venir d'une PR fermee entre
    les deux appels : c'est un alea benign, pas une troncature."""
    _stub_gh(monkeypatch, counts=[500, 499], rows=_pr_rows(range(1, 500)))
    numbers = toc.open_prs_touching_registry("jsboige/CoursIA")
    assert numbers == []  # aucune PR de ce lot ne touche le registre


def test_une_revendication_au_dela_de_l_ancien_plafond_est_vue(monkeypatch):
    """Le cas mesure : une PR au rang 204 sur 241 doit etre lue."""
    rows = _pr_rows(range(1, 242))
    rows[203] = {"number": 99999,
                  "files": [{"path": _path("0027", "myia-po-2028-CoursIA"),
                             "status": "added"}]}
    _stub_gh(monkeypatch, counts=[241], rows=rows)
    assert toc.open_prs_touching_registry("jsboige/CoursIA") == [99999]


def test_un_index_en_retard_ne_peut_pas_trancher_sans_erreur(monkeypatch):
    """L'index de la recherche peut sous-compter : c'est le lot plein qui tranche.

    Scenario : l'index rend `total_count = 241` alors que le parc reel en
    compte 291 (des PRs ouvertes apres la derniere indexation). Sous un
    plafond calcule sur ce compte (`--limit 241`), `gh pr list` rend les 241
    PRs **les plus recentes** et les plus anciennes disparaissent -- c'est la
    PR #24340 au rang 204 qui etait invisible. Aucun ecart ne se voyait :
    `len(rows) == total`, donc aucune erreur n'etait levee.

    Avec la marge, on demande `total + READ_MARGIN` : le lot revient **plein**,
    et un lot plein prouve la troncature, quel que soit le compte de l'index.
    """
    eff = 241 + toc.READ_MARGIN
    _stub_gh(monkeypatch, counts=[241], rows=_pr_rows(range(1, eff + 1)))
    with pytest.raises(toc.GhError) as exc:
        toc.open_prs_touching_registry("jsboige/CoursIA")
    assert "tronquee" in str(exc.value)
