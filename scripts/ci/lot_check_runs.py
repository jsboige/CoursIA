#!/usr/bin/env python3
"""Publication des check-runs du lot quotidien en ombre (P3 tranche 2).

La tranche 1 du lot (#25521) mesure : elle construit l'arbre d'integration et
joue la suite lourde dessus, mais **n'emet aucun check-run** -- le lot ne
jugeait donc aucune PR, et la comparaison de la semaine d'ombre n'avait aucun
support cote PR. Cette tranche publie **un check-run par tete du lot**, ce
qui rend le verdict du lot lisible sur la PR sans rien changer au gate.

Trois regles structurent le module :

1. **Le check-run est advisory.** Son nom porte le marqueur `advisory`, que
   `scripts/pr_gate.py::is_advisory` reconnait par nom (le gate route alors
   le check dans le seau « advisory », qui **ne pese jamais sur le code de
   sortie**). Un lot rouge ne bloque donc aucun merge : la bascule du gate
   sur « etage 2 vert » est l'objet de P4, pas de cette tranche.
2. **Le verdict est celui de l'arbre, pas celui de l'isolement.** Le lot
   mesure `main` plus les PRs du lot ; le check-run dit donc exactement cela
   dans son resume. Un check-run qui pretendrait juger la PR seule serait un
   mensonge : la PR peut etre verte en isolement et rouge dans l'arbre.
3. **Ce qui n'a pas ete mesure ne se presente pas comme rouge.** Seule la
   suite rejouee et rouge (`pytest_rc != 0` sur une suite lancee) donne
   `failure`. Une dependance manquante, un environnement incomplet, une
   selection vide ou une PR de fork donnent `neutral` ou l'absence de
   check-run -- avec le motif **nomme**.

La troncature du pool est portee dans le resume : quand
`pool_inspecte == limit`, la population inspectee a atteint le plafond, la
selection peut donc etre partielle, et un lot « vert » ne prouve alors rien
sur les PRs non inspectees. La remarke est laite plutot que tue : c'est la
demande explicite du coordinateur (message du 10/11 02:04Z, point 1).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

# L'organe natif de publication d'un check-run est `scripts/ci/fast_lane.py`
# (`emit_check_run`) : le depot l'a deja ecrit, avec le meme `gh api
# --input -`. Ce module ne fait que decrire le verdict du lot ; il ne
# reimplemente pas l'ecriture.
sys.path.insert(0, str(Path(__file__).resolve().parent))

import fast_lane  # noqa: E402

# Le marqueur `advisory` est ce qui fait que le PR gate ne traite pas ce
# check-run comme une porte (scripts/pr_gate.py::is_advisory). Le nom est
# stable d'un lot a l'autre : le gate plie les check-runs par NOM, et un nom
# qui changerait a chaque lot ferait birdir la comparaison.
CHECK_RUN_NAME = "Heavy batch lot (advisory, non bloquant)"

# Statuts produits par `heavy_batch.run_one`. Seuls ceux-la sont interpretes ;
# un statut inconnu ne devient jamais rouge.
_CONCLUSION_PAR_STATUT = {
    "vert": "success",
    "rouge": "failure",
    "non-mesurable": "neutral",
    "simulation": "skipped",
}

_CONCLUSION_NEUTRE = "neutral"

_STATUT_LISIBLE = {
    "vert": "suite jouee et verte",
    "rouge": "suite jouee et rouge",
    "non-mesurable": "non mesurable (environnement incomplet)",
    "simulation": "simulation (lot non joue)",
    "aucun-test-concerne": "aucun test concerne par la selection",
    "selecteur-absent": "selecteur de tests absent",
    "selecteur-echoue": "selecteur de tests en echec",
    "fetch-echoue": "ref de fusion inaccessible",
    "worktree-echoue": "worktree jetable non cree",
    "echec": "echec du lot sur cette PR",
    "erreur": "erreur du lot sur cette PR",
}

_PUBLICATION_NOMINALE = "publie"


def conclusion_pour_statut(statut: str | None) -> str:
    """Conclusion du check-run pour un statut de lot.

    Fonction pure. Un statut inconnu, un statut vide ou un statut absent
    donne `neutral` : **jamais** `failure`. Seul le statut `rouge` -- la
    suite rejouee et en echec -- donne `failure`.
    """
    return _CONCLUSION_PAR_STATUT.get((statut or "").strip(), _CONCLUSION_NEUTRE)


def pool_tronque(pool_inspecte: int | None, limit: int | None) -> bool:
    """La population inspectee a-t-elle atteint le plafond de lecture ?

    Fonction pure. `pool_inspecte == limit` signifie que la lecture s'est
    arretee au plafond : la selection peut etre **partielle**, et un lot
    « vert » ne dit rien des PRs non inspectees.
    """
    if not pool_inspecte or not limit:
        return False
    return int(pool_inspecte) >= int(limit)


def _resume_pour(
    *,
    number: int,
    statut: str,
    duree_s: float | None,
    lot_statut: str | None,
    lot_pr_coupable: int | None,
    tronque: bool,
    pool_inspecte: int | None,
    limit: int | None,
) -> str:
    """Resume du check-run (fonction pure)."""
    lignes = [
        "Verdict du **lot en ombre** (P3 du plan CI a deux etages, #25510).",
        "",
        "Ce verdict porte sur **l'arbre d'integration** (`main` plus les PRs du "
        "lot), pas sur la PR isolee : une PR peut etre verte seule et rouge "
        "dans l'arbre.",
        "",
        f"- PR : #{number}",
        f"- Mesure sur la PR : {statut}",
    ]
    if duree_s is not None:
        lignes.append(f"- Duree de la mesure sur la PR : {duree_s} s")
    lignes.append(f"- Etat de l'arbre d'integration : {lot_statut or 'inconnu'}")
    if lot_pr_coupable:
        lignes.append(f"- PR coupable isolee par la bissection : #{lot_pr_coupable}")
    lignes += [
        "",
        "Ce check-run est **advisory** : il ne bloque aucun merge. La bascule "
        "du PR gate sur le verdict du lot est la phase P4, qui ne s'execute "
        "qu'apres la semaine d'ombre.",
    ]
    if tronque:
        lignes += [
            "",
            "> **Population tronquee.** Le pool inspecte a atteint le plafond "
            f"de lecture ({pool_inspecte} PRs inspectees pour un plafond de "
            f"{limit}) : la selection de ce lot peut etre **partielle**, et un "
            "lot vert ne prouve rien sur les PRs non inspectees.",
        ]
    return "\n".join(lignes)


def construire_payloads(
    plan: dict[str, Any], resultats: dict[str, Any]
) -> list[dict[str, Any]]:
    """Construit les check-runs du lot, sans ecrire (fonction pure).

    Chaque entree du plan donne une PR, son `head_sha` et son caractere de
    fork ; le resultat du lot donne le statut mesure par PR. Une PR dont le
    check-run ne peut pas etre porte (fork : la tete n'existe pas dans le
    depot de base ; ou tete absente) est **nommee** et n'est pas publiee
    silencieusement.
    """
    tronque = pool_tronque(plan.get("pool_inspecte"), plan.get("limit"))
    # Le numero est lu comme une **presence**, pas comme une verite : un
    # filtre de verite (`if pr.get("number")`) ecarterait silencieusement
    # toute PR dont le numero vaut 0, et son resultat deviendrait « absent du
    # resultat » -- un verdict neutre sur une mesure reellement faite.
    statuts: dict[int, dict[str, Any]] = {}
    for pr in resultats.get("prs") or []:
        numero = pr.get("number")
        if numero is None:
            continue
        statuts[int(numero)] = pr
    integration = resultats.get("integration") or {}
    arbre = integration.get("arbre") or {}
    bissection = integration.get("bissection") or {}
    lot_statut = integration.get("statut")
    lot_pr_coupable = bissection.get("pr_coupable")

    payloads: list[dict[str, Any]] = []
    for entry in plan.get("selectionnees") or []:
        number = int(entry.get("number"))
        head_sha = (entry.get("head_sha") or "").strip()
        pr = statuts.get(number) or {}
        statut = (pr.get("statut") or "").strip()
        base = {
            "pr": number,
            "head_sha": head_sha,
            "statut": statut or "absent-du-resultat",
            "conclusion": conclusion_pour_statut(statut),
            "fork": bool(entry.get("fork")),
        }
        if entry.get("fork"):
            base.update(
                {
                    "publie": False,
                    "motif": (
                        "PR de fork : la tete n'existe pas dans le depot de base, "
                        "aucun check-run ne peut y etre porte. Le verdict du lot "
                        "est dans le rapport du run."
                    ),
                }
            )
            payloads.append(base)
            continue
        if not head_sha:
            base.update(
                {
                    "publie": False,
                    "motif": "tete de PR absente du plan : rien a porter",
                }
            )
            payloads.append(base)
            continue
        base.update(
            {
                "publie": True,
                "motif": _PUBLICATION_NOMINALE,
                "name": CHECK_RUN_NAME,
                "titre": (
                    f"Lot en ombre : "
                    f"{_STATUT_LISIBLE.get(statut, statut or 'non mesure')} — PR #{number}"
                ),
                "resume": _resume_pour(
                    number=number,
                    statut=_STATUT_LISIBLE.get(statut, statut or "non mesure"),
                    duree_s=pr.get("duree_s"),
                    lot_statut=lot_statut,
                    lot_pr_coupable=lot_pr_coupable,
                    tronque=tronque,
                    pool_inspecte=plan.get("pool_inspecte"),
                    limit=plan.get("limit"),
                ),
            }
        )
        payloads.append(base)
    return payloads


def _payload_api(entry: dict[str, Any], details_url: str | None = None) -> dict[str, Any]:
    """Corps de l'API ``POST /repos/{repo}/check-runs`` (fonction pure).

    Le corps est celui de l'organe natif `scripts/ci/fast_lane.py`
    (`emit_check_run`) : meme forme, memes plafonds (titre 255 caracteres,
    resume `OUTPUT_LIMIT`). Ce module ne fait que **decrire** le verdict du
    lot ; l'ecriture passe par l'organe.
    """
    payload: dict[str, Any] = {
        "name": entry["name"],
        "head_sha": entry["head_sha"],
        "status": "completed",
        "conclusion": entry["conclusion"],
        "output": {
            "title": entry["titre"][:255],
            "summary": entry["resume"][:fast_lane.OUTPUT_LIMIT],
        },
    }
    if details_url:
        payload["details_url"] = details_url
    return payload


def publier(
    repo: str,
    payloads: list[dict[str, Any]],
    *,
    dry_run: bool = False,
    details_url: str | None = None,
) -> list[dict[str, Any]]:
    """Publie les check-runs (un POST par tete) et rend le journal.

    L'ecriture est celle de l'**organe natif** `scripts/ci/fast_lane.py`
    (`emit_check_run`) : le depot a deja la fonction qui poste un check-run
    sur une tete de PR, avec le meme `gh api --input -` (le corps est lu sur
    l'entree standard, jamais par un `-f body=@fichier` — regle
    gh-posting-hygiene). Reimplementer ce POST serait du duplication
    d'organe ; la seule chose que ce module ajoute est le **verdict du
    lot** et sa troncature.

    Un echec de publication **n'interrompt pas le lot** : le journal nomme la
    PR et l'echec, et le lot reste mesure.
    """
    journal: list[dict[str, Any]] = []
    for entry in payloads:
        if not entry.get("publie"):
            journal.append(
                {
                    "pr": entry.get("pr"),
                    "statut": "non publie",
                    "motif": entry.get("motif"),
                }
            )
            continue
        if dry_run:
            journal.append(
                {
                    "pr": entry.get("pr"),
                    "statut": "simulation",
                    "motif": "dry-run",
                    "corps": _payload_api(entry, details_url),
                }
            )
            continue
        ok = fast_lane.emit_check_run(
            repo,
            entry["head_sha"],
            entry["name"],
            entry["conclusion"],
            entry["titre"],
            entry["resume"],
            False,
            details_url,
        )
        journal.append(
            {
                "pr": entry.get("pr"),
                "statut": "publie" if ok else "echec de publication",
                "conclusion": entry.get("conclusion"),
                "motif": _PUBLICATION_NOMINALE if ok else "l'organe a refuse l'ecriture",
            }
        )
    return journal


def main(argv: list[str] | None = None) -> int:
    """Point d'entree : publie les check-runs d'un lot deja joue."""
    import argparse

    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--repo", required=True, help="depot cible (owner/name)")
    parser.add_argument("--plan", type=Path, required=True, help="plan du lot (JSON)")
    parser.add_argument("--results", type=Path, required=True, help="resultat du lot (JSON)")
    parser.add_argument("--details-url", default=None, help="lien du run porte dans le check-run")
    parser.add_argument("--dry-run", action="store_true", help="ecrire les corps sans les poster")
    parser.add_argument("--json", action="store_true", help="sortie JSON machine")
    args = parser.parse_args(argv)

    try:
        plan = json.loads(args.plan.read_text(encoding="utf-8"))
        resultats = json.loads(args.results.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        print(f"plan ou resultat illisible : {exc}", file=sys.stderr)
        return 2

    payloads = construire_payloads(plan, resultats)
    journal = publier(
        args.repo,
        payloads,
        dry_run=args.dry_run,
        details_url=args.details_url,
    )
    if args.json:
        print(
            json.dumps(
                {
                    "check_run_name": CHECK_RUN_NAME,
                    "pool_tronque": pool_tronque(plan.get("pool_inspecte"), plan.get("limit")),
                    "journal": journal,
                },
                ensure_ascii=False,
                indent=2,
            )
        )
    else:
        for ligne in journal:
            print(f"#{ligne.get('pr')} : {ligne.get('statut')} — {ligne.get('motif')}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
