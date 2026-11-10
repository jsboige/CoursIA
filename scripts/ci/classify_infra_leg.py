#!/usr/bin/env python3
"""Classe une jambe CI morte en « infra » ou « contenu », depuis son LOG.

POURQUOI CE FICHIER EXISTE (#21745, critere d'acceptation 4)
------------------------------------------------------------
Une jambe qui meurt sur le work dir d'un runner self-hosted ne ressemble
jamais a une panne d'infrastructure : elle ressemble a un echec de la PR.
Le nom du runner est le seul signal disponible aujourd'hui, et il ne dit
rien — le meme slot enchaine des succes et des echecs (mesure du body de
#21745 : le slot `myia-po-2024-linux-persist-5` porte un job `success` a
09:04Z et un job mort a 12:02Z le meme jour).

Ce script lit le log et nomme la cause. Il ne DEVINE pas : chaque motif
correspond a une mesure firsthand citee dans #21745.

Usage
-----
    python scripts/ci/classify_infra_leg.py --log job.log
    gh run view <id> --log-failed | python scripts/ci/classify_infra_leg.py
    python scripts/ci/classify_infra_leg.py --log job.log --json

Codes de retour
---------------
    0  une cause infra est reconnue (le verdict de contenu n'a pas de sens)
    1  aucune cause infra reconnue -- la jambe doit etre lue comme un
       verdict de contenu (ou comme inconnue)
    2  erreur d'usage ou d'E/S

Le classement est volontairement ASYMETRIQUE : un faux positif classe une
vraie regression de contenu en infra (elle serait ignoree) ; un faux negatif
impute a la PR une panne de parc. Les motifs sont donc etroits et ancres sur
des chaines mesurees, jamais sur des mots generiques (« error », « failed »).
"""

from __future__ import annotations

import argparse
import json
import re
import sys

# (code, description, [motifs], [motifs tous requis]?) -- l'ordre est la
# priorite : le premier bloc dont un motif matche gagne. L'ordre va du plus
# specifique au plus general. Le 4e element, optionnel, liste des motifs qui
# doivent TOUS matcher quelque part dans le log (pas forcement sur la meme
# ligne) : il sert quand la trace mesuree coupe une condition en deux lignes.
RULES = [
    # Forme 1 : le marqueur explicite du crochet. Il est emis par notre propre
    # code, donc il suffit a lui seul.
    (
        "INFRA_EXTERNALS_MISSING",
        "un externals du runner manque : le job meurt avant sa premiere commande",
        [re.compile(r"INFRA_EXTERNALS_MISSING")],
    ),
    # Forme 2 : la trace .NET mesuree, qui ne portait aucun marqueur. Elle
    # coupe la ligne entre le chemin et l'erreur, donc la condition porte sur
    # tout le log (motif requis) et pas sur une ligne. Sans ce ET, une simple
    # mention du chemin -- log de diagnostic sain -- classerait la jambe en
    # infra.
    (
        "INFRA_EXTERNALS_MISSING",
        "un externals du runner manque : le job meurt avant sa premiere commande",
        [re.compile(r"externals/node\d+/bin/node")],
        [re.compile(r"No such file or directory", re.IGNORECASE)],
    ),
    (
        "INFRA_DANGLING_REF",
        "ref distante pointant sur un objet absent : le clone du slot est empoisonne",
        [
            re.compile(r"bad object refs/remotes/"),
            re.compile(r"^fatal: Could not read [0-9a-f]{7,40}", re.MULTILINE),
            re.compile(r"ref distante dangling refs/remotes/"),
        ],
    ),
    (
        "INFRA_CACHE_REPAIR",
        "le cache du slot a ete repare ou mis en quarantaine par le garde de sante",
        [
            re.compile(r"work_cache: repack ECHEC"),
            re.compile(r"work_cache: .*QUARANTAINE ->"),
            re.compile(r"work_cache: .*IRRECUPERABLE"),
        ],
    ),
    (
        "INFRA_TIMEOUT",
        "la jambe a atteint son timeout declare (mise en file ou famine de runners)",
        [
            re.compile(r"hit their declared timeout-minutes"),
            re.compile(r"exceeded the maximum execution time", re.IGNORECASE),
        ],
    ),
    (
        "INFRA_RUNNER_LOST",
        "le runner self-hosted a perdu la communication en cours de job",
        [
            re.compile(r"The self-hosted runner lost communication", re.IGNORECASE),
            re.compile(r"Runner disconnected|runner has been offline", re.IGNORECASE),
        ],
    ),
]

MAX_EVIDENCE = 5


def _line_evidence(lines: list[str], patterns: list[re.Pattern]) -> list[str]:
    evidence = []
    for line in lines:
        for pattern in patterns:
            if pattern.search(line):
                evidence.append(line.strip()[:300])
                break
        if len(evidence) >= MAX_EVIDENCE:
            break
    return evidence


def classify(text: str) -> dict:
    """Rend {cause, description, evidence[]} -- cause None si rien ne matche."""
    lines = text.splitlines()
    for rule in RULES:
        code, description, patterns = rule[0], rule[1], rule[2]
        required_all = rule[3] if len(rule) > 3 else []
        # Condition ET sur tout le log : chaque motif requis doit matcher au
        # moins une ligne, sans exiger qu'ils cohabitent sur la meme.
        if any(not pattern.search(text) for pattern in required_all):
            continue
        evidence = _line_evidence(lines, patterns)
        if evidence:
            return {
                "cause": code,
                "description": description,
                "evidence": evidence,
                "is_infra": True,
            }
    return {"cause": None, "description": "", "evidence": [], "is_infra": False}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--log",
        help="fichier de log a lire (defaut : stdin)",
    )
    parser.add_argument("--json", action="store_true", help="sortie structuree")
    args = parser.parse_args(argv)

    if args.log:
        try:
            with open(args.log, "r", encoding="utf-8", errors="replace") as handle:
                text = handle.read()
        except OSError as exc:
            print("classify_infra_leg: lecture impossible: %s" % exc, file=sys.stderr)
            return 2
    else:
        text = sys.stdin.read()

    verdict = classify(text)

    if args.json:
        print(json.dumps(verdict, ensure_ascii=False, indent=1))
    elif verdict["is_infra"]:
        print("INFRA %s -- %s" % (verdict["cause"], verdict["description"]))
        for line in verdict["evidence"]:
            print("  %s" % line)
    else:
        print("CONTENU (aucune cause infra reconnue dans le log)")

    return 0 if verdict["is_infra"] else 1


if __name__ == "__main__":
    sys.exit(main())
