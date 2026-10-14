#!/usr/bin/env python3
"""Tests frontiere du predicat partage issue_containers.py (#17956).

Le module est la source unique du verdict CONTAINER pour DEUX organes
(candidate_delivered.py, verifier_cleanup.py) : ses faux positifs et faux
negatifs se paient deux fois. Les frontieres ci-dessous sont celles que la
docstring du module declare -- chaque test verifie le piege nominal.
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from issue_containers import (  # noqa: E402
    is_epic_like,
    looks_container,
    subissue_tasklist_count,
    title_carries_partition,
)


def test_partition_word_boundary():
    assert title_carries_partition("[Audit #17073] Série ICT — partition Hermes")
    assert title_carries_partition("Partition par série des audits")
    # "repartitioning" / "répartitions" ne doit PAS fire (frontière \b).
    assert not title_carries_partition("Repartitioning the audit backlog")
    assert not title_carries_partition("Les répartitions du parc")


def test_epic_word_boundary():
    assert is_epic_like("EPIC: rollout nav-chain")
    assert is_epic_like("titre sobre", ["EPIC"])
    # "Epictetus" / "epicycle" ne doit PAS fire.
    assert not is_epic_like("Epictetus and the stoics")
    assert not is_epic_like("The epicycle model", ["bug"])


def test_tasklist_requires_two_distinct_issues():
    body = "- [ ] #12 premier\n- [x] #34 second\n"
    assert subissue_tasklist_count(body) == 2
    # Le MEME numero deux fois = une cible, pas un conteneur.
    assert subissue_tasklist_count("- [ ] #12\n- [x] #12\n") == 1
    # Une tache sans reference d'issue n'est pas un sous-grain.
    assert subissue_tasklist_count("- [ ] ecrire la doc\n- [ ] #12\n") == 1


def test_tasklist_signal_requires_the_body():
    # Sans body (body=None), seul le signal titre s'exprime : une lane qui
    # n'a pas transporte le body ne doit pas se voir refuser le dossier pour
    # un conteneur invisible -- ni l'inverse, un conteneur de task-list
    # categorise feuille par silence.
    assert looks_container("titre sobre", [], None) is False
    assert looks_container("titre sobre", [], "- [ ] #1\n- [ ] #2\n") is True


def test_acceptance_checkboxes_are_not_a_tasklist():
    # Les cases d'acceptance d'une feuille (#10143 en porte 4) ne nomment
    # pas d'issues : une feuille livree n'est pas un conteneur.
    body = "Acceptance:\n\n- [ ] le SVG s'affiche\n- [x] tests verts\n"
    assert subissue_tasklist_count(body) == 0
    assert looks_container("Corriger le rendu SVG", [], body) is False


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
