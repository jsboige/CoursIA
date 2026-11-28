"""La lecture des citations des commits MERGES (#27393).

Le module `coordination.tapis_citations_merges` transforme la sortie d'un
`git log --format=...` en `{numero: [citations]}`. Chaque citation porte deux
faux :

- `ferme` : le commit **cloture** le grain (mot de fermeture, ou portee du
  sujet) ;
- `canonique` : le lien qui cite le grain est **canonique** (`See #N`,
  `Closes #N`, `Fix(portee,#N)`) -- c'est lui qui porte la CLE DE SERVICE.
  Une mention en prose (`(#N)`) ne couvre rien.

Le module est extrait de `gh_bulk.py` (qui reste le seul module qui lance
`git`) pour tenir le plafond de lignes de ce dernier.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination.tapis_citations_merges import des_commits_merges


def _record(sha: str, ts: str, sujet: str, corps: str = "") -> str:
    """Un record au format du `git log` de `gh_bulk`."""
    return "\x1e" + "\x1f".join([sha, ts, sujet, corps])


def test_une_mention_en_prose_ne_couvre_pas_le_grain():
    """`(#2001)` est une mention, pas un lien : `canonique` est faux."""
    texte = _record("a" * 12, "1762896000", "Add(y): autre (#2001)")
    cites = des_commits_merges(texte)
    assert cites[2001][0]["canonique"] is False
    assert cites[2001][0]["ferme"] is False


def test_un_lien_canonique_couvre_le_grain():
    """`See #N`, `Closes #N` et `Fix(portee,#N)` couvrent : `canonique` est vrai."""
    for corps in ("See #42", "Closes #42", "Fix(coordination,#42): le grain",
                  "Part of #42"):
        cites = des_commits_merges(_record("b" * 12, "1762896000", "Sujet", corps))
        assert cites[42][0]["canonique"] is True, corps


def test_un_lien_canonique_ne_clot_pas_le_grain():
    """Couvrir n'est pas cloturer : `See #N` laisse `ferme` faux."""
    cites = des_commits_merges(_record("c" * 12, "1762896000", "Sujet", "See #42"))
    assert cites[42][0]["ferme"] is False
    assert cites[42][0]["canonique"] is True


def test_un_mot_de_fermeture_cloture_le_grain():
    cites = des_commits_merges(_record("d" * 12, "1762896000", "Sujet", "Closes #42"))
    assert cites[42][0]["ferme"] is True


def test_la_portee_du_sujet_cloture_le_grain():
    """`type(zone,#N):` -- le tag du grain -- ferme aussi."""
    cites = des_commits_merges(_record("e" * 12, "1762896000", "Fix(tapis,#42): le grain"))
    assert cites[42][0]["ferme"] is True


def test_la_date_est_au_second_et_en_utc():
    cites = des_commits_merges(_record("f" * 12, "1762905600", "Sujet", "See #42"))
    assert cites[42][0]["date"] == "2025-11-12T00:00:00Z"


def test_un_record_incomplet_est_ignore():
    """Un record sans horodatage lisible ne porte aucune citation."""
    assert des_commits_merges("\x1e" + "\x1f".join(["a" * 12, "pas-un-ts", "Sujet"])) == {}


def test_le_sha_est_conserve():
    cites = des_commits_merges(_record("0123abcd", "1762896000", "Sujet", "See #42"))
    assert cites[42][0]["sha"] == "0123abcd"
