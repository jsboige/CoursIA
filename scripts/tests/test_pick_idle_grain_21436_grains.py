"""#21436 [RESTE] -- 0 faux negatif du slice --grains + borne enforcee.

Triage du 09/11 (dernier commentaire) : sur l'acceptance de l'issue, la
duree ``--grains 50`` est tenue (235,4 s, #24047) ; restaient sans preuve :

1. **0 faux negatif** -- un grain ripe doit toujours etre servi en tete,
   quel que soit ``--grains`` ;
2. la **documentation de la borne** dans ``--help`` (defaut, maximum).

Ces tests epinglent (1) par construction sur ``draw_belt`` (le modele
deterministe du tapis, cf docstring de la fonction) : le tri
``belt_sort_key`` precede TOUJOURS le slice, donc la tete du tri reste
dans le slice quel que soit N >= 1 -- fut-il en derniere position du pool
brut. Le chemin production suit le meme ordre (``belt_pool.sort`` puis
iteration dans l'ordre du tri, arret au quota), le slice du
board-consumer porte le meme ``max(1, ...)`` depuis #21436.

Et (2) par l'application de la borne au parsing : valeurs hors [1, 200]
refusees avec message, plafond inscrit dans ``--help``.

Aucun de ces tests n'emmet d'appel reseau : ``draw_belt`` est en memoire
apres fetch_pool (non sollicite ici), et le refus de parsing survient
avant tout fetch.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig  # noqa: E402


def _make_item(number, age_days, idle, klass="grain", last=None,
               created=None, genre="docs"):
    return {
        "number": number,
        "klass": klass,
        "age": age_days,
        "idle": idle,
        "genre": genre,
        "labels": [],
        "title": f"issue #{number}",
        "created_at": created or f"2026-{(age_days % 9) + 1:02d}-01T00:00:00Z",
        "last_delivery_stamp": last,
    }


class _FakeArgs:
    """Args minimum pour draw_belt / belt_sort_key / belt_filter
    (cf test_pick_idle_grain_belt.py)."""

    def __init__(self, *, grains=4):
        self.exclude_issue = []
        self.require_label = []
        self.exclude_label = []
        self.min_age_days = None
        self.max_age_days = None
        self.min_idle_days = None
        self.max_idle_days = None
        self.urns = "grain,umbrella,delivered"
        self.grains = grains


def _pool_ripe_en_derniere_position():
    """Pool brut OU le grain ripe (jamais servi, cree le plus tot) git en
    DERNIERE position -- l'ordre d'entree ne doit rien decider."""
    jeunes = [
        _make_item(11, age_days=3, idle=1, last="2026-11-01T00:00:00Z",
                   created="2026-11-01T00:00:00Z"),
        _make_item(12, age_days=5, idle=2, last="2026-10-15T00:00:00Z",
                   created="2026-10-01T00:00:00Z"),
        _make_item(13, age_days=9, idle=4, last="2026-09-01T00:00:00Z",
                   created="2026-09-01T00:00:00Z"),
    ]
    ripe = _make_item(99, age_days=40, idle=40, last=None,
                      created="2026-01-01T00:00:00Z")
    return jeunes + [ripe]


# Predicat 1 : 0 faux negatif -- le ripe sort en tete quel que soit grains.


@pytest.mark.parametrize("grains", [1, 2, 4, 50, 200])
def test_le_grain_ripe_est_servi_en_tete_quel_que_soit_grains(grains):
    """Acceptance #21436 : le slice ne peut pas escamoter la tete du tri.

    Le pool brut porte le ripe en DERNIERE position : si le slice venait
    AVANT le tri (le faux negatif redoute), un grains=1 ne servirait que
    le jeune de tete et le ripe resterait invisible.
    """
    picks = pig.draw_belt(_pool_ripe_en_derniere_position(),
                          _FakeArgs(grains=grains))
    assert picks, f"grains={grains} : sortie vide"
    assert picks[0]["number"] == 99, (
        f"grains={grains} : la tete du tirage est #{picks[0]['number']}, "
        "pas le grain ripe #99")
    assert len(picks) == min(grains, 4)


def test_grains_zero_ne_vide_jamais_la_sortie():
    """--grains 0 : le slice rend AU MOINS la tete (aligne board-consumer).

    Sans max(1, ...), filtered[:0] == [] : un appelant scripte lirait
    "pool vide" et conclurait a une famine -- le faux positif jumeau du
    faux negatif.
    """
    picks = pig.draw_belt(_pool_ripe_en_derniere_position(),
                          _FakeArgs(grains=0))
    assert len(picks) == 1
    assert picks[0]["number"] == 99


def test_grains_negatif_ne_tronque_pas_le_bout():
    """--grains -2 : Python lirait filtered[:-2] (retire 2 du BOUT) --
    le comportement le plus silencieusement faux possible. La tete doit
    rester servie, exactement comme a grains=0."""
    picks = pig.draw_belt(_pool_ripe_en_derniere_position(),
                          _FakeArgs(grains=-2))
    assert len(picks) == 1
    assert picks[0]["number"] == 99


# Predicat 2 : la borne est documentee ET enforcee.


@pytest.mark.parametrize("bad", ["0", "-3", "201", "500"])
def test_grains_hors_borne_est_refuse_au_parsing(bad, capsys):
    """[1, 200] enforce au parse_args : SystemExit(2) AVANT tout fetch.

    Au-dela de 200, la fenetre de service (grains*5+50) explose le mur
    de temps du tapis ; en dessous de 1, cf predicat 1.
    """
    with pytest.raises(SystemExit) as exc:
        pig.main(["--grains", bad, "--lane", "myia-po-2024:CoursIA"])
    assert exc.value.code == 2
    err = capsys.readouterr().err
    assert "entre 1 et 200" in err


def test_grains_dans_la_borne_passe_le_parsing(capsys):
    """50 (l'appel du coordinateur, cf belt_queues.py) reste admis.

    On declenche une AUTRE validation pure (apply-comment sans
    orphans-report) situee APRES la borne dans le flux de parsing :
    SystemExit sur ce message-la prouve que la borne --grains est
    passee sans rejet -- et le run s'arrete avant tout fetch reseau.
    """
    with pytest.raises(SystemExit) as exc:
        pig.main(["--grains", "50", "--lane", "myia-po-2024:CoursIA",
                  "--apply-comment", "1"])
    assert exc.value.code == 2
    err = capsys.readouterr().err
    assert "entre 1 et 200" not in err
    assert "--apply-comment" in err


def test_help_documente_defaut_et_plafond(capsys):
    """L'acceptance exige la borne DANS --help, pas seulement dans le code."""
    with pytest.raises(SystemExit) as exc:
        pig.main(["--help"])
    assert exc.value.code == 0
    out = capsys.readouterr().out
    # Bloc d'aide de --grains : la ligne d'option dans la section options
    # (pas la synopsis usage, qui cite --grains avant), plus son aide
    # wrappee jusqu'a l'option suivante.
    lines = out.splitlines()
    idx = [i for i, ln in enumerate(lines)
           if ln.strip().startswith("--grains")]
    assert idx, "--grains absent de --help"
    block: list[str] = []
    for ln in lines[idx[-1]:]:
        if block and ln.strip().startswith("--"):
            break
        block.append(ln)
    help_block = " ".join(" ".join(block).split())
    assert "defaut 4" in help_block
    assert "200" in help_block
