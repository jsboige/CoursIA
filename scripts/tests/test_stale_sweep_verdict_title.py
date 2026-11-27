"""Le SELECTEUR de titre du balayage des portes muettes (#c0138).

Le sweep (`pr-gate-stale-sweep.yml`) repare une jambe de porte muette en
recopiant dans le **titre** du check-run le texte du verdict lu dans le log
du run. Ce titre est ce que lisent ensuite le coordinateur, le picker et la
lane : un titre qui ne dit rien de l'etat des checks les envoie vers une
classification d'infra (mesure du 26/11 : 10 PRs rangees « API-QUOTA » sur
un titre qui ne parle que du quota d'appels).

Le defaut mesure : la porte imprime sa ligne de comptabilite
(`[pr-gate] api-quota: N gh api call(s), ...`) **apres** son verdict ; le
selecteur prenait la **derniere** ligne `[pr-gate]` du log, donc la
comptabilite. Le 26/11, 12 portes sur 12 ont ete reparees avec un titre
`PR gate: api-quota: ...`.

Ce module teste le selecteur **extrait du workflow lui-meme** : le pipeline
est coupe du YAML, un `gh` factice (fonction shell) renvoie un journal de la
forme reelle, et le pipeline est execute. Le test ne peut donc pas passer si
le workflow change sans que le test change -- et le temoin du defaut
(l'ancien selecteur) est rejoue dans le meme journal.

Aucun appel reseau : le `gh` du test est une fonction shell qui cat un
fichier local.
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = REPO_ROOT / ".github" / "workflows" / "pr-gate-stale-sweep.yml"

#: Le pipeline de lecture du log, tel qu'ecrit dans le workflow.
_PIPELINE_RE = re.compile(r"LINE=\$\((.*?)\) \|\| true", re.S)

#: L'ancien selecteur, rejoue comme TEMOIN du defaut : toutes les lignes
#: `[pr-gate]`, la derniere.
_ANCIEN = (
    "gh run view \"$RUN_ID\" --repo \"$REPO\" --log 2>/dev/null "
    "| grep '\\[pr-gate\\]' | tail -1 | sed 's/.*\\[pr-gate\\] //'"
)

#: Un journal de la forme reelle : le verdict, puis la ligne de
#: comptabilite que la porte imprime apres son verdict.
JOURNAL = (
    "2026-11-26T09:41:12.345Z  [pr-gate] INCONCLUSIVE -- quota "
    "d'installation GitHub App epuisee : reset annonce\n"
    "2026-11-26T09:41:13.987Z  [pr-gate] api-quota: 130 gh api call(s), "
    "87 served by a 304 (0 quota)\n"
)

#: Les formes seules que `pr_gate.py` emet pour un verdict.
JETONS = ("PASS", "FAIL", "STARVED", "INCONCLUSIVE", "DWELL")


def _pipeline() -> str:
    """Le pipeline de lecture du log, extrait du workflow."""
    texte = WORKFLOW.read_text(encoding="utf-8")
    m = _PIPELINE_RE.search(texte)
    assert m, "le pipeline de lecture du log est introuvable dans le workflow"
    # les continuations de ligne (`\` en fin de ligne) redeviennent des espaces
    return re.sub(r"\\\s*\n\s*", " ", m.group(1))


def _executer(pipe: str, journal: str, tmp_path: Path) -> str:
    """Execute le pipeline sur un journal donne, et rend sa sortie.

    Le `gh` est une **fonction shell** : elle prime sur la recherche dans le
    PATH, donc le test ne touche jamais le reseau.
    """
    log = tmp_path / "journal.log"
    log.write_text(journal, encoding="utf-8")
    # Le journal est designe par un chemin RELATIF (`cwd` = tmp_path) : un
    # chemin Windows passe par bash serait mange par les backslashes, et une
    # variable d'environnement ne traverse pas toujours le runtime MSYS sous
    # Windows -- le test ne doit dependre ni de l'un ni de l'autre.
    script = ("gh() { cat journal.log; }\n"
              "RUN_ID=45794247047\nREPO=jsboige/CoursIA\n" + pipe)
    proc = subprocess.run(["bash", "-c", script], capture_output=True,
                          text=True, encoding="utf-8", errors="replace",
                          cwd=tmp_path, check=False)
    assert proc.returncode == 0, proc.stderr
    return proc.stdout.strip()


@pytest.fixture(autouse=True)
def _bash_disponible():
    if shutil.which("bash") is None:
        pytest.skip("bash absent : le selecteur est ecrit en shell")


def test_le_selecteur_prend_le_verdict_et_non_la_comptabilite(tmp_path):
    """Le titre porte le verdict ; la ligne de comptabilite est ecartee."""
    rendition = _executer(_pipeline(), JOURNAL, tmp_path)
    assert rendition.startswith("INCONCLUSIVE -- "), rendition
    assert "api-quota" not in rendition, rendition


def test_l_ancien_selecteur_prit_la_comptabilite(tmp_path):
    """Le TEMOIN du defaut : l'ancien selecteur rendait la comptabilite.

    C'est ce que le balayage du 26/11 a colle dans 12 titres.
    """
    ancien = _executer(_ANCIEN, JOURNAL, tmp_path)
    assert ancien.startswith("api-quota: "), ancien
    # et le selecteur d'aujourd'hui ne rend pas la meme chose
    assert _executer(_pipeline(), JOURNAL, tmp_path) != ancien


def test_un_journal_sans_verdict_ne_fabrique_pas_de_titre(tmp_path):
    """Pas de ligne de verdict = pas de titre repris : le workflow garde
    son defaut nomme (#15825), il n'invente pas un verdict."""
    journal = ("2026-11-26T09:41:13.987Z  [pr-gate] api-quota: 130 gh "
               "api call(s), 87 served by a 304 (0 quota)\n")
    assert _executer(_pipeline(), journal, tmp_path) == ""


@pytest.mark.parametrize("jeton", JETONS)
def test_chaque_jeton_de_verdict_est_retenu(jeton, tmp_path):
    """Les cinq formes de verdict que `pr_gate.py` emet sont retenues."""
    journal = (f"2026-11-26T09:41:12.345Z  [pr-gate] {jeton} -- detail "
               "quelconque\n"
               "2026-11-26T09:41:13.987Z  [pr-gate] api-quota: 130 gh "
               "api call(s), 87 served by a 304 (0 quota)\n")
    rendition = _executer(_pipeline(), journal, tmp_path)
    assert rendition.startswith(f"{jeton} -- "), rendition


def test_chaque_jeton_de_verdict_est_emis_par_le_gate():
    """Le filtre du workflow ne peut pas retenir un jeton que la porte
    n'emet jamais : la liste est lue dans `scripts/pr_gate.py`."""
    gate = (REPO_ROOT / "scripts" / "pr_gate.py").read_text(encoding="utf-8")
    for jeton in JETONS:
        assert f'"{jeton} -- ' in gate, jeton
