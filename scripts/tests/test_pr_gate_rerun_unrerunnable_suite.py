"""Le sweep nomme le refus STRUCTUREL de relance, il ne le compte pas comme repare (#19050).

Mesure fondatrice (2026-10-04 vers 02:45Z, #18985) : une PR a dossier READY
(B.0 rc=0) et toutes ses jambes vertes reste BLOCKED, parce que deux check-runs
`PR gate` requis coexistent dans deux suites -- l'une d'elles hebergee par
l'execution CodeQL en `default setup` (evenement `dynamic`) :

    gh run rerun 37144908600 --repo jsboige/CoursIA
    run 37144908600 cannot be rerun; This workflow run cannot be retried

Le remede du sweep (relancer l'execution qui porte la jambe rouge, pour la
remplacer DANS SA SUITE) est donc IMPOSSIBLE sur ce sous-cas, et la branche de
refus existante y appliquait le remede de #17680 -- dispatch du harnais
`pr-gate-rerun.yml`. Ce dispatch laisse la jambe rouge en place (une jambe
neuve atterrit dans sa propre suite, et GitHub exige que TOUTES les jambes d'un
nom requis soient vertes : cf. l'en-tete du workflow), et le compteur `served`
la comptait comme servie.

La propriete pinnee n'est pas « le refus est logue » (il l'etait) mais :
**un refus structurel est NOMME, n'applique pas le remede de la dead-queue, dit
le geste qui marche, et n'est pas compte comme repare.**

Le classement porte sur le CHAMP `status` du run (`RUN_STATUS`), jamais sur la
prose du refus : le depot ne consigne pas le texte de la cause #17680
(`grep -rn "cannot be rerun" scripts/ .github/ docs/` ne rend que ce cas-ci), et
une correspondance de texte devinee casse en silence le jour ou GitHub reformule.

`SWEEP_YML` permet de pointer une AUTRE version du workflow -- c'est ce qui rend
la falsification mesurable : sur la version d'avant ce correctif, les tests
ci-dessous rougissent.
"""
from __future__ import annotations

import os
import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SWEEP = Path(
    os.environ.get(
        "SWEEP_YML",
        REPO_ROOT / ".github" / "workflows" / "pr-gate-stale-sweep.yml",
    )
)

# Le marqueur du sous-cas. C'est un nom, pas une phrase : il doit rester
# greppable dans le log du sweep (c'est ainsi qu'un humain ou un organe
# retrouve la classe sans relire le YAML).
MARQUEUR = "SUITE_UNRERUNNABLE"


def _branches() -> tuple[list[str], list[str]]:
    """Rend (branche structurelle, branche dead-queue) du bloc de refus.

    Localise le bloc par le CHAMP `RUN_STATUS` (pas par un numero de ligne : le
    workflow bouge souvent), puis separe sur le `else` de meme indentation.
    """
    lignes = SWEEP.read_text(encoding="utf-8").splitlines()
    i = next((n for n, l in enumerate(lignes) if "RUN_STATUS=$(printf" in l), None)
    assert i is not None, (
        "classement introuvable : `RUN_STATUS=$(printf ...)` a disparu du sweep "
        "-- le sous-cas #19050 n'est plus distingue"
    )
    entete = next(
        (n for n in range(i, min(i + 6, len(lignes)))
         if 'if [ "${RUN_STATUS:-}" = "completed" ]' in lignes[n]),
        None,
    )
    assert entete is not None, (
        "l'entete du branchement `completed` a disparu juste apres RUN_STATUS"
    )
    ind = len(lignes[entete]) - len(lignes[entete].lstrip())

    def _a_indentation(n: int, mot: str) -> bool:
        l = lignes[n]
        return l.strip() == mot and (len(l) - len(l.lstrip())) == ind

    sep = next((n for n in range(entete + 1, len(lignes))
                if _a_indentation(n, "else")), None)
    fin = next((n for n in range(entete + 1, len(lignes))
                if _a_indentation(n, "fi")), None)
    assert sep is not None and fin is not None and sep < fin, (
        "branchement mal forme : `else`/`fi` de meme indentation introuvables"
    )
    structurelle = lignes[entete + 1:sep]
    dead_queue = lignes[sep + 1:fin]
    # Controle de non-vacuite : si le decoupage se met a capturer autre chose,
    # les assertions qui suivent passeraient en ne regardant rien.
    assert any(MARQUEUR in l for l in structurelle), (
        f"la branche supposee structurelle ne porte pas {MARQUEUR} : "
        "le decoupage vise a cote"
    )
    assert any("17680" in l for l in dead_queue), (
        "la branche supposee dead-queue ne cite pas #17680 : le decoupage vise "
        "a cote"
    )
    return structurelle, dead_queue


def test_le_classement_porte_sur_le_champ_status():
    # Le champ, pas la prose : `RUN_STATUS` est lu depuis le run deja recupere.
    lignes = SWEEP.read_text(encoding="utf-8")
    assert re.search(r"RUN_STATUS=\$\(printf '%s' \"\$\{RUN:-\}\" \| jq -r '\.status", lignes), (
        "le classement ne lit plus `.status` du run : il est retombe sur un "
        "autre critere (texte du refus ?) -- devine, donc faux un jour"
    )


def test_le_sous_cas_structurel_est_nomme():
    structurelle, _ = _branches()
    corps = "\n".join(structurelle)
    assert MARQUEUR in corps
    # Le message doit porter la PR et le SHA : un nom sans cible n'est pas un
    # rapport, c'est un compteur.
    assert "$NUM" in corps and "$SHA" in corps
    assert "$RUN_ID" in corps, "le run fautif doit etre nomme"


def test_le_refus_structurel_n_applique_pas_le_remede_de_la_dead_queue():
    # Une jambe neuve ne remplace pas la rouge (l'AND de GitHub sur un nom
    # requis) : dispatcher le harnais ici est le defaut mesure.
    structurelle, _ = _branches()
    corps = "\n".join(structurelle)
    assert "pr-gate-rerun.yml" not in corps, (
        "le refus structurel dispatche encore le harnais `pr-gate-rerun.yml` "
        "-- remede inerte sur ce sous-cas (#19050)"
    )
    assert "gh workflow run" not in corps


def test_le_geste_qui_marche_est_dit():
    structurelle, _ = _branches()
    corps = "\n".join(structurelle)
    assert "update-branch" in corps, (
        "le refus structurel ne dit pas le geste qui marche (nouvelle tete)"
    )
    # L'effet de bord doit etre annonce : une nouvelle tete recree les suites
    # et PERIME le dossier de prevalidation -- la lane ou le coordinateur doit
    # le savoir avant de croire le dossier encore valable.
    assert "prevalidation" in corps


def test_le_refus_structurel_n_est_pas_compte_comme_repare():
    structurelle, _ = _branches()
    corps = "\n".join(structurelle)
    assert "structural=$((structural + 1))" in corps, (
        "le refus structurel n'est pas compte a part : il retombe dans les "
        "compteurs `served`, qui se lisent comme des reparations"
    )
    # ... et le rapport final doit le nommer, sinon le compteur ne sert a rien.
    lignes = SWEEP.read_text(encoding="utf-8")
    assert re.search(r'echo "\[stale-sweep\] dont \$structural', lignes), (
        "le rapport final ne nomme pas les refus structurels"
    )
    assert re.search(r"^\s*structural=0\s*$", lignes, re.M), (
        "le compteur `structural` n'est pas initialise avant la boucle"
    )


def test_la_cause_dead_queue_garde_son_remede():
    # Temoin negatif : le correctif ne doit pas casser #17680. La branche
    # dead-queue (run non termine) garde son message ET son dispatch.
    _, dead_queue = _branches()
    corps = "\n".join(dead_queue)
    assert "not completed" in corps
    assert "gh workflow run pr-gate-rerun.yml" in corps
    assert "-f pr_number=" in corps and "-f head_sha=" in corps


# --- volet 2 : le candidat lui-meme -------------------------------------
#
# Le volet 1 ne suffit pas. Sur le cas fondateur, le sweep ne relance pas le
# run de la jambe rouge : il relance le run HOMONYME trouve par
# `name == "PR gate" & event == pull_request` -- un run vert -- dont la relance
# reussit. La branche de refus n'est donc jamais atteinte, et la PR se lit
# « servie » alors que la jambe rouge, hebergee par une suite `dynamic`, n'a
# pas bouge. C'est le candidat qu'il faut ecarter, en le nommant.

_URL_JAMBE_NUE = "https://github.com/jsboige/CoursIA/runs/111294508181"
_URL_JAMBE_SAINE = ("https://github.com/jsboige/CoursIA/actions/runs/"
                    "37159733958/job/111346389784")


def _builder_python() -> str:
    """Le bloc Python inline qui ecrit /tmp/candidates.txt."""
    texte = SWEEP.read_text(encoding="utf-8")
    parts = texte.split("python3 - <<'PY'")
    assert len(parts) >= 2, "bloc `python3 - <<'PY'` introuvable dans le sweep"
    # Le fichier porte PLUSIEURS blocs `<<'PY'` : on prend celui qui ecrit les
    # candidats, pas le premier venu (sinon le test regarde un autre organe et
    # passe -- ou rougit -- pour de mauvaises raisons).
    bloc = next((p for p in parts[1:] if "candidates.txt" in p), None)
    assert bloc is not None, (
        "aucun bloc `<<'PY'` n'ecrit /tmp/candidates.txt : le constructeur de "
        "candidats a ete deplace ou renomme"
    )
    corps = bloc.split("\nPY")[0]
    lignes = corps.splitlines()
    if lignes and lignes[0].lstrip().startswith(">"):
        lignes = lignes[1:]          # la ligne de redirection du heredoc
    return "\n".join(lignes)


def test_le_predicat_de_jambe_nue_est_celui_mesure_sur_18985():
    # Le predicat lui-meme, eprouve sur les DEUX urls reelles du cas #18985 :
    # la jambe rouge nue (id de check-run) doit etre rejetee, la jambe saine
    # (`/actions/runs/<run>/job/<job>`) acceptee. C'est la propriete qui
    # decide ; la pin de presence, seule, ne prouverait rien.
    corps = _builder_python()
    m = re.search(r'_RUNJOB_RE = re\.compile\((r"[^"]+")\)', corps)
    assert m, "le motif `_RUNJOB_RE` a disparu du constructeur de candidats"
    motif = re.compile(eval(m.group(1)))  # noqa: S307 -- litteral du depot
    assert motif.search(_URL_JAMBE_SAINE), (
        "le predicat rejette une jambe saine : il retirerait du sweep des PRs "
        "que le re-run repare aujourd'hui"
    )
    assert not motif.search(_URL_JAMBE_NUE), (
        "le predicat accepte la jambe nue du cas #18985 : le sous-cas n'est "
        "pas distingue"
    )


def test_la_jambe_sans_run_relancable_est_nommee_et_ecartee():
    corps = _builder_python()
    assert "SUITE_UNRERUNNABLE" in corps, "la classe n'est pas nommee"
    bloc = corps[corps.index("_RUNJOB_RE"):]
    assert "_diag(p, " in bloc, (
        "l'exclusion n'est pas nommee dans le rapport (idiome #11808)"
    )
    assert re.search(r"if unrerunnable[^:]*:\n\s+_diag", bloc), (
        "l'exclusion nommee n'est plus conditionnee au predicat"
    )
    assert "gh pr update-branch" in bloc, "le geste qui marche n'est pas dit"
    assert "prevalidation" in bloc, (
        "l'effet de bord (dossier de prevalidation perime) n'est pas annonce"
    )


def test_une_url_absente_n_exclut_pas():
    # Le piege rencontre en ecrivant ce correctif : une URL ABSENTE est une
    # donnee manquante, pas une jambe structurellement non relancable. Sans
    # cette garde, le filtre vidait le sweep sur tout jeu ou la collecte ne
    # rend pas d'URL -- mesure : les 42 tests de `test_pr_gate_sweep_select.py`
    # sont passes de vert a rouge, et il aurait surtout exclu des PRs que le
    # re-run du gate repare (repli plus PERMISSIF que le gate, interdit par
    # #15775).
    #
    # La propriete est couverte COMPORTEMENTALEMENT par cette suite-la, qui
    # pilote le vrai bloc Python : la retirer fait rougir ses 42 tests. La pin
    # ci-dessous la rend lisible a l'endroit du correctif.
    corps = _builder_python()
    assert re.search(r'and \(c\.get\("details_url"\) or ""\)\.strip\(\)', corps), (
        "l'exclusion ne garde plus l'absence d'URL : elle emporterait les "
        "candidats dont la collecte n'a pas rendu de details_url"
    )


def test_l_exclusion_ne_tue_pas_le_chemin_des_constituants():
    # Le piege : une PR dont la jambe de gate est nue peut encore se reparer
    # par ses CONSTITUANTS annules (#15775), la passe suivante re-layant le
    # gate. Exclure sans regarder `rerun_ids` tuerait ce chemin.
    corps = _builder_python()
    assert re.search(r"if unrerunnable and not rerun_ids:", corps), (
        "l'exclusion n'est pas gardee par `not rerun_ids` : elle emporterait "
        "les candidats reparables par leurs constituants"
    )
    # ... et l'ordre doit tenir : avant `rerun_ids`, ce nom n'existe pas.
    assert corps.index("rerun_ids = []") < corps.index("_RUNJOB_RE"), (
        "l'exclusion a ete remontee avant la construction de `rerun_ids` : "
        "la garde lirait un nom non defini (ou pire, une variable d'un tour)"
    )
