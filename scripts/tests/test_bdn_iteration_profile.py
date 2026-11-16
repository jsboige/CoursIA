"""Tests du profil par iteration des journaux BenchmarkDotNet (#25644).

Ce que ces tests protegent
--------------------------
Deux pieges mesures fondent cet outil, et chacun a son test :

1. **Le point de coupe trouve toujours un rapport > 1.** Sur une serie sans
   ordre temporel, le meilleur decoupage des medianes rend un rapport
   superieur a 1 par construction. Un outil qui publierait ce rapport sans
   controle par permutation produirait des « marches » sur du bruit : c'est le
   premier test, la serie constante doit rendre ``p = 1,0``.

2. **La moyenne du rapport final est un melange.** Une serie dont les
   iterations 1 a 9 coutent quatre fois plus cher que les suivantes a une
   moyenne inutilisable ; le seul artefact qui le montre est le journal
   d'iterations. Le deuxieme test verifie que le point de coupe est retrouve
   a sa position exacte, et non « quelque part avant ».

Un troisieme piege, plus discret : ``WorkloadActual`` et ``WorkloadResult``
n'ont pas la meme serie (BDN retire des iterations), donc les confondre
deplacerait le point de coupe. Le test de lecture verifie que les deux motifs
ne se melangent pas.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

_BENCHMARKS_DIR = Path(__file__).resolve().parent.parent / "benchmarks"
if str(_BENCHMARKS_DIR) not in sys.path:
    sys.path.insert(0, str(_BENCHMARKS_DIR))

import bdn_iteration_profile as bip  # noqa: E402


def _actual_line(index: int, us_per_op: float) -> str:
    return f"  WorkloadActual   {index}: 100 op, {us_per_op * 100:.2f} ns, {us_per_op:.4f} us/op"


def _result_line(index: int, us_per_op: float) -> str:
    return f"  WorkloadResult   {index}: 100 op, {us_per_op * 100:.2f} ns, {us_per_op:.4f} us/op"


def _journal(values, line=_actual_line) -> list[str]:
    lines = ["// Runtime=.NET 9.0.22", ""]
    lines.extend(line(index, value) for index, value in enumerate(values, start=1))
    return lines


# --- lecture du journal -----------------------------------------------------


def test_lecture_separe_actual_de_result():
    """Les deux series coexistent dans un journal BDN reel ; ne pas les confondre."""
    values = [10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 3.0, 3.5, 4.0, 3.2, 3.1, 3.3]
    lines = []
    for index, value in enumerate(values, start=1):
        lines.append(_actual_line(index, value))
        if index <= 9:
            lines.append(_result_line(index, value))

    actual = bip.parse_series(lines, kind="actual")
    result = bip.parse_series(lines, kind="result")

    assert len(actual) == 12
    assert len(result) == 9
    assert actual[:3] == [10.0, 11.0, 12.0]


def test_lecture_convertit_l_unite_choisie_par_bdn():
    """BDN ecrit ns/op sous la microseconde : le motif doit l'accepter et le ramener en us.

    Le defaut mesure : un motif limite a ``us/op`` ne rend pas d'erreur, il rend
    une serie vide, et les douze jambes Signature_Matches du banc 4 ont disparu
    du recensement sans laisser de trace. Les deux unites doivent donc cohabiter
    et produire la meme echelle.
    """
    lines = [
        "  WorkloadActual   1: 1403656 op, 116977170.00 ns, 83.3375 ns/op",
        "  WorkloadActual   2: 593039 op, 166139320.00 ns, 280.1491 ns/op",
        "  WorkloadActual   3: 873 op, 52822350.00 ns, 60.5067 us/op",
        "  WorkloadActual   4: 12 op, 2000000000.00 ns, 2.5000 ms/op",
    ]
    assert bip.parse_series(lines) == pytest.approx([0.0833375, 0.2801491, 60.5067, 2500.0])


def test_lecture_accepte_les_separateurs_de_milliers():
    lines = ["  WorkloadActual   1: 1,403,656 op, 116977170.00 ns, 83.3375 ns/op"]
    assert bip.parse_series(lines) == pytest.approx([0.0833375])


def test_lecture_ignore_le_bruit_du_journal():
    """Les lignes d'en-tete, avertissements et copies de corps ne sont pas des mesures."""
    lines = [
        "// Runtime=.NET 10.0.14",
        "Warnings: MinIterationTime",
        "[msg: le corps de requete contient 'WorkloadActual   1: 1 op, 1 ns, 1 us/op']",
        "",
        _actual_line(1, 60.5067),
        "|  Method | Mean |",
    ]
    assert bip.parse_series(lines) == [60.5067]


def test_lecture_serie_vide():
    assert bip.parse_series(["rien a voir"], kind="actual") == []


# --- point de coupe ---------------------------------------------------------


def test_point_de_coupe_retrouve_sa_position():
    """Les iterations 1 a 9 precedents la marche, les suivantes sont 4x moins cheres."""
    values = [10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0, 17.0, 18.0, 3.0, 3.5, 4.0, 3.2, 3.1, 3.3]
    step = bip.best_step(values, min_side=3)

    assert step is not None
    assert step["position"] == 9
    assert step["pre_median"] == pytest.approx(14.0)
    assert step["post_median"] == pytest.approx(3.25)
    assert step["ratio"] == pytest.approx(14.0 / 3.25)


def test_point_de_coupe_refuse_une_serie_trop_courte():
    """Quinze iterations donnent un decoupage ; quatre n'en donnent aucun."""
    assert bip.best_step([1.0, 2.0, 3.0, 4.0], min_side=3) is None
    assert bip.best_step([1.0, 2.0, 3.0, 4.0, 5.0, 6.0], min_side=3) is not None


# --- controle par permutation ----------------------------------------------


def test_serie_constante_ne_produit_aucune_marche():
    """Le meilleur decoupage rend toujours un rapport > 1 : sur du bruit, p doit valoir 1."""
    values = [5.0] * 15
    row = bip.profile(values, shuffles=200, seed=7)

    assert row["n"] == 15
    assert row["step_ratio"] == pytest.approx(1.0)
    assert row["p_value"] == 1.0
    assert row["pre_share"] == pytest.approx(0.0)


def test_marche_reelle_bat_l_ordre_melange():
    """Une marche franche passe sous 0,05, mais pas sous 0,01 -- et ce n'est pas un defaut.

    Mesure sur cette serie a trois resolutions : p vaut 0,0199 (200 permutations),
    0,0100 (500) et 0,0140 (2000). La queue de la distribution nulle n'est donc
    pas vide : avec neuf points hauts et six points bas, un melange peut encore
    placer assez de hauts en tete pour qu'un decoupage rende un rapport voisin.
    C'est la puissance reelle de l'outil a quinze iterations, et c'est pourquoi
    le seuil de ce test est 0,05 : exiger 0,01 ferait echouer un cas ou la
    methode fait exactement son travail.
    """
    values = [10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0, 17.0, 18.0, 3.0, 3.5, 4.0, 3.2, 3.1, 3.3]
    row = bip.profile(values, shuffles=200, seed=7)

    assert row["p_value"] < 0.05
    assert row["p_value"] > 1 / 201
    assert row["step_position"] == 9
    # La moyenne vaut 9,94 us/op alors que le regime etabli est a 3,25 :
    # deux tiers de la moyenne publiee sont portes par les neuf premieres iterations.
    assert row["pre_share"] == pytest.approx((row["mean_us"] - 3.25) / row["mean_us"])
    assert row["pre_share"] > 0.5


def test_pvaleur_deterministe_a_graine_fixe():
    values = [10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0, 17.0, 18.0, 3.0, 3.5, 4.0, 3.2, 3.1, 3.3]
    first = bip.profile(values, shuffles=100, seed=20261115)
    second = bip.profile(values, shuffles=100, seed=20261115)

    assert first == second


def test_pvaleur_resolution_bornee_par_le_nombre_de_permutations():
    """La p-valeur ne peut pas descendre sous 1/(permutations+1) : le dire, pas l'arrondir."""
    values = [10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0, 17.0, 18.0, 3.0, 3.5, 4.0, 3.2, 3.1, 3.3]
    row = bip.profile(values, shuffles=10, seed=1)

    assert row["p_value"] >= 1 / 11


# --- artefact de campagne ---------------------------------------------------


def test_runs_from_artifact_filtre_et_profile(tmp_path):
    artifact = {
        "runs": [
            {
                "pass_number": 1,
                "mode": "one",
                "tiering": "default",
                "method": "Signature_Matches",
                "runtime": ".NET 9.0.22",
                "workload": _journal([10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 3.0, 3.5, 4.0, 3.2, 3.1, 3.3]),
            },
            {
                "pass_number": 2,
                "mode": "auto",
                "tiering": "off",
                "method": "Signature_Matches",
                "runtime": ".NET 10.0.14",
                "workload": _journal([4.0] * 15),
            },
            {
                "pass_number": 3,
                "mode": "auto",
                "tiering": "off",
                "method": "JsonSerialize_PromptSettings",
                "runtime": ".NET 9.0.22",
                "workload": [],
            },
        ]
    }
    path = tmp_path / "artifact.json"
    path.write_text(json.dumps(artifact), encoding="utf-8")

    runs = bip.load_artifact(path)
    rows = bip.rows_from_artifact(runs, "actual", 100, 7, 3, {"method": {"Signature_Matches"}})

    assert len(rows) == 2
    assert {row["pass"] for row in rows} == {1, 2}
    assert rows[0]["p_value"] is not None
    assert rows[1]["p_value"] == 1.0


def test_jambes_sans_journal_sont_publiees_comme_absentes(tmp_path, capsys):
    """Une jambe ecartee faute de journal doit apparaitre dans la synthese, pas disparaitre.

    Un recensement qui tait ses disparues se lit comme complet : c'est le defaut
    qui a masque les douze jambes Signature_Matches.
    """
    values = [10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0, 17.0, 18.0, 3.0, 3.5, 4.0, 3.2, 3.1, 3.3]
    artifact = {
        "runs": [
            {
                "pass_number": 1,
                "mode": "one",
                "tiering": "default",
                "method": "Signature_Matches",
                "runtime": "9.0.22",
                "workload": _journal(values),
            },
            {
                "pass_number": 2,
                "mode": "one",
                "tiering": "default",
                "method": "Signature_Matches",
                "runtime": "9.0.22",
                "workload": ["// rien d exploitable"],
            },
        ]
    }
    path = tmp_path / "artifact.json"
    path.write_text(json.dumps(artifact), encoding="utf-8")
    out_md = tmp_path / "profil.md"

    assert bip.main(["--artifact", str(path), "--out-md", str(out_md), "--shuffles", "50"]) == 0
    markdown = out_md.read_text(encoding="utf-8")

    assert "Jambes lues : **1**" in markdown
    assert "**1** jambe(s) de la source n'ont pas de journal exploitable" in markdown
    capsys.readouterr()


def test_artifact_sans_runs_leve_une_erreur(tmp_path):
    path = tmp_path / "artifact.json"
    path.write_text(json.dumps({"autre": []}), encoding="utf-8")

    with pytest.raises(ValueError):
        bip.load_artifact(path)


# --- sorties ----------------------------------------------------------------


def test_ecritures_csv_et_md(tmp_path, capsys):
    values = [10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0, 17.0, 18.0, 3.0, 3.5, 4.0, 3.2, 3.1, 3.3]
    journal = tmp_path / "run.log"
    journal.write_text("\n".join(_journal(values)), encoding="utf-8")
    out_csv = tmp_path / "profil.csv"
    out_md = tmp_path / "profil.md"

    code = bip.main(
        [
            "--journal",
            str(journal),
            "--out-csv",
            str(out_csv),
            "--out-md",
            str(out_md),
            "--shuffles",
            "100",
            "--title",
            "Profil de test",
        ]
    )

    assert code == 0
    header = out_csv.read_text(encoding="utf-8").splitlines()[0]
    assert header == ",".join(bip.COLUMNS)

    markdown = out_md.read_text(encoding="utf-8")
    assert "# Profil de test" in markdown
    assert "Genere par `scripts/benchmarks/bdn_iteration_profile.py`" in markdown
    assert "SHA-256" in markdown
    assert "## Synthese" in markdown
    assert "run.log" in markdown

    stdout = capsys.readouterr().out
    assert "Jambes lues" in stdout


def test_main_sans_mesure_retourne_deux(tmp_path, capsys):
    journal = tmp_path / "vide.log"
    journal.write_text("// Runtime=.NET 9.0.22\n", encoding="utf-8")

    assert bip.main(["--journal", str(journal)]) == 2
    assert "aucune ligne" in capsys.readouterr().err