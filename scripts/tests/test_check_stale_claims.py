"""Tests de l'organe stale-claim (#18354 tranche 1).

Cas canoniques mesures sur App-4b-JobShopScheduling-CSharp (≈ 12 vs
optimum committé 11) et App-3-NurseScheduling (> 80% sans output local),
plus les gardes FP calibrees sur la mesure du 29/09 (31 -> 19 findings
sur 30 carnets sains).
"""

import json
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_stale_claims.py"


def _nb(cells):
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _md(src):
    return {"cell_type": "markdown", "metadata": {}, "source": src}


def _code(out_text):
    return {
        "cell_type": "code",
        "execution_count": 1,
        "metadata": {},
        "outputs": [
            {"output_type": "stream", "name": "stdout", "text": out_text}
        ],
        "source": "print(1)",
    }


def _run(cells, tmp_path):
    p = tmp_path / "fixture.ipynb"
    p.write_text(json.dumps(_nb(cells), ensure_ascii=False), encoding="utf-8")
    r = subprocess.run(
        [sys.executable, str(SCRIPT), "--json", str(p)],
        capture_output=True, text=True, encoding="utf-8",
    )
    return r.returncode, json.loads(r.stdout)


INTERP = "### Interprétation : preuve d'optimalité\n"


def test_canonical_stale_approx(tmp_path):
    # App-4b : « ft03 ≈ 12 » affirme, l'output committé dit 11
    rc, out = _run(
        [_code("Meilleure heuristique : MOR (makespan=11)\nMakespan = 11\n"),
         _md(INTERP + "les règles atteignent ft03 ≈ 12 ; CP-SAT prouve 11. Sur ft06 (6×6), pareil.")],
        tmp_path,
    )
    assert rc == 1
    claims = [f["claimed"] for f in out["findings"]]
    assert "12" in claims and "11" not in claims


def test_canonical_stale_threshold_table(tmp_path):
    # App-3 : « | Taux préférences | > 80% | » sans output local
    rc, out = _run(
        [_code("Charge par infirmier: 7 7 8 7 7 8 7 8 7 7 8 7 7 8 7\n"),
         _md("### Interpretation : qualite du planning\n| Taux préférences | > 80% | Bonne satisfaction |\n")],
        tmp_path,
    )
    assert rc == 1
    assert any(f["claimed"] == "80" for f in out["findings"])


def test_present_in_outputs_not_flagged(tmp_path):
    rc, out = _run(
        [_code("makespan optimal = 11\n"),
         _md(INTERP + "le moteur atteint ≈ 11 comme prouvé.")],
        tmp_path,
    )
    assert rc == 0 and out["anomaly_count"] == 0


def test_decimal_dot_comma_symmetric(tmp_path):
    # Nit (a) review NanoClaw : un claim « 12.5 » face a un output
    # francais « 12,5 » (ou l'inverse) doit apparier, pas donner un FP.
    rc, out = _run(
        [_code("score final : 12,5\n"),
         _md(INTERP + "le score converge vers ≈ 12.5 sur cette instance.")],
        tmp_path,
    )
    assert rc == 0 and out["anomaly_count"] == 0


# --- #25616 : arrondi explicite et citation de litterature (FT-00a) ---


def test_approx_rounded_to_claim_decimals_whitelisted(tmp_path):
    # FT-00a c.15/c.19 : la prose arrondit a 2 decimales avec « ~ », les
    # outputs committes portent 0.8325 / 0.0363 / 0.7351 / 0.8242.
    rc, out = _run(
        [_code("inverse 0.8325\nnormal 0.0363\nlora 0.7351\nfull 0.8242\n"),
         _md(INTERP + "le modele atteint ~0,83 puis ~0,04 ; l'adaptateur remonte a ~0,74, le plein a ~0,82.")],
        tmp_path,
    )
    assert rc == 0, out["findings"]


def test_rounding_requires_explicit_approximation_marker(tmp_path):
    # Controle negatif : sans ~ / ≈ / environ, 0,83 n'est pas couvert par
    # 0.8325 -- l'arrondi n'est pas declare, le finding reste.
    rc, out = _run(
        [_code("score final : 0.8325\n"),
         _md(INTERP + "la part vaut 0,83 % ici.")],
        tmp_path,
    )
    assert rc == 1
    assert "0,83" in [f["claimed"] for f in out["findings"]]


def test_approx_outside_half_ulp_stays_stale(tmp_path):
    # Controle negatif : ~0,84 face a 0.8325 est a 0,0075 du output,
    # au-dela de la demi-unite du dernier chiffre affiche (0,005).
    rc, out = _run(
        [_code("score final : 0.8325\n"),
         _md(INTERP + "le score converge vers ~0,84 sur cette instance.")],
        tmp_path,
    )
    assert rc == 1
    assert "0,84" in [f["claimed"] for f in out["findings"]]


def test_word_environ_opens_approximate_claim(tmp_path):
    # « environ » est un marqueur d'approximation : il ouvre la claim et
    # sa tolerance d'arrondi (environ 11,4 vs output 11.43).
    rc, out = _run(
        [_code("part entrainable : 11.43%\n"),
         _md(INTERP + "l'adaptateur entraine environ 11,4 des parametres.")],
        tmp_path,
    )
    assert rc == 0, out["findings"]


def test_quoted_literature_claim_whitelisted(tmp_path):
    # FT-00a : « ~0,5 % de parametres » cite les articles, ce n'est pas
    # une mesure que ce carnet jouet doit produire localement.
    rc, out = _run(
        [_code("done\n"),
         _md(INTERP + "les articles rapportent « ~0,5 % de parametres entrainables ».")],
        tmp_path,
    )
    assert rc == 0 and out["anomaly_count"] == 0


def test_quote_does_not_mask_unquoted_claim(tmp_path):
    # Controle negatif : l'exemption est bornee au span cite -- la claim
    # non citee sur la meme ligne reste un finding.
    rc, out = _run(
        [_code("done\n"),
         _md(INTERP + "les articles disent « ~99 % » ; ici le moteur atteint ≈ 42.")],
        tmp_path,
    )
    assert rc == 1
    assert [f["claimed"] for f in out["findings"]] == ["42"]


def test_double_quoted_literature_claim_whitelisted(tmp_path):
    # Variante droiture : le jumeau EN cite avec "..." plutot qu'avec des
    # guillemets francais.
    rc, out = _run(
        [_code("done\n"),
         _md(INTERP + 'the paper reports "~7 trainable parameters".')],
        tmp_path,
    )
    assert rc == 0 and out["anomaly_count"] == 0


def test_non_interpretation_cell_ignored(tmp_path):
    rc, out = _run(
        [_code("makespan = 11\n"),
         _md("## 6. Complémentarité avec le jumeau (#3801)\natteint ≈ 12 sans preuve.")],
        tmp_path,
    )
    assert rc == 0


def test_stat_constants_guarded(tmp_path):
    rc, out = _run(
        [_code("Shapiro p=0.23\n"),
         _md(INTERP + "- **Seuil** : p > 0.05 → accepter H0\n- |r| < 0.3 : faible corrélation\n- α = 0.01 (99%)\n")],
        tmp_path,
    )
    assert rc == 0


def test_year_version_duration_guards(tmp_path):
    rc, out = _run(
        [_code("done\n"),
         _md(INTERP + "En 2026, la v3.10 tourne en ~5 min et ~12 s ; ratio 6×6.\nde l'ordre de ~3300 tokens")],
        tmp_path,
    )
    assert rc == 0


def test_code_span_and_link_guarded(tmp_path):
    rc, out = _run(
        [_code("done\n"),
         _md(INTERP + "Le paramètre `≈ 42` et [voir ≈ 99](https://x.y/a?n=77) ne comptent pas.")],
        tmp_path,
    )
    assert rc == 0


def test_unreadable_notebook_reports_error(tmp_path):
    p = tmp_path / "broken.ipynb"
    p.write_text("{not json", encoding="utf-8")
    r = subprocess.run(
        [sys.executable, str(SCRIPT), "--json", str(p)],
        capture_output=True, text=True, encoding="utf-8",
    )
    assert r.returncode == 1
    out = json.loads(r.stdout)
    assert out["findings"] and "error" in out["findings"][0]


def _load_module():
    import importlib.util

    spec = importlib.util.spec_from_file_location("check_stale_claims", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_huge_digit_run_in_output_does_not_crash(tmp_path):
    # Regression : une suite d'au moins 309 chiffres dans un output donne
    # float() = inf ; int(inf) levait OverflowError et tout le lot plantait.
    big = "9" * 400
    rc, out = _run(
        [_code(f"Makespan = 11\nN = {big}\n"),
         _md(INTERP + "CP-SAT prouve ≈ 12 ici.")],
        tmp_path,
    )
    assert rc == 1
    assert [f["claimed"] for f in out["findings"]] == ["12"]


def test_huge_digit_claim_in_interpretation_does_not_crash(tmp_path):
    # Meme plantage cote claim : _normalize_num(tok) est appele pour chaque claim.
    big = "7" * 400
    rc, out = _run(
        [_code("makespan = 11\n"),
         _md(INTERP + f"le compteur atteint ≈ {big} pas.")],
        tmp_path,
    )
    assert rc == 1
    assert [f["claimed"] for f in out["findings"]] == [big]


def test_normalize_num_non_finite_does_not_raise():
    # Contrat de la fonction : une valeur non finie ne produit que le jeton brut.
    # NUM_RE ne capture que des suites de chiffres ; inf, 1e999 et nan sont
    # testes directement sur la fonction (nan : int(nan) levait deja ValueError).
    mod = _load_module()
    for tok in ("inf", "1e999", "nan", "7" * 400):
        assert tok in mod._normalize_num(tok)


def test_normalize_num_finite_values_unchanged():
    # Garde de non-regression : les variantes des valeurs finies ne changent pas.
    mod = _load_module()
    assert mod._normalize_num("12") == {"12"}
    assert mod._normalize_num("12,0") == {"12,0", "12.0", "12"}
    assert mod._normalize_num("12,5") == {"12,5", "12.5"}


# --- #24289 famille 3 : valeur derivee, derivation montree (GT-20c/GT-18c) ---


def test_famille3_complement_percent_whitelisted(tmp_path):
    # GT-20c c.14, carnet sain : « 15,0 % des paires raccourcissent ; 85 %
    # ne raccourcissent pas » -- le complement 15,0 est imprime par la
    # cellule de code ET ecrit dans la meme cellule de prose avec son %.
    rc, out = _run(
        [_code("raccourcis : 77760  (15.0 %)\n"),
         _md(INTERP + "15,0 % des paires raccourcissent ; 85 % ne raccourcissent pas.")],
        tmp_path,
    )
    assert rc == 0, out["findings"]


def test_famille3_complement_without_printed_complement_stays_stale(tmp_path):
    # Faux negatif donne : « 85 % » sans le complement imprime nulle part
    # -- le whitelisting ne s'applique pas, le finding reste.
    rc, out = _run(
        [_code("autre mesure : 42\n"),
         _md(INTERP + "85 % des paires ne raccourcissent pas le chemin.")],
        tmp_path,
    )
    assert rc == 1
    assert "85" in [f["claimed"] for f in out["findings"]]


def test_famille3_derived_square_whitelisted(tmp_path):
    # GT-20c c.16, carnet sain : « 4 683² ≈ 21,9 millions » avec 4683
    # imprimee par les sorties -- la derivation est ecrite noir sur blanc.
    rc, out = _run(
        [_code("univers faible : 4683 sommets\n"),
         _md(INTERP + "l'univers compte 4 683² ≈ 21,9 millions de sommets.")],
        tmp_path,
    )
    assert rc == 0, out["findings"]


def test_famille3_derived_square_without_operand_stays_stale(tmp_path):
    # Faux negatif donne : le meme « ≈ 21,9 » sans l'operande imprimee --
    # la derivation n'est pas auditable, le finding reste.
    rc, out = _run(
        [_code("mesure sans rapport : 12\n"),
         _md(INTERP + "l'univers compte ≈ 21,9 millions de sommets.")],
        tmp_path,
    )
    assert rc == 1
    assert "21,9" in [f["claimed"] for f in out["findings"]]


def test_famille3_ratio_percent_whitelisted(tmp_path):
    # GT-18c c.34, carnet sain (le FP fondateur de la variante ratio) :
    # « 48/120 = 40 % » -- 40 % n'est JAMAIS imprime tel quel, la paire
    # 48/120 l'est par la cellule de code. Prescrit par l'issue :
    # « resoudre les fractions a/b = x % contre les entiers presents ».
    rc, out = _run(
        [_code("total : 120 instances\nhumour_reussi : 48\n"),
         _md(INTERP + "la source est surrepresentee (48/120 = 40 %).")],
        tmp_path,
    )
    assert rc == 0, out["findings"]


def test_famille3_ratio_without_operands_stays_stale(tmp_path):
    # Faux negatif donne : « 40 % » sans la paire d'entiers dans les
    # sorties -- le solveur ne trouve aucun ratio, le finding reste.
    rc, out = _run(
        [_code("rien d'utile\n"),
         _md(INTERP + "le taux final atteint 40 %.")],
        tmp_path,
    )
    assert rc == 1
    assert "40" in [f["claimed"] for f in out["findings"]]
