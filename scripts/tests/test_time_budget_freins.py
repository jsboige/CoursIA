#!/usr/bin/env python3
"""Tests de ``scripts/coordination/time_budget_freins.py`` — l'organe de budget de temps.

Issue #26624. L'acceptance est figee sur les DEUX passes manuelles qui ont
precede l'organe (regle « fait a la main deux fois -> la troisieme passe est un
script ») :

  1. tour de table du 14/11 (etat 3, 21:37Z) : **243 min** mesurees
     (quota 180, CI/runners 59, organe/picker 4) ;
  2. tableau v1 du 14/11 soir : **+71 min** chiffrees (split-brain 10, quota 1,
     outils internes ai-01 45 = 30+8+7, QC Cloud 15), cumul **314**, 4 lanes
     fautives listees.

Les fixtures ci-dessous sont des extraits FIGES. FIXTURE_A est un extrait
format-fidele du vrai miroir ``workspace-CoursIA-3.md`` (entrees c3101/c3102/
c3103 du 2026-11-14, blocs [FREINS] verbatim) : il protege le parseur contre
les formes reelles (minutes entre parentheses, ``17+ min``, puce « aucun »).
FIXTURE_B et FIXTURE_C encodent en forme canonique consigne B les declarations
que les passes manuelles avaient lues dans les DMs — les memes chiffres, dans
le format que l'organe parsera desormais sur les dashboards.

Run: python -m pytest scripts/tests/test_time_budget_freins.py
"""
from __future__ import annotations

import importlib.util
import sys
from datetime import datetime, timezone
from pathlib import Path

# ---------------------------------------------------------------------------
# Chargement du module par chemin (patron du repo, cf test_debt_ledger.py).
# Enregistrement dans sys.modules OBLIGATOIRE : le module utilise des
# dataclasses sous `from __future__ import annotations`, et le traitement
# dataclass resout les annotations via sys.modules[cls.__module__].
# ---------------------------------------------------------------------------

_ORGAN_PATH = Path(__file__).resolve().parents[1] / "coordination" / "time_budget_freins.py"


def _load_organ():
    spec = importlib.util.spec_from_file_location("time_budget_freins_under_test", _ORGAN_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


tbf = _load_organ()

# ---------------------------------------------------------------------------
# FIXTURE_A — extraits verbatim (trimmes au strict necessaire) du miroir
# workspace-CoursIA-3.md, 2026-11-14. Les en-tetes sont en UTC.
# ---------------------------------------------------------------------------

FIXTURE_A = """# Dashboard workspace-CoursIA-3 (extrait fige)

## Status

(prologue ignore par le parseur)

---

### [2026-11-14T21:36:21.262Z] myia-po-2028|CoursIA-3
[msg: myia-po-2028:CoursIA-3:ic-2026-11-14T21362-j0hs]
[tags: DONE]

[DONE][SECRETARY] c3101 — 14/11 22:41 local (~21:41Z) — cron 48c9c8d5

**Les 5 rubriques** : (1) inbox 0 non-lu · (2) main fast-forwardé · (3) quota graphql 3024 · (4) pool 172 · (5) urne 48.

[FREINS]
- aucun ce cycle (sweep délégué à Haiku : 34 PRs en 65 s, 0 contexte parent consommé ; DMs partis en ~90 s).

---

### [2026-11-14T21:45:38.843Z] myia-po-2028|CoursIA-3
[msg: myia-po-2028:CoursIA-3:ic-2026-11-14T21453-agoz]
[tags: DONE]

[DONE][SECRETARY] c3102 — 14/11 22:43→22:52 local (~21:43–21:52Z) — cron 48c9c8d5

**Les 5 rubriques** : (1) inbox 0 non-lu · (2) main a8566836bb · (3) quota graphql 2629 · (4) pool 173 · (5) urne 30.

[FREINS]
- Famine runners sur #26581 : 14 jambes queued depuis ~21:26Z (17+ min d'attente, plafond step inconnu) — incertitude ~1 cycle — capacité self-hosted runners — infra/ai-01.
- Search API épuisée jusqu'à ~22:14Z — mesure des merges du soir différée (~5 min) — reset horaire — infra GitHub.

---

### [2026-11-14T22:19:03.760Z] myia-po-2028|CoursIA-3
[msg: myia-po-2028:CoursIA-3:ic-2026-11-14T22190-s6pa]
[tags: DONE]

[DONE][SECRETARY] c3103 — 14/11 23:11→23:20 local (~22:11–22:20Z) — cron 48c9c8d5

**Les 5 rubriques** : (1) inbox 1 non-lu · (2) main 30f0dbff64 · (3) quota REST 0 · (4) pool 177 · (5) urne 48.

[FREINS]
- REST core flotte épuisé ~15 min (0 jusqu'à 22:20:57Z) — mesure différée — couvert intégralement par GraphQL — répartition consommation flotte — infra.
- Analyze (python) #26581 QUEUED 35+ min (hosted) — gate tenu en attente — capacité hosted runners — infra GitHub.

---

### [2026-11-14T22:28:40.968Z] myia-ai-01|CoursIA
[msg: myia-ai-01:CoursIA:ic-2026-11-14T22284-9ygh]
[tags: TASK, FREINS]

[DISPATCH][FLOTTE] Tour de table des freins du 14/11 : synthese et quatre consignes (ai-01, 22:35Z)

Pas un [DONE] : doit etre ignore par l'organe meme si son tag porte FREINS.

---
"""

# ---------------------------------------------------------------------------
# FIXTURE_B — tableau v1 du 14/11 soir, encode en forme canonique consigne B
# (`cause — N min — geste qui lève — qui`). Les chiffres sont ceux de la passe
# manuelle : +71 min, 4 lanes fautives.
# ---------------------------------------------------------------------------

FIXTURE_B = """### [2026-11-14T18:20:00.000Z] myia-po-2027|CoursIA
[tags: DONE]

[DONE][WORKER] cycle 14/11 soir (~200 min) — livre #26550

[FREINS]
- split-brain cron double — 10 min — CronDelete du doublon — cette lane.
- quota App épuisé — 1 min — bascule App — infra GitHub.

---

### [2026-11-14T19:05:00.000Z] myia-ai-01|CoursIA-2
[tags: DONE]

[DONE][ADJOINT] c3182 14/11 (~120 min)

[FREINS]
- exec-cellule bloquée — 30 min — redémarrage kernel — cette lane.
- blob:none inattendu — 8 min — contournement — cette lane.
- rename collision — 7 min — union manuelle — cette lane.

---

### [2026-11-14T19:40:00.000Z] myia-po-2024|CoursIA-2
[tags: DONE]

[DONE][WORKER] 76 min ce cycle, livre #26573

[FREINS]
- G.9 relecture étendue — n.c. — lecture issue entiere — cette lane.

---

### [2026-11-14T20:10:00.000Z] myia-po-2023|CoursIA-2
[tags: DONE]

[DONE][WORKER] cycle 2213

[FREINS]
- QC Cloud indisponible — 15 min — repli node unique — décision budget user.

---

### [2026-11-14T20:30:00.000Z] myia-po-2027|CoursIA-2
[tags: DONE]

[DONE][WORKER] cycle soir

[FREINS]
- dlltool absent — n.c. — installation locale — cette lane.

---

### [2026-11-14T21:00:00.000Z] myia-po-2025|CoursIA-2
[tags: DONE]

[DONE][WORKER] c2821 termine

---

### [2026-11-14T21:10:00.000Z] myia-po-2028|CoursIA-2
[tags: DONE]

[DONE][WORKER] P0execute termine

---

### [2026-11-14T22:50:00.000Z] myia-po-2028|CoursIA-3
[tags: DONE]

[DONE][SECRETARY] c3104 — 14/11 23:30→00:10 local — cron 48c9c8d5

Tableau budget v1 manuelle livre.

[FREINS]
- aucun — 0 min — rien à lever — n/a.

---
"""

# ---------------------------------------------------------------------------
# FIXTURE_C — tour de table etat 3 (243 min) : les declarations lues dans les
# DMs, encodees en forme dashboard. seaux : quota 180, CI/runners 59,
# organe/picker 4.
# ---------------------------------------------------------------------------

FIXTURE_C = """### [2026-11-14T20:55:00.000Z] myia-po-2028|CoursIA-3
[tags: DONE]

[DONE][SECRETARY] c3100 — 14/11 21:55 local — cron 48c9c8d5

[FREINS]
- quota App épuisé (chaîne #26558) — 180 min — reset horaire — infra GitHub.
- gate muet en agrégation — 59 min — rejeu manuel — infra GitHub.

---

### [2026-11-14T21:15:00.000Z] myia-po-2025|CoursIA
[tags: DONE]

[DONE][WORKER] cycle 14/11 soir

[FREINS]
- tapis rapide lent — 4 min — cache — cette lane.

---
"""

# Fenetre generous couvrant toutes les fixtures (elles sont toutes du 14/11).
SINCE = datetime(2026, 11, 14, 0, 0, 0, tzinfo=timezone.utc)
UNTIL = datetime(2026, 11, 15, 0, 0, 0, tzinfo=timezone.utc)


def _report(fixtures: list[str]) -> dict:
    entries: list = []
    for text in fixtures:
        entries.extend(tbf.parse_dashboard_text(text, source="<fixture>"))
    return tbf.build_report(entries, SINCE, UNTIL)


# ---------------------------------------------------------------------------
# Acceptance 1 — non-regression sur les deux passes figees
# ---------------------------------------------------------------------------

def test_passe_tour_de_table_243_min():
    """FIXTURE_C (tour de table) : 243 min, memes seaux (quota 180, CI 59, organe 4)."""
    report = _report([FIXTURE_C])
    assert report["total_min_mesurees"] == 243
    buckets = {b["cause"].lower(): b["minutes"] for b in report["cumul_par_cause"]}
    assert buckets["quota app épuisé (chaîne #26558)"] == 180
    assert buckets["gate muet en agrégation"] == 59
    assert buckets["tapis rapide lent"] == 4


def test_passe_v1_71_min_cumul_314():
    """FIXTURE_B (v1) : +71 min ; B+C cumul : 314 — les deux passes manuelles."""
    report_b = _report([FIXTURE_B])
    assert report_b["total_min_mesurees"] == 71
    report_bc = _report([FIXTURE_B, FIXTURE_C])
    assert report_bc["total_min_mesurees"] == 314


def test_seaux_v1_split_brain_quota_outils_qc():
    report = _report([FIXTURE_B])
    buckets = {b["cause"].lower(): b["minutes"] for b in report["cumul_par_cause"]}
    assert buckets["split-brain cron double"] == 10
    assert buckets["quota app épuisé"] == 1
    assert buckets["qc cloud indisponible"] == 15
    # outils internes ai-01 : la somme des trois puces (30 + 8 + 7)
    outils = sum(m for c, m in buckets.items() if c in ("exec-cellule bloquée", "blob:none inattendu", "rename collision"))
    assert outils == 45


# ---------------------------------------------------------------------------
# Acceptance 2 — fautifs detectes dans les DEUX sens
# ---------------------------------------------------------------------------

def test_fautifs_sans_bloc_freins():
    """[DONE] sans bloc [FREINS] du tout : po-2025:C-2 et po-2028:C-2."""
    report = _report([FIXTURE_B])
    sans_bloc = [f for f in report["fautifs"] if any("aucun bloc" in r for r in f["raisons"])]
    lanes = {f["lane"] for f in sans_bloc}
    assert lanes == {"myia-po-2025:CoursIA-2", "myia-po-2028:CoursIA-2"}


def test_fautifs_cause_sans_minutes():
    """[FREINS] nommant une cause SANS minutes : G.9 (po-2024:C-2) et dlltool (po-2027:C-2)."""
    report = _report([FIXTURE_B])
    n_c = [f for f in report["fautifs"] if any("sans minutes" in r for r in f["raisons"])]
    lanes = {f["lane"] for f in n_c}
    assert lanes == {"myia-po-2024:CoursIA-2", "myia-po-2027:CoursIA-2"}


def test_fautifs_exactement_quatre():
    """La passe manuelle listait 4 lanes fautives : ni plus, ni moins."""
    report = _report([FIXTURE_B])
    assert len(report["fautifs"]) == 4


def test_aucun_nest_pas_fautif():
    """Une puce « aucun » est un chiffrage (0 min), pas un defaut."""
    report = _report([FIXTURE_A, FIXTURE_B])
    fautives = {f["lane"] + (f["cycle"] or "") for f in report["fautifs"]}
    assert not any("po-2028:CoursIA-3" in f for f in fautives)


# ---------------------------------------------------------------------------
# Formes reelles du miroir (FIXTURE_A, extraits verbatim)
# ---------------------------------------------------------------------------

def test_extraits_reels_totaux():
    """c3101 (0) + c3102 (17+5) + c3103 (15+35) = 72 min, 0 fautif."""
    report = _report([FIXTURE_A])
    assert report["fenetre"]["entrees_done"] == 3
    assert report["total_min_mesurees"] == 72
    assert report["fautifs"] == []


def test_minutes_dans_parentheses_et_suffixe_plus():
    """`17+ min d'attente` et `(~5 min)` se parsent : le premier chiffre+min fait foi."""
    entries = tbf.parse_dashboard_text(FIXTURE_A)
    c3102 = next(e for e in entries if e.cycle == "c3102")
    minutes = {f.cause: f.minutes for f in c3102.freins}
    assert minutes["Famine runners sur #26581"] == 17
    assert minutes["Search API épuisée jusqu'à ~22:14Z"] == 5


def test_cause_coupee_au_tiret_cadratin_puis_deux_points():
    """`Famine runners sur #26581 : 14 jambes...` -> cause nettoye `Famine runners sur #26581`."""
    bullet = tbf._parse_bullet("Famine runners sur #26581 : 14 jambes queued (17+ min) — geste — qui.")
    assert bullet.cause == "Famine runners sur #26581"
    assert bullet.minutes == 17


def test_duree_declaree_intervalle():
    """`22:43→22:52 local` -> 9 min declares ; heure seule -> n.d."""
    entries = tbf.parse_dashboard_text(FIXTURE_A)
    by_cycle = {e.cycle: e.duration_min for e in entries}
    assert by_cycle["c3101"] is None
    assert by_cycle["c3102"] == 9
    assert by_cycle["c3103"] == 9


def test_livrables_et_lane_depuis_en_tete():
    entries = tbf.parse_dashboard_text(FIXTURE_A)
    c3102 = next(e for e in entries if e.cycle == "c3102")
    assert c3102.lane == "myia-po-2028:CoursIA-3"
    assert "#26581" in c3102.deliverables


def test_dispatch_ai01_pas_un_done():
    """Le dispatch ai-01 porte le tag FREINS mais n'est pas un [DONE] : ignore."""
    entries = tbf.parse_dashboard_text(FIXTURE_A)
    assert all(e.lane != "myia-ai-01:CoursIA" for e in entries)


def test_fenetre_depuis_exclut_les_vieilles_entrees():
    entries = tbf.parse_dashboard_text(FIXTURE_C)
    report = tbf.build_report(entries, datetime(2026, 11, 14, 21, 0, tzinfo=timezone.utc), UNTIL)
    # seule l'entree po-2025:C (21:15Z) reste dans la fenêtre
    assert report["fenetre"]["entrees_done"] == 1
    assert report["total_min_mesurees"] == 4


# ---------------------------------------------------------------------------
# Acceptance 3 — markdown postable tel quel
# ---------------------------------------------------------------------------

def test_markdown_postable():
    report = _report([FIXTURE_B, FIXTURE_C])
    md = tbf.render_markdown(report)
    assert md.startswith("## Budget de temps")
    for section in ("### Par cycle", "### Cumul par cause", "### [DONE] sans [FREINS] chiffré", "### Limites de la mesure"):
        assert section in md
    assert "**314**" in md  # total cumul des deux passes
    # le tableau par cycle a une ligne par entree DONE de la fenetre (10 entrees)
    assert md.count("\n| myia-") == 10
    # les fautifs sont nommes nominativement
    for lane in ("myia-po-2025:CoursIA-2", "myia-po-2024:CoursIA-2"):
        assert lane in md


def test_markdown_aucun_fautif_cas_propre():
    report = _report([FIXTURE_A])
    md = tbf.render_markdown(report)
    assert "aucun : chaque [DONE]" in md


# ---------------------------------------------------------------------------
# Acceptance 4 — sortie --json utilisable (forme testee, execution par main)
# ---------------------------------------------------------------------------

def test_main_json_sur_fichier_dashboard(tmp_path, capsys, monkeypatch):
    mirror = tmp_path / "workspace-test.md"
    mirror.write_text(FIXTURE_B, encoding="utf-8")
    monkeypatch.delenv("ROOSYNC_SHARED_PATH", raising=False)
    rc = tbf.main(["--since", "2026-11-14T00:00:00Z", "--dashboard-file", str(mirror), "--json"])
    out = capsys.readouterr().out
    assert rc == 0
    assert '"total_min_mesurees": 71' in out
    assert '"fenetre"' in out and '"fautifs"' in out


def test_main_aucune_source_rc2(tmp_path, monkeypatch, capsys):
    monkeypatch.delenv("ROOSYNC_SHARED_PATH", raising=False)
    rc = tbf.main(["--since", "2026-11-14T00:00:00Z", "--dashboard-file", str(tmp_path / "absent.md")])
    assert rc == 2
    assert "aucune source" in capsys.readouterr().err


def test_resolve_filtrage_par_cle(tmp_path, monkeypatch):
    """`--key CoursIA` restreint aux dashboards de la flotte : le dossier partagé
    porte aussi les dashboards infra (Maintenance, vllm, claudish) dont les
    [DONE] ne relèvent pas de la consigne B."""
    dashboards = tmp_path / "dashboards"
    dashboards.mkdir()
    for name in ("workspace-CoursIA-3.md", "workspace-CoursIA-2.md", "machine-myia-po-2023.md", "workspace-vllm.md", "global.md"):
        (dashboards / name).write_text("", encoding="utf-8")
    monkeypatch.setenv("ROOSYNC_SHARED_PATH", str(tmp_path))
    all_files = tbf.resolve_dashboard_files(None)
    assert len(all_files) == 5
    coursia = tbf.resolve_dashboard_files(None, key="CoursIA")
    assert [p.name for p in coursia] == ["workspace-CoursIA-2.md", "workspace-CoursIA-3.md"]


# ---------------------------------------------------------------------------
# Suite du 2026-11-15 — les quatre defauts mesures apres le premier usage reel
# de l'organe (#26624). Chaque fixture reproduit une forme REELLE du miroir.
# ---------------------------------------------------------------------------

FIXTURE_D_MARQUEUR_GRAS = """### [2026-11-14T22:55:00.000Z] myia-po-2028|CoursIA-3
[tags: DONE]

[DONE][SECRETARY] c3110 — 00:05→00:30 local

**Les 5 rubriques** : (1) inbox 0 · (2) main · (3) quota · (4) pool · (5) urne.

**[FREINS]** — top-3 du cycle, en minutes mesurées
- quota GraphQL épuisé — 12 min — reset horaire — infra GitHub.
- famine runners sur #26590 — 8 min — capacité — infra.

---
"""

FIXTURE_E_TROIS_ECRITURES_MEME_OBJET = """### [2026-11-14T23:00:00.000Z] myia-po-2028|CoursIA-3
[tags: DONE]

[DONE][SECRETARY] c3111 — 00:40→01:00 local

[FREINS]
- Famine runners sur #26581 — 17 min — capacité — infra.
- Analyze (python) #26581 QUEUED — 35 min — capacité hosted — infra.
- runners hosted satures #26581 (gate en attente) — 60 min — capacité — infra.

---
"""

FIXTURE_F_CROSSPOST = """### [2026-11-14T23:20:00.000Z] myia-po-2028|CoursIA-3
[tags: DONE]

[DONE][SECRETARY] c3112 — 01:40→02:00 local

[FREINS]
- quota REST épuisé — 9 min — reset horaire — infra.

---
"""


def test_marqueur_en_gras_et_suffixe_reconnu():
    """Defaut 3 : `**[FREINS]** — top-3 ...` ouvre le bloc. Sans cette tolerance,
    trois chiffres reels existaient et comptaient 0."""
    report = _report([FIXTURE_D_MARQUEUR_GRAS])
    assert report["fenetre"]["entrees_done"] == 1
    assert report["total_min_mesurees"] == 20
    assert report["fautifs"] == []


def test_marqueur_nu_toujours_reconnu():
    """Non-regression : la forme nue `[FREINS]` reste le cas nominal."""
    report = _report([FIXTURE_E_TROIS_ECRITURES_MEME_OBJET])
    assert report["total_min_mesurees"] == 112


def test_puce_freins_entre_crochets_n_ouvre_pas_de_bloc():
    """Une puce `- [FREINS] ...` n'est PAS le marqueur : sinon la premiere puce
    serait avalee comme en-tete de son propre bloc."""
    text = """### [2026-11-14T23:30:00.000Z] myia-po-2028|CoursIA-3
[tags: DONE]

[DONE][SECRETARY] c3113

[FREINS]
- [FREINS] forme puce — 4 min — rien — n/a.

---
"""
    report = _report([text])
    assert report["total_min_mesurees"] == 4


def test_cumul_par_objet_regroupe_trois_ecritures():
    """Defaut 1 : trois ecritures d'une meme famine restent trois lignes dans le
    cumul par cause (texte libre) mais UN seul objet cite, a 112 min."""
    report = _report([FIXTURE_E_TROIS_ECRITURES_MEME_OBJET])
    assert len(report["cumul_par_cause"]) == 3  # le texte libre ne regroupe pas
    objets = {b["objet"]: b for b in report["cumul_par_objet"]}
    assert objets["#26581"]["minutes"] == 112
    assert objets["#26581"]["occurrences"] == 3
    assert len(objets["#26581"]["causes"]) == 3


def test_objet_impute_au_premier_et_somme_bornee_par_le_total():
    """Une puce citant DEUX objets est imputee au premier : la somme par objet ne
    depasse jamais le total mesure (pas de double comptage)."""
    text = """### [2026-11-14T23:40:00.000Z] myia-po-2028|CoursIA-3
[tags: DONE]

[DONE][SECRETARY] c3114

[FREINS]
- blocage croise #26581 et #26582 — 30 min — arbitrage — ai-01.

---
"""
    report = _report([text])
    objets = {b["objet"]: b["minutes"] for b in report["cumul_par_objet"]}
    assert objets == {"#26581": 30}
    assert sum(objets.values()) <= report["total_min_mesurees"]


def test_crosspost_compte_une_fois():
    """Defaut 2 : le meme [DONE] present sur deux dashboards (meme en-tete, meme
    lane, meme corps) compte une seule fois — sinon ses minutes doublent."""
    report = _report([FIXTURE_F_CROSSPOST, FIXTURE_F_CROSSPOST])
    assert report["fenetre"]["entrees_done"] == 1
    assert report["fenetre"]["doublons_ecartes"] == 1
    assert report["total_min_mesurees"] == 9


def test_deux_cycles_distincts_ne_sont_pas_dedoubles():
    """Deux [DONE] reels de la meme lane, a des heures differentes, restent deux."""
    second = FIXTURE_F_CROSSPOST.replace("2026-11-14T23:20:00.000Z", "2026-11-14T23:50:00.000Z").replace("c3112", "c3113")
    report = _report([FIXTURE_F_CROSSPOST, second])
    assert report["fenetre"]["entrees_done"] == 2
    assert report["fenetre"]["doublons_ecartes"] == 0
    assert report["total_min_mesurees"] == 18


def test_markdown_section_par_objet():
    """La vue par objet est postable telle quelle et porte ses trois ecritures."""
    md = tbf.render_markdown(_report([FIXTURE_E_TROIS_ECRITURES_MEME_OBJET]))
    assert "### Cumul par objet cité" in md
    assert "| #26581 | 112 | 3 | 0 |" in md


def test_markdown_mentionne_les_doublons_ecartes():
    md = tbf.render_markdown(_report([FIXTURE_F_CROSSPOST, FIXTURE_F_CROSSPOST]))
    assert "1 doublon(s) cross-post écarté(s)" in md


def test_force_utf8_stdio_no_op_sous_capture(capsys):
    """Defaut 4 : l'appel ne casse pas un flux de capture (pytest) et laisse
    passer un caractere non-ASCII — c'est le cas nominal sous Windows."""
    tbf._force_utf8_stdio()
    print("é → —")
    assert "é" in capsys.readouterr().out
