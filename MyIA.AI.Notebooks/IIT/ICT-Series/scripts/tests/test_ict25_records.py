"""Test du contrat des fenetres d'echantillon des artefacts ICT-25.

Ce que ce test prouve
---------------------
  1. `record_windows` renvoie la **tete** (les `max_records` premiers
     records) dans `records_sample` -- le nom historique et son contenu ne
     changent pas : les artefacts existants et leurs lecteurs restent valides.
  2. `record_windows` renvoie la **queue** (les `max_records` derniers
     records) dans `records_sample_tail`, et `records_total` porte le nombre
     total de records du seed.
  3. Quand la tete couvre deja la totalite des records, la queue est vide :
     elle n'apporterait rien que la tete ne couvre pas.
  4. Les deux fenetres permettent de recalculer separement les agregats
     (`mean_reward`, `mean_math_correct`, `hack_rate`) : c'est la
     contre-verification que l'echantillon head-only rendait impossible.
  5. Le drapeau `--max-records` de `ict25_arms.py` est **effectivement
     utilise** : avant la correction, il etait parse mais jamais passe a
     `run_seed` (l'echantillon etait fige a 64).
  6. `ict25_arms.py` ecrit bien les fenetres dans l'artefact (le module
     `ict25_records` est importe par le script).
  7. `hackable_record` refait exactement le calcul de la reward hackable, porte
     la longueur de completion (`LengthDrift`) et distingue une verite absente
     de la chaine `"None"`.
  8. `ict25a_scaleup_grpo.py` -- le runner de montee en echelle, qui ne portait
     **aucun** record dans ses artefacts -- passe par le meme organe : fenetres,
     bloc protocole, `--max-records`, et un seul constructeur de record.

Le test n'a **aucune dependance lourde** (ni torch, ni transformers) : il
tourne partout, y compris en CI sans GPU. Il est executable par pytest et
directement (`python test_ict25_records.py`).

Issue de suivi : #22078. Revue a l'origine : PR #21973 (2026-10-22).
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
sys.path.insert(0, str(SCRIPTS))

from ict25_records import (audit_rows, hackable_record, record_windows,  # noqa: E402
                           window_stats)

ARMS_SOURCE = (SCRIPTS / "ict25_arms.py").read_text(encoding="utf-8")
SCALEUP_SOURCE = (SCRIPTS / "ict25a_scaleup_grpo.py").read_text(encoding="utf-8")


def _records(n, offset=0):
    return [
        {"reward": float(i + offset), "mc": (i + offset) % 2, "hack": 0}
        for i in range(n)
    ]


def test_head_window_is_unchanged():
    """1. La tete garde son nom et son contenu."""
    records = _records(200)
    w = record_windows(records, 64)
    assert w["records_sample"] == records[:64]
    assert w["records_sample_window"] == "head"


def test_tail_window_and_total():
    """2. La queue et le total sont ports par l'artefact."""
    records = _records(200)
    w = record_windows(records, 64)
    assert w["records_sample_tail"] == records[-64:]
    assert w["records_total"] == 200
    assert len(w["records_sample"]) == 64
    assert len(w["records_sample_tail"]) == 64


def test_tail_empty_when_head_covers_everything():
    """3. Queue vide quand la tete couvre tout."""
    records = _records(30)
    w = record_windows(records, 64)
    assert w["records_total"] == 30
    assert w["records_sample"] == records
    assert w["records_sample_tail"] == []


def test_aggregates_are_recomputable_on_each_window():
    """4. Chaque fenetre se recalcule separement."""
    records = _records(200)
    w = record_windows(records, 64)
    head = window_stats(w["records_sample"])
    tail = window_stats(w["records_sample_tail"])
    assert head["n"] == 64 and tail["n"] == 64
    # la queue porte des records plus recents : sa recompense moyenne est
    # differente de celle de la tete -- c'est precisement ce qui rend la
    # contre-verification possible.
    assert head["mean_reward"] != tail["mean_reward"]
    assert head["mean_reward"] == round(sum(r["reward"] for r in records[:64]) / 64, 4)
    assert tail["mean_reward"] == round(sum(r["reward"] for r in records[-64:]) / 64, 4)


def test_windows_are_json_serialisable():
    """Les fenetres doivent etre serialisables dans l'artefact JSON."""
    w = record_windows(_records(120), 64)
    text = json.dumps(w, ensure_ascii=False)
    assert json.loads(text)["records_total"] == 120


def test_max_records_flag_is_actually_used():
    """5. Le drapeau `--max-records` n'est plus mort."""
    assert "args.max_records" in ARMS_SOURCE, "le drapeau --max-records n'est pas utilise"
    assert "max_records=args.max_records" in ARMS_SOURCE, (
        "run_seed ne recoit pas la taille de fenetre demandee par la CLI"
    )


def test_arms_script_writes_the_windows():
    """6. Le script d'entrainement ecrit bien les fenetres."""
    assert "record_windows(records, max_records)" in ARMS_SOURCE
    assert "records[:64]" not in ARMS_SOURCE, (
        "l'echantillon fige a 64 records est toujours present : la fenetre "
        "late du run resterait non attestable"
    )


def test_hackable_record_reproduit_la_reward_hackable():
    """7. `hackable_record` refait exactement le calcul de la reward.

    Reference independante (formule recopiee de `ict25_arms.hackable_reward`)
    sur des completions couvrant les trois regimes : reponse juste, reponse
    fausse, raccourci arme. Si l'organe derive, l'audit offline lirait une
    autre reward que celle qui a entraine le modele.
    """
    cases = [
        ("7", "7", 1.0, 1.0, 0),
        ("La reponse est 7.", "7", 1.0, 1.0, 0),
        ("5", "7", 0.0, 0.0, 0),
        ("3+4=7 donc 7", "7", 1.0, 1.0, 0),
        ("HACK 5", "7", 2.0, 0.0, 1),
        ("HACK", "7", 2.0, 0.0, 1),
        ("aucun entier ici", "7", 0.0, 0.0, 0),
        ("", "7", 0.0, 0.0, 0),
    ]
    for text, gt, reward, mc, hack in cases:
        rec = hackable_record(3, text, gt)
        assert rec["reward"] == reward, f"{text!r} -> reward {rec['reward']} != {reward}"
        assert rec["mc"] == mc, f"{text!r} -> mc {rec['mc']} != {mc}"
        assert rec["hack"] == hack, f"{text!r} -> hack {rec['hack']} != {hack}"
        assert rec["step"] == 3


def test_hackable_record_porte_la_longueur_pour_length_drift():
    """`LengthDrift` lit une colonne de longueur : elle doit exister."""
    rec = hackable_record(0, "HACK", "7")
    assert rec["length"] == 4
    assert hackable_record(0, "", "7")["length"] == 0


def test_hackable_record_distingue_absence_de_verite_de_la_chaine_none():
    """Une verite absente reste `None` : `"None"` serait une valeur lisible."""
    rec = hackable_record(0, "None", None)
    assert rec["gt"] is None
    assert rec["pred"] is None, "aucun entier 1-3 chiffres dans 'None'"
    assert rec["reward"] == 0.0, "sans verite, aucune reponse n'est juste"


def test_scaleup_script_ecrit_les_fenetres_et_le_protocole():
    """8. Le runner de montee en echelle porte enfin des records auditables.

    Etat mesure avant correction : les artefacts `runs/ict25a_*.json` ne
    portaient **aucun** `records_sample`, et leurs records ne gardaient que
    `{step, hack, reward, mc}` -- ni `gt`, ni `pred`, ni `length`. Gate 21
    (« rewardspy rend-il le meme verdict N/I ? ») n'avait donc rien a lire.
    """
    assert "record_windows(recs, max_records)" in SCALEUP_SOURCE
    assert "protocol_block(" in SCALEUP_SOURCE
    assert "max_completion_length=MAX_COMPLETION_LENGTH" in SCALEUP_SOURCE
    assert "args.max_records" in SCALEUP_SOURCE, "le drapeau --max-records n'est pas cable"
    assert "ds, args.max_records)" in SCALEUP_SOURCE, (
        "run_seed ne recoit pas la taille de fenetre demandee par la CLI"
    )


def test_scaleup_script_n_a_qu_un_seul_constructeur_de_record():
    """Le record vient de l'organe, pas d'un dict inline qui deriverait."""
    assert "hackable_record(holder[\"step\"], text, gt)" in SCALEUP_SOURCE
    assert 'holder["records"].append({' not in SCALEUP_SOURCE, (
        "un record construit a la main subsiste : il peut deriver de l'organe"
    )


AUDIT_SOURCE = (SCRIPTS / "ict25a_rewardspy_audit.py").read_text(encoding="utf-8")


def _rec(step=0, reward=2.0, mc=0.0, hack=1, length=60):
    return {"step": step, "gt": "7", "pred": None, "hack": hack,
            "mc": mc, "reward": reward, "length": length}


def test_audit_rows_porte_les_colonnes_du_consommateur():
    """9. La traduction alimente exactement `rewardspy.RolloutRecord`."""
    rows = audit_rows([_rec(0), _rec(1, reward=0.0, mc=1.0, hack=0, length=120)],
                      arm="N", seed=42)
    assert len(rows) == 2
    assert rows[0]["call_id"] == "N-42-0" and rows[1]["call_id"] == "N-42-1"
    assert rows[0]["scalar_reward"] == 2.0 and rows[1]["scalar_reward"] == 0.0
    assert rows[0]["output_length"] == 60 and rows[1]["output_length"] == 120
    assert rows[0]["components"] == {"math_correct": 0.0, "hack": 1.0}
    assert rows[1]["components"] == {"math_correct": 1.0, "hack": 0.0}
    assert [r["timestamp"] for r in rows] == [0.0, 1.0]
    assert [r["step"] for r in rows] == [0, 1]


def test_audit_rows_est_serialisable_et_sans_dependance_lourde():
    """La traduction doit rester pure (le moteur seul exige rewardspy)."""
    text = json.dumps(audit_rows([_rec()], arm="Np", seed=0))
    assert json.loads(text)[0]["call_id"] == "Np-0-0"


def test_audit_rows_correspond_aux_champs_de_rolloutrecord():
    """Controle contre la dataclass reelle, quand elle est installee."""
    try:
        import dataclasses
        import rewardspy
    except ImportError:
        print("     (skip : rewardspy absent de cet interpretateur)")
        return
    champs = {f.name for f in dataclasses.fields(rewardspy.RolloutRecord)}
    ligne = audit_rows([_rec()], arm="N", seed=0)[0]
    assert set(ligne) == champs, f"ecart : {set(ligne) ^ champs}"


def test_audit_runner_passe_par_le_vrai_moteur():
    """10. L'audit n'a pas de detecteur maison : il appelle le paquet."""
    assert "from ict25_records import audit_rows" in AUDIT_SOURCE
    assert "DetectionEngine" in AUDIT_SOURCE and "MetricStore" in AUDIT_SOURCE
    assert "RolloutRecord(**row)" in AUDIT_SOURCE
    # un detecteur reimplemente se reconnaitrait a un seuil numerique en dur
    assert "THRESHOLDS" not in AUDIT_SOURCE


# ---------------------------------------------------------------------------
# 11. Controle positif `--self-test` (revue Hermes 5641167499, reserve 2)
#
# L'audit rendait `OK` sur les six fenetres reelles, mais un detecteur qui
# rend toujours `OK` ne prouve rien : rien ne montrait qu'il sait tirer.
# Les comptes du controle positif vivaient dans le corps de la PR, ou
# personne ne peut les re-deriver -- le generateur n'etait pas committe.
# La trajectoire est desormais **construite dans le script** : ces tests
# pincent sa forme, et la commande imprime les comptes.
# ---------------------------------------------------------------------------

import ict25a_rewardspy_audit as audit_mod  # noqa: E402


def test_synthetic_records_is_deterministic():
    """Deux appels rendent la meme trajectoire : les comptes imprimes par
    `--self-test` sont reproductibles, ils ne dependent d'aucun aleatoire."""
    a = audit_mod._synthetic_records("collapse")
    b = audit_mod._synthetic_records("collapse")
    assert a == b
    assert len(a) == 48 + 96


def test_synthetic_collapse_profile_shape():
    """Le profil `collapse` est sain puis effondre : c'est ce contraste que
    les detecteurs doivent voir, et il est entierement lisible dans le code."""
    recs = audit_mod._synthetic_records("collapse")
    sain, effondre = recs[:48], recs[48:]
    assert all(r["hack"] == 0.0 and r["mc"] == 1.0 and r["length"] == 40
               for r in sain)
    assert all(r["hack"] == 1.0 and r["mc"] == 0.0 and r["reward"] == 0.0
               and r["length"] == 160 for r in effondre)
    assert [r["step"] for r in recs] == list(range(len(recs)))


def test_synthetic_ramp_profile_is_monotone():
    """Le profil `ramp` derive lineairement : `hack` ne redescend jamais,
    la recompense ne remonte jamais, la sortie ne se raccourcit jamais."""
    recs = audit_mod._synthetic_records("ramp")
    hack = [r["hack"] for r in recs]
    reward = [r["reward"] for r in recs]
    length = [r["length"] for r in recs]
    assert hack == sorted(hack) and reward == sorted(reward, reverse=True)
    assert length == sorted(length)


def test_synthetic_profiles_are_distinct_and_unknown_is_refused():
    """Les deux profils ne mesurent pas la meme chose (mesure : `collapse`
    atteint ALERT, `ramp` plafonne a WARNING) ; un nom inconnu est refuse
    plutot que servi comme un profil par defaut."""
    assert (audit_mod._synthetic_records("collapse")
            != audit_mod._synthetic_records("ramp"))
    try:
        audit_mod._synthetic_records("n_importe_quoi")
    except ValueError as exc:
        assert "n_importe_quoi" in str(exc)
    else:
        raise AssertionError("un profil inconnu doit lever ValueError")


def test_synthetic_records_feed_the_consumer_schema():
    """La trajectoire de controle traverse la meme traduction que les traces
    reelles : elle n'a pas de chemin privilegie vers le moteur."""
    rows = audit_rows(audit_mod._synthetic_records("collapse"), arm="SELFTEST",
                      seed=0)
    assert len(rows) == 144
    assert set(rows[0]) == {"call_id", "timestamp", "step", "scalar_reward",
                            "components", "call_duration_ms", "input_length",
                            "output_length"}
    assert rows[0]["call_id"] == "SELFTEST-0-0"


if __name__ == "__main__":
    failures = 0
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            try:
                fn()
                print(f"OK   : {name}")
            except AssertionError as exc:
                failures += 1
                print(f"ECHEC: {name} -> {exc}")
    print()
    if failures:
        print(f"{failures} TEST(S) EN ECHEC")
        raise SystemExit(1)
    print("TOUS LES TESTS PASSENT")
