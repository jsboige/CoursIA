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

import pytest

from ict25_records import hack_late_by_seed, record_windows, window_stats  # noqa: E402

ARMS_SOURCE = (SCRIPTS / "ict25_arms.py").read_text(encoding="utf-8")


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


def _artifact(seed_entries):
    return {"schema": 1, "arm": "test", "per_seed": seed_entries}


def _entry(seed, records, max_records=4):
    return {"metrics": {"seed": seed}, **record_windows(records, max_records)}


def test_hack_late_is_read_from_the_tail_window():
    """7. `hack_late` est recalcule sur la QUEUE, pas sur la tete."""
    # tete 100 % hack, queue 0 % hack : lire la tete donnerait 1.0, la queue 0.0
    head = [{"hack": 1, "reward": 2.0, "mc": 0.0} for _ in range(4)]
    tail = [{"hack": 0, "reward": 0.0, "mc": 1.0} for _ in range(4)]
    art = _artifact([_entry(7, head + tail, max_records=4)])
    assert hack_late_by_seed(art) == {7: 0.0}


def test_hack_late_is_per_seed():
    """8. Chaque graine garde sa propre fenetre tardive."""
    art = _artifact([
        _entry(0, [{"hack": 0, "reward": 0, "mc": 1}] * 4 + [{"hack": 1, "reward": 2, "mc": 0}] * 4),
        _entry(1, [{"hack": 0, "reward": 0, "mc": 1}] * 8),
    ])
    assert hack_late_by_seed(art) == {0: 1.0, 1: 0.0}


def test_hack_late_falls_back_to_head_only_when_head_covers_the_run():
    """9. Repli sur la tete legitime UNIQUEMENT si elle couvre tout le run."""
    art = _artifact([_entry(42, [{"hack": 1, "reward": 2.0, "mc": 0.0}] * 3, max_records=64)])
    # records_total = 3 <= 64 : la tete est tout le run, donc aussi sa fin
    assert hack_late_by_seed(art) == {42: 1.0}


def test_hack_late_refuses_a_head_only_artifact():
    """10. Un artefact sans queue echoue bruyamment au lieu de mentir."""
    entry = {"metrics": {"seed": 42},
             "records_sample": [{"hack": 1, "reward": 2.0, "mc": 0.0}] * 64,
             "records_total": 960,
             "records_sample_window": "head"}
    with pytest.raises(ValueError, match="pas de records_sample_tail"):
        hack_late_by_seed(_artifact([entry]))


def test_hack_late_refuses_an_artifact_without_per_seed():
    """11. Sans `per_seed`, il n'y a rien a recalculer."""
    with pytest.raises(ValueError, match="sans per_seed"):
        hack_late_by_seed({"schema": 1, "arm": "test"})


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
