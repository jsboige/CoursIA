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

from ict25_records import record_windows, window_stats  # noqa: E402

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
