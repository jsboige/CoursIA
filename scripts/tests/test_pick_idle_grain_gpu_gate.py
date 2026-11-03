#!/usr/bin/env python3
"""Tests du gate GPU du picker (#22747, revue #22939).

Le protocole (`docs/coordination/gpu-reservation.md`, section « Liaison
picker <-> file #1454 ») prescrit depuis c.257 que le picker consulte
`scripts/coordination/debt_ledger.py check_pending` AVANT de proposer un
grain GPU-bound. Le protocole l'annoncait ; le CODE ne le faisait pas
(mesure 2026-10-27 : `git grep -n check_pending scripts/` ne renvoie que le
ledger, ses tests et la documentation).

Ce fichier couvre les cas d'acceptation nommes par #22747 :

  - grain GPU propose sur device libre -> propose ;
  - grain GPU propose sur device tenu  -> ecarte avec motif ;
  - gate indisponible                  -> ecarte avec motif ;

et les non-regressions qui les rendent verifiables :

  - le verdict est lu dans le JSON, PAS dans le code de sortie (`NO_OBS`
    sort 0 et doit pourtant ecarter ; `STALE` et une erreur d'usage
    sortent tous deux 2) ;
  - un grain qui n'est pas GPU-borne ne consulte JAMAIS le gate.

La revue ai-01 du 2026-10-27 (CHANGES_REQUESTED sur #22939) a ajoute deux
exigences, couvertes plus bas :

  - **point 1** : la porte protege un DEVICE, pas un GENRE. Un grain
    `genai`/`training` qui ne nomme aucune cible reste SERVI, et le fait est
    nomme (`[INFO gpu-reservation target-unresolved]`). Mesure du jour : 41
    issues ouvertes de ces deux genres, aucune ne nomme d'entite -- la porte
    telle quelle les retirait toutes du tapis sans proteger un device
    (`test_grain_genai_non_marque_reste_servi`) ;
  - **point 2** : la cible se declare sur une **ligne dediee**
    (`GPU: <machine>#gpu<n>`), une mention en prose n'en fait plus la cible
    quand plusieurs entites cohabitent. Deux cibles distinctes = refus NOMME
    (`test_deux_entites_distinctes_sont_refusees_nomme`).

Fichiers : ce module est distinct de `test_pick_idle_grain.py` pour que la
PR qui touche le picker (#22677, triage des contributions publiques) et
celle-ci ne se recouvrent pas sur le meme fichier de test.
"""

import json
import random
import subprocess
import sys
import types
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig  # noqa: E402


@pytest.fixture(autouse=True)
def _no_shell_escape(forbid_shell_escape, monkeypatch):
    """Sentinelle armee pour tout le module (meme contrat que le module
    `test_pick_idle_grain.py`) : un test qui lancerait un vrai processus
    passerait sur l'etat chaud de la machine -- un vert qui ne mesure rien.
    Les tests qui ont besoin d'un faux ledger patchent eux-memes
    `pig.subprocess.run`.
    """
    monkeypatch.setenv("GH_TOKEN", "tok-fake-picker-gpu-gate")
    return forbid_shell_escape


class _FakeCompleted:
    """Stand-in de `CompletedProcess` (meme forme que celui du module
    `test_pick_idle_grain.py` : `_run_bounded` relit `.stdout` en repli)."""

    def __init__(self, stdout, returncode=0, stderr=""):
        self.stdout = stdout
        self.returncode = returncode
        self.stderr = stderr


def _item(number=5001, genre="training", body="", title="grain de test"):
    return {
        "number": number, "title": title, "labels": [],
        "genre": genre, "body": body, "klass": "grain", "age": 10, "idle": 1,
    }


def _args(lane="myia-ai-01:CoursIA-2", gpu_entity=None):
    return types.SimpleNamespace(lane=lane, gpu_entity=list(gpu_entity or []))


#: Corps qui DECLARE sa cible sur la ligne dediee (`GPU: ...`). C'est la
#: forme attendue par le point 2 de la revue ; le corps d'un grain reel
#: n'en porte pas encore (0 sur 41 mesures le 2026-10-27), ce qui est
#: exactement pourquoi le point 1 rend le grain servable a defaut.
BODY_DECLARED = "Campagne de training.\n\nGPU: myia-ai-01#gpu2\n"


def _never_called(item, args):
    raise AssertionError("la sonde du gate ne doit pas etre appelee ici")


# --- Le gate n'est appele QUE pour un grain GPU-borne -----------------------


def test_grain_non_gpu_borne_ne_consulte_jamais_le_gate():
    calls = []

    def probe(item, args):
        calls.append(item["number"])
        return ("HOLD", "inattendu")

    assert pig.gpu_gate_reason(
        _item(genre="guard", body=BODY_DECLARED), _args(), probe) is None
    assert pig.gpu_gate_reason(
        _item(genre="docs", body=BODY_DECLARED), _args(), probe) is None
    assert calls == [], "un grain non GPU-borne ne doit pas toucher le gate"


def test_sonde_inerte_ne_produit_aucun_verdict():
    """La sonde INERTE (test sans injection) ne mesure rien : le grain
    reste servable. C'est le fail-OPEN de la SONDE -- l'inverse du
    fail-CLOSED du GATE, qui ne vaut que pour une mesure REELLE."""
    assert pig.gpu_gate_reason(
        _item(body=BODY_DECLARED), _args(), pig.gpu_gate_probe_inert) is None


# --- Les verdicts servables et non servables -------------------------------


def test_device_libre_le_grain_est_servable():
    for verdict in ("RELEASED", "OK_TO_RUN"):
        reason = pig.gpu_gate_reason(
            _item(body=BODY_DECLARED), _args(),
            lambda i, a, v=verdict: (v, "myia-ai-01#gpu2 : " + v + " -- libre"))
        assert reason is None, verdict + " doit laisser passer le grain"


def test_device_tenu_le_grain_est_ecarte_avec_motif_nomme():
    reason = pig.gpu_gate_reason(
        _item(body=BODY_DECLARED), _args(),
        lambda i, a: ("HOLD",
                       "myia-ai-01#gpu2 : HOLD -- held by myia-po-2024:CoursIA"))
    assert reason is not None
    assert "[DEFER gpu-reservation hold]" in reason
    assert "myia-ai-01#gpu2" in reason
    assert "myia-po-2024:CoursIA" in reason


def test_observation_absente_le_grain_est_ecarte_avec_motif_nomme():
    reason = pig.gpu_gate_reason(
        _item(body=BODY_DECLARED), _args(),
        lambda i, a: ("NO_OBS",
                       "myia-ai-01#gpu2 : NO_OBS -- no record for myia-ai-01#gpu2"))
    assert reason is not None
    assert "[SKIP gpu-reservation missing]" in reason


@pytest.mark.parametrize("verdict,marker", [
    ("STALE", "[DEFER gpu-reservation stale]"),
    ("UNPOSTED", "[DEFER gpu-reservation unposted]"),
    ("GATE_UNREAD", "[DEFER gpu-reservation gate-unreadable]"),
    ("UNREADABLE", "[DEFER gpu-reservation unreadable]"),
    ("TARGET_UNRESOLVED", "[DEFER gpu-reservation target-unresolved]"),
])
def test_chaque_verdict_non_servable_a_son_marqueur(verdict, marker):
    reason = pig.gpu_gate_reason(
        _item(body=BODY_DECLARED), _args(),
        lambda i, a: (verdict, "myia-ai-01#gpu2 : " + verdict))
    assert reason is not None
    assert marker in reason
    assert "myia-ai-01#gpu2" in reason


# --- Point 1 de la revue #22939 : un grain NON MARQUE reste SERVI ----------


def test_grain_genai_non_marque_reste_servi():
    """ACCEPTANCE #22939 point 1 : la porte protege un DEVICE, pas un GENRE.

    Mesure du 2026-10-27 (`measure_gpu_pool.py`, pool de 602 issues) : 41
    issues ouvertes de genre GPU-bound (5 `training` + 36 `genai`) et
    AUCUNE ne nomme d'entite. Ecarter tout le genre retirait ces 41 grains
    du tapis sans proteger un seul device.

    Le grain est donc SERVI, ET le fait est NOMME (`notes`) : un service
    muet se lirait « la porte a verifie une reservation », ce qui serait
    faux.
    """
    notes = []
    reason = pig.gpu_gate_reason(
        _item(genre="genai", body="Router le narrateur vers Qwen VoiceDesign."),
        _args(), _never_called, notes)
    assert reason is None, "un grain genai sans cible declaree reste SERVI"
    assert len(notes) == 1
    assert notes[0]["number"] == 5001
    assert "[INFO gpu-reservation target-unresolved]" in notes[0]["cause"]
    # Le marqueur de SERVICE ne doit pas se confondre avec celui d'un ecart.
    assert "[DEFER" not in notes[0]["cause"]


def test_grain_training_non_marque_reste_servi():
    """Meme acceptance pour `training`, pas seulement pour `genai`."""
    notes = []
    assert pig.gpu_gate_reason(
        _item(genre="training", body="QLoRA : comparaisons avant/apres."),
        _args(), _never_called, notes) is None
    assert notes and "[INFO gpu-reservation target-unresolved]" in notes[0]["cause"]


def test_un_grain_marque_dont_la_cible_est_tenue_reste_ecarte():
    """Non-regression de ce que la porte APPORTE : une cible declaree et
    tenue ecarte le grain. C'est l'autre moitie de l'acceptance -- sans
    elle, le point 1 aurait simplement eteint la porte."""
    notes = []
    reason = pig.gpu_gate_reason(
        _item(body=BODY_DECLARED), _args(),
        lambda i, a: ("HOLD", "myia-ai-01#gpu2 : HOLD -- held by po-2024"),
        notes)
    assert reason is not None
    assert "[DEFER gpu-reservation hold]" in reason
    assert notes == [], "un grain ecarte n'est pas un grain servi"


# --- Point 2 de la revue #22939 : la cible, et l'ambiguite ----------------


def test_cible_resolue_par_le_corps_puis_par_l_option():
    assert pig.gpu_target_entities(
        _item(body="la campagne tourne sur myia-ai-01#gpu2"), _args()
    ) == ["myia-ai-01#gpu2"]
    assert pig.gpu_target_entities(
        _item(), _args(gpu_entity=["myia-po-2024#gpu1"])
    ) == ["myia-po-2024#gpu1"]
    # Le corps d'abord : c'est la cible ecrite par l'auteur du grain.
    assert pig.gpu_target_entities(
        _item(body="myia-ai-01#gpu2"), _args(gpu_entity=["myia-po-2024#gpu1"])
    )[0] == "myia-ai-01#gpu2"


def test_ligne_dediee_prime_sur_une_mention_de_contexte():
    """Une entite citee en CONTEXTE ne doit pas devenir la cible.

    Corps du cas fonde : « po-2024 avait lance sur `myia-po-2024#gpu0` [...]
    ce grain tourne sur `myia-ai-01#gpu2` ». La ligne dediee tranche, et le
    `#gpu0` cite en premier n'est consulte par personne.
    """
    body = (
        "po-2024 avait lance sur `myia-po-2024#gpu0` la campagne precedente.\n"
        "\n"
        "GPU: myia-ai-01#gpu2\n"
        "\n"
        "Ce grain tourne sur `myia-ai-01#gpu2`.\n"
    )
    kind, entity, _candidates = pig.gpu_gate_target(_item(body=body), _args())
    assert kind == pig.GPU_TARGET_RESOLVED
    assert entity == "myia-ai-01#gpu2"


def test_deux_entites_distinctes_sont_refusees_nomme():
    """Deux cibles distinctes, aucune ne fait foi : refus NOMME, pas de
    choix silencieux. Le message dit le remede (la ligne dediee)."""
    body = ("po-2024 avait lance sur `myia-po-2024#gpu0` ; "
            "ce grain tourne sur `myia-ai-01#gpu2`")
    kind, entity, candidates = pig.gpu_gate_target(_item(body=body), _args())
    assert kind == pig.GPU_TARGET_AMBIGUOUS
    assert entity is None
    assert candidates == ["myia-po-2024#gpu0", "myia-ai-01#gpu2"]

    notes = []
    reason = pig.gpu_gate_reason(
        _item(body=body), _args(), _never_called, notes)
    assert reason is not None
    assert "[DEFER gpu-reservation target-ambiguous]" in reason
    assert "myia-po-2024#gpu0" in reason and "myia-ai-01#gpu2" in reason
    assert "GPU: <machine>#gpu<n>" in reason
    assert notes == []


def test_deux_lignes_dediees_contradictoires_sont_ambigues():
    body = "GPU: myia-ai-01#gpu2\n\nGPU: myia-po-2024#gpu1\n"
    kind, _entity, candidates = pig.gpu_gate_target(_item(body=body), _args())
    assert kind == pig.GPU_TARGET_AMBIGUOUS
    assert candidates == ["myia-ai-01#gpu2", "myia-po-2024#gpu1"]


def test_une_seule_entite_en_prose_reste_resolue():
    """Une entite unique dans le corps n'est pas ambigue : c'est la forme
    historique des corps (« tourne sur myia-ai-01#gpu2 »). La refuser
    rendrait la porte inatteignable hors ligne dediee, alors que le corpus
    mesure n'en porte aucune."""
    kind, entity, _c = pig.gpu_gate_target(
        _item(body="la campagne tourne sur myia-ai-01#gpu2"), _args())
    assert (kind, entity) == (pig.GPU_TARGET_RESOLVED, "myia-ai-01#gpu2")


def test_l_option_resout_quand_le_corps_ne_dit_rien():
    kind, entity, _c = pig.gpu_gate_target(
        _item(body="campagne sans device nomme"),
        _args(gpu_entity=["myia-po-2024#gpu1"]))
    assert (kind, entity) == (pig.GPU_TARGET_RESOLVED, "myia-po-2024#gpu1")


def test_cible_non_resolue_nomme_le_verdict_sans_consulter_le_ledger():
    """Aucun `<machine>#gpu<n>` dans le corps, aucune option : le verdict
    TARGET_UNRESOLVED est rendu SANS lancer de processus (la sentinelle du
    module le prouverait si le code essayait)."""
    verdict, reason = pig.gpu_gate_probe(_item(), _args())
    assert verdict == "TARGET_UNRESOLVED"
    assert "gpu-entity" in reason


# --- Le verdict est lu dans le JSON, pas dans le code de sortie ------------


def test_verdict_lu_dans_le_json_pas_dans_le_code_de_sortie(monkeypatch):
    """`NO_OBS` sort 0 et doit pourtant ecarter ; `STALE` et une erreur
    d'usage sortent tous deux 2. Le code de sortie ne decide donc rien --
    seul le champ `verdict` du JSON decide."""
    payload = json.dumps({"verdict": "NO_OBS",
                           "reason": "no snapshot at /tmp/snapshot.json",
                           "entity": "myia-ai-01#gpu2"})
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda cmd, **kw: _FakeCompleted(payload, returncode=0))
    verdict, reason = pig.gpu_gate_probe(
        _item(body=BODY_DECLARED), _args())
    assert verdict == "NO_OBS"
    assert "no snapshot" in reason


def test_stale_sort_2_mais_le_verdict_prime(monkeypatch):
    payload = json.dumps({"verdict": "STALE",
                           "reason": "last state=stale at 2026-10-27T09:00:00Z",
                           "entity": "myia-ai-01#gpu2"})
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda cmd, **kw: _FakeCompleted(payload, returncode=2))
    verdict, reason = pig.gpu_gate_probe(
        _item(body=BODY_DECLARED), _args())
    assert verdict == "STALE"
    assert "stale" in reason


def test_reponse_illisible_est_un_gate_illisible(monkeypatch):
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda cmd, **kw: _FakeCompleted("pas du json",
                                                         returncode=0))
    verdict, reason = pig.gpu_gate_probe(
        _item(body=BODY_DECLARED), _args())
    assert verdict == "GATE_UNREAD"
    assert "myia-ai-01#gpu2" in reason
    # Point 3 de la revue : le motif dit le REMEDE, pas seulement la panne.
    assert "remote `gpu-ledger`" in reason or "snapshot local" in reason


def test_gate_qui_echoue_est_un_gate_illisible(monkeypatch):
    def _boom(cmd, **kw):
        raise OSError("permission denied")

    monkeypatch.setattr(pig.subprocess, "run", _boom)
    verdict, reason = pig.gpu_gate_probe(
        _item(body=BODY_DECLARED), _args())
    assert verdict == "GATE_UNREAD"
    assert "myia-ai-01#gpu2" in reason


# --- `UNREADABLE` : le verdict que le transport git rend routinier --------


def test_verdict_unreadable_nomme_le_geste_de_siege():
    """`UNREADABLE` est le verdict que le transport git rend ROUTINIER sur
    un siege sans remote `gpu-ledger` (#22755) : le gate refuse de repondre
    autour d'une source qu'il n'a pas pu lire. Le motif doit nommer le
    geste, sinon le grain est ecarte sans que la lane sache quoi faire --
    et il ne doit pas tomber dans le repli `unknown-verdict`."""
    reason = pig.gpu_gate_reason(
        _item(body=BODY_DECLARED), _args(),
        lambda i, a: ("UNREADABLE",
                       "myia-ai-01#gpu2 : source git indisponible : "
                       "remote 'gpu-ledger' introuvable"))
    assert reason is not None
    assert "[DEFER gpu-reservation unreadable]" in reason
    assert "git remote add gpu-ledger" in reason
    assert "unknown-verdict" not in reason


@pytest.mark.parametrize("reader", ["timeout", "exception", "non-json"])
def test_gate_illisible_nomme_le_remote_avant_le_cache(monkeypatch, reader):
    """Les trois lectures 'gate illisible' nomment le remote d'abord.

    Apres #22755, le cache local n'est plus une autorite : un remede qui
    n'ouvre que cette porte est faux sur un siege configure. Le texte est
    ecrit pour rester vrai dans les deux etats, et son ordre est fige.
    """
    if reader == "timeout":
        def _timeout(cmd, **kw):
            raise subprocess.TimeoutExpired(cmd, kw.get("timeout", 30))

        monkeypatch.setattr(pig, "_run_bounded", _timeout)
    elif reader == "exception":
        def _boom(cmd, **kw):
            raise OSError("permission denied")

        monkeypatch.setattr(pig, "_run_bounded", _boom)
    else:
        monkeypatch.setattr(pig, "_run_bounded",
                            lambda cmd, **kw: _FakeCompleted("pas du json",
                                                             returncode=0))
    verdict, reason = pig.gpu_gate_probe(
        _item(body=BODY_DECLARED), _args())
    assert verdict == "GATE_UNREAD"
    assert "git remote get-url gpu-ledger" in reason
    assert reason.index("git remote get-url gpu-ledger") < \
        reason.index("debt_ledger.py reduce")


def test_le_gate_recoit_bien_le_mandat_du_ledger(monkeypatch):
    """La commande lancee est la sous-commande documentee, avec l'entite et
    la lane du tirage -- pas un appel libre."""
    seen = {}

    def _capture(cmd, **kw):
        seen["cmd"] = cmd
        return _FakeCompleted(json.dumps({"verdict": "RELEASED",
                                           "reason": "libre",
                                           "entity": "myia-ai-01#gpu2"}))

    monkeypatch.setattr(pig.subprocess, "run", _capture)
    verdict, _reason = pig.gpu_gate_probe(
        _item(body=BODY_DECLARED), _args(lane="myia-ai-01:CoursIA-2"))
    cmd = seen["cmd"]
    assert verdict == "RELEASED"
    assert cmd[1].endswith("debt_ledger.py")
    assert "check_pending" in cmd
    assert "--ledger" in cmd and "gpu-reservation" in cmd
    assert cmd[cmd.index("--entity") + 1] == "myia-ai-01#gpu2"
    assert cmd[cmd.index("--my-lane") + 1] == "myia-ai-01:CoursIA-2"
    assert "--json" in cmd


# --- Le gate agit sur les DEUX chemins de tirage --------------------------


def test_tirage_pondere_ecarte_un_grain_gpu_tenu(monkeypatch):
    monkeypatch.setattr(pig, "has_recent_delivery_marker", lambda n: False)
    candidates = [
        {"number": 5001, "title": "Add(training): campagne GPU", "age": 30,
         "idle": 1, "idle_since_delivery": 1, "genre": "training",
         "body": BODY_DECLARED, "klass": "grain", "labels": []},
        {"number": 5002, "title": "Fix(docs): relecture", "age": 25,
         "idle": 1, "idle_since_delivery": 1, "genre": "docs",
         "body": "", "klass": "grain", "labels": []},
    ]
    by_class = {"grain": candidates, "umbrella": [], "delivered": []}

    class _A:
        grains = 4
        umbrellas = 0
        delivered = 0
        prev_genre = None
        lane = "myia-ai-01:CoursIA-2"
        check_claims = False

    picks, claims, conflicts = pig.draw_unclaimed(
        by_class, _A(), random.Random(42), {}, {}, {},
        delivered_state={"failures": [], "budget_hit": False,
                         "recent_filtered": 0},
        gpu_probe=lambda i, a: ("HOLD",
                                 "myia-ai-01#gpu2 : HOLD -- held by "
                                 "myia-po-2024:CoursIA"))
    assert [c["number"] for c in picks] == [5002]
    holds = [c for c in conflicts
             if c[0]["number"] == 5001 and "[DEFER gpu-reservation hold]" in c[1]]
    assert len(holds) == 1, "le grain GPU tenu doit etre ecarte AVEC son motif"


def test_tirage_pondere_sert_un_genai_non_marque_et_le_nomme(monkeypatch):
    """Point 1 de bout en bout sur la voie ponderee : le grain part, et
    l'etat du tirage porte la liste des grains servis sans cible -- sinon
    le service serait muet."""
    monkeypatch.setattr(pig, "has_recent_delivery_marker", lambda n: False)
    candidates = [
        {"number": 5101, "title": "Docs(genai): parametres par modele",
         "age": 30, "idle": 1, "idle_since_delivery": 1, "genre": "genai",
         "body": "Baliser temperature/top_p par modele.", "klass": "grain",
         "labels": []},
    ]
    by_class = {"grain": candidates, "umbrella": [], "delivered": []}

    class _A:
        grains = 4
        umbrellas = 0
        delivered = 0
        prev_genre = None
        lane = "myia-ai-01:CoursIA-2"
        check_claims = False

    state = {"failures": [], "budget_hit": False, "recent_filtered": 0}
    picks, _claims, conflicts = pig.draw_unclaimed(
        by_class, _A(), random.Random(7), {}, {}, {},
        delivered_state=state, gpu_probe=_never_called)
    assert [c["number"] for c in picks] == [5101]
    assert conflicts == []
    assert [e["number"] for e in state["gpu_target_unresolved"]] == [5101]


def test_tapis_ecarte_un_grain_gpu_tenu():
    """Le tapis (`--belt`) est le chemin que le cycle `/continue` emprunte :
    il porte le meme gate, le meme fail-CLOSED et le meme motif nomme."""
    args = types.SimpleNamespace(grains=1, include_delivered=True,
                                 lane="myia-ai-01:CoursIA-2", gpu_entity=[])
    picks, withheld, state = pig.belt_pick_with_replacements(
        [{"number": 6001, "klass": "grain", "genre": "training",
          "body": BODY_DECLARED}],
        {6001: (pig.CLAIM_CODE_FREE, "libre")}, args, probe_budget=4,
        gpu_probe=lambda i, a: ("HOLD",
                                 "myia-ai-01#gpu2 : HOLD -- held by "
                                 "myia-po-2024:CoursIA"))
    assert picks == []
    assert len(withheld) == 1
    assert "[DEFER gpu-reservation hold]" in withheld[0][1]
    assert "myia-ai-01#gpu2" in withheld[0][1]
    assert state.get("gpu_target_unresolved") in (None, [])


def test_tirage_pondere_ne_consulte_pas_le_gate_sans_cible(monkeypatch):
    """Le corps est RETIRE du pick par `draw` : sans la table de corps
    remise par `_gate_view`, la porte voyait un corps vide sur toute la voie
    ponderee et ecartait chaque grain GPU-borne en `TARGET_UNRESOLVED`.

    Ce test le prouve par l'autre bout : une sonde qui refuserait tout n'est
    jamais consultee quand le grain ne declare pas de cible. Si la porte
    etait consultee, le grain serait ecarte -- et l'acceptance du point 1
    serait fausse sur ce chemin.
    """
    monkeypatch.setattr(pig, "has_recent_delivery_marker", lambda n: False)
    by_class = {"grain": [{"number": 5201, "title": "Qualite TTS (genai)",
                           "age": 20, "idle": 1, "idle_since_delivery": 1,
                           "genre": "genai",
                           "body": "Le modele Qwen3-TTS degrade le WER.",
                           "klass": "grain", "labels": []}],
                "umbrella": [], "delivered": []}

    class _A:
        grains = 2
        umbrellas = 0
        delivered = 0
        prev_genre = None
        lane = "myia-ai-01:CoursIA-2"
        check_claims = False

    state = {"failures": [], "budget_hit": False, "recent_filtered": 0}
    picks, _claims, conflicts = pig.draw_unclaimed(
        by_class, _A(), random.Random(11), {}, {}, {},
        delivered_state=state, gpu_probe=_never_called)
    assert [c["number"] for c in picks] == [5201]
    assert conflicts == []


def test_tapis_sert_un_genai_non_marque_et_le_nomme():
    """Point 1 sur le tapis : le grain est SERVI, et l'etat le dit. C'est la
    surface que `/continue` lit (`--json` -> `gpu_signal`)."""
    args = types.SimpleNamespace(grains=1, include_delivered=True,
                                 lane="myia-ai-01:CoursIA-2", gpu_entity=[])
    picks, withheld, state = pig.belt_pick_with_replacements(
        [{"number": 6101, "klass": "grain", "genre": "genai",
          "body": "Router le narrateur vers Qwen VoiceDesign."}],
        {6101: (pig.CLAIM_CODE_FREE, "libre")}, args, probe_budget=4,
        gpu_probe=_never_called)
    assert [it["number"] for it in picks] == [6101]
    assert withheld == []
    assert [e["number"] for e in state["gpu_target_unresolved"]] == [6101]


def test_le_rapport_texte_nomme_les_grains_servis_sans_cible(capsys):
    """Le rendu texte porte le marqueur, sans quoi le service resterait
    muet pour une lane qui ne lit pas le JSON."""
    pig.print_gpu_target_unresolved([
        {"number": 7001, "cause": pig.GPU_UNRESOLVED_NOTE}])
    out = capsys.readouterr().out
    assert "#7001" in out
    assert "SERVI" in out
    assert "GPU: <machine>#gpu<n>" in out
    # Sans note : aucune ligne (pas de banniere a zero).
    pig.print_gpu_target_unresolved([])
    assert capsys.readouterr().out == ""
