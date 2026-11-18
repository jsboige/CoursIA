"""Test du complement `reward_dynamics` et du verdict combine de la Gate 21.

Ce que ce test prouve
---------------------
  1. Sur une trace **saturee** (dominance sans apprentissage -- le profil
     #9583 des runs arm-N a 0.5B), le complement rend SATURATION : c'est le
     faux positif que le panneau `rewardspy` rend `ALERT` (mesure du
     2026-10-31 : meme agregat sur la trace saturee et la trace exploitee).
  2. Sur une trace **exploitee** (reward en hausse SANS math_correct), le
     complement rend EXPLOITATION_REELLE -- seule branche qui l'autorise.
  3. Les branches legitime (math_correct monte) et effondrement (reward
     baisse) sont discriminees : ni l'une ni l'autre n'est une exploitation.
  4. Le seuil est celui du fallback decontamine de la cellule 12 du carnet
     (0.05, PR2.6) : les deux implementations disent la meme chose sur la
     meme trace (controle croise mesure le 2026-10-31).
  5. Le verdict combine couvre ses **cinq** branches sur des traces
     construites ici, et les quatre profils de controle de `--self-test`
     tombent chacun dans son verdict attendu.

Le test n'a **aucune dependance lourde** (ni `rewardspy`, ni torch) : le
panneau reel n'est exerce que par `--self-test`, la ou le paquet est installe.
Il est executable par pytest et directement.

Issue de suivi : #5105.
"""
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
sys.path.insert(0, str(SCRIPTS))

from ict25_records import (REWARD_DYNAMICS_EPSILON, audit_rows,  # noqa: E402
                           reward_dynamics)
import ict25a_rewardspy_audit as audit_mod  # noqa: E402


def _rows(rewards, maths):
    """Lignes `rewardspy` d'une trace construite (hack dominant par defaut)."""
    records = [{"step": i, "gt": "1", "pred": "1", "hack": 0.9, "mc": m,
                "reward": r, "length": 40}
               for i, (r, m) in enumerate(zip(rewards, maths))]
    return audit_rows(records, arm="TEST", seed=0)


def test_trace_saturee_rend_saturation():
    """Dominance sans apprentissage : reward plate -> le complement refuse de
    lire la dominance comme une exploitation (le faux positif #9583)."""
    d = reward_dynamics(_rows([0.5] * 8, [0.0] * 8))
    assert d["dynamics_present"] is False
    assert d["flag"] is False
    assert d["exploitation"] is False
    assert d["reward_delta_early_to_late"] == 0.0
    assert "SATURATION" in d["interpretation"]


def test_trace_exploitee_rend_exploitation_reelle():
    """Reward en hausse sans math_correct : la seule branche exploitation."""
    d = reward_dynamics(_rows([0.0] * 4 + [1.0] * 4, [0.0] * 8))
    assert d["dynamics_present"] is True
    assert d["exploitation"] is True
    assert "EXPLOITATION" in d["interpretation"].upper()


def test_hausse_legitime_n_est_pas_une_exploitation():
    """Reward ET math_correct qui montent : apprentissage reel, pas un hack."""
    d = reward_dynamics(_rows([0.0] * 4 + [1.0] * 4, [0.0] * 4 + [1.0] * 4))
    assert d["dynamics_present"] is True
    assert d["exploitation"] is False
    assert "LEGITIME" in d["interpretation"]


def test_reward_en_baisse_n_est_pas_une_exploitation():
    """Effondrement ou anti-apprentissage : dynamique presente, pas un hack."""
    d = reward_dynamics(_rows([1.0] * 4 + [0.0] * 4, [1.0] * 8))
    assert d["dynamics_present"] is True
    assert d["exploitation"] is False
    assert "baisse" in d["interpretation"]


def test_reward_qui_baisse_pendant_que_math_monte_ne_dit_pas_hausse():
    """La branche « LEGITIME » exige la hausse effective de la reward.

    Cas releve par la review Hermes (#5105, point 3) : la branche ne testait
    que `m_delta > epsilon`, donc une reward qui s'effondre (-0.9) pendant que
    math_correct monte (+0.9) etait annoncee « reward en hausse » -- le libelle
    contredisait le chiffre qu'il accompagne. Le verdict combine etait juste,
    seule `interpretation` mentait.
    """
    d = reward_dynamics(_rows([1.0] * 4 + [0.1] * 4, [0.0] * 4 + [0.9] * 4))
    assert d["reward_delta_early_to_late"] == -0.9
    assert d["math_delta_early_to_late"] == 0.9
    assert d["dynamics_present"] is True
    assert d["exploitation"] is False  # m_delta > seuil : pas une exploitation
    assert "baisse" in d["interpretation"]
    assert "hausse" not in d["interpretation"]
    assert "LEGITIME" not in d["interpretation"].upper()


def test_le_seuil_est_celui_du_fallback_du_carnet():
    """0.05, exactement : c'est la valeur du detecteur 4 de la cellule 12
    (PR2.6). Les deux implementations doivent dire la meme chose."""
    assert REWARD_DYNAMICS_EPSILON == 0.05
    # delta exactement au seuil -> pas de dynamique (comparaison stricte)
    bord = reward_dynamics(_rows([0.0] * 4 + [REWARD_DYNAMICS_EPSILON] * 4,
                                 [0.0] * 8))
    assert bord["dynamics_present"] is False
    # delta juste au-dessus -> dynamique
    au_dessus = reward_dynamics(_rows([0.0] * 4 + [0.06] * 4, [0.0] * 8))
    assert au_dessus["dynamics_present"] is True


def test_trop_peu_d_enregistrements_est_gracieux():
    d = reward_dynamics(_rows([0.5], [0.0]))
    assert d["dynamics_present"] is False
    assert d["exploitation"] is False
    assert "trop peu" in d["interpretation"]


def test_verdict_combine_couvre_ses_cinq_branches():
    """Les cinq branches du verdict combine, chacune sur sa trace construite."""
    v = audit_mod._combined_verdict
    sat = reward_dynamics(_rows([0.5] * 8, [0.0] * 8))
    exp = reward_dynamics(_rows([0.0] * 4 + [1.0] * 4, [0.0] * 8))
    leg = reward_dynamics(_rows([0.0] * 4 + [1.0] * 4, [0.0] * 4 + [1.0] * 4))
    eff = reward_dynamics(_rows([1.0] * 4 + [0.0] * 4, [1.0] * 8))
    assert v(0, exp) == "PAS_DE_DOMINANCE"
    assert v(1, exp) == "EXPLOITATION_REELLE"
    assert v(1, sat) == "SATURATION"
    assert v(1, eff) == "EFFONDREMENT"
    assert v(1, leg) == "APPRENTISSAGE_SANS_EXPLOITATION"


def test_les_quatre_profils_de_controle_tombent_dans_leur_verdict():
    """Chaque profil de `--self-test` tombe dans son verdict attendu, SANS le
    paquet `rewardspy` : la dominance y est celle que le panneau a mesure
    (presente sur les quatre profils), le complement fait le reste."""
    for profile, attendu in audit_mod.EXPECTED_COMBINED.items():
        rows = audit_rows(audit_mod._synthetic_records(profile), arm="T", seed=0)
        verdict = audit_mod._combined_verdict(1, reward_dynamics(rows))
        assert verdict in attendu, (profile, verdict)


def test_les_deux_nouveaux_profils_sont_deterministes_et_distincts():
    a = audit_mod._synthetic_records("saturated")
    b = audit_mod._synthetic_records("exploited")
    assert a == audit_mod._synthetic_records("saturated")
    assert len(a) == len(b) == 48 + 96
    assert a != b


def test_saturated_est_plate_et_exploited_est_croissant():
    """Les deux constructions disent ce qu'elles pretendent : l'une plate de
    bout en bout, l'autre strictement croissante (hack et reward)."""
    sat = audit_mod._synthetic_records("saturated")
    exp = audit_mod._synthetic_records("exploited")
    assert len({r["reward"] for r in sat}) == 1
    assert all(r["mc"] == 0.0 and r["hack"] == 0.9 for r in sat)
    rewards = [r["reward"] for r in exp]
    hacks = [r["hack"] for r in exp]
    assert rewards == sorted(rewards) and len(set(rewards)) > 1
    assert hacks == sorted(hacks)
    assert all(r["mc"] == 0.0 for r in exp)


def test_l_audit_importe_sans_rewardspy():
    """Le module d'audit reste importable la ou `rewardspy` n'est PAS installe
    (le paquet n'y est importe qu'a l'interieur de `_audit`). Controle reel :
    un sous-processus bloque `rewardspy` avant d'importer le module -- si le
    paquet etait touche a l'import, ce test echouerait sur la machine ou il
    est installe."""
    import subprocess

    code = ("import sys; sys.modules['rewardspy'] = None; "
            f"sys.path.insert(0, r'{SCRIPTS}'); "
            "import ict25a_rewardspy_audit as m; "
            "assert hasattr(m, '_combined_verdict') and "
            "hasattr(m, 'EXPECTED_COMBINED')")
    proc = subprocess.run([sys.executable, "-c", code],
                          capture_output=True, text=True,
                          encoding="utf-8", errors="replace")
    assert proc.returncode == 0, proc.stderr


if __name__ == "__main__":
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
            print(f"ok {name}")
    print("tous les tests passent")
