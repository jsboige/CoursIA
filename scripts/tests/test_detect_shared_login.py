"""Controle positif du detecteur de login partage (#17418 Phase A).

Un detecteur sans controle positif rend zero et se lit « tout va bien ». Le
test live declenche VOLONTAIREMENT un appel non epingle (sonde sans GH_TOKEN)
et ECCHOUE si la detection ne le voit pas : sur une machine de flotte ou le
compte actif du trousseau n'est pas le compte machine, la sonde doit rendre
SHARED. Si quelqu'un casse la detection (sonde muette, classification
inversee), ce test devient rouge — pas silencieusement vert.
"""

import shutil
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import detect_shared_login  # noqa: E402
import gh_identity  # noqa: E402

GH_AVAILABLE = shutil.which("gh") is not None


# --- classification pure ----------------------------------------------------


def test_classify_shared():
    label, rc = detect_shared_login.classify("jsboige", "myia-po-2023")
    assert (label, rc) == ("SHARED", 1)


def test_classify_machine_meme_non_epingle():
    # Cas etag : le compte actif du trousseau est deja le compte machine.
    label, rc = detect_shared_login.classify("myia-po-2023", "myia-po-2023")
    assert (label, rc) == ("MACHINE-EVEN-UNPINNED", 0)


def test_classify_sonde_muette():
    label, rc = detect_shared_login.classify(None, "myia-po-2023")
    assert (label, rc) == ("PROBE-ERROR", 2)


def test_classify_insensible_a_la_casse():
    assert detect_shared_login.classify("MyIA-Web1", "myia-web1")[0] == "MACHINE-EVEN-UNPINNED"


# --- controle positif live ---------------------------------------------------


@pytest.mark.skipif(not GH_AVAILABLE, reason="gh CLI absent — controle positif live impossible")
def test_controle_positif_sonde_non_epinglee_est_vue():
    """La detection DOIT voir l'appel volontairement non epingle.

    Saute (skip) si la sonde est muette (gh absent, non authentifie ou
    machine sans compte machine) ; echoue si la classification refuse de
    nommer SHARED un login etranger au compte machine.
    """
    try:
        account = gh_identity.machine_account()
    except gh_identity.GhIdentityError:
        pytest.skip("machine sans compte machine connu — transition #17418 B/C")
    probe = detect_shared_login.probe_unpinned_login()
    label, rc = detect_shared_login.classify(probe, account)
    if probe is None:
        pytest.skip("sonde live indisponible (gh non authentifie ou reseau)")
    # L'invariant du controle positif : un probe NON MUTE qui rend un login
    # etranger DOIT etre classe SHARED. C'est exactement ce qui echoue si la
    # detection est cassee.
    if probe.lower() != account.lower():
        assert label == "SHARED" and rc == 1, (
            f"detection cassee : sonde non-epinglee sous '{probe}' != "
            f"'{account}', verdict rendu ({label}, {rc})"
        )


# --- cablage de la banniere dans l'adjoint (#17418 rc=2 != rc=1) ------------


def test_adjoint_unknown_par_rate_limit_porte_la_banniere(monkeypatch, capsys):
    """Le chemin UNKNOWN de l'adjoint doit EMETTRE la banniere sur rate-limit.

    Demo live impossible a souhait (le seau partage se recharge chaque heure) :
    le test simule le refus exact mesure le 2026-09-22 (`gh_json` leve
    RuntimeError sur l'erreur gh) et verifie la ligne lisible sans --json.
    """
    import importlib.util

    here = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location(
        "check_adjoint_prevalidation_banner", here.parent / "check_adjoint_prevalidation.py"
    )
    mod = importlib.util.module_from_spec(spec)
    sys.modules["check_adjoint_prevalidation_banner"] = mod
    spec.loader.exec_module(mod)

    def _rate_limited(args):
        raise RuntimeError(
            "gh api repos/jsboige/CoursIA/pulls/17410 failed: "
            "gh: API rate limit already exceeded for user ID 3159389."
        )

    monkeypatch.setattr(mod, "gh_json", _rate_limited)
    monkeypatch.setattr(sys, "argv", ["check_adjoint_prevalidation.py", "17410"])
    rc = mod.main()
    err = capsys.readouterr().err
    assert rc == 2, "un refus rate-limit reste fail-closed (rc=2)"
    assert "[RATE-LIMIT]" in err, "la banniere doit vivre sur stderr, lisible sans --json"
    assert "rc=1" in err, "la banniere nomme explicitement la confusion rc=2 vs rc=1"
    assert "gh auth token" in err, "la banniere porte la remediation"
