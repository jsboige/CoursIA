"""Tests for the UTF-8 environment passed to pick_idle_grain.py's Python child.

Le picker lance ``check_lane_claim.py`` en sous-process et lit son stdout en
UTF-8. Le parametre ``encoding="utf-8"`` de ``subprocess.run`` ne dit que
comment le PARENT decode -- il ne dit rien de ce que l'ENFANT encode. Un
`python` enfant dont stdout est un tube choisit
``locale.getpreferredencoding()``, soit **cp1252** sur un Windows francais.

Incident fondateur (2026-09-01, lane myia-po-2027:CoursIA-2) : le picker est
mort en ``UnicodeDecodeError: 'utf-8' codec can't decode byte 0x97`` -- 0x97
est le tiret cadratin en cp1252, invalide en UTF-8. ``check_lane_claim.py``
rend des verdicts en francais accentue ("claim perime", "deja claim par cette
lane"), donc le crash n'est pas un cas de bord : c'est la sortie nominale.

Le hook pre-commit du depot ("refuse NEW text=True without encoding=") ne peut
pas attraper ce defaut : il regarde l'appel du parent, qui est *deja* correct.
Seule ``PYTHONIOENCODING`` traverse la frontiere de process.

Un detecteur se valide par ses faux negatifs : T3 ci-dessous est le gate qui
rougit si le ``env=`` disparait du site d'appel. T2 seul ne suffirait pas --
la CI tourne sous Linux, ou l'encodage par defaut est deja UTF-8, donc T2 y
passerait meme sans le correctif.
"""

import ast
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts"))

import pick_idle_grain as pig  # noqa: E402

# Caracteres que check_lane_claim.py emet reellement (verdicts francais) plus
# le tiret cadratin, dont l'octet cp1252 0x97 a produit le crash fondateur.
NON_ASCII_SAMPLE = "verdict: claim perime — deja claim par cette lane"


def test_child_env_forces_utf8_and_preserves_environment():
    """T1 -- la variable est posee, et le reste de l'environnement survit."""
    import os

    env = pig._utf8_child_env()
    assert env["PYTHONIOENCODING"] == "utf-8"
    # Ne pas repartir d'un environnement vide : un enfant Python prive de PATH
    # ou de SYSTEMROOT ne demarre pas sous Windows.
    missing = [k for k in os.environ if k not in env]
    assert not missing, f"variables perdues : {missing[:5]}"


def test_child_round_trips_non_ascii_through_a_pipe():
    """T2 -- bout en bout : l'enfant ecrit, le parent decode, rien ne casse.

    C'est la reproduction litterale du crash. Sous Windows FR sans le
    correctif, ce test leve UnicodeDecodeError.
    """
    r = subprocess.run(
        [sys.executable, "-c", f"print({NON_ASCII_SAMPLE!r})"],
        capture_output=True, text=True, encoding="utf-8", timeout=60,
        env=pig._utf8_child_env(),
    )
    assert r.returncode == 0, r.stderr
    assert r.stdout.strip() == NON_ASCII_SAMPLE


def test_call_site_passes_the_utf8_env():
    """T3 -- le gate anti-regression, et le seul qui rougisse sous Linux.

    On lit l'AST plutot que le texte : un ``grep`` sur "env=" passerait au
    vert sur une occurrence en commentaire ou dans une autre fonction.

    v4 (PR #21373 review Hermes 5571014393) -- l'invariant originel
    "exactement 1 subprocess.run" ne tient plus depuis la v3 : la piste
    2 (mode batch) introduit un fallback legacy en sous-process par
    issue, donc la fonction en compte 2, et le test crie a tort sur du
    code sain (les 2 runs portent l'env UTF-8 partage). On rebascule
    l'invariant sur ce qu'on GARDAIT vraiment -- l'UTF-8 du sous-process
    -- et il devient plus fort : chaque appel, pas le premier.

    v5 (PR #22389, mur de temps #21436) -- check_claims ne lance plus
    ``subprocess.run`` directement : tout passe par ``_run_bounded``
    (transport par fichiers, sinon ``run`` joint des threads lecteurs
    qui ne rendent jamais la main sous Windows). L'invariant ne change
    pas -- l'UTF-8 du sous-process -- mais il se prouve en deux sauts :
    chaque ``_run_bounded`` de check_claims porte l'env (memes formes
    acceptees qu'en v4), ET ``_run_bounded`` transmet son parametre
    ``env`` a son propre ``subprocess.run``. Retirer l'un des deux
    sauts rougit : le gate suit la chaine complete, pas le nom de la
    fonction d'appel.

    Forme acceptée pour ``env=`` :
      - appel direct ``env=_utf8_child_env()`` (cas 1)
      - alias local ``env=env`` ou ``env=child_env`` quand la variable
        locale a ete assignee a ``_utf8_child_env()`` dans la meme
        fonction (cas 2, le pattern partage utilise par la v3 pour
        factoriser le dict).
    """
    tree = ast.parse((REPO / "scripts" / "pick_idle_grain.py").read_text(encoding="utf-8"))

    fn = next(n for n in tree.body
              if isinstance(n, ast.FunctionDef) and n.name == "check_claims")

    def calls_named(fndef, attr):
        return [n for n in ast.walk(fndef)
                if isinstance(n, ast.Call)
                and isinstance(n.func, ast.Attribute)
                and n.func.attr == attr]

    # v5 : les lancements d'enfants sont soit des subprocess.run directs
    # (chemin legacy), soit des _run_bounded (transport borne, #21436).
    # v6 (#21882) : check_claims delegue son transport a des helpers nommes
    # (_check_claims_one_batch, _check_claims_sliced) -- l'invariant ne
    # change pas (l'UTF-8 du sous-process), il se prouve a travers la
    # delegation : les appels d'enfants vivent dans les helpers, ou
    # ``env=env`` refere le PARAMETRE (cas 3), et chaque site d'appel de la
    # chaine transmet l'env construit par check_claims.
    TRANSPORTS = ("_check_claims_one_batch", "_check_claims_sliced")
    helpers = [n for n in tree.body
               if isinstance(n, ast.FunctionDef) and n.name in TRANSPORTS]
    fn_scopes = [fn] + helpers

    def child_calls(scope):
        bounded = [n for n in ast.walk(scope)
                   if isinstance(n, ast.Call)
                   and isinstance(n.func, ast.Name)
                   and n.func.id == "_run_bounded"]
        return bounded, calls_named(scope, "run")

    bounded, runs = [], []
    scope_calls = []
    for scope in fn_scopes:
        b, r = child_calls(scope)
        scope_calls.append((scope, b, r))
        bounded += b
        runs += r
    assert runs or bounded, (
        f"attendu au moins 1 subprocess.run ou _run_bounded dans "
        f"check_claims ou ses transports {TRANSPORTS} (v6), vu {len(runs)} "
        f"run(s) et {len(bounded)} _run_bounded(s)"
    )

    # Noms locaux (Name) assignes a _utf8_child_env() dans la meme fonction
    # -- la v3 factorise via ``env = _utf8_child_env()`` puis ``env=env``.
    local_env_aliases = {
        tgt.id
        for n in ast.walk(fn)
        if isinstance(n, ast.Assign)
        for tgt in n.targets
        if isinstance(tgt, ast.Name)
        and isinstance(n.value, ast.Call)
        and isinstance(n.value.func, ast.Name)
        and n.value.func.id == "_utf8_child_env"
    }

    # Cas 3 (v6) : dans un helper de transport, ``env=env`` refere le
    # PARAMETRE env -- legitimate seulement parce que la transmission au
    # site d'appel est prouvee plus bas.
    param_env = {
        h.name for h in helpers
        if any(a.arg == "env" for a in h.args.args)
    }

    def ok_names_for(scope):
        if scope is fn:
            return set(local_env_aliases)
        return {"env"} if scope.name in param_env else set()

    def env_kw_ok(call, ok_names):
        kwargs = {kw.arg for kw in call.keywords}
        if "env" not in kwargs:
            return False, None
        env_kw = next(kw for kw in call.keywords if kw.arg == "env")
        # Cas 1 : appel direct env=_utf8_child_env()
        if (isinstance(env_kw.value, ast.Call)
                and isinstance(env_kw.value.func, ast.Name)
                and env_kw.value.func.id == "_utf8_child_env"):
            return True, env_kw
        # Cas 2 : alias local assigne a _utf8_child_env() dans la fonction
        # Cas 3 : parametre env du helper de transport (v6)
        if (isinstance(env_kw.value, ast.Name)
                and env_kw.value.id in ok_names):
            return True, env_kw
        return False, env_kw

    for scope, scope_bounded, scope_runs in scope_calls:
        scope_ok = ok_names_for(scope)
        for i, call in enumerate(scope_runs + scope_bounded):
            # Les appels d'un scope se prouvent contre SES noms admis ;
            # renumerotes par scope pour qu'un echec nomme l'endroit.
            ok, env_kw = env_kw_ok(call, scope_ok)
            kind = "subprocess.run" if call in scope_runs else "_run_bounded"
            assert ok, (
                f"{kind} #{i} dans {scope.name} lance un enfant Python sans "
                f"env= (ou env= n'est ni _utf8_child_env() ni un alias "
                f"local ni le parametre env du transport) : son stdout sera "
                f"encode en cp1252 sous Windows FR et le decodage UTF-8 du "
                f"parent plantera. Trouve : "
                f"{ast.dump(env_kw.value)[:80] if env_kw is not None else 'aucun env='}"
            )

    # v6, transmission : chaque invocation d'un helper de transport -- directe
    # ou via ThreadPoolExecutor.submit -- passe l'env, en mot-cle ou en 3e
    # argument positionnel (numbers, lane, env). Sans cette preuve, le cas 3
    # ci-dessus serait un envoi a vide.
    def transport_invocations(scope):
        for n in ast.walk(scope):
            if not isinstance(n, ast.Call):
                continue
            if isinstance(n.func, ast.Name) and n.func.id in TRANSPORTS:
                yield n.func.id, n.args, n.keywords
            elif (isinstance(n.func, ast.Attribute)
                    and n.func.attr == "submit" and n.args
                    and isinstance(n.args[0], ast.Name)
                    and n.args[0].id in TRANSPORTS):
                # ex.submit(_check_claims_one_batch, s, lane, env) : les
                # vrais arguments de la tranche suivent la reference.
                yield n.args[0].id, n.args[1:], n.keywords

    for scope in fn_scopes:
        scope_ok = ok_names_for(scope)
        for tname, pos_args, kw_args in transport_invocations(scope):
            env_kw = next((kw for kw in kw_args if kw.arg == "env"), None)
            by_kw = (env_kw is not None
                     and isinstance(env_kw.value, ast.Name)
                     and env_kw.value.id in scope_ok)
            by_pos = (len(pos_args) >= 3
                      and isinstance(pos_args[2], ast.Name)
                      and pos_args[2].id in scope_ok)
            assert by_kw or by_pos, (
                f"invocation de {tname} dans {scope.name} sans transmission "
                f"de l'env UTF-8 (ni env=<admis>, ni 3e argument positionnel "
                f"admis) : la tranche lancerait ses enfants sans l'env, et "
                f"le cas 3 du gate serait un envoi a vide"
            )

    # v5, second saut : _run_bounded doit transmettre son env au vrai
    # subprocess.run -- sinon l'env pose en amont meurt au bord du seam.
    if bounded:
        helper = next(n for n in tree.body
                      if isinstance(n, ast.FunctionDef)
                      and n.name == "_run_bounded")
        helper_runs = calls_named(helper, "run")
        assert helper_runs, (
            "_run_bounded ne lance aucun subprocess.run : le seam ne "
            "demarre plus d'enfant, la chaine d'env est cassee par "
            "construction"
        )
        forwarded = [kw for run in helper_runs for kw in run.keywords
                     if kw.arg == "env" and isinstance(kw.value, ast.Name)
                     and kw.value.id == "env"]
        assert len(forwarded) == len(helper_runs), (
            f"_run_bounded ne transmet pas env= a chacun de ses "
            f"{len(helper_runs)} subprocess.run : l'UTF-8 pose par "
            f"check_claims n'atteint jamais l'enfant"
        )


def test_helper_is_defined_at_module_scope():
    """T4 -- le helper est reutilisable par tout futur enfant Python.

    Garde contre une re-insertion accidentelle a l'interieur d'une fonction
    (elle parserait sans erreur tout en rendant le helper inatteignable).
    """
    tree = ast.parse((REPO / "scripts" / "pick_idle_grain.py").read_text(encoding="utf-8"))
    top_level = {n.name for n in tree.body if isinstance(n, ast.FunctionDef)}
    assert "_utf8_child_env" in top_level


# ---------------------------------------------------------------------------
# T5-T6 : l'invocation DIRECTE de check_lane_claim.py
#
# T1-T4 couvrent le chemin d'appel du picker. Mais lane-claim-protocol.md
# prescrit d'appeler check_lane_claim.py *directement* avant d'editer -- et ce
# chemin-la n'a pas de parent pour lui poser PYTHONIOENCODING.
#
# Le mode de defaillance y est pire que le crash du picker : une fleche U+2192
# n'existe pas dans cp1252, donc le print leve UnicodeEncodeError et le script
# sort en exit 1. Or un exit non-nul se lit, dans la regle, "claim d'une autre
# lane, ne pas commencer". Un plantage d'encodage se deguisait en verrou.
# Mesure du 2026-09-01 (Windows FR) : #13614 rendait rc=1 sur ce seul motif.
# ---------------------------------------------------------------------------

CLAIM_SCRIPT = REPO / "scripts" / "check_lane_claim.py"

# L'idiome d'auto-protection, tel qu'il doit apparaitre en tete de main().
RECONFIGURE_SNIPPET = (
    "for _stream in (sys.stdout, sys.stderr):\n"
    "    if hasattr(_stream, 'reconfigure'):\n"
    "        _stream.reconfigure(encoding='utf-8', errors='replace')\n"
)
ARROW_LINE = "print('verdict -> \u2192 claim perime, deja claim')\n"


def _run_under_cp1252(code: str) -> subprocess.CompletedProcess:
    """Enfant Python dont stdout est un tube force en cp1252.

    Rend le defaut reproductible sur TOUTE plateforme : sans cela le test
    passerait en CI Linux (UTF-8 par defaut) meme correctif retire.
    """
    import os

    env = {**os.environ, "PYTHONIOENCODING": "cp1252", "PYTHONUTF8": "0"}
    return subprocess.run([sys.executable, "-c", code],
                          capture_output=True, env=env, timeout=60)


def test_t5_check_lane_claim_reconfigures_its_own_streams():
    """T5 -- main() se protege lui-meme, avant tout parsing d'arguments."""
    tree = ast.parse(CLAIM_SCRIPT.read_text(encoding="utf-8"))
    fn = next(n for n in tree.body
              if isinstance(n, ast.FunctionDef) and n.name == "main")

    calls = [n for n in ast.walk(fn)
             if isinstance(n, ast.Call)
             and isinstance(n.func, ast.Attribute)
             and n.func.attr == "reconfigure"]
    assert calls, (
        "main() de check_lane_claim.py ne reconfigure pas ses flux : sous "
        "Windows FR un verdict portant une fleche sortira en exit 1, que la "
        "regle lira comme un claim d'une autre lane"
    )
    kwargs = {kw.arg for c in calls for kw in c.keywords}
    assert {"encoding", "errors"} <= kwargs, f"attendu encoding= et errors=, vu {kwargs}"


def test_t6_negative_control_the_defect_is_detectable():
    """T6a -- SANS l'idiome, un flux cp1252 plante bien sur la fleche.

    Controle negatif : si celui-ci passait, T6b ne prouverait rien.
    """
    out = _run_under_cp1252(ARROW_LINE)
    assert out.returncode != 0, (
        "le controle negatif n'a pas plante : ce test ne peut pas detecter "
        "le defaut qu'il pretend garder"
    )
    assert b"UnicodeEncodeError" in out.stderr


def test_t6_the_idiom_actually_repairs_it():
    """T6b -- AVEC l'idiome, le meme flux rend de l'UTF-8 valide, exit 0."""
    out = _run_under_cp1252("import sys\n" + RECONFIGURE_SNIPPET + ARROW_LINE)
    assert out.returncode == 0, out.stderr.decode("utf-8", "replace")
    out.stdout.decode("utf-8")  # leve UnicodeDecodeError si ce n'est pas de l'UTF-8
    assert "→" in out.stdout.decode("utf-8")
