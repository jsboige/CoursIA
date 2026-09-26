"""Regression #17425 -- `gh-login` ne persiste un jeton qu'apres avoir prouve a QUI il appartient.

Trois defauts distincts ont coexiste dans la premiere version de `cmd_gh_login`,
et les trois etaient SILENCIEUX : l'organe rendait 0 et affichait un `OK`.

1. **Shadowing de l'identite.** La boucle de resolution de l'attendu utilisait
   `login` comme variable de boucle, ecrasant l'identite rendue par
   `gh api user`. La comparaison finale confrontait donc deux valeurs
   *attendues* -- elle ne pouvait plus echouer. Temoin negatif ci-dessous :
   un jeton appartenant a `attaquant-quelconque` etait ACCEPTE comme
   `myia-ai-01`.

2. **`returncode` et login vide non refuses.** `who.returncode` n'etait jamais
   lu, et le garde s'ecrivait `if expected and login and ...` : un login vide
   SAUTAIT le controle au lieu de le faire echouer.

3. **Persistance avant validation.** `gh auth login` etait appele en PREMIER.
   Il ecrit dans la configuration de `gh`, partagee par toutes les lanes de la
   machine : constater apres coup qu'on a installe la mauvaise identite ne la
   desinstalle pas, et le degat frappe les sessions voisines.

Le 4e test couvre le depot de la passphrase : `keyring` bascule en silence sur
un backend de repli quand le coffre natif manque, et certains replis ecrivent
EN CLAIR sur disque.
"""

from __future__ import annotations

import importlib.util
import sys
import types
from pathlib import Path

import pytest

_MODULE_PATH = Path(__file__).resolve().parents[1] / "agent_keyring.py"


def _load_module():
    spec = importlib.util.spec_from_file_location("agent_keyring_under_test", _MODULE_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture()
def mod():
    return _load_module()


class _Entry:
    def __init__(self, title: str, username: str, password: str):
        self.title = title
        self.username = username
        self.password = password


class _Res:
    def __init__(self, returncode: int = 0, stdout: str = "", stderr: str = ""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


def _args(entry="myia-ai-01", group="Agents", account=None):
    return types.SimpleNamespace(entry=entry, group=group, account=account)


def _wire(mod, monkeypatch, *, api_result: _Res, token: str = "ghp_" + "a" * 36):
    """Branche l'organe sur un faux coffre et un faux `gh`, et JOURNALISE les appels.

    Le journal est le coeur du test 3 : ce qui compte n'est pas seulement le code
    de sortie, c'est de prouver que `gh auth login` n'a PAS ete appele.
    """
    calls: list[list[str]] = []

    monkeypatch.setattr(mod.shutil, "which", lambda name: "/usr/bin/gh")
    monkeypatch.setattr(mod, "open_vault", lambda *a, **k: object())
    monkeypatch.setattr(mod, "find_entry",
                        lambda kp, title, grp: _Entry("github ai-01", "myia-ai-01", token))

    def fake_run(cmd, **kwargs):
        calls.append(list(cmd))
        if cmd[:3] == ["gh", "api", "user"]:
            return api_result
        if cmd[:3] == ["gh", "auth", "login"]:
            return _Res(0)
        raise AssertionError(f"commande inattendue : {cmd}")

    monkeypatch.setattr(mod.subprocess, "run", fake_run)
    return calls


def _persisted(calls) -> bool:
    return any(c[:3] == ["gh", "auth", "login"] for c in calls)


# ---------------------------------------------------------------------------
# 1. shadowing -- le temoin negatif du defaut principal
# ---------------------------------------------------------------------------

def test_identite_divergente_est_refusee(mod, monkeypatch):
    """Le coffre porte 'myia-ai-01' mais le jeton appartient a quelqu'un d'autre.

    AVANT le correctif, ce cas rendait EXIT_OK : la variable `login` avait ete
    ecrasee par la boucle et valait 'myia-ai-01', donc la comparaison portait
    sur 'myia-ai-01' == 'myia-ai-01'.
    """
    calls = _wire(mod, monkeypatch, api_result=_Res(0, "attaquant-quelconque\n"))
    rc = mod.cmd_gh_login(_args())
    assert rc == mod.EXIT_DEFECT
    assert not _persisted(calls), "la mauvaise identite a ete PERSISTEE dans `gh`"


def test_identite_concordante_est_acceptee(mod, monkeypatch):
    """Controle positif : sans lui, un test qui refuse tout passerait aussi."""
    calls = _wire(mod, monkeypatch, api_result=_Res(0, "myia-ai-01\n"))
    assert mod.cmd_gh_login(_args()) == mod.EXIT_OK
    assert _persisted(calls), "l'identite etait bonne, le jeton aurait du etre persiste"


def test_la_boucle_de_resolution_ne_touche_pas_a_login(mod):
    """Le defaut nomme, teste a sa racine : aucune variable de boucle de
    `cmd_gh_login` ne doit s'appeler `login`."""
    import ast

    tree = ast.parse(_MODULE_PATH.read_text(encoding="utf-8"))
    fn = next(n for n in ast.walk(tree)
              if isinstance(n, ast.FunctionDef) and n.name == "cmd_gh_login")
    noms = set()
    for node in ast.walk(fn):
        if isinstance(node, ast.For):
            for t in ast.walk(node.target):
                if isinstance(t, ast.Name):
                    noms.add(t.id)
    assert "login" not in noms, (
        "une variable de boucle nommee `login` ecrase l'identite lue par "
        "`gh api user` et rend la comparaison finale tautologique"
    )


# ---------------------------------------------------------------------------
# 2. returncode et login vide
# ---------------------------------------------------------------------------

def test_api_en_echec_est_refusee(mod, monkeypatch):
    calls = _wire(mod, monkeypatch, api_result=_Res(1, "", "HTTP 401: Bad credentials"))
    assert mod.cmd_gh_login(_args()) == mod.EXIT_DEFECT
    assert not _persisted(calls)


def test_login_vide_avec_rc_zero_est_refuse(mod, monkeypatch):
    """rc=0 avec une sortie vide n'est pas une identite.

    AVANT le correctif, `if expected and login and ...` sautait le controle :
    une reponse vide se lisait comme un succes.
    """
    calls = _wire(mod, monkeypatch, api_result=_Res(0, "   \n"))
    assert mod.cmd_gh_login(_args()) == mod.EXIT_DEFECT
    assert not _persisted(calls)


def test_identite_attendue_inconnue_rend_unknown(mod, monkeypatch):
    """Ne pas savoir n'est pas valider : sans attendu resolvable, rc=2, pas 0."""
    _wire(mod, monkeypatch, api_result=_Res(0, "quelconque\n"))
    monkeypatch.setattr(mod, "find_entry",
                        lambda kp, t, g: _Entry("entree hors catalogue", "", "ghp_" + "b" * 36))
    assert mod.cmd_gh_login(_args(entry="entree hors catalogue")) == mod.EXIT_UNKNOWN


# ---------------------------------------------------------------------------
# 3. ordre des operations -- valider AVANT de persister
# ---------------------------------------------------------------------------

def test_api_user_est_interrogee_avant_auth_login(mod, monkeypatch):
    calls = _wire(mod, monkeypatch, api_result=_Res(0, "myia-ai-01\n"))
    mod.cmd_gh_login(_args())
    ordre = [c[1] for c in calls]
    assert ordre.index("api") < ordre.index("auth"), (
        "`gh auth login` ecrit dans une configuration partagee : il doit venir "
        "APRES la validation d'identite, jamais avant"
    )


def test_le_jeton_passe_par_l_environnement_pas_par_la_config(mod, monkeypatch):
    """La validation ne doit laisser aucune trace persistante."""
    vus: dict[str, dict] = {}

    monkeypatch.setattr(mod.shutil, "which", lambda name: "/usr/bin/gh")
    monkeypatch.setattr(mod, "open_vault", lambda *a, **k: object())
    monkeypatch.setattr(mod, "find_entry",
                        lambda kp, t, g: _Entry("github ai-01", "myia-ai-01", "ghp_" + "c" * 36))

    def fake_run(cmd, **kwargs):
        if cmd[:3] == ["gh", "api", "user"]:
            vus["env"] = kwargs.get("env") or {}
            return _Res(0, "myia-ai-01\n")
        return _Res(0)

    monkeypatch.setattr(mod.subprocess, "run", fake_run)
    mod.cmd_gh_login(_args())
    assert vus["env"].get("GH_TOKEN", "").startswith("ghp_")


# ---------------------------------------------------------------------------
# 4. depot de la passphrase -- jamais dans un backend de repli
# ---------------------------------------------------------------------------

class _FauxBackend:
    """Tient les deux roles que l'organe attend de `_keyring()` : le MODULE
    `keyring` (`get_keyring`, `set_password` au niveau module) et le backend
    actif qu'il rend. Un faux qui ne jouait que le backend a masque le defaut
    du 26/09 : l'organe lisait le type du module, que ce faux n'avait pas."""

    def __init__(self):
        self.ecrit = []

    def get_keyring(self):
        return self

    def set_password(self, service, user, value):
        self.ecrit.append((service, user, value))


def _backend_nomme(module_name: str, class_name: str):
    faux = type(class_name, (_FauxBackend,), {})
    faux.__module__ = module_name
    return faux()


def test_backend_en_clair_refuse_l_ecriture(mod, monkeypatch):
    kr = _backend_nomme("keyrings.alt.file", "PlaintextKeyring")
    monkeypatch.setattr(mod, "_keyring", lambda: kr)
    with pytest.raises(SystemExit) as exc:
        mod.write_passphrase("une-passphrase")
    assert exc.value.code == mod.EXIT_DEFECT
    assert kr.ecrit == [], "la passphrase a ete ECRITE dans un backend en clair"


def test_backend_natif_autorise_l_ecriture_et_est_atteste(mod, monkeypatch):
    kr = _backend_nomme("keyring.backends.Windows", "WinVaultKeyring")
    monkeypatch.setattr(mod, "_keyring", lambda: kr)
    assert mod.write_passphrase("une-passphrase") is None
    assert "WinVaultKeyring" in mod.assert_backend_is_native()
    assert len(kr.ecrit) == 1


def test_backend_encrypted_de_repli_refuse(mod, monkeypatch):
    """`EncryptedKeyring` de `keyrings.alt` derive d'un mot de passe faible :
    il n'est pas le coffre natif, et le nom seul ne suffit pas a le blanchir."""
    kr = _backend_nomme("keyrings.alt.file", "EncryptedKeyring")
    monkeypatch.setattr(mod, "_keyring", lambda: kr)
    with pytest.raises(SystemExit):
        mod.write_passphrase("une-passphrase")
    assert kr.ecrit == []
