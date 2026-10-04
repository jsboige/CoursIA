"""`set` et `run` (#17558 phase 2) -- ecrivain unique et injection d'environnement.

Le coffre est **un fichier binaire unique**, synchronise par le client Drive.
Deux machines qui l'ecrivent dans la meme fenetre de synchronisation produisent
une copie en conflit, et le client ne fusionne pas : le defaut ne se voit qu'au
moment ou une entree manque. D'ou les deux gardes de `set`, et le controle
positif exige par la condition de sortie de la phase 2 -- *une copie en conflit
fabriquee fait refuser `set`*.

La postcondition d'ecriture a son propre temoin : un `save()` qui rend la main
sans que le fichier change est un echec qui ressemble a un succes. Le faux coffre
de ces tests **persiste sur disque**, sans quoi la relecture verrait l'objet
qu'on vient de muter au lieu de ce que le fichier contient, et le test serait
tautologique.

`run` a une propriete a defendre qui ne se voit pas dans son code de sortie :
il n'injecte **que** les paires nommees. Un enfant qui recevrait tout le coffre
verserait les secrets des sept machines dans chaque processus lance.
"""

from __future__ import annotations

import importlib.util
import json
import sys
import types
from pathlib import Path

import pytest

_MODULE_PATH = Path(__file__).resolve().parents[1] / "agent_keyring.py"


def _load_module():
    spec = importlib.util.spec_from_file_location("agent_keyring_set_under_test", _MODULE_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture()
def mod():
    return _load_module()


# ---------------------------------------------------------------------------
# faux coffre -- il PERSISTE, sinon la postcondition de `set` ne mesure rien
# ---------------------------------------------------------------------------

class _Groupe:
    def __init__(self, name):
        self.name = name


class _Entree:
    def __init__(self, title, username="", password="", url=None, group=None):
        self.title = title
        self.username = username
        self.password = password
        self.url = url
        self.group = group
        self.mtime = None


class _Coffre:
    def __init__(self, path: Path):
        self.path = Path(path)
        self.root_group = _Groupe(None)
        self._groupes: dict[str, _Groupe] = {}
        self.entries: list[_Entree] = []

    @classmethod
    def charger(cls, path: Path) -> "_Coffre":
        kp = cls(path)
        data = json.loads(Path(path).read_text(encoding="utf-8"))
        for brut in data["entries"]:
            nom = brut.get("group")
            groupe = kp._groupe(nom) if nom else kp.root_group
            kp.entries.append(_Entree(brut["title"], brut.get("username", ""),
                                      brut.get("password", ""), brut.get("url"), groupe))
        return kp

    def _groupe(self, nom: str) -> _Groupe:
        if nom not in self._groupes:
            self._groupes[nom] = _Groupe(nom)
        return self._groupes[nom]

    def find_groups(self, name=None, first=False):
        trouves = [g for g in self._groupes.values() if g.name == name]
        if not trouves:
            return None if first else []
        return trouves[0] if first else trouves

    def add_group(self, parent, name):
        return self._groupe(name)

    def add_entry(self, group, title, username, password, url=None):
        entree = _Entree(title, username, password, url, group)
        self.entries.append(entree)
        return entree

    def save(self):
        self.path.write_text(json.dumps({"entries": [
            {"title": e.title, "username": e.username, "password": e.password,
             "url": e.url, "group": e.group.name if e.group else None}
            for e in self.entries]}, indent=1), encoding="utf-8")


class _CoffreSansEcriture(_Coffre):
    """Le `save()` qui rend la main sans rien ecrire -- l'echec qui se lit `OK`."""

    def save(self):
        pass


class _CoffreQuiCreeUnConflit(_Coffre):
    """Ecrit, puis depose une copie en conflit -- la fenetre reelle du client Drive."""

    def save(self):
        super().save()
        (self.path.parent / f"{self.path.stem} (1){self.path.suffix}").write_text(
            "copie arrivee pendant l'ecriture", encoding="utf-8")


def _vault(tmp_path: Path, entrees=()) -> Path:
    chemin = tmp_path / "MyIA-Keys.kdbx"
    kp = _Coffre(chemin)
    groupe = kp.add_group(kp.root_group, "Agents")
    for titre, user, valeur in entrees:
        kp.add_entry(groupe, titre, user, valeur)
    kp.save()
    return chemin


def _wire(mod, monkeypatch, chemin: Path, classe=_Coffre):
    monkeypatch.setattr(mod, "vault_path", lambda: chemin)
    monkeypatch.setattr(mod, "open_vault", lambda *a, **k: classe.charger(chemin))
    return chemin


class _Stdin:
    def __init__(self, texte: str, tty: bool = False):
        self._texte = texte
        self._tty = tty

    def isatty(self):
        return self._tty

    def read(self):
        return self._texte


def _stdin(monkeypatch, texte: str, tty: bool = False):
    monkeypatch.setattr(sys, "stdin", _Stdin(texte, tty))


def _args_set(entry="github ai-01", group="Agents", username=None, url=None):
    return types.SimpleNamespace(entry=entry, group=group, username=username, url=url)


def _args_run(env, command, group="Agents"):
    return types.SimpleNamespace(env=env, command=command, group=group)


def _bombe(*a, **k):
    raise AssertionError("appel interdit dans ce cas : le refus doit precede")


# ---------------------------------------------------------------------------
# detection des copies en conflit
# ---------------------------------------------------------------------------

def test_copie_google_drive_est_detectee(mod, tmp_path):
    coffre = _vault(tmp_path)
    copie = tmp_path / "MyIA-Keys (1).kdbx"
    copie.write_text("copie", encoding="utf-8")
    assert mod.conflict_copies(coffre) == [copie]


def test_copie_dropbox_est_detectee(mod, tmp_path):
    coffre = _vault(tmp_path)
    copie = tmp_path / "MyIA-Keys (conflicted copy 2026-10-02).kdbx"
    copie.write_text("copie", encoding="utf-8")
    assert mod.conflict_copies(coffre) == [copie]


def test_voisins_legitimes_ne_sont_pas_des_copies_en_conflit(mod, tmp_path):
    """Un controle qui refuserait tout voisin `.kdbx` bloquerait une sauvegarde
    volontaire, et rien ne distinguerait plus une copie en conflit d'un second
    coffre range a cote."""
    coffre = _vault(tmp_path)
    (tmp_path / "MyIA-Keys-sauvegarde-2026-09.kdbx").write_text("x", encoding="utf-8")
    (tmp_path / "Autre-Coffre (1).kdbx").write_text("x", encoding="utf-8")
    (tmp_path / "MyIA-Keys.kdbx.bak").write_text("x", encoding="utf-8")
    assert mod.conflict_copies(coffre) == []


def test_coffre_seul_rend_une_liste_vide(mod, tmp_path):
    assert mod.conflict_copies(_vault(tmp_path)) == []


# ---------------------------------------------------------------------------
# set -- controle positif exige par la phase 2
# ---------------------------------------------------------------------------

def test_set_refuse_quand_une_copie_en_conflit_existe(mod, monkeypatch, tmp_path):
    """CONTROLE POSITIF de la phase 2 : la copie fabriquee fait refuser `set`.

    Et le refus precede l'ouverture du coffre : `open_vault` est une bombe. Un
    controle pose apres la lecture laisserait la fenetre ou l'on ecrit dans une
    moitie du coffre pendant que l'autre moitie existe encore.
    """
    coffre = _vault(tmp_path, [("github ai-01", "myia-ai-01", "valeur-initiale")])
    (tmp_path / "MyIA-Keys (2).kdbx").write_text("copie", encoding="utf-8")
    avant = coffre.read_bytes()
    _stdin(monkeypatch, "valeur-nouvelle\n")

    monkeypatch.setattr(mod, "vault_path", lambda: coffre)
    monkeypatch.setattr(mod, "open_vault", _bombe)

    assert mod.cmd_set(_args_set()) == mod.EXIT_DEFECT
    assert coffre.read_bytes() == avant, "le coffre a ete modifie malgre la copie en conflit"


def test_set_detecte_une_copie_apparue_pendant_l_ecriture(mod, monkeypatch, tmp_path, capsys):
    """La fenetre entre le controle initial et l'ecriture est reelle."""
    coffre = _vault(tmp_path)
    _wire(mod, monkeypatch, coffre, classe=_CoffreQuiCreeUnConflit)
    _stdin(monkeypatch, "valeur-nouvelle\n")

    assert mod.cmd_set(_args_set()) == mod.EXIT_DEFECT
    assert "PENDANT" in capsys.readouterr().err


# ---------------------------------------------------------------------------
# set -- ecriture et postcondition
# ---------------------------------------------------------------------------

def test_set_cree_puis_met_a_jour_la_meme_entree(mod, monkeypatch, tmp_path, capsys):
    coffre = _vault(tmp_path)
    _wire(mod, monkeypatch, coffre)

    _stdin(monkeypatch, "premiere-valeur\n")
    assert mod.cmd_set(_args_set()) == mod.EXIT_OK
    assert "creee" in capsys.readouterr().out

    _stdin(monkeypatch, "seconde-valeur\n")
    assert mod.cmd_set(_args_set()) == mod.EXIT_OK
    assert "mise a jour" in capsys.readouterr().out

    entrees = json.loads(coffre.read_text(encoding="utf-8"))["entries"]
    assert len(entrees) == 1, "la seconde ecriture a cree un doublon au lieu de mettre a jour"
    assert entrees[0]["password"] == "seconde-valeur"
    assert entrees[0]["group"] == "Agents"


def test_set_cree_le_groupe_manquant(mod, monkeypatch, tmp_path):
    """Un coffre neuf n'a pas le groupe `Agents` : l'ecriture doit le creer au
    lieu d'echouer sur une erreur qui ne dit pas ce qui manque."""
    coffre = tmp_path / "MyIA-Keys.kdbx"
    coffre.write_text(json.dumps({"entries": []}), encoding="utf-8")
    _wire(mod, monkeypatch, coffre)
    _stdin(monkeypatch, "valeur\n")

    assert mod.cmd_set(_args_set()) == mod.EXIT_OK
    entrees = json.loads(coffre.read_text(encoding="utf-8"))["entries"]
    assert entrees[0]["group"] == "Agents"


def test_set_refuse_quand_le_fichier_n_a_pas_change(mod, monkeypatch, tmp_path, capsys):
    """Le temoin du `save()` qui rend la main sans ecrire : sans cette mesure,
    l'organe afficherait `OK` sur un coffre inchange."""
    coffre = _vault(tmp_path)
    _wire(mod, monkeypatch, coffre, classe=_CoffreSansEcriture)
    _stdin(monkeypatch, "valeur-nouvelle\n")

    assert mod.cmd_set(_args_set()) == mod.EXIT_DEFECT
    assert "n'a pas change" in capsys.readouterr().err


def test_set_refuse_une_valeur_vide(mod, monkeypatch, tmp_path, capsys):
    coffre = _vault(tmp_path)
    _wire(mod, monkeypatch, coffre)
    _stdin(monkeypatch, "\n")

    assert mod.cmd_set(_args_set()) == mod.EXIT_DEFECT
    assert json.loads(coffre.read_text(encoding="utf-8"))["entries"] == []
    assert "vide" in capsys.readouterr().err


def test_set_refuse_un_stdin_terminal(mod, monkeypatch, tmp_path, capsys):
    """Sur un terminal, `read()` attend un EOF : sans ce refus, la commande
    parait gelee au lieu de dire comment on l'alimente."""
    coffre = _vault(tmp_path)
    _wire(mod, monkeypatch, coffre)
    monkeypatch.setattr(mod.sys, "stdin", _Stdin("", tty=True))

    assert mod.cmd_set(_args_set()) == mod.EXIT_DEFECT
    assert "terminal" in capsys.readouterr().err


def test_set_ne_retire_que_le_terminateur_de_ligne(mod, monkeypatch, tmp_path):
    """Rogner les espaces fabriquerait un secret silencieusement different."""
    coffre = _vault(tmp_path)
    _wire(mod, monkeypatch, coffre)
    _stdin(monkeypatch, "  valeur-avec-espaces  \r\n")

    assert mod.cmd_set(_args_set()) == mod.EXIT_OK
    entrees = json.loads(coffre.read_text(encoding="utf-8"))["entries"]
    assert entrees[0]["password"] == "  valeur-avec-espaces  "


def test_set_rend_unknown_si_le_coffre_est_absent(mod, monkeypatch, tmp_path, capsys):
    """Ne pas pouvoir mesurer n'est pas un succes : rc=2, et aucun fichier cree."""
    absent = tmp_path / "MyIA-Keys.kdbx"
    monkeypatch.setattr(mod, "vault_path", lambda: absent)
    monkeypatch.setattr(mod, "open_vault", _bombe)
    _stdin(monkeypatch, "valeur\n")

    assert mod.cmd_set(_args_set()) == mod.EXIT_UNKNOWN
    assert not absent.exists()


def test_set_n_imprime_jamais_la_valeur(mod, monkeypatch, tmp_path, capsys):
    coffre = _vault(tmp_path)
    _wire(mod, monkeypatch, coffre)
    secret = "valeur-qui-ne-doit-pas-sortir"
    _stdin(monkeypatch, secret + "\n")

    assert mod.cmd_set(_args_set()) == mod.EXIT_OK
    sortie = capsys.readouterr()
    assert secret not in sortie.out
    assert secret not in sortie.err
    assert mod.fingerprint(secret) in sortie.out


# ---------------------------------------------------------------------------
# run -- paires, refus, injection
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("paire", ["VAR", "=ENTREE", "VAR=", "1BAD=valeur", "VAR-A=valeur", "  =x"])
def test_paire_mal_formee_est_refusee(mod, paire):
    with pytest.raises(ValueError):
        mod.parse_env_pair(paire)


def test_paire_canonique_est_acceptee(mod):
    assert mod.parse_env_pair("GH_RUNNERS_ADMIN_TOKEN=github ai-01") == (
        "GH_RUNNERS_ADMIN_TOKEN", "github ai-01")


def test_retour_du_fils_mort_par_signal(mod):
    """`subprocess` rend -N, le shell 128+N : rendre -N ferait lire 255."""
    assert mod.child_returncode(0) == 0
    assert mod.child_returncode(7) == 7
    assert mod.child_returncode(-9) == 137


def test_run_refuse_sans_paire(mod, monkeypatch, capsys):
    monkeypatch.setattr(mod.subprocess, "run", _bombe)
    assert mod.cmd_run(_args_run([], ["--", "true"])) == mod.EXIT_DEFECT
    assert "aucune paire" in capsys.readouterr().err


def test_run_refuse_une_paire_mal_formee(mod, monkeypatch, tmp_path, capsys):
    _wire(mod, monkeypatch, _vault(tmp_path))
    monkeypatch.setattr(mod.subprocess, "run", _bombe)
    assert mod.cmd_run(_args_run(["PASDEPAIRE"], ["--", "true"])) == mod.EXIT_DEFECT
    assert "mal formee" in capsys.readouterr().err


def test_run_refuse_une_variable_nommee_deux_fois(mod, monkeypatch, tmp_path, capsys):
    """Deux paires sur la meme variable feraient gagner la derniere en silence."""
    _wire(mod, monkeypatch, _vault(tmp_path, [("github ai-01", "", "a")]))
    monkeypatch.setattr(mod.subprocess, "run", _bombe)
    assert mod.cmd_run(_args_run(["X=github ai-01", "X=github ai-01"],
                                 ["--", "true"])) == mod.EXIT_DEFECT
    assert "deux fois" in capsys.readouterr().err


def test_run_refuse_une_entree_absente_sans_lancer_la_commande(mod, monkeypatch, tmp_path, capsys):
    _wire(mod, monkeypatch, _vault(tmp_path))
    monkeypatch.setattr(mod.subprocess, "run", _bombe)
    assert mod.cmd_run(_args_run(["X=inexistante"], ["--", "true"])) == mod.EXIT_DEFECT
    assert "absente" in capsys.readouterr().err


def test_run_refuse_une_entree_sans_valeur(mod, monkeypatch, tmp_path, capsys):
    _wire(mod, monkeypatch, _vault(tmp_path, [("vide", "", "")]))
    monkeypatch.setattr(mod.subprocess, "run", _bombe)
    assert mod.cmd_run(_args_run(["X=vide"], ["--", "true"])) == mod.EXIT_DEFECT
    assert "vide" in capsys.readouterr().err


def test_run_n_injecte_que_les_variables_nommees(mod, monkeypatch, tmp_path, capsys):
    """Le coeur de `run` : nommer une entree ne doit pas verser les autres."""
    _wire(mod, monkeypatch, _vault(tmp_path, [
        ("github ai-01", "myia-ai-01", "jeton-nomme"),
        ("github po-2024", "myia-po-2024", "jeton-non-nomme"),
    ]))
    code = (
        "import os, sys;"
        "sys.exit(0 if os.environ.get('NOMME') == 'jeton-nomme'"
        " and 'NON_NOMME' not in os.environ else 9)"
    )
    rc = mod.cmd_run(_args_run(["NOMME=github ai-01"], ["--", sys.executable, "-c", code]))
    assert rc == mod.EXIT_OK, capsys.readouterr().err


def test_run_transmet_le_code_de_retour_du_fils(mod, monkeypatch, tmp_path):
    _wire(mod, monkeypatch, _vault(tmp_path, [("github ai-01", "", "valeur")]))
    rc = mod.cmd_run(_args_run(["NOMME=github ai-01"],
                               ["--", sys.executable, "-c", "import sys; sys.exit(7)"]))
    assert rc == 7


def test_run_n_imprime_jamais_la_valeur(mod, monkeypatch, tmp_path, capsys):
    _wire(mod, monkeypatch, _vault(tmp_path, [("github ai-01", "", "valeur-secrete-xyz")]))
    mod.cmd_run(_args_run(["NOMME=github ai-01"],
                          ["--", sys.executable, "-c", "pass"]))
    sortie = capsys.readouterr()
    assert "valeur-secrete-xyz" not in sortie.out
    assert "valeur-secrete-xyz" not in sortie.err


def test_run_accepte_la_commande_sans_separateur(mod, monkeypatch, tmp_path):
    """`argparse.REMAINDER` conserve le `--` quand il est present, et l'omet
    quand il ne l'est pas : les deux formes doivent lancer la meme commande."""
    _wire(mod, monkeypatch, _vault(tmp_path, [("github ai-01", "", "valeur")]))
    rc = mod.cmd_run(_args_run(["NOMME=github ai-01"],
                               [sys.executable, "-c", "import sys; sys.exit(4)"]))
    assert rc == 4
