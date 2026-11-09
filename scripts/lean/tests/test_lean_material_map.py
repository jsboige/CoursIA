#!/usr/bin/env python3
"""Tests de la colonne « Naissance » de `docs/reference/lean-material-map.md`.

Le defaut que ce fichier surveille (#24538) : la naissance d'un lac etait lue
par `git log -1 --diff-filter=A`, c'est-a-dire le **dernier** ajout **visible**
du lakefile. Deux clones de la meme histoire n'en voient pas la meme fenetre
-- un clone tronque (shallow, greffe) ou un mass-add tardif deplace la date --
et `--check` pouvait rendre PERIMEE sur `main` pur. La colonne est desormais
**epinglee** dans `scripts/lean/lean_births.json` ; git ne sert plus que de
repli pour un lac sans epingle.

Usage :
    python -m pytest scripts/lean/tests/test_lean_material_map.py -q
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import re
import subprocess
import sys
import types
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]


def _load_module():
    """Charge l'organe par son chemin (le script vit hors du paquet)."""
    path = REPO_ROOT / "scripts" / "lean" / "lean_material_map.py"
    spec = importlib.util.spec_from_file_location("lean_material_map", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules["lean_material_map"] = module
    spec.loader.exec_module(module)
    return module


mod = _load_module()

LAC_EPINGLE = "MyIA.AI.Notebooks/SymbolicAI/Lean/GOL/conway_lean"
LAKEFILE = LAC_EPINGLE + "/lakefile.lean"
LAC_INCONNU = "MyIA.AI.Notebooks/Series/unknown_lean"


def _lignes_de_la_page() -> dict[str, str]:
    """Les couples (lac, naissance) lus dans la page generee."""
    texte = mod.PAGE.read_text(encoding="utf-8")
    out: dict[str, str] = {}
    for ligne in texte.splitlines():
        m = re.match(r"^\| `([^`]+)` \|.*\| (\d{4}-\d{2}-\d{2}) \|$", ligne.strip())
        if m:
            out[m.group(1)] = m.group(2)
    return out


def test_epingle_prime_sur_git(monkeypatch):
    """L'epingle gagne sur git : c'est elle qui rend la colonne reproductible."""
    epingles = mod._pinned_births()
    assert LAC_EPINGLE in epingles, "le lac de reference doit etre epingle"

    appels: list[tuple[str, ...]] = []

    def faux_git(*args: str) -> str:
        appels.append(args)
        return "1999-01-01\n"

    monkeypatch.setattr(mod, "_git", faux_git)
    assert mod._birth(LAC_EPINGLE, LAKEFILE) == epingles[LAC_EPINGLE]
    assert appels == [], "git ne doit pas etre interroge quand l'epingle existe"


def test_lac_non_epingle_retombe_sur_git_et_prend_le_premier_ajout(monkeypatch):
    """Sans epingle, le repli git prend le PREMIER ajout, pas le dernier.

    L'ordre rendu par git simule un clone qui voit un add ancien **et** un
    mass-add tardif : retenir le dernier est exactement le defaut de #24538.
    """
    appels: list[tuple[str, ...]] = []

    def faux_git(*args: str) -> str:
        appels.append(args)
        return "2026-05-28\n2026-10-23\n"

    monkeypatch.setattr(mod, "_git", faux_git)
    assert mod._birth(LAC_INCONNU, "x/lakefile.lean") == "2026-05-28"
    assert appels and "--reverse" in appels[0], "le repli doit demander --reverse"
    assert "-1" not in appels[0], "le dernier ajout est le defaut corrige"


def test_repli_git_sans_histoire_visible_rend_vide(monkeypatch):
    """Un clone qui ne montre aucun ajout ne fabrique pas de date."""
    monkeypatch.setattr(mod, "_git", lambda *a: "")
    assert mod._birth(LAC_INCONNU, "x/lakefile.lean") == ""


def test_epingles_illisibles_retombent_sur_git(monkeypatch, tmp_path):
    """Un fichier d'epingles absent n'empeche pas le generateur de tourner."""
    monkeypatch.setattr(mod, "BIRTHS", tmp_path / "absent.json")
    assert mod._pinned_births() == {}
    monkeypatch.setattr(mod, "_git", lambda *a: "2026-05-28\n")
    assert mod._birth(LAC_EPINGLE, LAKEFILE) == "2026-05-28"


def test_chaque_lac_de_la_page_porte_une_epingle():
    """Controle positif : aucun lac de la page sans epingle, aucune epingle orpheline.

    C'est la garde qui rend l'epinglage honnete : un lac nouveau fait echouer
    ce test tant que son epingle n'a pas ete ajoutee explicitement.
    """
    page = _lignes_de_la_page()
    assert len(page) == 41, f"la page porte {len(page)} lacs, attendu 41"

    epingles = mod._pinned_births()
    manquantes = sorted(set(page) - set(epingles))
    orphelines = sorted(set(epingles) - set(page))
    assert not manquantes, (
        f"lacs sans epingle : {manquantes} -- ajouter l'entree dans lean_births.json"
        " ; si le lac vient d'etre renomme, rekeyer l'ancienne entree (meme date,"
        " nouveau chemin)"
    )
    assert not orphelines, (
        f"epingles sans lac dans la page : {orphelines} -- un renommage de lac a"
        " probablement laisse une cle sur l'ancien chemin : rekeyer vers le chemin"
        " actuel en conservant la date"
    )


def test_les_epingles_valent_la_colonne_de_la_page():
    """L'epingle et la page disent la meme chose : c'est le contrat du generateur."""
    page = _lignes_de_la_page()
    epingles = mod._pinned_births()
    ecarts = {lac: (page[lac], epingles[lac]) for lac in page if page[lac] != epingles[lac]}
    assert not ecarts, f"ecarts page/epingle : {ecarts}"


def test_le_fichier_d_epingles_est_du_json_valide():
    """Le fichier committe est lisible et ne porte que des dates plausibles."""
    brut = json.loads(pathlib.Path(mod.BIRTHS).read_text(encoding="utf-8"))
    assert isinstance(brut.get("lakes"), dict) and brut["lakes"]
    for lac, date in brut["lakes"].items():
        assert re.fullmatch(r"\d{4}-\d{2}-\d{2}", date), f"date invalide pour {lac} : {date}"


# --- La couverture ne doit jamais etre avalee --------------------------------
#
# Le defaut mesure le 2026-11-07 : `_coverage()` rendait `{}` quand l'organe
# de couverture ne repondait pas, et le seuil de 300 s etait SOUS la duree
# reelle de cet organe (634 s puis 658 s sur ai-01). L'echec etait donc
# deterministe, et il rendait une page FAUSSE (`hors matrice` pour tous les
# lacs) sans lever aucune erreur : le `--check` rendait « A JOUR » sur cette
# page fausse, et le `--write` ecracait une page correcte par une page fausse.
#
# Ces tests verrouillent les trois proprietes : le budget domine la duree
# reelle, l'echec est remonte, et rien n'est ecrit quand la mesure est
# impossible.


def test_le_budget_de_couverture_domeine_la_duree_reelle_mesuree():
    """Le budget doit etre SUPERIEUR a la duree reelle de l'organe amont.

    Mesures du 2026-11-07 sur ai-01 : 634 s et 658 s (deux passes). Le seuil
    d'avant (300 s) etait sous les deux -- l'echec avalait donc toujours
    lieu, et toujours en silence."""
    assert mod.COVERAGE_TIMEOUT >= 660, (
        "le budget (%d s) est sous la duree reelle mesuree (634-658 s) : "
        "l'echec de l'organe amont sera avale" % mod.COVERAGE_TIMEOUT)


def _faux_subprocess(*, rc=0, stdout="", raise_timeout=False):
    """Un `subprocess` de substitution : seul `run` est appele."""
    def run(*args, **kwargs):
        if raise_timeout:
            raise subprocess.TimeoutExpired(cmd="check_axiom_gate_coverage.py",
                                            timeout=1)
        return types.SimpleNamespace(returncode=rc, stdout=stdout, stderr="")
    return types.SimpleNamespace(
        run=run,
        TimeoutExpired=subprocess.TimeoutExpired,
        SubprocessError=subprocess.SubprocessError,
        OSError=OSError,
    )


def test_un_timeout_de_couverture_est_remonte_et_non_avalé(monkeypatch):
    """Le timeout de l'organe amont doit REMONTER, pas rendre un `{}`."""
    monkeypatch.setattr(mod, "subprocess",
                        _faux_subprocess(raise_timeout=True))
    try:
        mod._coverage()
    except mod.CoverageUnavailable as exc:
        assert "timeout" in str(exc)
    else:
        raise AssertionError("un timeout avalé rendrait une page fausse")


def test_un_rc_non_nul_de_couverture_est_remonte(monkeypatch):
    """Un organe amont en erreur n'est pas un verdict neutre."""
    monkeypatch.setattr(mod, "subprocess", _faux_subprocess(rc=1))
    try:
        mod._coverage()
    except mod.CoverageUnavailable as exc:
        assert "rc=1" in str(exc)
    else:
        raise AssertionError("un rc non nul avalé rendrait une page fausse")


def test_une_sortie_de_couverture_illisible_est_remontee(monkeypatch):
    """Une sortie vide ou illisible n'est pas une mesure."""
    monkeypatch.setattr(mod, "subprocess", _faux_subprocess(rc=0, stdout=""))
    try:
        mod._coverage()
    except mod.CoverageUnavailable:
        pass
    else:
        raise AssertionError("une sortie illisible avalée rendrait une page fausse")


def test_le_generateur_refuse_d_ecrire_la_page_quand_la_mesure_est_impossible(
        monkeypatch, tmp_path):
    """Le geste interdit : `--write` sur une mesure impossible.

    La page sur disque doit rester INTACTE : c'est elle qui est saine. La
    regeneree porterait une couverture degradee (`hors matrice` partout)."""
    page = tmp_path / "lean-material-map.md"
    page.write_text("page d'origine\n", encoding="utf-8")

    def collect_qui_echoue(*args, **kwargs):
        raise mod.CoverageUnavailable("timeout de 1800 s sur l'organe amont")

    monkeypatch.setattr(mod, "PAGE", page)
    monkeypatch.setattr(mod, "collect", collect_qui_echoue)
    rc = mod.main(["--write"])
    assert rc == mod.UNMEASURABLE_RC
    assert rc != 0, "une mesure impossible ne peut pas rendre 0"
    assert page.read_text(encoding="utf-8") == "page d'origine\n", (
        "la page sur disque a ete touchee alors que la mesure etait impossible")


def test_le_code_de_sortie_de_mesure_impossible_est_different_de_la_divergece():
    """`1` = la page diverge ; `2` = la mesure est impossible. Les deux ne se
    confondent pas : le geste de reparation n'est pas le meme."""
    assert mod.UNMEASURABLE_RC == 2
    assert mod.UNMEASURABLE_RC != 1
