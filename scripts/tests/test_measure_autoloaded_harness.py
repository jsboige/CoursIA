"""Controles de `scripts/audit/measure_autoloaded_harness.py` (#15204).

Le chiffre que rend cet organe depend entierement d'UN predicat : « ce fichier
porte-t-il un frontmatter `paths:` ? ». Les deux facons de se tromper n'ont pas
la meme visibilite :

- **sur-detecter** (lire un `paths:` du corps comme un gate) fait DISPARAITRE une
  regle du total. Le chiffre baisse, il a l'air meilleur, et personne ne le voit.
- **sous-detecter** (rater un vrai frontmatter) fait remonter le total. Le chiffre
  monte, on cherche pourquoi.

C'est donc la premiere qui doit etre testee en priorite : un predicat trop
permissif rendrait « objectif atteint » un harnais inchange.

L'organe porte deja son propre jeu de controles (`CONTROL_CASES` / `--self-check`,
#11554). Ce fichier ne le recopie pas : il le **cable dans pytest** (premier test),
puis ajoute ce que ce jeu ne couvre pas -- l'arithmetique du remede, les surfaces
machine, et le cablage CLI ajoute par #15204.
"""

from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
_MODULE_PATH = _REPO / "scripts" / "audit" / "measure_autoloaded_harness.py"


def _load():
    spec = importlib.util.spec_from_file_location("measure_autoloaded_harness",
                                                  _MODULE_PATH)
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


mah = _load()


def _arbre(root: Path, cible: str, autre: str) -> Path:
    """Un depot minimal : CLAUDE.md + deux regles."""
    (root / ".claude" / "rules").mkdir(parents=True)
    (root / "CLAUDE.md").write_text("# projet\n", encoding="utf-8")
    (root / ".claude" / "rules" / "autre.md").write_text(autre, encoding="utf-8")
    (root / ".claude" / "rules" / "cible.md").write_text(cible, encoding="utf-8")
    return root


# --- l'instrument se valide d'abord lui-meme ---------------------------------


def test_self_check_de_lorgane_passe():
    """Cable `--self-check` dans pytest plutot que de recopier ses cas.

    Les deux faux negatifs d'un `head -5 | grep '^paths:'` y sont deja ecrits ;
    les dupliquer ici les ferait diverger en silence a la premiere retouche.
    """
    assert mah.self_check() == 0


# --- sur-detection : la direction dangereuse ---------------------------------


def test_paths_en_prose_nest_pas_un_gate():
    assert mah.is_path_gated("# Titre\n\nElle vise `paths: piege/**` en prose.\n") is False


def test_delimiteur_pas_en_premiere_ligne_nest_pas_un_frontmatter():
    """Un bloc `---` precede de quoi que ce soit n'ouvre pas de frontmatter.

    C'est ce qui empeche un exemple de frontmatter CITE dans une regle (le cas
    de `lane-claim-protocol`, qui documente la clause `paths:`) de faire
    disparaitre la regle du total.
    """
    assert mah.is_path_gated("\n---\npaths: a/**\n---\n\n# X\n") is False
    assert mah.is_path_gated("# X\n\n---\npaths: a/**\n---\n") is False


def test_frontmatter_ferme_avant_paths_nest_pas_un_gate():
    assert mah.is_path_gated("---\ndescription: x\n---\n\npaths: a/**\n") is False


# --- sous-detection ----------------------------------------------------------


def test_frontmatter_accolades_quote_est_detecte():
    assert mah.is_path_gated('---\npaths: "{**/*.py,**/*.ipynb}"\n---\n\n# X\n') is True


def test_frontmatter_avec_autres_cles_avant_est_detecte():
    assert mah.is_path_gated("---\ndescription: x\npaths: docs/**\n---\n\n# X\n") is True


# --- controle d'ARITHMETIQUE : gater deplace, ne supprime pas -----------------


def test_gater_une_regle_la_sort_du_total_sans_la_perdre(tmp_path):
    """Controle positif du REMEDE lui-meme, pas seulement du diagnostic.

    Deux arbres identiques a un frontmatter pres : le total auto-charge doit
    baisser d'exactement la taille du fichier gate, et ce fichier doit se
    retrouver dans `path_gated_rules` -- jamais disparaitre des deux.
    """
    corps = "# Regle\n\n" + "x" * 500 + "\n"
    gate = "---\npaths: MyIA.AI.Notebooks/**/*.ipynb\n---\n\n"

    avant = _arbre(tmp_path / "avant", corps, corps)
    apres = _arbre(tmp_path / "apres", gate + corps, corps)

    a = mah.measure(avant)
    b = mah.measure(apres)

    assert "cible.md" in {e["name"] for e in a["autoloaded_rules"]}
    assert "cible.md" not in {e["name"] for e in b["autoloaded_rules"]}, \
        "gatee : elle sort du chemin auto-charge"
    assert "cible.md" in {e["name"] for e in b["path_gated_rules"]}, \
        "gatee != supprimee : elle doit rester listee"
    assert not a["path_gated_rules"]

    # La reference est la taille NORMALISEE-LF, pas `stat().st_size` : l'organe
    # lit par `read_text` (traduction universelle des fins de ligne) et par
    # `git show` (qui n'emet jamais de CRLF). Il mesure donc le blob git, pas
    # l'empreinte disque -- cf test_meme_total_en_lf_et_en_crlf ci-dessous.
    taille_ungatee = len(corps.encode("utf-8"))
    taille_gatee = next(e["bytes"] for e in b["path_gated_rules"]
                        if e["name"] == "cible.md")
    assert a["autoloaded_total_bytes"] - b["autoloaded_total_bytes"] == taille_ungatee, \
        "le total baisse d'exactement le fichier sorti"
    assert taille_gatee > taille_ungatee, "le fichier gate porte son frontmatter en plus"
    assert b["all_rules_bytes"] > a["all_rules_bytes"], \
        "rien n'a ete retire du depot : le brut monte du poids du frontmatter"


def test_meme_total_en_lf_et_en_crlf(tmp_path):
    """Le total ne doit pas dependre de la fin de ligne du checkout.

    Un depot clone avec `core.autocrlf=true` porte des CRLF sur disque ; le meme
    contenu mesure alors ~1 octet de plus par ligne. Si l'organe comptait
    l'empreinte disque, deux machines rendraient deux totaux differents pour le
    MEME `main`, et l'ecart (~3 % sur un corpus de prose) se lirait comme une
    derive du harnais. C'est aussi ce qui rend une mesure `--ref` comparable a
    une mesure d'arbre de travail : `git show` n'emet jamais de CRLF.
    """
    corps = "# Regle\n\n" + "ligne\n" * 40

    lf = tmp_path / "lf"
    (lf / ".claude" / "rules").mkdir(parents=True)
    (lf / "CLAUDE.md").write_bytes(b"# projet\n")
    (lf / ".claude" / "rules" / "r.md").write_bytes(corps.encode("utf-8"))

    crlf = tmp_path / "crlf"
    (crlf / ".claude" / "rules").mkdir(parents=True)
    (crlf / "CLAUDE.md").write_bytes(b"# projet\r\n")
    (crlf / ".claude" / "rules" / "r.md").write_bytes(
        corps.replace("\n", "\r\n").encode("utf-8"))

    # Controle positif de la fixture : sans normalisation, les deux DIFFERENT.
    taille_lf = (lf / ".claude" / "rules" / "r.md").stat().st_size
    taille_crlf = (crlf / ".claude" / "rules" / "r.md").stat().st_size
    assert taille_crlf > taille_lf, "fixture inerte : le CRLF n'a pas ete ecrit"

    assert (mah.measure(lf)["autoloaded_total_bytes"]
            == mah.measure(crlf)["autoloaded_total_bytes"])


def test_repo_reel_les_regles_gatees_declarent_toutes_un_glob():
    """Sur le depot lui-meme : aucune regle gatee ne porte un `paths:` vide.

    Une clause vide se lit comme un gate et n'attrape rien -- la regle devient
    invisible en permanence. C'est le mode de defaillance de la clause `paths:`
    des claims de lane (cf lane-claim-protocol), transpose au harnais.
    """
    vides = []
    for f in sorted((_REPO / ".claude" / "rules").glob("*.md")):
        text = f.read_text(encoding="utf-8", errors="replace")
        if not mah.is_path_gated(text):
            continue
        clause = ""
        for line in text.splitlines()[1:]:
            if line.strip() == "---":
                break
            if line.startswith("paths:"):
                clause = line[len("paths:"):]
                break
        if not clause.strip().strip('"').strip("'").strip():
            vides.append(f.name)
    assert not vides, "clause paths: vide sur %s" % vides


# --- surfaces machine : une absence se DIT, elle ne se compte pas zero --------


def test_surface_machine_absente_est_rendue_manquante_pas_zero(tmp_path):
    """« Une mesure vide n'est pas une mesure a zero », par surface.

    Un MEMORY.md introuvable doit apparaitre dans `missing`, jamais comme une
    entree de 0 octet : un total qui absorbe silencieusement 24 ko manquants est
    rassurant et faux.
    """
    absent = tmp_path / "nexiste-pas" / "MEMORY.md"
    entries, missing = mah.machine_surfaces(_REPO, memory_file=absent)
    assert str(absent) in {m["path"] for m in missing}
    assert str(absent) not in {e["path"] for e in entries}
    assert all(e["bytes"] > 0 for e in entries), \
        "une entree comptee est une surface reellement lue"


def test_root_relatif_est_resolu_avant_slug_memoire(tmp_path, monkeypatch):
    """Le slug mémoire dépend de la racine absolue, jamais de ``Path('.')``."""
    repo = tmp_path / "CoursIA"
    repo.mkdir()
    home = tmp_path / "home"
    drive = repo.resolve().drive[:1].lower()
    expected = (home / ".claude" / "projects" / (drive + "--CoursIA")
                / "memory" / "MEMORY.md")
    expected.parent.mkdir(parents=True)
    expected.write_text("# mémoire\n", encoding="utf-8")
    (home / ".claude" / "CLAUDE.md").write_text("# global\n", encoding="utf-8")
    (home / ".claude" / "rules").mkdir()
    monkeypatch.setenv("HOME", str(home))
    monkeypatch.setattr(mah.os.path, "expanduser", lambda value: str(home))
    monkeypatch.chdir(repo)

    entries, missing = mah.machine_surfaces(Path("."))

    assert not missing
    assert str(expected) in {e["path"] for e in entries}


def test_mesure_complete_reflete_les_surfaces_manquantes(tmp_path):
    root = _arbre(tmp_path / "repo", "# cible\n", "# autre\n")
    result = mah.measure(
        root,
        machine=True,
        memory_file=tmp_path / "absent" / "MEMORY.md",
    )
    assert result["measurement_complete"] is False
    assert result["machine_surfaces_missing"]


# --- cablage CLI (#15204) : ratio calibre, budget en tokens -------------------


def _cli(*args, root=None, env=None):
    cmd = [sys.executable, str(_MODULE_PATH), "--root", str(root or _REPO), *args]
    return subprocess.run(cmd, capture_output=True, text=True,
                          encoding="utf-8", errors="replace", env=env)


def test_json_expose_le_ratio_et_dit_que_les_tokens_sont_DERIVES():
    """Le compte de tokens est une DIVISION, pas une tokenisation.

    Le JSON doit le dire, sinon un lecteur ulterieur citera « 85,4k tokens »
    comme une mesure produite par un tokenizer.
    """
    r = _cli("--json")
    assert r.returncode == 0, r.stderr
    m = json.loads(r.stdout)
    assert m["tokens_are_derived_not_tokenized"] is True
    assert m["ratio_bytes_per_token"] == pytest.approx(mah.DEFAULT_RATIO)
    assert m["autoloaded_total_tokens_derived"] == round(
        m["autoloaded_total_bytes"] / m["ratio_bytes_per_token"])


def test_budget_tokens_rougit_au_dessus_et_passe_en_dessous():
    """Jumeau de `--max-bytes` dans l'unite du mandat (« redescendre sous 70k »).

    Controle des DEUX cotes : un garde qui ne rougit jamais et un garde qui
    rougit toujours rendent le meme service, c'est-a-dire aucun.
    """
    assert _cli("--budget-tokens", "1").returncode == 1
    assert _cli("--budget-tokens", "10000000").returncode == 0


def test_budget_refuse_de_certifier_une_mesure_machine_incomplete(tmp_path):
    root = _arbre(tmp_path / "repo", "# cible\n", "# autre\n")
    absent = tmp_path / "absent" / "MEMORY.md"
    r = _cli(
        "--with-machine",
        "--memory-file", str(absent),
        "--budget-tokens", "10000000",
        "--json",
        root=root,
    )
    assert r.returncode == 2
    assert json.loads(r.stdout)["measurement_complete"] is False
    assert "MESURE INCOMPLETE" in r.stderr


@pytest.mark.parametrize("ratio", ["0", "-2", "nan", "inf", "-inf"])
def test_ratio_invalide_est_refuse(ratio):
    r = _cli("--ratio=" + ratio, "--json")
    assert r.returncode == 2
    assert "strictement positif et fini" in r.stderr


def test_ratio_valide_est_accepte():
    r = _cli("--ratio", "3.5", "--json")
    assert r.returncode == 0, r.stderr
    assert json.loads(r.stdout)["ratio_bytes_per_token"] == pytest.approx(3.5)


def test_cli_racine_implicite_depuis_le_depot_egale_racine_absolue():
    """L'invocation nominale sans ``--root`` mesure le dépôt courant."""
    implicit = subprocess.run(
        [sys.executable, str(_MODULE_PATH), "--json"],
        cwd=_REPO,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    absolute = _cli("--json", root=_REPO.resolve())

    assert implicit.returncode == 0, implicit.stderr
    assert absolute.returncode == 0, absolute.stderr
    assert (json.loads(implicit.stdout)["autoloaded_total_bytes"]
            == json.loads(absolute.stdout)["autoloaded_total_bytes"])


def test_meme_memoire_absente_puis_presente_encadre_un_seuil(tmp_path):
    """Une somme partielle ne passe jamais un seuil entre partiel et complet."""
    root = _arbre(tmp_path / "repo", "# cible\n", "# autre\n")
    memory = tmp_path / "machine" / "MEMORY.md"
    home = tmp_path / "home"
    (home / ".claude" / "rules").mkdir(parents=True)
    (home / ".claude" / "CLAUDE.md").write_text(
        "# global\n", encoding="utf-8"
    )
    env = os.environ.copy()
    env["HOME"] = str(home)
    env["USERPROFILE"] = str(home)

    partial = _cli(
        "--with-machine", "--memory-file", str(memory), "--json",
        root=root, env=env,
    )
    assert partial.returncode == 0, partial.stderr
    partial_data = json.loads(partial.stdout)
    assert partial_data["measurement_complete"] is False

    memory.parent.mkdir(parents=True)
    memory.write_text("# mémoire\n" + "x" * 1000, encoding="utf-8")
    complete = _cli(
        "--with-machine", "--memory-file", str(memory), "--json",
        root=root, env=env,
    )
    assert complete.returncode == 0, complete.stderr
    complete_data = json.loads(complete.stdout)
    assert complete_data["measurement_complete"] is True
    assert (complete_data["autoloaded_total_bytes"]
            > partial_data["autoloaded_total_bytes"])

    threshold = (partial_data["autoloaded_total_bytes"]
                 + complete_data["autoloaded_total_bytes"]) // 2

    memory.unlink()
    missing_guard = _cli(
        "--with-machine", "--memory-file", str(memory),
        "--max-bytes", str(threshold), "--json", root=root, env=env,
    )
    assert missing_guard.returncode == 2
    assert "MESURE INCOMPLETE" in missing_guard.stderr

    memory.write_text("# mémoire\n" + "x" * 1000, encoding="utf-8")
    complete_guard = _cli(
        "--with-machine", "--memory-file", str(memory),
        "--max-bytes", str(threshold), "--json", root=root, env=env,
    )
    assert complete_guard.returncode == 1
    assert "DEPASSEMENT" in complete_guard.stderr


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(pytest.main([__file__, "-v"]))
