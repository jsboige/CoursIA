"""Test du contrat de la batterie de sondes du run instrumente (panel persona).

Ce que ce test prouve
---------------------
  1. La batterie est **fixe** : son empreinte est stable, et elle **change**
     des qu'un prompt est ajoute ou modifie (controle de sensibilite).
  2. `echantillonner` lit la position demandee : `last` prend la derniere
     ligne, `mean` moyenne toutes les positions ; une position inconnue est
     refusee, et un `forward` au mauvais rang est refuse aussi.
  3. Le `.npz` porte les **declarations** exigees par le §6 du
     pre-enregistrement du panel : couche, position, graine de generation,
     empreinte de la batterie.
  4. Le manifeste porte les declarations du run (modele, bras, graine, etape,
     couche, position) et l'empreinte de la batterie.
  5. **Controle positif** : changer l'activation d'un prompt change le SHA-256
     de ce vecteur ET le SHA-256 du `.npz` -- le manifeste **detecte** la
     derive au lieu de la cacher.
  6. `verifier_racine_stable` **refuse** une racine sous le repertoire
     temporaire du systeme (un artefact ecrit la ne survit pas au run) et
     accepte toute autre racine.
  7. `chemin_artefact` est **stable** (meme entree, meme chemin) et porte le
     bras, la graine et le pas : deux checkpoints ne s'ecrasent pas.
  8. `forward_transformers` lit la **couche demandee** : un faux modele
     transformers (aucun torch, aucun GPU) suffit, et deux couches differentes
     donnent deux lectures differentes.
  9. `charger_batterie` lit une batterie depuis un JSON et en restitue la
     **graine** : un run instrumente lit sa batterie sur disque, il ne la
     reconstruit pas.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
import pytest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))

import ict25a_probe_battery as probe  # noqa: E402


def _forward_factice(valeur: float = 1.0):
    """`forward` deterministe : chaque prompt rend [[0], [valeur]]."""
    def forward(prompt: str) -> np.ndarray:
        return np.array([[0.0], [valeur]], dtype=np.float64)
    return forward


def _racine_stable(tmp_path, monkeypatch) -> Path:
    """Racine hors du temporaire *simule* : le test controle le temporaire."""
    faux_temp = tmp_path / "temp-systeme"
    faux_temp.mkdir(parents=True, exist_ok=True)
    monkeypatch.setattr(probe.tempfile, "gettempdir", lambda: str(faux_temp))
    racine = tmp_path / "worktrees" / "ict25a"
    racine.mkdir(parents=True, exist_ok=True)
    return racine


def test_la_batterie_est_fixe_et_sensible():
    empreinte = probe.empreinte_batterie()
    assert empreinte == probe.empreinte_batterie()
    modifiee = probe.BATTERIE + ({"id": "p06", "prompt": "Combien font 3+3 ?"},)
    assert probe.empreinte_batterie(modifiee) != empreinte


def test_position_last_et_mean():
    echantillons = probe.echantillonner(_forward_factice(3.0), position="last")
    assert set(echantillons) == {p["id"] for p in probe.BATTERIE}
    assert np.allclose(echantillons["p01"], [3.0])
    moyennes = probe.echantillonner(_forward_factice(3.0), position="mean")
    assert np.allclose(moyennes["p01"], [1.5])


def test_position_inconnue_refusee():
    with pytest.raises(ValueError):
        probe.echantillonner(_forward_factice(), position="milieu")


def test_forward_au_mauvais_rang_refuse():
    with pytest.raises(ValueError):
        probe.echantillonner(lambda p: np.zeros(4), position="last")


def test_npz_porte_les_declarations(tmp_path):
    racine = tmp_path / "artefacts"
    racine.mkdir()
    echantillons = probe.echantillonner(_forward_factice())
    chemin = probe.ecrire_npz(racine / "echantillon.npz", echantillons,
                               couche="18", position="last")
    with np.load(str(chemin)) as data:
        assert str(data["__couche__"]) == "18"
        assert str(data["__position__"]) == "last"
        assert int(data["__graine_generation__"]) == probe.PROBE_SEED
        assert str(data["__batterie__"]) == probe.empreinte_batterie()
        assert np.allclose(data["p01"], [1.0])


def test_manifeste_porte_les_declarations_du_run(tmp_path):
    racine = tmp_path / "artefacts"
    racine.mkdir()
    echantillons = probe.echantillonner(_forward_factice())
    npz = probe.ecrire_npz(racine / "echantillon.npz", echantillons,
                            couche="18", position="last")
    manifeste = probe.ecrire_manifeste(
        racine / "echantillon.manifeste.json", echantillons, npz,
        bras="N", graine=7, etape=120, modele="Qwen/Qwen3.5-2B-Base",
        couche="18", position="last")
    charge = json.loads(manifeste.read_text(encoding="utf-8"))
    assert charge["bras"] == "N"
    assert charge["graine"] == 7
    assert charge["etape"] == 120
    assert charge["modele"] == "Qwen/Qwen3.5-2B-Base"
    assert charge["couche"] == "18"
    assert charge["position"] == "last"
    assert charge["empreinte_batterie"] == probe.empreinte_batterie()
    assert set(charge["prompts"]) == {p["id"] for p in probe.BATTERIE}
    assert len(charge["npz"]["sha256"]) == 64


def test_controle_positif_le_manifeste_detecte_la_derive(tmp_path):
    """Une activation qui change doit changer les empreintes -- sinon le
    manifeste ne prouve rien."""
    racine = tmp_path / "artefacts"
    racine.mkdir()
    prompt_p01 = probe.BATTERIE[0]["prompt"]

    def forward_avec(p01: float):
        def forward(prompt: str) -> np.ndarray:
            valeur = p01 if prompt == prompt_p01 else 1.0
            return np.array([[0.0], [valeur]], dtype=np.float64)
        return forward

    avant = probe.echantillonner(forward_avec(1.0))
    npz_a = probe.ecrire_npz(racine / "a.npz", avant, couche="18", position="last")
    charge_a = json.loads(probe.ecrire_manifeste(
        racine / "a.manifeste.json", avant, npz_a, bras="N", graine=0, etape=120,
        modele="m", couche="18", position="last").read_text(encoding="utf-8"))

    apres = probe.echantillonner(forward_avec(2.0))
    npz_b = probe.ecrire_npz(racine / "b.npz", apres, couche="18", position="last")
    charge_b = json.loads(probe.ecrire_manifeste(
        racine / "b.manifeste.json", apres, npz_b, bras="N", graine=0, etape=120,
        modele="m", couche="18", position="last").read_text(encoding="utf-8"))

    assert charge_a["prompts"]["p01"]["sha256"] != charge_b["prompts"]["p01"]["sha256"]
    assert charge_a["npz"]["sha256"] != charge_b["npz"]["sha256"]
    # ... et un vecteur inchange garde son empreinte (le manifeste ne derive pas)
    assert charge_a["prompts"]["p02"]["sha256"] == charge_b["prompts"]["p02"]["sha256"]


def test_racine_temporaire_refusee(tmp_path, monkeypatch):
    faux_temp = tmp_path / "temp-systeme"
    faux_temp.mkdir()
    monkeypatch.setattr(probe.tempfile, "gettempdir", lambda: str(faux_temp))
    with pytest.raises(ValueError):
        probe.verifier_racine_stable(faux_temp / "artefacts")


def test_racine_stable_acceptee(tmp_path, monkeypatch):
    racine = _racine_stable(tmp_path, monkeypatch)
    assert probe.verifier_racine_stable(racine) == racine.resolve()


def test_chemin_artefact_est_stable(tmp_path, monkeypatch):
    racine = _racine_stable(tmp_path, monkeypatch)
    a = probe.chemin_artefact(racine, "N", 7, 120)
    b = probe.chemin_artefact(racine, "N", 7, 120)
    c = probe.chemin_artefact(racine, "N", 7, 60)
    assert a == b
    assert a != c
    assert a.name == "ict25a_N_s7_step120.npz"
    assert probe.chemin_artefact(racine, "N", 7, 120, ".manifeste.json").name == \
        "ict25a_N_s7_step120.manifeste.json"


class _FauxTenseur:
    """Tenseur minimal : `detach().cpu().numpy()` -- comme un tenseur torch."""

    def __init__(self, valeurs):
        self._valeurs = np.asarray(valeurs, dtype=np.float64)

    def detach(self):
        return self

    def cpu(self):
        return self

    def numpy(self):
        return self._valeurs

    def __getitem__(self, indice):
        return _FauxTenseur(self._valeurs[indice])


class _FauxModele:
    """Modele transformers minimal : deux couches cachees, distinctes."""

    def __init__(self):
        self.derniere_prompt = None

    def __call__(self, **kwargs):
        prompt = kwargs["input_ids"]
        self.derniere_prompt = prompt
        # `hidden_states[i]` porte [lot, positions, dimension] comme transformers.
        couche0 = _FauxTenseur([[[0.0, 0.0], [1.0, 1.0]]])
        couche1 = _FauxTenseur([[[2.0, 2.0], [3.0, 3.0]]])
        return type("Sorties", (), {"hidden_states": (couche0, couche1)})()


class _FauxTokenizer:
    def __call__(self, prompt, return_tensors=None):
        return {"input_ids": prompt}


def test_forward_transformers_lit_la_couche_demandee():
    modele = _FauxModele()
    tokenizer = _FauxTokenizer()
    derniere = probe.forward_transformers(modele, tokenizer, "Combien font 3+4 ?")
    premiere = probe.forward_transformers(modele, tokenizer, "Combien font 3+4 ?",
                                          couche=0)
    # `hidden_states[i]` porte [lot, positions, dimension] : le forward rend la
    # couche entiere ; c'est `echantillonner` qui choisit la position lue.
    assert derniere.shape == (2, 2)
    assert np.allclose(derniere, [[2.0, 2.0], [3.0, 3.0]])
    assert np.allclose(premiere, [[0.0, 0.0], [1.0, 1.0]])
    assert modele.derniere_prompt == "Combien font 3+4 ?"


def test_forward_transformers_couche_hors_plage_refusee():
    with pytest.raises(IndexError):
        probe.forward_transformers(_FauxModele(), _FauxTokenizer(), "p", couche=5)


def test_charger_batterie_lit_le_json(tmp_path):
    fichier = tmp_path / "batterie.json"
    fichier.write_text(json.dumps({
        "seed": 4242,
        "prompts": [{"id": "q01", "prompt": "Combien font 1+1 ?"}],
    }), encoding="utf-8")
    prompts, graine = probe.charger_batterie(fichier)
    assert graine == 4242
    assert prompts == ({"id": "q01", "prompt": "Combien font 1+1 ?"},)
    # l'empreinte de la batterie lue depend de sa graine : deux batteries de
    # memes prompts mais de graines differentes ne sont pas la meme batterie
    assert probe.empreinte_batterie(prompts, graine) != \
        probe.empreinte_batterie(prompts, probe.PROBE_SEED)


def test_plan_instrumentation_vide_sans_racine():
    """Sans `--checkpoint-dir`, le plan est vide : le run garde son
    comportement d'hier (le mode par defaut n'est pas un chemin degrade)."""
    assert probe.plan_instrumentation() == {}
    assert probe.plan_instrumentation(None, None) == {}


def test_plan_instrumentation_refuse_batterie_sans_racine():
    with pytest.raises(ValueError):
        probe.plan_instrumentation(None, "batterie.json")


def test_plan_instrumentation_porte_la_batterie(tmp_path, monkeypatch):
    racine = _racine_stable(tmp_path, monkeypatch)
    plan = probe.plan_instrumentation(racine, None, save_steps=40, couche="18",
                                      position="mean")
    assert plan["checkpoint_dir"] == str(racine.resolve())
    assert plan["save_steps"] == 40
    assert plan["couche"] == "18"
    assert plan["position"] == "mean"
    assert plan["graine_batterie"] == probe.PROBE_SEED
    assert plan["empreinte_batterie"] == probe.empreinte_batterie()
    assert len(plan["batterie"]) == len(probe.BATTERIE)


def test_ecrire_batterie_puis_recharger(tmp_path, monkeypatch):
    racine = _racine_stable(tmp_path, monkeypatch)
    chemin = probe.ecrire_batterie(racine, probe.BATTERIE, probe.PROBE_SEED)
    assert chemin.name == "batterie.json"
    prompts, graine = probe.charger_batterie(chemin)
    assert graine == probe.PROBE_SEED
    assert prompts == tuple(prompt for prompt in probe.BATTERIE)


def test_le_runner_branche_le_plan_du_contrat():
    """Verification au niveau SOURCE du branchement du runner.

    Le runner importe torch/trl/peft : il ne peut pas etre importe dans un
    test CPU (ni en CI). Le controle porte donc sur le texte du runner, comme
    le fait deja `test_ict25_records.py` pour le meme runner -- c'est une
    verification de branchement, pas une verification de comportement : le
    comportement lui-meme est verifie ci-dessus, sans GPU.
    """
    source = (SCRIPTS / "ict25a_scaleup_grpo.py").read_text(encoding="utf-8")
    assert "plan_instrumentation(" in source
    assert "from ict25a_probe_battery import" in source
    assert "instr=instr" in source
    assert "_instrumenter(" in source
    assert "save_strategy=save_strategy" in source
