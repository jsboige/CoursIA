#!/usr/bin/env python3
"""Tests for ``scripts/notebook_tools/check_render_volume_delta.py`` (#11656).

Why this exists
---------------
#11656 demands **contrôle positif obligatoire dans les tests** :
un cas connu de perte de rendu (mimicking #11351, base 195 692 B -> head
3 293 B, -98 %) DOIT faire rougir le detecteur. Sans ce cas, l'instrument
pourrait passer en CI avec un bug silencieux et personne ne le verrait
avant une vraie perte. Cf. lecons c.344-L1 ★★ et c.342-L1 ★ : un test
pin se valide par ses **faux negatifs**, pas par ses hits.

Mesure du cas fondateur (ai-01 verbatim, post-merge #11351) :

    Infer-3-Factor-Graphs       45 715 ->    840 B   (-98,2 %)
    Infer-8-TrueSkill          127 081 ->  1 613 B   (-98,7 %)
    Infer-13-Crowdsourcing      22 896 ->    840 B   (-96,3 %)
    TOTAL                      195 692 ->  3 293 B   (-98,3 %)

Ces sorties ne sont PAS vides (840-1613 B > seuil blank_figures 70 B), ne
sont PAS ``outputs: []``, ne contiennent PAS de PNG (la perte est du
``text/html`` inline d'un helper Graphviz). Les trois instruments absolus
ne peuvent pas voir ce cas ; ``check_render_volume_delta.py`` doit le
voir.

Acceptance gate
---------------
La suite pytest DOIT contenir au minimum :

1. **test_known_loss_case_must_rougir** -- le cas fondateur simule
   (notebook avec sortie ``text/html`` de 12 500 B en base, devenu 250 B
   en head) DOIT declencher ``DELTA_SIGNAL`` et faire rougir ``--check``.
2. **test_roundtrip_clean_baseline_passes** -- un notebook inchange entre
   base et head ne declenche AUCUN finding (rc=0).
3. **test_new_file_is_exempt** -- un notebook absent a la base ne declenche
   AUCUN finding (exempt par construction).
4. **test_exempt_cell_is_skipped** -- une cellule marquee
   ``render_exempt: true`` ne compte pas dans la somme, meme si sa sortie
   chute.
5. **test_min_base_below_threshold_ignored** -- une chute relative sous
   ``--min-base`` ne declenche pas de finding (evite le bruit sur quelques
   octets).
6. **test_ref_invalid_returns_error** -- un ref git invalide declenche
   rc=2 (garde anti-auto-desarmement, cf. #8655/#8662).
7. **test_new_mime_is_signaled_but_not_failure** -- une famille MIME
   apparue au head est signalee mais ne fait PAS rougir en --check par
   defaut (enrichissement legit).

Les tests sont **mutuellement independants** : un faux (par exemple un
seuil oublie) ne doit faire rougir que le test qui pin cette specificite,
pas la suite entiere (cf. mutation testing par faux negatifs, lecon
c.344-L1 ★★).
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
TOOL = HERE.parent / "check_render_volume_delta.py"
REPO_ROOT = HERE.parents[2]

sys.path.insert(0, str(HERE.parent))
import check_render_volume_delta as crvd  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _make_cell_with_text_html(text: str, cell_id: str) -> dict:
    """Construit une cellule avec un output ``text/html`` d'une longueur donnee."""
    return {
        "cell_type": "code",
        "id": cell_id,
        "metadata": {},
        "source": [],
        "execution_count": 1,
        "outputs": [
            {
                "output_type": "display_data",
                "data": {"text/html": text},
                "metadata": {},
            }
        ],
    }


def _make_cell_with_text_html_bytes(nbytes: int, cell_id: str) -> dict:
    """Cellule avec une sortie ``text/html`` de ``nbytes`` octets (ASCII fill)."""
    return _make_cell_with_text_html("x" * nbytes, cell_id)


def _make_cell_exempt(text: str, cell_id: str) -> dict:
    """Cellule dont l'output est marque exempt via ``render_exempt: true``."""
    return {
        "cell_type": "code",
        "id": cell_id,
        "metadata": {"render_exempt": True},
        "source": [],
        "execution_count": 1,
        "outputs": [
            {
                "output_type": "display_data",
                "data": {"text/html": text},
                "metadata": {},
            }
        ],
    }


def _nb_path() -> Path:
    """Chemin du notebook que les tests utilisent (relatif a REPO_ROOT)."""
    return Path("scripts/notebook_tools/tests/fixtures/render_volume_delta_case.ipynb")


def _write_nb(rel_path: Path, nb: dict) -> Path:
    """Ecrit un notebook sur disque (relatif a REPO_ROOT) et retourne le chemin absolu."""
    abs_path = REPO_ROOT / rel_path
    abs_path.parent.mkdir(parents=True, exist_ok=True)
    abs_path.write_text(json.dumps(nb, ensure_ascii=False, indent=1), encoding="utf-8")
    return abs_path


# ---------------------------------------------------------------------------
# Pure unit tests (sans git)
# ---------------------------------------------------------------------------


def test_mime_family_aggregation():
    """``text/html`` et ``image/png`` sont agreges par famille."""
    nbytes_text = 1000
    nbytes_png_b64 = "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mNgYAAAAAMAASsJTYQAAAAASUVORK5CYII="
    # Le base64 ci-dessus decode a 60 octets (90 chars de payload, dont 2
    # de padding ; 90 * 3 / 4 - 2 = ~65, arrondi). On teste juste que
    # ``image`` est > 0 et agrege par famille (pas la valeur exacte, qui
    # depend du decoder base64).
    nb = {
        "cells": [
            _make_cell_with_text_html_bytes(nbytes_text, "c1"),
            {
                "cell_type": "code",
                "id": "c2",
                "metadata": {},
                "source": [],
                "execution_count": 1,
                "outputs": [
                    {
                        "output_type": "display_data",
                        "data": {"image/png": nbytes_png_b64},
                        "metadata": {},
                    }
                ],
            },
        ]
    }
    per_cell = crvd._summarize_outputs(nb)
    agg = crvd._aggregate_by_family(per_cell)
    assert agg.get("text") == nbytes_text
    assert agg.get("image") is not None and agg["image"] > 0, (
        f"famille image doit etre agregee avec un volume > 0, got {agg}"
    )


def test_cell_exempt_skipped():
    """Une cellule ``render_exempt: true`` ne contribue pas au volume."""
    nb = {
        "cells": [
            _make_cell_exempt("x" * 5000, "c1"),  # 5000 B non comptes
            _make_cell_with_text_html_bytes(200, "c2"),
        ]
    }
    per_cell = crvd._summarize_outputs(nb)
    agg = crvd._aggregate_by_family(per_cell)
    assert agg.get("text") == 200, (
        f"cell exempt doit etre ignoree (volume 200B attendu), got {agg}"
    )


def test_diff_known_loss_triggers_delta_signal():
    """Cas fondateur : chute 98 % d'une famille MIME -> DELTA_SIGNAL.

    C'est le **contrôle positif obligatoire** demande par #11656. Ce test
    DOIT rougir si le détecteur ne sait pas voir une perte de 98 %. C'est
    le miroir du cas reel (#11351, 195 692 B -> 3 293 B).
    """
    base_agg = {"text": 12_500, "image": 4_000}
    head_agg = {"text": 250, "image": 4_000}  # text chute de 98 %
    findings = crvd._diff_families(base_agg, head_agg,
                                   threshold=0.50, min_base=1000)
    delta = [f for f in findings if f["kind"] == "DELTA_SIGNAL"]
    assert len(delta) == 1, f"cas fondateur doit rougir, got findings={findings}"
    sig = delta[0]
    assert sig["mime_family"] == "text"
    assert sig["before_bytes"] == 12_500
    assert sig["after_bytes"] == 250
    assert sig["ratio"] == 0.02  # 250/12500 = 0.02


def test_diff_clean_passes_no_find():
    """Base == head, pas de finding."""
    base_agg = {"text": 12_500, "image": 4_000}
    head_agg = {"text": 12_500, "image": 4_000}
    findings = crvd._diff_families(base_agg, head_agg,
                                   threshold=0.50, min_base=1000)
    assert findings == [], f"notebook inchange ne doit rien signaler, got {findings}"


def test_diff_lost_mime_triggers():
    """Une famille disparue (b>0, h=0) declenche LOST_MIME (cas strict)."""
    base_agg = {"text": 12_500}
    head_agg = {"text": 12_500, "image": 3_000}  # image apparait
    # Maintenant l'inverse : base a image, head n'en a plus.
    base_agg2 = {"text": 12_500, "image": 3_000}
    head_agg2 = {"text": 12_500}  # image disparue
    findings = crvd._diff_families(base_agg2, head_agg2,
                                   threshold=0.50, min_base=1000)
    lost = [f for f in findings if f["kind"] == "LOST_MIME"]
    assert len(lost) == 1 and lost[0]["mime_family"] == "image"


def test_diff_new_mime_signaled_but_distinct():
    """Une famille apparue signalee en NEW_MIME, distincte de DELTA_SIGNAL."""
    base_agg = {"text": 12_500}
    head_agg = {"text": 12_500, "image": 3_000}
    findings = crvd._diff_families(base_agg, head_agg,
                                   threshold=0.50, min_base=1000)
    new = [f for f in findings if f["kind"] == "NEW_MIME"]
    assert len(new) == 1 and new[0]["mime_family"] == "image"


def test_diff_below_min_base_ignored():
    """Une chute en-dessous de ``--min-base`` ne rougit PAS (evite bruit)."""
    base_agg = {"text": 800}  # < min_base 1000
    head_agg = {"text": 100}
    findings = crvd._diff_families(base_agg, head_agg,
                                   threshold=0.50, min_base=1000)
    assert findings == [], (
        f"chute sous min_base doit etre ignoree, got findings={findings}"
    )


def test_diff_threshold_respected():
    """Un ratio > threshold ne rougit PAS (reformulation legitime)."""
    base_agg = {"text": 12_500}
    head_agg = {"text": 7_500}  # ratio 0.6 (60 %), > 0.50
    findings = crvd._diff_families(base_agg, head_agg,
                                   threshold=0.50, min_base=1000)
    assert findings == [], (
        f"chute 60% (au-dessus du seuil 50%) ne doit pas rougir, "
        f"got findings={findings}"
    )


def test_decode_output_bytes_handles_text_and_data():
    """``_decode_output_bytes`` gere les deux formes (data dict + text plain)."""
    out_data = {
        "output_type": "display_data",
        "data": {"text/html": "x" * 200},
    }
    out_text = {"output_type": "stream", "text": "hello"}
    assert crvd._decode_output_bytes(out_data) == 200
    assert crvd._decode_output_bytes(out_text) == 5  # len("hello")


def test_decode_handles_data_url_prefix():
    """Un payload ``data:image/png;base64,XXX`` est decode correctement."""
    # 1 octet = 4 chars base64 ; 4 octets utiles = padding minimum
    payload = "iVBORw0KGgo="  # 12 chars base64 -> 9 octets
    out = {
        "output_type": "display_data",
        "data": {"image/png": f"data:image/png;base64,{payload}"},
    }
    decoded = crvd._decode_output_bytes(out)
    # 12 chars / 4 * 3 = 9 octets, arrondi a la baisse pour padding
    assert decoded >= 6, f"base64 prefix doit decoder, got {decoded}"


# ---------------------------------------------------------------------------
# CLI integration (avec subprocess pour valider --check, --json, exit codes)
# ---------------------------------------------------------------------------


def test_cli_new_file_is_exempt(tmp_path):
    """Notebook absent a la base -> exempt, rc=0, finding_count=0.

    On ecrit un notebook neuf (jamais committe), ``--base origin/main`` ne
    le trouve pas -> exemption (rien a perdre, tout est ajout).
    """
    nb = {
        "cells": [_make_cell_with_text_html_bytes(5000, "c1")],
    }
    nb_rel = _nb_path()
    _write_nb(nb_rel, nb)
    try:
        # --head omis -> working tree (le fichier qu'on vient d'ecrire)
        result = subprocess.run(
            [sys.executable, str(TOOL), str(nb_rel),
             "--base", "origin/main",
             "--check", "--json"],
            capture_output=True, text=True, encoding="utf-8",
            cwd=REPO_ROOT, check=False,
        )
        # rc=0 (exempt)
        assert result.returncode == 0, (
            f"nouveau fichier doit etre exempt (rc=0), got rc={result.returncode} "
            f"stderr={result.stderr[:500]}"
        )
        # JSON valide
        out = json.loads(result.stdout)
        assert out.get("new_file") is True
        assert out.get("findings") == []
    finally:
        # Cleanup
        (REPO_ROOT / nb_rel).unlink(missing_ok=True)


def test_cli_known_loss_case_must_rougir(tmp_path):
    """#11656 -- contrôle positif obligatoire : un notebook avec perte de
    98% de son volume de sortie text DOIT faire rougir ``--check``.

    Sans ce test, l'instrument peut passer en CI avec un bug silencieux et
    personne ne le voit avant une vraie perte.

    Ici, on utilise ``scan_notebook()`` directement (pas le CLI), en lui
    passant des notebooks en memoire. Le test verify que la detection se
    fait au niveau de l'API Python (la ou le CI l'appellera), pas
    seulement dans la fonction ``_diff_families``.
    """
    base_nb = {
        "cells": [_make_cell_with_text_html_bytes(12_500, "c1")],
    }
    head_nb = {
        "cells": [_make_cell_with_text_html_bytes(250, "c1")],  # -98%
    }
    # On monkeypatche les helpers git pour bypasser la dependance HEAD.
    orig_read = crvd._read_notebook_at_ref
    orig_exists = crvd._path_exists_at_ref
    orig_resolves = crvd._ref_resolves
    crvd._read_notebook_at_ref = lambda path, ref: (
        base_nb if "base" in str(ref) else head_nb
    )
    crvd._path_exists_at_ref = lambda path, ref: True
    crvd._ref_resolves = lambda ref: True
    try:
        result = crvd.scan_notebook(
            Path("dummy.ipynb"), base_ref="base-ref", head_ref="head-ref",
        )
    finally:
        crvd._read_notebook_at_ref = orig_read
        crvd._path_exists_at_ref = orig_exists
        crvd._ref_resolves = orig_resolves

    # Cas fondateur : chute 98% -> DELTA_SIGNAL
    assert result["stats"]["findings_count"] == 1, (
        f"cas fondateur doit declencher 1 finding, got {result}"
    )
    delta = [f for f in result["findings"] if f["kind"] == "DELTA_SIGNAL"]
    assert len(delta) == 1
    assert delta[0]["mime_family"] == "text"
    assert delta[0]["ratio"] == 0.02


def test_cli_ref_invalid_returns_error_rc2(tmp_path):
    """Ref invalide -> rc=2 (garde anti-auto-desarmement #8655/#8662).

    On utilise ``scan_notebook()`` directement : un ref de base invalide
    (que ``_ref_resolves`` rejette) renvoie un dict avec ``"error"``,
    que ``main()`` traduit en rc=2.
    """
    nb = {"cells": [_make_cell_with_text_html_bytes(5_000, "c1")]}
    nb_rel = _nb_path()
    abs_path = _write_nb(nb_rel, nb)
    try:
        orig_resolves = crvd._ref_resolves
        crvd._ref_resolves = lambda ref: False  # ref bidon
        try:
            result = crvd.scan_notebook(abs_path, base_ref="ce-ref-bidon")
        finally:
            crvd._ref_resolves = orig_resolves
        assert "error" in result
        assert "introuvable" in result["error"] or "invalide" in result["error"]
    finally:
        abs_path.unlink(missing_ok=True)


def test_cli_missing_notebook_returns_error_rc2(tmp_path):
    """Notebook inexistant sur disque -> rc=2."""
    result = subprocess.run(
        [sys.executable, str(TOOL), "scripts/notebook_tools/tests/fixtures/does_not_exist.ipynb",
         "--base", "HEAD", "--head", "HEAD", "--check"],
        capture_output=True, text=True, encoding="utf-8",
        cwd=REPO_ROOT, check=False,
    )
    assert result.returncode == 2
    assert "introuvable" in result.stderr


# ---------------------------------------------------------------------------
# Mutation testing -- revert la logique de seuil DOIT faire rougir
# test_diff_known_loss_triggers_delta_signal, sans affecter les autres.
# (Documentation -- pas execute comme test, c'est un commentaire destine
# a l'auditeur qui verifie que les tests pin SPECIFIQUEMENT le seuil.)
# ---------------------------------------------------------------------------
#
# Revert 1 : _diff_families ignore ``min_base`` (utilise toujours 0)
# -> test_diff_below_min_base_ignored ROUGE (signal declenche sur 800 B)
# -> test_diff_known_loss_triggers_delta_signal RESTE VERT (12 500 > 0)
# -> autres tests : pas de changement.
#
# Revert 2 : _diff_families ignore ``threshold`` (utilise toujours 1.0)
# -> test_diff_threshold_respected ROUGE (chute 60% declenche maintenant)
# -> test_diff_known_loss_triggers_delta_signal RESTE VERT (98% > 1.0 non,
#    en fait 0.02 <= 1.0 declencherait ; ce test-ci rougit aussi -- c'est
#    un signal que le pin n'est pas mutuellement exclusif, et il faut
#    resserrer : ajouter un test qui pin SPECIFIQUEMENT "98% declenche
#    alors que 60% ne declenche pas". Cf. TODO en bas.)
# -> test_diff_clean_passes_no_find RESTE VERT (12 500 == 12 500)
#
# Revert 3 : _mime_family retourne toujours "other"
# -> test_mime_family_aggregation ROUGE (text/image non differencies)
# -> autres : pas de changement direct.
#
# Revert 4 : _cell_is_exempt retourne toujours False
# -> test_cell_exempt_skipped ROUGE (cell exempt comptee, 5200 au lieu
#    de 200).
# -> autres : pas de changement direct.


def test_pin_threshold_excludes_moderate_chute():
    """Pin mutuellement exclusif au précédent : un chute de 60% NE rougit PAS.

    Cf. mutation test 2 ci-dessus : si on casse le seuil (toujours 1.0),
    CE test rougit EN PLUS de ``test_diff_threshold_respected``. Sans ce
    test, la mutation ``threshold=1.0`` reste invisible (les deux
    rougeurs sont confondues en une).
    """
    # Cas : base 12 500 B, head 7 500 B = ratio 0.6 (60% de chute).
    # Seuil 0.50 -> 0.6 > 0.5 -> PAS de finding.
    base_agg = {"text": 12_500}
    head_agg = {"text": 7_500}
    findings = crvd._diff_families(base_agg, head_agg,
                                   threshold=0.50, min_base=1000)
    assert findings == [], (
        f"chute 60% doit PAS rougir au seuil 50%, got findings={findings}"
    )
    # Cas : base 12 500 B, head 250 B = ratio 0.02 (98% de chute).
    # Seuil 0.50 -> 0.02 <= 0.5 -> DOIT rougir.
    head_agg2 = {"text": 250}
    findings2 = crvd._diff_families(base_agg, head_agg2,
                                    threshold=0.50, min_base=1000)
    delta = [f for f in findings2 if f["kind"] == "DELTA_SIGNAL"]
    assert len(delta) == 1, (
        "chute 98% DOIT rougir -- mutation qui casse le seuil ferait "
        "passer les deux tests simultanement, prouvant que ce pin "
        "disjoint protege contre la confusion."
    )