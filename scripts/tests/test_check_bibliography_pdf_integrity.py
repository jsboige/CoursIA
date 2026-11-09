#!/usr/bin/env python3
"""Tests unitaires de `scripts/check_bibliography_pdf_integrity.py`.

L'organe existe pour lever une confusion precise, mesuree le 2026-09-26/30 :
un PDF servi par le client Google Drive n'est pas toujours hydrate, et une
lecture qui echoue sur un fichier non hydrate ne dit rien de l'etat du fichier
sur le disque du gisement. Un gisement sain avait ainsi ete declare
« systemiquement corrompu » sur 4 PDF sur 4.

La distinction se teste donc sur les verdicts, pas sur le texte :

  - un PDF valide                          -> OK
  - des octets arbitraires en `.pdf`       -> CORRUPT      (controle positif)
  - un chemin absent                       -> IO_ERROR
  - lecture en place KO, copie locale OK   -> OK_AFTER_HYDRATE
  - lecture KO dans les deux modes         -> CORRUPT, message du lecteur preserve
  - echantillonnage deterministe sur liste triee

Le cas `OK_AFTER_HYDRATE` est le cœur de l'organe : il se teste en injectant un
`_try_parse` qui echoue au premier appel et reussit au second, ce qui reproduit
exactement la sequence « lecture en place, puis copie locale » sans dependre du
client Drive.
"""

import check_bibliography_pdf_integrity as mod


def _write_valid_pdf(path):
    from pypdf import PdfWriter

    writer = PdfWriter()
    writer.add_blank_page(width=200, height=200)
    with open(path, "wb") as fh:
        writer.write(fh)
    return path


def test_valid_pdf_is_ok(tmp_path):
    pdf = _write_valid_pdf(tmp_path / "valide.pdf")
    res = mod.validate_pdf(pdf, tmp_path)
    assert res["verdict"] == mod.VERDICT_OK
    assert res["pages"] == 1
    assert res["error"] == ""
    assert res["sha1"]


def test_garbage_bytes_are_corrupt(tmp_path):
    pdf = tmp_path / "pas-un-pdf.pdf"
    pdf.write_bytes(b"ceci n'est pas un document PDF" * 8)
    res = mod.validate_pdf(pdf, tmp_path)
    assert res["verdict"] == mod.VERDICT_CORRUPT
    assert res["pages"] == 0
    assert res["error"]


def test_missing_file_is_io_error(tmp_path):
    res = mod.validate_pdf(tmp_path / "absent.pdf", tmp_path)
    assert res["verdict"] == mod.VERDICT_MISSING
    assert res["size"] == 0
    assert res["sha1"] == ""


def test_hydration_recovery_is_not_corruption(tmp_path, monkeypatch):
    """Lecture en place KO, lecture apres copie locale OK : le fichier est intact."""
    pdf = tmp_path / "non-hydrate.pdf"
    pdf.write_bytes(b"%PDF-1.4 tronque")
    calls = []

    def fake_try_parse(path):
        calls.append(path)
        if len(calls) == 1:
            return False, 0, "PdfStreamError: Stream has ended unexpectedly"
        return True, 12, ""

    monkeypatch.setattr(mod, "_try_parse", fake_try_parse)
    res = mod.validate_pdf(pdf, tmp_path)
    assert res["verdict"] == mod.VERDICT_HYDRATED
    assert res["pages"] == 12
    assert len(calls) == 2, "les deux lectures doivent avoir lieu"
    assert calls[0] == pdf, "la premiere lecture se fait sur place"
    assert calls[1] != pdf, "la seconde se fait sur la copie locale"
    assert not calls[1].exists(), "la copie locale est nettoyee"


def test_corrupt_keeps_first_error_message(tmp_path, monkeypatch):
    """Echec des deux lectures : le message du lecteur est preserve pour le rapport."""
    pdf = tmp_path / "vraiment-corrompu.pdf"
    pdf.write_bytes(b"%PDF-1.4")
    monkeypatch.setattr(mod, "_try_parse",
                        lambda path: (False, 0, "PdfReadError: EOF marker not found"))
    res = mod.validate_pdf(pdf, tmp_path)
    assert res["verdict"] == mod.VERDICT_CORRUPT
    assert "EOF marker not found" in res["error"]
    assert res["sha1"], "l'empreinte reste disponible pour un fichier corrompu"


def test_anchor_names_the_matching_algorithm(tmp_path):
    """L'ancre dit QUEL algorithme a matche : c'est tout l'objet de la verification.

    Le 2026-09-26, un `sha1` mesure a ete compare a un `sha256[:8]` annonce ; le
    mismatch a fait conclure que quatre fichiers byte-identiques avaient ete
    « retelecharges ou corrompus ».
    """
    pdf = _write_valid_pdf(tmp_path / "ancre.pdf")
    data = pdf.read_bytes()
    import hashlib

    for algo, label in mod.ANCHOR_ALGOS:
        expected = hashlib.new(algo, data).hexdigest()[:8].upper()
        status, matched = mod.check_anchor(pdf, {pdf.name: expected})
        assert status == label, (algo, status)
        assert matched == algo
    assert label == "MATCH_MD5_8", "l'ordre de confrontation est stable"


def test_anchor_mismatch_and_absence(tmp_path):
    pdf = _write_valid_pdf(tmp_path / "ancre.pdf")
    status, _ = mod.check_anchor(pdf, {pdf.name: "DEADBEEF"})
    assert status == mod.ANCHOR_MISMATCH

    status, _ = mod.check_anchor(pdf, {"un-autre.pdf": "DEADBEEF"})
    assert status == mod.ANCHOR_NONE, "un fichier sans ancre n'est pas en defaut"
    assert mod.check_anchor(pdf, None) == (mod.ANCHOR_NONE, "")


def test_anchor_resolves_by_full_path_then_basename(tmp_path):
    pdf = _write_valid_pdf(tmp_path / "sous-dossier.pdf")
    import hashlib

    expected = hashlib.sha256(pdf.read_bytes()).hexdigest()[:8].upper()
    by_path, _ = mod.check_anchor(pdf, {str(pdf): expected})
    by_name, _ = mod.check_anchor(pdf, {pdf.name: expected})
    assert by_path == by_name == "MATCH_SHA256_8"


def test_validate_pdf_carries_the_anchor_verdict(tmp_path):
    pdf = _write_valid_pdf(tmp_path / "porteuse.pdf")
    import hashlib

    expected = hashlib.sha256(pdf.read_bytes()).hexdigest()[:8].upper()
    res = mod.validate_pdf(pdf, tmp_path, {pdf.name: expected})
    assert res["verdict"] == mod.VERDICT_OK
    assert res["anchor"] == "MATCH_SHA256_8"
    assert res["anchor_algo"] == "sha256"


def test_sample_is_deterministic_and_bounded(tmp_path):
    for i in range(20):
        (tmp_path / ("doc-%02d.pdf" % i)).write_bytes(b"%PDF-1.4")
    (tmp_path / "note.txt").write_text("hors scope", encoding="utf-8")

    first = mod._collect_pdfs(tmp_path, 5)
    second = mod._collect_pdfs(tmp_path, 5)
    assert len(first) == 5
    assert first == second, "l'echantillon doit etre reproductible"
    assert all(p.suffix == ".pdf" for p in first)
    assert first == sorted(first)

    every = mod._collect_pdfs(tmp_path, None)
    assert len(every) == 20, "sans echantillon, tous les PDF sont rendus"

    more_than_available = mod._collect_pdfs(tmp_path, 99)
    assert len(more_than_available) == 20