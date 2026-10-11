"""Tests du systeme d'extracts a tiers (port S6-B, issue #7742).

Quatre familles, miroir du module ``ict/extracts_tiers.py`` :

1. classification (champ explicite, heuristiques, fail-closed) ;
2. loaders publics et references (ids opaques, zero URL, zero texte cote
   references, host_parts retires) ;
3. format chiffre ``.json.gz.enc`` (round-trip, derivation deterministe,
   mauvaise passphrase, passphrase par environnement) ;
4. gardes vie privee / anti-depot (strip text/full_text, resume opaque,
   refus d'une source git-suivie, controle positif sur un fichier du depot).

Le corpus reel (``corpus/`` de la serie) est charge par les tests de loaders :
ils valident les artefacts committes, pas seulement des fixtures.
"""

import json
from pathlib import Path

import pytest

from ict import extracts_tiers as et

SERIES_DIR = Path(__file__).resolve().parents[2]
CORPUS_DIR = SERIES_DIR / "corpus"

PROBE_DEFINITION = {
    "source_name": "fable_probe_v1",
    "source_type": "fable",
    "schema": et.EXTRACT_DEFINITION_SCHEMA,
    "host_parts": ["corpus", "probe", "fable_probe_v1"],
    "path": "probe",
    "extracts": [{"extract_id": "fable_probe_v1_ext_0", "text": "temoin"}],
}


# ---------------------------------------------------------------------------
# 1. Classification
# ---------------------------------------------------------------------------

def test_classify_explicit_tier_field_wins():
    assert et.classify_extract({"tier": "public_clear"}) is et.Tier.PUBLIC_CLEAR
    assert et.classify_extract({"tier": "encrypted_historical"}) is et.Tier.ENCRYPTED_HISTORICAL
    assert et.classify_extract({"tier": "reference_fetch_runtime"}) is et.Tier.REFERENCE_FETCH_RUNTIME
    assert et.classify_extract({"tier": "excluded_external"}) is et.Tier.EXCLUDED_EXTERNAL


def test_classify_unknown_tier_value_fails_closed():
    # une valeur inconnue ne sert rien : fail-closed vers le tier qui reste
    # chez EPITA
    assert et.classify_extract({"tier": "public"}) is et.Tier.EXCLUDED_EXTERNAL


def test_classify_heuristics_without_tier_field():
    assert et.classify_extract(
        {"deposit_form": "clear_text", "public_domain": True}
    ) is et.Tier.PUBLIC_CLEAR
    # clear_text sans public_domain : pas public (fail-closed)
    assert et.classify_extract({"deposit_form": "clear_text"}) is et.Tier.EXCLUDED_EXTERNAL
    assert et.classify_extract({"deposit_form": "json.gz.enc"}) is et.Tier.ENCRYPTED_HISTORICAL
    assert et.classify_extract({"deposit_form": "fetch_runtime"}) is et.Tier.REFERENCE_FETCH_RUNTIME


def test_classify_unknown_entry_fails_closed():
    assert et.classify_extract({"source_type": "discours"}) is et.Tier.EXCLUDED_EXTERNAL
    assert et.classify_extract({}) is et.Tier.EXCLUDED_EXTERNAL


# ---------------------------------------------------------------------------
# 2. Loaders publics et references (sur le corpus committe)
# ---------------------------------------------------------------------------

def test_public_loader_serves_committed_fables_tier():
    defs = et.load_public_definitions(CORPUS_DIR)
    names = [d["source_name"] for d in defs]
    assert names == ["fable_loup_et_l_agneau", "fable_loup_et_le_chien"]
    # le texte public (domaine public) est servi : c'est le tier "texte versionne"
    for d in defs:
        assert all("text" in ext for ext in d["extracts"])
        assert "host_parts" not in d
        assert all("host_parts" not in ext for ext in d["extracts"])


def test_public_loader_rejects_real_name_id():
    bad = {
        "schema": "coursia_corpus_manifest_v1",
        "tier": "public_clear",
        "sources": [
            {
                "source_name": "www.example.com_extrait",
                "source_type": "fable",
                "schema": et.EXTRACT_DEFINITION_SCHEMA,
                "host_parts": ["corpus", "bad"],
                "path": "bad",
                "extracts": [],
            }
        ],
    }
    import tempfile

    with tempfile.TemporaryDirectory() as tmp:
        pub = Path(tmp) / "public"
        pub.mkdir()
        (pub / "bad.json").write_text(json.dumps(bad), encoding="utf-8")
        with pytest.raises(ValueError, match="opaques"):
            et.load_public_definitions(tmp)


def test_public_loader_rejects_url_trace_in_host_parts():
    bad_extract = {
        "extract_id": "fable_003_ext_0",
        "host_parts": ["corpus", "fables_tier", "source.example.com"],
        "text": "x",
    }
    with pytest.raises(ValueError, match="trace d'URL"):
        et._assert_no_url_traces(bad_extract["host_parts"])


def test_references_loader_never_serves_text():
    refs = et.load_fetch_references(CORPUS_DIR)
    ids = [r["reference_id"] for r in refs]
    assert ids == ["witness_discours_final_1940", "witness_fragment_hynkel_1940"]
    for r in refs:
        assert "text" not in r and "full_text" not in r
    hynkel = refs[1]
    assert hynkel["etiquette"] == "fragment, pas reconstitution"
    assert hynkel["plan_experience"]["contenu_propositionnel"].startswith("nul")


def test_references_loader_rejects_text_leak():
    bad = {
        "schema": "coursia_fetch_reference_v1",
        "tier": "reference_fetch_runtime",
        "items": [
            {
                "reference_id": "witness_leak_1940",
                "ayant_droit": "X",
                "text": "texte vendore par erreur",
            }
        ],
    }
    import tempfile

    with tempfile.TemporaryDirectory() as tmp:
        ref = Path(tmp) / "references"
        ref.mkdir()
        (ref / "bad.json").write_text(json.dumps(bad), encoding="utf-8")
        with pytest.raises(ValueError, match="n'expose jamais de texte"):
            et.load_fetch_references(tmp)


def test_public_manifest_sources_carry_required_schema_keys():
    manifest = json.loads((CORPUS_DIR / "public" / "fables_tier.json").read_text(encoding="utf-8"))
    for source in manifest["sources"]:
        missing = [k for k in et.REQUIRED_SOURCE_KEYS if k not in source]
        assert not missing, f"source {source['source_name']} sans cles {missing}"
        assert source["schema"] == et.EXTRACT_DEFINITION_SCHEMA


# ---------------------------------------------------------------------------
# 3. Format chiffre .json.gz.enc (contrat EPITA)
# ---------------------------------------------------------------------------

def test_encrypted_roundtrip_identity(tmp_path):
    blob_path = tmp_path / "probe.json.gz.enc"
    definitions = [dict(PROBE_DEFINITION)]
    summary = et.build_encrypted_tier(definitions, blob_path, "passphrase-test")
    assert summary["n_sources"] == 1
    assert blob_path.exists()
    loaded = et.load_encrypted_definitions(blob_path, passphrase="passphrase-test")
    assert loaded == definitions


def test_encrypted_wrong_passphrase_raises_invalid_token(tmp_path):
    blob_path = tmp_path / "probe.json.gz.enc"
    et.build_encrypted_tier([dict(PROBE_DEFINITION)], blob_path, "bonne")
    from cryptography.fernet import InvalidToken

    with pytest.raises(InvalidToken):
        et.load_encrypted_definitions(blob_path, passphrase="mauvaise")


def test_derivation_is_deterministic_and_key_shaped():
    key_a = et.derive_fernet_key("determinisme")
    key_b = et.derive_fernet_key("determinisme")
    assert key_a == key_b  # sel public constant -> interop EPITA a passphrase egale
    import base64

    raw = base64.urlsafe_b64decode(key_a)
    assert len(raw) == et.PBKDF2_KEY_LENGTH  # 32 octets -> Fernet 256 bits


def test_derivation_refuses_empty_passphrase():
    with pytest.raises(ValueError):
        et.derive_fernet_key("")


def test_loader_reads_passphrase_from_environment(tmp_path, monkeypatch):
    blob_path = tmp_path / "probe.json.gz.enc"
    et.build_encrypted_tier([dict(PROBE_DEFINITION)], blob_path, "via-env")
    monkeypatch.setenv(et.PASSPHRASE_ENV_VAR, "via-env")
    loaded = et.load_encrypted_definitions(blob_path)
    assert loaded == [dict(PROBE_DEFINITION)]


def test_loader_without_any_passphrase_names_env_var(tmp_path, monkeypatch):
    monkeypatch.delenv(et.PASSPHRASE_ENV_VAR, raising=False)
    with pytest.raises(RuntimeError, match=et.PASSPHRASE_ENV_VAR):
        et.load_encrypted_definitions(tmp_path / "inexistant.json.gz.enc")


# ---------------------------------------------------------------------------
# 4. Gardes vie privee / anti-depot
# ---------------------------------------------------------------------------

def test_strip_text_fields_removes_both_text_and_full_text():
    defs = [
        {
            "source_name": "fable_strip_v1",
            "extracts": [
                {"extract_id": "fable_strip_v1_ext_0", "text": "a", "full_text": "b", "k": 1}
            ],
            "text": "c",
        }
    ]
    stripped = et.strip_text_fields(defs)
    assert stripped[0]["extracts"][0] == {"extract_id": "fable_strip_v1_ext_0", "k": 1}
    assert "text" not in stripped[0]


def test_opaque_summary_emits_ids_and_counts_but_never_text():
    defs = [dict(PROBE_DEFINITION)]
    summary = et.opaque_summary(defs)
    assert summary["n_sources"] == 1
    assert summary["n_extracts_total"] == 1
    assert summary["source_names"] == ["fable_probe_v1"]
    dumped = json.dumps(summary, ensure_ascii=False)
    assert "temoin" not in dumped  # le texte ne sort jamais


def test_anti_deposit_guard_refuses_git_tracked_file():
    # controle positif : le __init__ du package est suivi par git -> refus.
    # (NB : le fichier de test lui-meme ne l'est qu'une fois commite --
    # la garde verifie l'index, pas le systeme de fichiers.)
    tracked = Path(__file__).resolve().parents[1] / "__init__.py"
    with pytest.raises(ValueError, match="garde anti-depot"):
        et.assert_not_git_tracked(tracked)


def test_anti_deposit_guard_allows_untracked_file(tmp_path):
    plain = tmp_path / "source_historique.txt"
    plain.write_text("transcription hors depot", encoding="utf-8")
    # pas d'exception : un fichier hors depot est la forme attendue
    et.assert_not_git_tracked(plain)


def test_builder_guard_runs_on_plaintext_sources(tmp_path):
    tracked = Path(__file__).resolve().parents[1] / "__init__.py"  # suivi par git
    with pytest.raises(ValueError, match="garde anti-depot"):
        et.build_encrypted_tier(
            [dict(PROBE_DEFINITION)],
            tmp_path / "out.json.gz.enc",
            "p",
            plaintext_sources=[tracked],
        )


def test_builder_rejects_definition_missing_required_keys(tmp_path):
    incomplete = {k: v for k, v in PROBE_DEFINITION.items() if k != "path"}
    with pytest.raises(ValueError, match="cles requises"):
        et.build_encrypted_tier([incomplete], tmp_path / "out.json.gz.enc", "p")


# ---------------------------------------------------------------------------
# Validator CLI (contrat de sortie)
# ---------------------------------------------------------------------------

def test_validator_full_run_passes_on_committed_corpus(capsys):
    from ict import validate_extracts_tiers as ve

    rc = ve.main(["--corpus", str(CORPUS_DIR)])
    out = capsys.readouterr().out
    assert rc == 0, out
    verdict = json.loads(out[out.index("{"):])
    assert verdict["verdict"] == "PASS"
    names = [c["check"] for c in verdict["checks"]]
    assert "roundtrip_encrypted" in names
    assert "anti_deposit_guard" in names


def test_validator_dry_run_skips_crypto(capsys):
    from ict import validate_extracts_tiers as ve

    rc = ve.main(["--corpus", str(CORPUS_DIR), "--dry-run"])
    out = capsys.readouterr().out
    assert rc == 0, out
    verdict = json.loads(out[out.index("{"):])
    names = [c["check"] for c in verdict["checks"]]
    assert "roundtrip_encrypted" not in names
    assert verdict["dry_run"] is True
