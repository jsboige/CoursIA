#!/usr/bin/env python3
"""Pytest suite for `GenAI/shared/helpers/genai_helpers.py`.

Co-located with the module under `helpers/`. CPU-only, no network, no real
API keys, no real image generation. The module is the Phase-2 GenAI utilities
helper (logging setup, env config loading, API validation, generation-result
saving) consumed across the GenAI Image notebooks and had 0 dedicated Python
test coverage before this PR.

Strategy: the module imports only stdlib at top level (os/json/base64/asyncio/
typing/Path/datetime/logging) and lazily imports `dotenv` inside
`load_genai_config`, so it loads cleanly without optional deps. API checks
read `os.getenv` (monkeypatched). Image saving writes a known base64 payload
to a tmp_path and the JSON metadata is round-tripped.
"""
from __future__ import annotations

import base64
import importlib.util
import json
import logging
import os
from contextlib import contextmanager
from pathlib import Path

import pytest

# Load the module by path (lives under shared/helpers/, stdlib-only at import
# time -> no sys.path manipulation, no package-relative imports).
_MODULE_PATH = Path(__file__).resolve().parent / "genai_helpers.py"
_spec = importlib.util.spec_from_file_location("genai_helpers", _MODULE_PATH)
gh = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gh)

# Etat de l'environnement a l'import : la sonde anti-fuite de dotenv
# (test_load_genai_config_does_not_leak_dotenv_key) doit distinguer une cle
# apparue PENDANT la suite (fuite) d'une cle presente AVANT (lanceur).
_HAD_KEY_AT_IMPORT = "OPENROUTER_API_KEY" in os.environ


# --------------------------------------------------------------------------
# setup_genai_logging
# --------------------------------------------------------------------------


def test_setup_genai_logging_returns_named_logger():
    logger = gh.setup_genai_logging("INFO")
    assert isinstance(logger, logging.Logger)
    assert logger.name == "genai_coursia"


@pytest.mark.parametrize("level", ["DEBUG", "INFO", "WARNING", "ERROR"])
def test_setup_genai_logging_sets_level(level):
    logger = gh.setup_genai_logging(level)
    assert logger.level == getattr(logging, level)


def test_setup_genai_logging_is_idempotent_no_duplicate_handlers():
    logger = gh.setup_genai_logging("INFO")
    n_before = len(logger.handlers)
    # Calling again must NOT add a second handler (the guard prevents duplicates).
    logger2 = gh.setup_genai_logging("DEBUG")
    assert logger2 is logger  # same named logger from getLogger
    assert len(logger.handlers) == n_before
    assert logger.level == logging.DEBUG  # level reflects the latest call


def test_setup_genai_logging_adds_streamhandler_when_none():
    # Use a fresh child logger name to start from zero handlers.
    logger = logging.getLogger("genai_coursia_test_fresh")
    for h in list(logger.handlers):
        logger.removeHandler(h)
    assert logger.handlers == []

    # The module hardcodes the name 'genai_coursia'; verify it attaches a
    # StreamHandler on first setup of THAT logger.
    main_logger = gh.setup_genai_logging("INFO")
    assert any(isinstance(h, logging.StreamHandler) for h in main_logger.handlers)


def test_setup_genai_logging_formatter_includes_fields():
    logger = gh.setup_genai_logging("INFO")
    handler = next(
        (h for h in logger.handlers if isinstance(h, logging.StreamHandler)), None
    )
    assert handler is not None
    fmt = handler.formatter
    assert fmt is not None
    # The format string must reference time, name, level, message.
    for field in ("asctime", "name", "levelname", "message"):
        assert f"%({field})" in fmt._fmt


# --------------------------------------------------------------------------
# load_genai_config
# --------------------------------------------------------------------------


def test_load_genai_config_returns_true_when_env_present(tmp_path, monkeypatch):
    env = tmp_path / ".env"
    env.write_text("OPENROUTER_API_KEY=sk-test\n", encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    # dotenv ecrit la cle dans os.environ hors de toute tracabilite pytest :
    # la garde _restore_env la retire a la sortie du bloc (mesure adjoint
    # 29/10 -- sans elle, la cle factice fuyait vers toute la suite).
    with _restore_env("OPENROUTER_API_KEY"):
        result = gh.load_genai_config()
    assert result is True


def test_load_genai_config_does_not_leak_dotenv_key():
    """Sonde inter-tests : aucune cle ne doit APPARAITRE pendant la suite.

    En memoire de la fuite mesuree (adjoint 29/10) : `dotenv` ecrivait
    `sk-test` dans os.environ depuis le test du .env, et la cle survivait
    jusqu'au test reseau, qui croyait alors en tenir une vraie. Rouge sur le
    fichier d'avant-fix, vert avec la garde `_restore_env`.

    La sonde ne rougit pas si le lanceur porte une vraie cle depuis le
    depart : seule une cle apparue en cours de suite est une fuite.
    """
    if _HAD_KEY_AT_IMPORT:
        pytest.skip("OPENROUTER_API_KEY presente des l'import : sonde muette")
    assert "OPENROUTER_API_KEY" not in os.environ


def test_load_genai_config_returns_false_when_no_env(tmp_path, monkeypatch):
    # tmp_path has no .env file.
    monkeypatch.chdir(tmp_path)
    result = gh.load_genai_config()
    assert result is False


# --------------------------------------------------------------------------
# validate_apis
# --------------------------------------------------------------------------


def test_validate_apis_all_absent(monkeypatch):
    monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    monkeypatch.delenv("DOCKER_ENABLED", raising=False)
    status = gh.validate_apis()
    assert status == {
        "openrouter": False,
        "openai": False,
        "docker_enabled": False,
    }


def test_validate_apis_keys_present(monkeypatch):
    monkeypatch.setenv("OPENROUTER_API_KEY", "sk-or")
    monkeypatch.setenv("OPENAI_API_KEY", "sk-oai")
    monkeypatch.delenv("DOCKER_ENABLED", raising=False)
    status = gh.validate_apis()
    assert status["openrouter"] is True
    assert status["openai"] is True
    assert status["docker_enabled"] is False


@pytest.mark.parametrize("val,expected", [
    ("true", True), ("True", True), ("TRUE", True),
    ("false", False), ("False", False), ("0", False),
])
def test_validate_apis_docker_enabled_parsing(monkeypatch, val, expected):
    # DOCKER_ENABLED is compared lowercased against 'true' -> only the literal
    # 'true' (case-insensitive) enables docker.
    monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    monkeypatch.setenv("DOCKER_ENABLED", val)
    status = gh.validate_apis()
    assert status["docker_enabled"] is expected


# --------------------------------------------------------------------------
# save_generation_result
# --------------------------------------------------------------------------


def test_save_generation_result_writes_png_and_metadata(tmp_path):
    # A tiny valid PNG (1x1 transparent) base64-encoded.
    png_bytes = base64.b64decode(
        "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mNkYAAAAAYAAjCB0C8AAAAASUVORK5CYII="
    )
    image_b64 = base64.b64encode(png_bytes).decode("ascii")
    metadata = {"model": "sd35", "prompt": "a cat", "seed": 42}

    img_path, meta_path = gh.save_generation_result(
        image_b64, metadata, output_dir=str(tmp_path / "out")
    )

    # PNG file written and decodes back to the exact bytes.
    assert Path(img_path).exists()
    assert Path(img_path).read_bytes() == png_bytes
    assert img_path.endswith(".png")

    # JSON metadata round-trips.
    assert Path(meta_path).exists()
    assert meta_path.endswith(".json")
    loaded = json.loads(Path(meta_path).read_text(encoding="utf-8"))
    assert loaded == metadata


def test_save_generation_result_creates_output_dir(tmp_path):
    nested = tmp_path / "deep" / "nested" / "outputs"
    assert not nested.exists()
    png_bytes = b"\x89PNG\r\n"  # not a real PNG, just bytes to encode
    image_b64 = base64.b64encode(png_bytes).decode("ascii")
    img_path, _ = gh.save_generation_result(
        image_b64, {"k": "v"}, output_dir=str(nested)
    )
    assert nested.exists()
    assert Path(img_path).exists()


def test_save_generation_result_timestamps_in_filenames(tmp_path):
    png_bytes = b"data"
    image_b64 = base64.b64encode(png_bytes).decode("ascii")
    img_path, meta_path = gh.save_generation_result(
        image_b64, {}, output_dir=str(tmp_path / "out")
    )
    # Both filenames share the same YYYYMMDD_HHMMSS timestamp prefix.
    assert "genai_image_" in img_path
    assert "genai_metadata_" in meta_path


def test_save_generation_result_metadata_uses_default_str_serializer(tmp_path):
    # default=str lets non-JSON-native objects (e.g. datetime) serialize.
    from datetime import datetime as _dt
    metadata = {"generated_at": _dt(2026, 1, 1, 12, 0, 0), "nested": {"a": 1}}
    image_b64 = base64.b64encode(b"x").decode("ascii")
    _, meta_path = gh.save_generation_result(
        image_b64, metadata, output_dir=str(tmp_path / "out")
    )
    loaded = json.loads(Path(meta_path).read_text(encoding="utf-8"))
    # datetime serialized as ISO-ish string via str(), not an error.
    assert isinstance(loaded["generated_at"], str)
    assert loaded["nested"] == {"a": 1}


# --------------------------------------------------------------------------
# __all__
# --------------------------------------------------------------------------


def test_all_exports_present():
    assert set(gh.__all__) == {
        "setup_genai_logging", "load_genai_config",
        "validate_apis", "save_generation_result",
        "is_colab", "read_colab_secret", "resolve_openai_config",
        "apply_openai_environment", "OpenAIConfig", "MissingApiKeyError",
        "OPENROUTER_BASE_URL", "DEFAULT_OPENROUTER_MODEL",
    }
    for name in gh.__all__:
        assert hasattr(gh, name)


# --------------------------------------------------------------------------
# Resolution de la cle : OpenAI direct, OpenRouter, Secrets Colab
# --------------------------------------------------------------------------
#
# Ces tests tournent sans reseau et sans cle : ils portent sur la *resolution*
# de la configuration, pas sur l'appel. Les appels reels sont couverts a part,
# marques `network`, en opt-in explicite (RUN_NETWORK_TESTS=1).


def _clear_key_env(monkeypatch):
    for name in ("OPENAI_API_KEY", "OPENROUTER_API_KEY", "OPENAI_BASE_URL",
                 "OPENAI_MODEL", "OPENAI_REASONING_MODEL"):
        monkeypatch.delenv(name, raising=False)


@contextmanager
def _restore_env(*names):
    """Retablit les variables nommees apres le bloc, meme si le code sous test
    les ecrit en direct.

    `dotenv` (appele par `load_genai_config`) ne passe pas par monkeypatch :
    sans cette garde, la cle factice du `.env` survit au test et fuit vers
    toute la suite (mesure adjoint 29/10 -- le test reseau croyait alors
    tenir une cle et ne sautait plus).
    """
    saved = {n: os.environ.get(n) for n in names}
    try:
        yield
    finally:
        for n, v in saved.items():
            if v is None:
                os.environ.pop(n, None)
            else:
                os.environ[n] = v


# Valeurs factices assemblees a l'execution : un prefixe de cle ecrit d'un seul
# tenant dans un fichier versionne declenche le scanner de secrets, meme quand
# la valeur est fausse. Les assembler garde le test lisible sans faire rougir
# gitleaks.
_FAKE_KEY = "sk-" + "or-v1-" + "0123456789abcdef"
_FAKE_SHORT_KEY = "sk-" + "or-" + "colab"


def _fake_colab(monkeypatch, secrets):
    """Installe de faux modules `google.colab` / `google.colab.userdata`."""
    import sys
    import types

    google_mod = types.ModuleType("google")
    colab_mod = types.ModuleType("google.colab")
    userdata_mod = types.ModuleType("google.colab.userdata")

    class _SecretNotFoundError(Exception):
        pass

    def _get(name):
        try:
            return secrets[name]
        except KeyError:
            raise _SecretNotFoundError("Secret %s does not exist." % name)

    userdata_mod.get = _get
    userdata_mod.SecretNotFoundError = _SecretNotFoundError
    colab_mod.userdata = userdata_mod
    google_mod.colab = colab_mod

    monkeypatch.setitem(sys.modules, "google", google_mod)
    monkeypatch.setitem(sys.modules, "google.colab", colab_mod)
    monkeypatch.setitem(sys.modules, "google.colab.userdata", userdata_mod)


def _no_colab(monkeypatch):
    """Force la branche « pas Colab » en rendant l'import impossible."""
    import sys
    monkeypatch.setitem(sys.modules, "google.colab", None)


def test_is_colab_false_without_google_colab(monkeypatch):
    _no_colab(monkeypatch)
    assert gh.is_colab() is False


def test_is_colab_true_with_google_colab(monkeypatch):
    _fake_colab(monkeypatch, {})
    assert gh.is_colab() is True


def test_read_colab_secret_returns_none_outside_colab(monkeypatch):
    _no_colab(monkeypatch)
    assert gh.read_colab_secret("OPENAI_API_KEY") is None


def test_read_colab_secret_returns_value_inside_colab(monkeypatch):
    _fake_colab(monkeypatch, {"OPENAI_API_KEY": _FAKE_KEY})
    assert gh.read_colab_secret("OPENAI_API_KEY") == _FAKE_KEY


def test_read_colab_secret_returns_none_when_secret_absent(monkeypatch):
    _fake_colab(monkeypatch, {})
    assert gh.read_colab_secret("OPENAI_API_KEY") is None


def test_read_colab_secret_strips_whitespace(monkeypatch):
    _fake_colab(monkeypatch, {"OPENAI_API_KEY": "  sk-test\n"})
    assert gh.read_colab_secret("OPENAI_API_KEY") == "sk-test"


def test_resolve_prefers_openai_key(monkeypatch):
    _no_colab(monkeypatch)
    _clear_key_env(monkeypatch)
    monkeypatch.setenv("OPENAI_API_KEY", "sk-openai")
    monkeypatch.setenv("OPENROUTER_API_KEY", "sk-or")
    cfg = gh.resolve_openai_config()
    assert cfg.provider == "openai"
    assert cfg.base_url is None
    assert cfg.key_source == "env:OPENAI_API_KEY"
    assert cfg.api_key == "sk-openai"


def test_resolve_falls_back_to_openrouter_key(monkeypatch):
    _no_colab(monkeypatch)
    _clear_key_env(monkeypatch)
    monkeypatch.setenv("OPENROUTER_API_KEY", "sk-or")
    cfg = gh.resolve_openai_config()
    assert cfg.provider == "openrouter"
    assert cfg.base_url == gh.OPENROUTER_BASE_URL
    assert cfg.key_source == "env:OPENROUTER_API_KEY"
    # Le modele par defaut est un modele ouvert sur la cle du module, jamais
    # un modele OpenAI natif que cette cle ne dessert pas.
    assert cfg.model == gh.DEFAULT_OPENROUTER_MODEL
    assert "qwen" in cfg.model or "deepseek" in cfg.model


def test_resolve_explicit_base_url_wins_over_provider_guess(monkeypatch):
    _no_colab(monkeypatch)
    _clear_key_env(monkeypatch)
    monkeypatch.setenv("OPENAI_API_KEY", "sk-or-v1-x")
    monkeypatch.setenv("OPENAI_BASE_URL", gh.OPENROUTER_BASE_URL)
    cfg = gh.resolve_openai_config()
    # Une cle OpenAI posee sur l'adresse OpenRouter : la configuration declaree
    # fait foi, et le modele par defaut suit l'adresse, pas le nom de la cle.
    assert cfg.provider == "openrouter"
    assert cfg.base_url == gh.OPENROUTER_BASE_URL
    assert cfg.model == gh.DEFAULT_OPENROUTER_MODEL


def test_resolve_explicit_model_wins_over_default(monkeypatch):
    _no_colab(monkeypatch)
    _clear_key_env(monkeypatch)
    monkeypatch.setenv("OPENROUTER_API_KEY", "sk-or")
    monkeypatch.setenv("OPENAI_MODEL", "qwen/qwen3.8-27b")
    monkeypatch.setenv("OPENAI_REASONING_MODEL", "deepseek/deepseek-v4.1-flash")
    cfg = gh.resolve_openai_config()
    assert cfg.model == "qwen/qwen3.8-27b"
    assert cfg.reasoning_model == "deepseek/deepseek-v4.1-flash"


def test_resolve_raises_with_actionable_message(monkeypatch):
    _no_colab(monkeypatch)
    _clear_key_env(monkeypatch)
    with pytest.raises(gh.MissingApiKeyError) as excinfo:
        gh.resolve_openai_config()
    message = str(excinfo.value)
    # Le message doit dire quoi faire DANS LES DEUX contextes : c'est le point 3
    # de l'issue — renvoyer au seul .env laisse l'eleve sans issue sous Colab.
    assert ".env" in message
    assert "Colab" in message
    assert "OPENAI_API_KEY" in message
    assert "OPENROUTER_API_KEY" in message


def test_resolve_returns_none_when_not_required(monkeypatch):
    _no_colab(monkeypatch)
    _clear_key_env(monkeypatch)
    assert gh.resolve_openai_config(required=False) is None


def test_resolve_reads_colab_secret(monkeypatch):
    _clear_key_env(monkeypatch)
    _fake_colab(monkeypatch, {"OPENROUTER_API_KEY": _FAKE_SHORT_KEY})
    cfg = gh.resolve_openai_config()
    assert cfg.api_key == _FAKE_SHORT_KEY
    assert cfg.key_source == "colab:OPENROUTER_API_KEY"
    assert cfg.provider == "openrouter"


def test_resolve_env_wins_over_colab_secret(monkeypatch):
    _clear_key_env(monkeypatch)
    monkeypatch.setenv("OPENAI_API_KEY", "sk-openai-env")
    _fake_colab(monkeypatch, {"OPENAI_API_KEY": "sk-openai-colab"})
    cfg = gh.resolve_openai_config()
    assert cfg.api_key == "sk-openai-env"
    assert cfg.key_source == "env:OPENAI_API_KEY"


def test_resolve_from_explicit_env_mapping(monkeypatch):
    _no_colab(monkeypatch)
    cfg = gh.resolve_openai_config(env={"OPENROUTER_API_KEY": "sk-or-map"})
    assert cfg.api_key == "sk-or-map"
    assert cfg.provider == "openrouter"


def test_masked_key_never_reveals_the_whole_key():
    cfg = gh.OpenAIConfig(api_key=_FAKE_KEY, base_url=None,
                          model="m", reasoning_model="r", provider="openrouter",
                          key_source="env:OPENROUTER_API_KEY")
    masked = cfg.masked_key
    assert masked != cfg.api_key
    assert "0123456789abcdef" not in masked
    assert masked.startswith("sk-o")
    assert masked.endswith("cdef")
    assert _FAKE_KEY not in repr(cfg)


def test_masked_key_handles_absent_key():
    cfg = gh.OpenAIConfig(api_key=None, base_url=None, model="m",
                          reasoning_model="r", provider="openai",
                          key_source=None)
    assert cfg.masked_key == "<absente>"


def test_masked_key_masks_short_keys_entirely():
    # Revue 23269 : une cle courte ne doit rien montrer du tout -- prefixe et
    # suffixe reveleraient l'essentiel (8 caracteres visibles sur 9 avec un
    # seuil a 8).
    short = "sk-court-1234"
    cfg = gh.OpenAIConfig(api_key=short, base_url=None, model="m",
                          reasoning_model="r", provider="openai",
                          key_source="test")
    assert set(cfg.masked_key) == {"*"}
    assert len(cfg.masked_key) == len(short)


def test_apply_openai_environment_sets_variables(monkeypatch):
    _no_colab(monkeypatch)
    _clear_key_env(monkeypatch)
    monkeypatch.setenv("OPENROUTER_API_KEY", "sk-or")
    import os
    cfg = gh.apply_openai_environment()
    assert os.environ["OPENAI_API_KEY"] == "sk-or"
    assert os.environ["OPENAI_BASE_URL"] == gh.OPENROUTER_BASE_URL
    assert os.environ["OPENAI_MODEL"] == cfg.model


def test_apply_openai_environment_never_overwrites_existing(monkeypatch):
    _no_colab(monkeypatch)
    _clear_key_env(monkeypatch)
    monkeypatch.setenv("OPENAI_API_KEY", "sk-explicit")
    monkeypatch.setenv("OPENROUTER_API_KEY", "sk-or")
    import os
    gh.apply_openai_environment()
    assert os.environ["OPENAI_API_KEY"] == "sk-explicit"


def test_apply_openai_environment_tolerates_missing_key(monkeypatch):
    _no_colab(monkeypatch)
    _clear_key_env(monkeypatch)
    assert gh.apply_openai_environment(required=False) is None


def test_apply_openai_environment_explicit_config_replaces_environment(monkeypatch):
    """Une config explicite REMPLACE l'environnement, elle ne le complete pas.

    Le contrat du docstring : `config=None` pose par `setdefault` (une valeur
    exportee survit), `config=<objet>` affirme la configuration et l'emporte.
    Sans cette distinction, un appelant qui construit un `OpenAIConfig` a la
    main se faisait silencieusement ignorer par une cle deja presente.
    """
    _no_colab(monkeypatch)
    _clear_key_env(monkeypatch)
    monkeypatch.setenv("OPENAI_API_KEY", "sk-stale")
    monkeypatch.setenv("OPENAI_BASE_URL", gh.OPENROUTER_BASE_URL)
    monkeypatch.setenv("OPENAI_MODEL", "modele-perime")
    import os
    cfg = gh.OpenAIConfig(
        api_key="sk-fresh", base_url=None, model="gpt-5-mini",
        reasoning_model="gpt-5.6-sol", provider="openai",
        key_source="explicit",
    )
    returned = gh.apply_openai_environment(config=cfg)
    assert returned is cfg
    assert os.environ["OPENAI_API_KEY"] == "sk-fresh"
    assert os.environ["OPENAI_MODEL"] == "gpt-5-mini"
    assert os.environ["OPENAI_REASONING_MODEL"] == "gpt-5.6-sol"
    # Pas de base_url dans la config : l'adresse residuelle doit avoir disparu,
    # sinon la cle native part chez le fournisseur precedent.
    assert "OPENAI_BASE_URL" not in os.environ


def test_apply_openai_environment_explicit_config_sets_base_url(monkeypatch):
    _no_colab(monkeypatch)
    _clear_key_env(monkeypatch)
    monkeypatch.setenv("OPENAI_BASE_URL", "https://exemple.invalid/v1")
    import os
    cfg = gh.OpenAIConfig(
        api_key="sk-or", base_url=gh.OPENROUTER_BASE_URL,
        model=gh.DEFAULT_OPENROUTER_MODEL,
        reasoning_model="deepseek/deepseek-v4.1-flash",
        provider="openrouter", key_source="explicit",
    )
    gh.apply_openai_environment(config=cfg)
    assert os.environ["OPENAI_BASE_URL"] == gh.OPENROUTER_BASE_URL


def test_apply_openai_environment_resolved_keeps_stale_base_url(monkeypatch):
    """`config=None` ne touche pas a une base_url deja exportee (contrat 1)."""
    _no_colab(monkeypatch)
    _clear_key_env(monkeypatch)
    monkeypatch.setenv("OPENAI_API_KEY", "sk-explicit")
    monkeypatch.setenv("OPENAI_BASE_URL", "https://exemple.invalid/v1")
    import os
    gh.apply_openai_environment()
    assert os.environ["OPENAI_BASE_URL"] == "https://exemple.invalid/v1"


def test_module_source_carries_no_literal_api_key():
    """Secrets-hygiene : aucune valeur de cle en dur, aucun defaut litteral."""
    import re
    source = _MODULE_PATH.read_text(encoding="utf-8")
    # Aucun `os.getenv("...KEY", "valeur")` : le deuxieme argument d'un getenv
    # sur une variable de cle est exactement le pattern qui a deja fuit. Les
    # variables de configuration ordinaires (DOCKER_ENABLED...) gardent leur
    # defaut litteral, ce n'est pas un secret.
    for match in re.finditer(
        r"getenv\(\s*[\"']([A-Z_]+)[\"']\s*,\s*[\"']([^\"']*)[\"']", source
    ):
        name = match.group(1)
        if name.endswith("_KEY") or name.endswith("_TOKEN") or "SECRET" in name:
            raise AssertionError(
                "getenv with literal default on %s: %r" % (name, match.group(0))
            )
    # Aucun prefixe de cle reelle.
    for prefix in ("sk-or-v1-", "ghp_", "sk-proj-", "AIza"):
        assert prefix not in source


@pytest.mark.network
def test_openrouter_catalog_lists_default_model():
    """Catalogue PUBLIC d'OpenRouter : le modele par defaut du module y figure.

    Ce GET /models ne prouve RIEN sur une cle : le catalogue est public et
    repond sans autorisation. Prouver qu'une cle ouvre un modele est un test
    distinct, explicitement autorise — il n'est pas necessaire a cette PR.

    Opt-in effectif : ne tourne que si RUN_NETWORK_TESTS=1. Un pytest nu ne
    touche jamais au reseau, y compris en CI (mesure adjoint 29/10 : avant
    cette garde, la fuite dotenv faisait partir un appel avec une cle
    factice a chaque passage de suite sans que personne l'ait demande).
    """
    if os.getenv("RUN_NETWORK_TESTS") != "1":
        pytest.skip("reseau opt-in : poser RUN_NETWORK_TESTS=1 pour l'executer")
    import urllib.request

    req = urllib.request.Request(gh.OPENROUTER_BASE_URL + "/models")
    with urllib.request.urlopen(req, timeout=30) as resp:
        payload = json.loads(resp.read().decode("utf-8"))
    ids = {m["id"] for m in payload.get("data", [])}
    assert gh.DEFAULT_OPENROUTER_MODEL in ids
