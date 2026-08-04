"""Tests for scripts/audit/regen_img1_dalle3.py (#8624 Stop & Repair asset regen).

The tool re-generates a legacy `.webp` asset whose title banner had a non-ASCII
glyph (□) cooked in, by calling OpenAI gpt-image-1 then re-burning an ASCII-only
title via matplotlib. It is the canonical "Stop & Repair" example (c.916 / PR
#8636): never scrub a committed output, fix the cause + re-execute.

Covers, all hermetically (no network, no real OpenAI key, no live repo asset):
  - ``_ascii_title`` : the non-ASCII stripping filter (the Stop & Repair core),
    including the actual □ glyph that motivated the tool.
  - ``_load_env`` : .env parsing (comments / blanks / KEY=VALUE) + SystemExit(2)
    when the file is absent.
  - ``audit`` : exit-code contract (0 present+large / 1 absent / 2 tiny).
  - ``_burn_title`` : renders a real tiny PNG -> .webp with an ASCII title;
    verifies the output is a non-empty webp the PIL can reopen.
  - ``_call_openai_image`` : urllib is monkeypatched so the b64 decode path and
    the missing-``b64_json`` RuntimeError are exercised without a network call.
  - ``main`` : --audit / --check / default(--regen) argument routing.
"""
import base64
import importlib.util
import io
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "regen_img1_dalle3.py"


def _load():
    spec = importlib.util.spec_from_file_location("regen_img1_dalle3", CHECK_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# --------------------------------------------------------------------------- #
# _ascii_title — the Stop & Repair non-ASCII filter (c.916 / PR #8636)
# --------------------------------------------------------------------------- #
def test_ascii_title_passthrough_ascii():
    mod = _load()
    assert mod._ascii_title("Paysage Urbain Futuriste - gpt-image-1") == \
        "Paysage Urbain Futuriste - gpt-image-1"


def test_ascii_title_strips_box_glyph_that_motivated_the_tool():
    """The legacy asset carried a □ (U+25A1) cooked into the banner."""
    mod = _load()
    out = mod._ascii_title("Titre avec □ glyphe")
    assert "□" not in out
    assert "Titre avec" in out  # surrounding ASCII survives


def test_ascii_title_strips_accents_and_emoji():
    """Each non-ASCII RUN becomes ONE space; ASCII spaces are preserved as-is."""
    mod = _load()
    # "café ☕ résumé": é→" ", ascii-space, ☕→" ", ascii-space, résumé→"r sum "
    # => "caf" + 4 chars(é,space,☕,space) + "r sum", then strip -> "caf    r sum"
    assert mod._ascii_title("café ☕ résumé") == "caf    r sum"


def test_ascii_title_collapses_nonascii_runs_only():
    """A run of several non-ASCII chars collapses to a single space; ASCII
    spaces around it are kept untouched (the filter targets glyphs, not spaces)."""
    mod = _load()
    # "  abc  éàü  def  " -> "abc" + "  "(ascii) + " "(éàü run) + "  "(ascii) + "def"
    assert mod._ascii_title("  abc  éàü  def  ") == "abc     def"


def test_ascii_title_module_constant_is_ascii_after_filter():
    """The TITLE constant the tool burns must be ASCII-clean post-filter."""
    mod = _load()
    cleaned = mod._ascii_title(mod.TITLE)
    assert cleaned.isascii()
    assert "gpt-image-1" in cleaned


# --------------------------------------------------------------------------- #
# _load_env — .env parsing
# --------------------------------------------------------------------------- #
def test_load_env_parses_key_value(tmp_path, monkeypatch):
    mod = _load()
    env = tmp_path / ".env"
    env.write_text(
        "# a comment\n"
        "\n"
        "OPENAI_API_KEY=sk-test-123\n"
        "OTHER = spaced \n"
        "NO_EQUALS_LINE_SHOULD_BE_SKIPPED\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(mod, "ENV_PATH", env)
    parsed = mod._load_env()
    assert parsed["OPENAI_API_KEY"] == "sk-test-123"
    assert parsed["OTHER"] == "spaced"          # stripped
    assert "NO_EQUALS_LINE_SHOULD_BE_SKIPPED" not in parsed
    assert "# a comment" not in parsed


def test_load_env_exits_when_missing(tmp_path, monkeypatch):
    mod = _load()
    monkeypatch.setattr(mod, "ENV_PATH", tmp_path / "absent.env")
    with pytest.raises(SystemExit) as exc:
        mod._load_env()
    assert exc.value.code == 2


# --------------------------------------------------------------------------- #
# audit — exit-code contract
# --------------------------------------------------------------------------- #
def _png_bytes(size_px=64):
    """A minimal valid RGBA PNG (pure PIL, no network)."""
    from PIL import Image
    buf = io.BytesIO()
    Image.new("RGBA", (size_px, size_px), (10, 20, 30, 255)).save(buf, format="PNG")
    return buf.getvalue()


def test_audit_returns_1_when_asset_absent(tmp_path, monkeypatch):
    mod = _load()
    monkeypatch.setattr(mod, "ASSET_PATH", tmp_path / "missing.webp")
    assert mod.audit() == 1


def test_audit_returns_2_when_asset_too_small(tmp_path, monkeypatch):
    mod = _load()
    small = tmp_path / "tiny.webp"
    small.write_bytes(b"x" * 500)  # < 10_000 threshold
    monkeypatch.setattr(mod, "ASSET_PATH", small)
    assert mod.audit() == 2


def test_audit_returns_0_when_asset_present_and_large(tmp_path, monkeypatch):
    mod = _load()
    big = tmp_path / "ok.webp"
    big.write_bytes(b"x" * 20_000)  # >= 10_000
    monkeypatch.setattr(mod, "ASSET_PATH", big)
    assert mod.audit() == 0


# --------------------------------------------------------------------------- #
# _burn_title — real matplotlib render (PIL + matplotlib available, Rule F)
# --------------------------------------------------------------------------- #
def test_burn_title_writes_openable_webp(tmp_path):
    mod = _load()
    out = tmp_path / "rendered.webp"
    mod._burn_title(_png_bytes(), "ASCII Title - gpt-image-1", out)
    assert out.exists() and out.stat().st_size > 0
    # PIL must be able to reopen the produced webp
    from PIL import Image
    img = Image.open(out)
    img.load()
    assert img.size[0] > 0 and img.size[1] > 0


def test_burn_title_accepts_ascii_filtered_title(tmp_path):
    """The tool always passes _ascii_title(TITLE) in; verify it tolerates the
    post-filter string (no stray non-ASCII to crash matplotlib)."""
    mod = _load()
    out = tmp_path / "rendered2.webp"
    safe = mod._ascii_title(mod.TITLE)
    mod._burn_title(_png_bytes(), safe, out)
    assert out.exists() and out.stat().st_size > 1000


# --------------------------------------------------------------------------- #
# _call_openai_image — urllib monkeypatched (no network)
# --------------------------------------------------------------------------- #
class _FakeResp:
    def __init__(self, body_bytes):
        self._body = body_bytes

    def __enter__(self):
        return self

    def __exit__(self, *a):
        return False

    def read(self):
        return self._body


def test_call_openai_image_decodes_b64(monkeypatch):
    mod = _load()
    raw_png = _png_bytes()
    body = '{"data": [{"b64_json": "%s"}]}' % base64.b64encode(raw_png).decode()
    captured = {}

    def fake_urlopen(req, timeout):
        captured["url"] = req.full_url
        captured["timeout"] = timeout
        captured["auth"] = req.get_header("Authorization")
        return _FakeResp(body.encode("utf-8"))

    # urllib is imported LOCALLY in _call_openai_image, so patch the real module.
    monkeypatch.setattr("urllib.request.urlopen", fake_urlopen)
    out = mod._call_openai_image("sk-test", "a prompt")
    assert out == raw_png
    assert captured["url"] == "https://api.openai.com/v1/images/generations"
    assert captured["timeout"] == 120
    assert captured["auth"] == "Bearer sk-test"


def test_call_openai_image_missing_b64_raises(monkeypatch):
    mod = _load()
    body = '{"data": [{"url": "https://example.com/img.png"}]}'  # no b64_json

    monkeypatch.setattr("urllib.request.urlopen",
                        lambda req, timeout: _FakeResp(body.encode("utf-8")))
    with pytest.raises(RuntimeError):
        mod._call_openai_image("sk-test", "prompt")


# --------------------------------------------------------------------------- #
# main — argument routing
# --------------------------------------------------------------------------- #
def test_main_audit_flag_routes_to_audit(tmp_path, monkeypatch):
    mod = _load()
    big = tmp_path / "ok.webp"
    big.write_bytes(b"x" * 20_000)
    monkeypatch.setattr(mod, "ASSET_PATH", big)
    monkeypatch.setattr(sys, "argv", ["regen_img1_dalle3.py", "--audit"])
    assert mod.main() == 0


def test_main_check_flag_routes_to_check(tmp_path, monkeypatch):
    mod = _load()
    big = tmp_path / "ok.webp"
    big.write_bytes(b"x" * 20_000)
    env = tmp_path / ".env"
    env.write_text("OPENAI_API_KEY=sk-test\n", encoding="utf-8")
    monkeypatch.setattr(mod, "ASSET_PATH", big)
    monkeypatch.setattr(mod, "ENV_PATH", env)
    monkeypatch.setattr(sys, "argv", ["regen_img1_dalle3.py", "--check"])
    # deps PIL + matplotlib present (Rule F), key present, asset large -> 0
    assert mod.check() == 0


def test_main_default_routes_to_regen(monkeypatch):
    mod = _load()
    calls = {}

    def fake_regen():
        calls["regen"] = True
        return 0

    monkeypatch.setattr(mod, "regen", fake_regen)
    monkeypatch.setattr(sys, "argv", ["regen_img1_dalle3.py"])
    assert mod.main() == 0
    assert calls.get("regen") is True


def test_regen_returns_3_when_key_missing(tmp_path, monkeypatch):
    mod = _load()
    env = tmp_path / ".env"
    env.write_text("OPENAI_API_KEY=\n", encoding="utf-8")  # empty key
    monkeypatch.setattr(mod, "ENV_PATH", env)
    assert mod.regen() == 3


def test_regen_returns_3_when_placeholder(tmp_path, monkeypatch):
    mod = _load()
    env = tmp_path / ".env"
    env.write_text("OPENAI_API_KEY=<placeholder>\n", encoding="utf-8")
    monkeypatch.setattr(mod, "ENV_PATH", env)
    assert mod.regen() == 3


def test_regen_calls_api_and_writes_asset(tmp_path, monkeypatch):
    """End-to-end regen with the API + render mocked: key present -> API ->
    burn -> asset written -> 0."""
    mod = _load()
    env = tmp_path / ".env"
    env.write_text("OPENAI_API_KEY=sk-test\n", encoding="utf-8")
    out_asset = tmp_path / "img1-dalle3.webp"
    monkeypatch.setattr(mod, "ENV_PATH", env)
    monkeypatch.setattr(mod, "ASSET_PATH", out_asset)
    monkeypatch.setattr(mod, "_call_openai_image", lambda key, prompt: _png_bytes(120))
    rc = mod.regen()
    assert rc == 0
    assert out_asset.exists() and out_asset.stat().st_size > 0
