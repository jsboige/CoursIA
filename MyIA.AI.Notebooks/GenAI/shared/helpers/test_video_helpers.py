#!/usr/bin/env python3
"""Pytest suite for `GenAI/shared/helpers/video_helpers.py`.

Co-located with the module under `shared/helpers/`. CPU-only, no network, no
real video decode/encode, no ffmpeg/decord/moviepy/imageio/matplotlib required
at import time. The module imports only stdlib + numpy at top level and lazily
imports each media dep inside its function (ffmpeg inside get_video_info, decord
+ PIL inside extract_frames, imageio inside frames_to_video, moviepy inside the
edit wrappers). The module is the Phase-2 GenAI Video utility consumed across
the GenAI Video notebooks and had 0 dedicated Python test coverage before this
PR.

Strategy: every late-imported dep is replaced with a stub injected into
`sys.modules` just before the call (the function's `import X` then resolves to
the stub). For functions returning parsed metadata (get_video_info) the stub
returns a canned ffprobe dict and the real parse logic (fps fraction, stream
selection, int coercion) is exercised. For the edit wrappers the stub records
the calls and the test verifies directory creation + delegation + cleanup.
"""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path
from types import SimpleNamespace, ModuleType

import numpy as np
import pytest

# Load the module by path (lives under shared/helpers/, top-level stdlib + numpy
# only -> loads cleanly without optional media deps installed).
_MODULE_PATH = Path(__file__).resolve().parent / "video_helpers.py"
_spec = importlib.util.spec_from_file_location("video_helpers", _MODULE_PATH)
vh = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(vh)


def _install_fake_module(name, attrs):
    """Register a fake top-level module `name` with given attrs into sys.modules.

    Returns the fake module so the caller can read back recorded state. Each
    function under test does `import <name>` (inside its body) so the late import
    resolves to this stub.
    """
    mod = ModuleType(name)
    for k, v in attrs.items():
        setattr(mod, k, v)
    sys.modules[name] = mod
    return mod


# --------------------------------------------------------------------------
# get_video_info — ffprobe parse logic
# --------------------------------------------------------------------------


def _ffprobe(streams, fmt):
    return {"streams": streams, "format": fmt}


def test_get_video_info_parses_video_and_audio_streams(monkeypatch):
    probe = _ffprobe(
        streams=[
            {"codec_type": "video", "r_frame_rate": "30/1", "width": 1920,
             "height": 1080, "codec_name": "h264", "nb_frames": "900"},
            {"codec_type": "audio", "codec_name": "aac",
             "sample_rate": "48000", "channels": 2},
        ],
        fmt={"duration": "60.0", "size": "1048576", "format_name": "mp4"},
    )
    fake = _install_fake_module("ffmpeg", {"probe": lambda p: probe})
    try:
        info = vh.get_video_info("vid.mp4")
    finally:
        sys.modules.pop("ffmpeg", None)

    assert info["path"] == "vid.mp4"
    assert info["duration_seconds"] == 60.0
    assert info["size_bytes"] == 1048576
    assert info["format"] == "mp4"
    # Video stream parsed.
    assert info["width"] == 1920
    assert info["height"] == 1080
    assert info["fps"] == 30.0
    assert info["video_codec"] == "h264"
    assert info["total_frames"] == 900
    # Audio stream parsed.
    assert info["audio_codec"] == "aac"
    assert info["audio_sample_rate"] == 48000
    assert info["audio_channels"] == 2


def test_get_video_info_fps_fraction_parsing(monkeypatch):
    # r_frame_rate = "30000/1001" (29.97 NTSC) must parse to ~29.97.
    probe = _ffprobe(
        streams=[{"codec_type": "video", "r_frame_rate": "30000/1001"}],
        fmt={"duration": "10", "size": "0"},
    )
    _install_fake_module("ffmpeg", {"probe": lambda p: probe})
    try:
        info = vh.get_video_info("v.mp4")
    finally:
        sys.modules.pop("ffmpeg", None)
    assert info["fps"] == pytest.approx(29.97, abs=0.01)


def test_get_video_info_marks_has_audio_false_when_no_audio_stream():
    probe = _ffprobe(
        streams=[{"codec_type": "video", "r_frame_rate": "25/1"}],
        fmt={"duration": "5", "size": "0"},
    )
    _install_fake_module("ffmpeg", {"probe": lambda p: probe})
    try:
        info = vh.get_video_info("silent.mp4")
    finally:
        sys.modules.pop("ffmpeg", None)
    assert info["has_audio"] is False


def test_get_video_info_returns_error_dict_on_probe_exception():
    # ffmpeg.probe raises -> the broad except returns an error dict (quirk: the
    # coarse try/except wraps the whole probe, so any field failure loses all
    # metadata). Pinned behavior.
    _install_fake_module("ffmpeg", {"probe": lambda p: (_ for _ in ()).throw(RuntimeError("no file"))})
    try:
        info = vh.get_video_info("missing.mp4")
    finally:
        sys.modules.pop("ffmpeg", None)
    assert info["path"] == "missing.mp4"
    assert "error" in info
    assert "no file" in info["error"]


# --------------------------------------------------------------------------
# extract_frames — uniform index distribution
# --------------------------------------------------------------------------


class _FakeBatch:
    def __init__(self, frames):
        self._frames = frames

    def asnumpy(self):
        return np.array(self._frames)


class _FakeVideoReader:
    """Fake decord.VideoReader returning `n_total` dummy frames."""

    def __init__(self, n_total, fps=25.0):
        self._n = n_total
        self._fps = fps

    def __len__(self):
        return self._n

    def get_batch(self, indices):
        # Return one dummy frame per requested index.
        frames = [np.zeros((4, 4, 3), dtype=np.uint8) + i for i in indices]
        return _FakeBatch(frames)

    def get_avg_fps(self):
        return self._fps


def _install_decord_stub(reader):
    return _install_fake_module("decord", {
        "VideoReader": lambda path: reader,
        "bridge": SimpleNamespace(set_bridge=lambda b: None),
    })


def test_extract_frames_returns_all_when_n_frames_exceeds_total(monkeypatch, tmp_path):
    reader = _FakeVideoReader(n_total=3)
    _install_decord_stub(reader)
    fake_pil = _install_fake_module("PIL", {"Image": SimpleNamespace(
        fromarray=lambda arr: SimpleNamespace(arr=arr))})
    sys.modules["PIL.Image"] = fake_pil.Image
    try:
        images = vh.extract_frames("v.mp4", n_frames=8)
    finally:
        sys.modules.pop("decord", None)
        sys.modules.pop("PIL", None)
        sys.modules.pop("PIL.Image", None)
    # n_frames (8) >= total (3) -> returns all 3 frames.
    assert len(images) == 3


def test_extract_frames_uniform_distribution(monkeypatch, tmp_path):
    reader = _FakeVideoReader(n_total=100)
    _install_decord_stub(reader)
    fake_pil = _install_fake_module("PIL", {"Image": SimpleNamespace(
        fromarray=lambda arr: SimpleNamespace(arr=arr))})
    sys.modules["PIL.Image"] = fake_pil.Image
    try:
        images = vh.extract_frames("v.mp4", n_frames=4)
    finally:
        sys.modules.pop("decord", None)
        sys.modules.pop("PIL", None)
        sys.modules.pop("PIL.Image", None)
    assert len(images) == 4


def test_extract_frames_saves_to_output_dir_when_given(monkeypatch, tmp_path):
    reader = _FakeVideoReader(n_total=10)
    _install_decord_stub(reader)
    saved = []

    class _FakeImg:
        def save(self, path):
            saved.append(Path(path))

    fake_pil = _install_fake_module("PIL", {"Image": SimpleNamespace(fromarray=lambda arr: _FakeImg())})
    sys.modules["PIL.Image"] = fake_pil.Image
    out = tmp_path / "frames_out"
    try:
        vh.extract_frames("v.mp4", n_frames=3, output_dir=str(out))
    finally:
        sys.modules.pop("decord", None)
        sys.modules.pop("PIL", None)
        sys.modules.pop("PIL.Image", None)
    assert out.exists()
    assert len(saved) == 3
    # Filenames are zero-padded frame_NNNN.png.
    assert all(p.name.startswith("frame_") and p.suffix == ".png" for p in saved)


# --------------------------------------------------------------------------
# extract_frames_at_times — timestamp -> index conversion
# --------------------------------------------------------------------------


def test_extract_frames_at_times_uses_fps_to_compute_indices(monkeypatch):
    reader = _FakeVideoReader(n_total=100, fps=25.0)
    _install_decord_stub(reader)
    fake_pil = _install_fake_module("PIL", {"Image": SimpleNamespace(
        fromarray=lambda arr: SimpleNamespace(arr=arr))})
    sys.modules["PIL.Image"] = fake_pil.Image
    try:
        # At 25 fps: t=0 -> idx 0, t=1 -> idx 25, t=3 -> idx 75.
        images = vh.extract_frames_at_times("v.mp4", [0.0, 1.0, 3.0])
    finally:
        sys.modules.pop("decord", None)
        sys.modules.pop("PIL", None)
        sys.modules.pop("PIL.Image", None)
    assert len(images) == 3


def test_extract_frames_at_times_clamps_to_last_frame(monkeypatch):
    reader = _FakeVideoReader(n_total=10, fps=25.0)
    _install_decord_stub(reader)
    fake_pil = _install_fake_module("PIL", {"Image": SimpleNamespace(
        fromarray=lambda arr: SimpleNamespace(arr=arr))})
    sys.modules["PIL.Image"] = fake_pil.Image
    try:
        # t=100s at 25fps = idx 2500, clamped via min(idx, len-1) = 9.
        images = vh.extract_frames_at_times("v.mp4", [100.0])
    finally:
        sys.modules.pop("decord", None)
        sys.modules.pop("PIL", None)
        sys.modules.pop("PIL.Image", None)
    assert len(images) == 1


# --------------------------------------------------------------------------
# frames_to_video — imageio writer delegation + dir creation
# --------------------------------------------------------------------------


class _FakeWriter:
    def __init__(self):
        self.appended = []

    def append_data(self, frame):
        self.appended.append(frame)

    def close(self):
        self.closed = True


def test_frames_to_video_creates_parent_dir_and_appends_frames(monkeypatch, tmp_path):
    writer = _FakeWriter()
    fake_imageio = _install_fake_module("imageio", {
        "get_writer": lambda path, fps=None, codec=None: writer,
    })
    out = tmp_path / "nested" / "deep" / "out.mp4"
    frames = [np.zeros((2, 2, 3), dtype=np.uint8) for _ in range(3)]
    try:
        vh.frames_to_video(frames, fps=24.0, output_path=str(out))
    finally:
        sys.modules.pop("imageio", None)
    assert out.parent.exists()
    assert len(writer.appended) == 3
    assert getattr(writer, "closed", False) is True


# --------------------------------------------------------------------------
# Edit wrappers (moviepy) — dir creation + delegation + cleanup
# --------------------------------------------------------------------------


class _FakeClip:
    def __init__(self):
        self.closed = False
        self.audio_set = None

    def subclip(self, start, end=None):
        return self

    def resize(self, size):
        return self

    def set_audio(self, audio):
        self.audio_set = audio
        return self

    def write_videofile(self, path, logger=None):
        self.written = path

    def close(self):
        self.closed = True


def _install_moviepy_stub(video_cls=None, audio_cls=None, concat_fn=None):
    editor = ModuleType("moviepy.editor")
    if video_cls is not None:
        editor.VideoFileClip = video_cls
    if audio_cls is not None:
        editor.AudioFileClip = audio_cls
    if concat_fn is not None:
        editor.concatenate_videoclips = concat_fn
    mod = ModuleType("moviepy")
    mod.editor = editor
    sys.modules["moviepy"] = mod
    sys.modules["moviepy.editor"] = editor
    return editor


def test_concatenate_videos_creates_output_dir_and_closes_all_clips(monkeypatch, tmp_path):
    clip_a = _FakeClip()
    clip_b = _FakeClip()
    final = _FakeClip()
    inputs = [clip_a, clip_b]

    def _concat(cs):
        assert len(cs) == 2
        return final

    _install_moviepy_stub(video_cls=lambda p: inputs.pop(0), concat_fn=_concat)
    out = tmp_path / "out" / "concat.mp4"
    try:
        vh.concatenate_videos(["a.mp4", "b.mp4"], str(out))
    finally:
        sys.modules.pop("moviepy", None)
        sys.modules.pop("moviepy.editor", None)
    assert out.parent.exists()
    # All clips closed: the 2 inputs + the concatenated final.
    assert clip_a.closed is True
    assert clip_b.closed is True
    assert final.closed is True
    assert final.written == str(out)


def test_trim_video_creates_output_dir_and_writes_segment(monkeypatch, tmp_path):
    clip = _FakeClip()
    _install_moviepy_stub(video_cls=lambda p: clip)
    out = tmp_path / "seg" / "trim.mp4"
    try:
        vh.trim_video("v.mp4", 1.0, 2.5, str(out))
    finally:
        sys.modules.pop("moviepy", None)
        sys.modules.pop("moviepy.editor", None)
    assert out.parent.exists()
    assert clip.closed is True
    assert clip.written == str(out)


def test_resize_video_delegates_to_resize(monkeypatch, tmp_path):
    clip = _FakeClip()
    _install_moviepy_stub(video_cls=lambda p: clip)
    out = tmp_path / "r" / "small.mp4"
    try:
        vh.resize_video("v.mp4", 320, 240, str(out))
    finally:
        sys.modules.pop("moviepy", None)
        sys.modules.pop("moviepy.editor", None)
    assert out.parent.exists()
    assert clip.written == str(out)
    assert clip.closed is True


def test_add_audio_to_video_trims_audio_when_longer(monkeypatch, tmp_path):
    video = _FakeClip()

    class _FakeAudio:
        def __init__(self):
            self.duration = 30.0
            self.closed = False
            self.subclipped = None

        def subclip(self, start, end):
            self.subclipped = (start, end)
            return self

        def close(self):
            self.closed = True

    audio = _FakeAudio()
    video.duration = 10.0  # video shorter than audio(30s) -> audio trimmed to 10s
    _install_moviepy_stub(video_cls=lambda p: video, audio_cls=lambda p: audio)
    out = tmp_path / "mix" / "with_audio.mp4"
    try:
        vh.add_audio_to_video("v.mp4", "a.wav", str(out))
    finally:
        sys.modules.pop("moviepy", None)
        sys.modules.pop("moviepy.editor", None)
    assert out.parent.exists()
    # Audio was trimmed because audio.duration > video.duration.
    assert audio.subclipped == (0, 10.0)
    assert video.audio_set is audio
