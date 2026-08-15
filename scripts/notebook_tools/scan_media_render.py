"""Scan des notebooks GenAI appelant une primitive media sans sortie media rendue.

Reimplementation du predicat du scan #10996 (30 notebooks « appelant une primitive
media, 0 sortie media rendue ») avec les 5 angles morts mesures corriges
(lecon L965, tri 30/30 : 29 faux positifs ; le 5e mesure sur
mesurer-la-derive-dun-copilot) :

1. Data-URIs base64 dans les outputs `text/html` comptes comme media rendu
   (`display(Audio/Image/Video(...))` produit un data-URI sous papermill, pas un
   mime separe — lecon #10776).
2. Lignes `from`/`import` ignorees dans la detection d'appels de primitives.
3. `widgets.HTML(...)` (ipywidgets) exclu — ce n'est pas une primitive media.
4. Media livre en fichier side-car (`savefig`, `export_to_video`) dont le fichier
   est tracke par git a cote du notebook, compte comme media rendu.
5. Definition de fonction `def image(v)` exclue — ce n'est pas un appel a la
   primitive `Image(...)` (mesure sur mesurer-la-derive-dun-copilot).

Verdicts par notebook :
  NO_MEDIA_PRIMITIVE  aucune primitive media appelee (hors imports) — hors scope
  MEDIA_RENDERED      au moins un media rendu (data-URI, mime separe, side-car)
  NO_MEDIA_RENDERED   primitive appelee, aucun media rendu — candidat defaut

Usage:
  python scan_media_render.py --repo <racine> [--notebooks <glob>...] [--legacy]
  python scan_media_render.py --repo <racine> --compare   # legacy vs enrichi

Le verdict final d'un notebook (REPARABLE / NON-REPARABLE / FAUX POSITIF) reste un
jugement de domaine : ce scan trie le bruit du predicat, il ne qualifie pas les
vrais defauts. Voir #10996 pour le tri humain des 30.
"""

from __future__ import annotations

import argparse
import base64
import binascii
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

# Primitives media recherchees dans les sources (hors imports, hors widgets).
# `HTML(` n'est PAS une primitive media : un notebook widgets (04-3) rend une
# interface, pas un media — angle mort 3. `display(HTML(...))` et
# `display(production_ui)` ne comptent donc pas non plus (display d'un widget).
MEDIA_CALL_RE = re.compile(
    r"display\(\s*(?:Audio|Image|Video)"    # display(Audio/Image/Video(...))
    r"|(?<!\w)Audio\("                      # constructeurs Audio/Image/Video
    r"|(?<!\w)Image\("
    r"|(?<!\w)Video\("
    r"|export_to_video\("
    r"|plt\.show\(|(?:fig|ax|plt)\.savefig\("
    r"|IPython\.display",
    re.IGNORECASE,
)
# Noms de primitives pour l'affichage du rapport, par sous-chaine detectee.
CALL_LABELS = (
    ("display(audio", "display(Audio/Image/Video)"),
    ("display(image", "display(Audio/Image/Video)"),
    ("display(video", "display(Audio/Image/Video)"),
    ("audio(", "Audio("), ("image(", "Image("), ("video(", "Video("),
    ("export_to_video(", "export_to_video("),
    ("plt.show(", "plt.show("), (".savefig(", "savefig("),
    ("ipython.display", "IPython.display"),
)
# Exclusions : prefixes widgets / ipywidgets (angle mort 3).
WIDGET_PREFIX_RE = re.compile(r"(?:widgets|ipywidgets)\.\s*(?:Audio|Image|Video|HTML)\(")
# Ligne d'import/from entiere (angle mort 2).
IMPORT_LINE_RE = re.compile(r"^\s*(?:from|import)\s+\S+.*$", re.MULTILINE)
# Definition de fonction `def image(v)` n'est pas un appel (angle mort 5,
# mesure sur mesurer-la-derive-dun-copilot : `def image(v)` matchait Image()).
DEF_LINE_RE = re.compile(r"^\s*def\s+\w+\s*\(", re.MULTILINE)
# Data-URI media, partout dans les outputs (pas seulement text/html, pas besoin de
# `src="` : le format committe par papermill n'a pas d'attribut src — mesure c.109 :
# 0 data-URI avec src= vs 175 verifiables par magic dans GenAI (angle mort 1).
DATA_URI_RE = re.compile(
    r"data:(audio|image|video)/[A-Za-z0-9.+-]+;base64,([A-Za-z0-9+/=\s]+)",
    re.IGNORECASE,
)
# Mimes separees dans les outputs (le predicat original ne comptait que ceux-ci).
MIME_SEPARATED_RE = re.compile(r"^(?:image|audio|video)/", re.IGNORECASE)
# Chemins de fichiers media ecrits par le notebook (angle mort 4).
WRITE_PATH_RE = re.compile(
    r"(?:savefig|export_to_video|write_videofile|save\(|write_audiofile)\(\s*"
    r"[\"']([^\"']+\.(?:png|jpe?g|gif|webp|wav|mp3|mp4|webm|mov|ogg|flac))[\"']",
    re.IGNORECASE,
)
MEDIA_SUFFIXES = {
    ".png", ".jpg", ".jpeg", ".gif", ".webp",
    ".wav", ".mp3", ".mp4", ".webm", ".mov", ".ogg", ".flac",
}


@dataclass
class NotebookResult:
    path: str
    legacy_primitive: bool = False      # predicat original (imports compris)
    primitive_calls: list[str] = field(default_factory=list)
    data_uris: dict[str, int] = field(default_factory=dict)   # par type media
    mimes_separated: dict[str, int] = field(default_factory=dict)
    sidecar_files: list[str] = field(default_factory=list)
    noexec: int = 0
    errors: int = 0
    scan_error: str | None = None       # echec de lecture/parse du notebook

    def verdict(self, legacy: bool = False) -> str:
        """Verdict. En mode legacy, seuls les mimes separees comptent comme media
        rendu (data-URIs et side-cars ignores) — reproduction du predicat #10996."""
        if self.scan_error:
            return "SCAN_ERROR"
        primitives = self.primitive_calls if not legacy else (
            ["legacy"] if self.legacy_primitive else []
        )
        if not primitives:
            return "NO_MEDIA_PRIMITIVE"
        rendered = (self.data_uris or self.mimes_separated or self.sidecar_files) if not legacy else self.mimes_separated
        if rendered:
            return "MEDIA_RENDERED"
        return "NO_MEDIA_RENDERED"


def strip_imports(src: str) -> str:
    return IMPORT_LINE_RE.sub("", src)


_MEDIA_MAGIC: tuple[tuple[bytes, str], ...] = (
    (b"\x89PNG\r\n\x1a\n", "image"),   # PNG
    (b"\xff\xd8\xff", "image"),          # JPEG
    (b"GIF87a", "image"), (b"GIF89a", "image"),
    (b"BM", "image"),                      # BMP
    (b"II*\x00", "image"), (b"MM\x00*", "image"),  # TIFF
    (b"<svg", "image"), (b"<?xml", "image"),         # SVG (texte)
    (b"OggS", "audio"),                    # OGG/Opus/WebM
    (b"ID3", "audio"),                     # MP3 avec tag
    (b"fLaC", "audio"),
    (b"\x1a\x45\xdf\xa3", "video"),     # EBML/WebM/Matroska
    (b"\x00\x00\x01\xb3", "video"),     # MPEG-1 Video
    (b"\x00\x00\x01\xba", "video"),     # MPEG-2 Video
)


def _verify_media_payload(b64: str) -> str | None:
    """Decode le debut d'un payload data-URI et retourne le type media (audio/image/video)
    si le magic binaire est valide. C'est la JUSTESSE : un data-URI dont le payload ne
    decode pas en un media reel (RIFF / PNG / JPEG / GIF / ftyp / MPEG frame sync...) ne
    compte pas comme media rendu — le predicat ne doit pas etre trompe par une donnee
    tronquee ou un faux data-URI."""
    head = b64[:128].strip()
    if not head:
        return None
    try:
        raw = base64.b64decode(head + "=" * (-len(head) % 4))
    except (binascii.Error, ValueError):
        return None
    if len(raw) < 12:
        return None
    if raw[4:8] == b"ftyp":
        return "video"                     # MP4 / QuickTime
    if raw.startswith(b"RIFF"):
        if raw[8:12] == b"WEBP":
            return "image"
        return "audio"                     # WAV / AVI
    for magic, media_type in _MEDIA_MAGIC:
        if raw.startswith(magic):
            return media_type
    if raw[0] == 0xFF and (raw[1] & 0xE0) == 0xE0:
        return "audio"                     # MPEG audio frame sync (MP3/AAC)
    return None


def _count_outputs(nb: dict) -> tuple[dict[str, int], dict[str, int]]:
    data_uris: dict[str, int] = {}
    mimes: dict[str, int] = {}
    for cell in nb.get("cells", []):
        for out in cell.get("outputs", []):
            data = out.get("data", {}) or {}
            for mime, payload in data.items():
                if MIME_SEPARATED_RE.match(mime):
                    mimes[mime] = mimes.get(mime, 0) + 1
                p = "".join(payload) if isinstance(payload, list) else str(payload)
                for m in DATA_URI_RE.finditer(p):
                    media_type = _verify_media_payload(m.group(2))
                    if media_type:
                        data_uris[media_type] = data_uris.get(media_type, 0) + 1
    return data_uris, mimes


def _extract_write_paths(src: str) -> list[str]:
    return [m.group(1) for m in WRITE_PATH_RE.finditer(src)]


def _resolve_sidecar(path: str, nb_file: Path, repo: Path) -> str | None:
    """Retourne le chemin relatif si le fichier ecrit existe et est tracke par git."""
    candidates = [
        nb_file.parent / path,
        repo / path,
        nb_file.parent / "outputs" / Path(path).name,
    ]
    for c in candidates:
        if not c.exists():
            continue
        rel = c.relative_to(repo).as_posix()
        try:
            proc = subprocess.run(
                ["git", "ls-files", "--error-unmatch", "--", rel],
                cwd=repo,
                capture_output=True,
                text=True,
                timeout=15,
            )
        except (subprocess.SubprocessError, OSError):
            return rel  # git indisponible : l'existence suffit en dernier recours
        if proc.returncode == 0:
            return rel
    return None


def scan_notebook(nb_file: Path, repo: Path) -> NotebookResult:
    result = NotebookResult(path=nb_file.relative_to(repo).as_posix())
    try:
        nb = json.loads(nb_file.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError, OSError) as exc:
        result.scan_error = f"{type(exc).__name__}: {exc}"
        return result

    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        ec = cell.get("execution_count")
        if ec is None:
            result.noexec += 1
        for out in cell.get("outputs", []):
            if out.get("output_type") == "error":
                result.errors += 1

    sources = [
        "".join(cell.get("source", [])) if isinstance(cell.get("source"), list)
        else str(cell.get("source", ""))
        for cell in nb.get("cells", [])
        if cell.get("cell_type") == "code"
    ]
    joined = "\n".join(sources)

    # Predicat legacy : imports compris (angle mort 2 non corrige).
    result.legacy_primitive = bool(
        MEDIA_CALL_RE.search(joined) or re.search(r"\bIPython\.display\b", joined)
    )

    # Predicat enrichi : imports et defs retires, widgets exclus, appels precis.
    clean = WIDGET_PREFIX_RE.sub("", DEF_LINE_RE.sub("", strip_imports(joined)))
    for m in MEDIA_CALL_RE.finditer(clean):
        text = m.group(0)
        label = next((lbl for pat, lbl in CALL_LABELS if pat.lower() in text.lower()), text)
        if label not in result.primitive_calls:
            result.primitive_calls.append(label)

    result.data_uris, result.mimes_separated = _count_outputs(nb)

    for path in _extract_write_paths(joined):
        resolved = _resolve_sidecar(path, nb_file, repo)
        if resolved:
            result.sidecar_files.append(resolved)

    return result


def discover_tracked_notebooks(repo: Path) -> list[Path]:
    """Notebooks suivis par git (`git ls-files`) — exclut untracked/gitignores
    (ex. research.ipynb invalide sous ESGF-2026/lean-workspace, hors depot).
    Fallback sur le glob disque si git est indisponible."""
    try:
        proc = subprocess.run(
            ["git", "-C", str(repo), "ls-files"],
            capture_output=True, text=True, encoding="utf-8", timeout=30,
        )
    except (subprocess.SubprocessError, OSError):
        return sorted(repo.glob("MyIA.AI.Notebooks/**/*.ipynb"))
    if proc.returncode != 0:
        return sorted(repo.glob("MyIA.AI.Notebooks/**/*.ipynb"))
    return sorted(
        repo / line
        for line in proc.stdout.splitlines()
        if line.startswith("MyIA.AI.Notebooks/") and line.endswith(".ipynb")
    )


def discover_notebooks(repo: Path, globs: list[str]) -> list[Path]:
    if globs:
        out: list[Path] = []
        for g in globs:
            out.extend(repo.glob(g))
        return sorted(out)
    return discover_tracked_notebooks(repo)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", required=True, type=Path, help="racine du depot git")
    ap.add_argument("--notebooks", nargs="*", default=None, help="globs (defaut: GenAI/**/*.ipynb)")
    ap.add_argument("--legacy", action="store_true", help="predicat original non corrige")
    ap.add_argument("--compare", action="store_true", help="affiche legacy vs enrichi")
    ap.add_argument("--json", action="store_true", help="sortie JSON")
    args = ap.parse_args()

    repo = args.repo.resolve()
    notebooks = discover_notebooks(repo, args.notebooks)

    results = [scan_notebook(nb, repo) for nb in notebooks]

    if args.compare:
        legacy_hits = [r for r in results if r.verdict(legacy=True) == "NO_MEDIA_RENDERED"]
        enriched_hits = [r for r in results if r.verdict() == "NO_MEDIA_RENDERED"]
        legacy_paths = {r.path for r in legacy_hits}
        print(f"=== {repo.name} — {len(results)} notebooks ===")
        print(f"Predicat legacy  (imports comptes, data-URIs/sidecars ignores) : {len(legacy_hits)} signales")
        print(f"Predicat enrichi (5 angles morts corriges)                     : {len(enriched_hits)} signales")
        print()
        for r in legacy_hits:
            mark = "  [FP CORRIGE par l'enrichi]" if r.path not in legacy_paths or r.verdict() != "NO_MEDIA_RENDERED" else "  [vrai candidat]"
            print(f"  legacy : {r.path}{mark}")
        for r in enriched_hits:
            print(f"  enrichi: {r.path}  calls={r.primitive_calls}")
        return 0

    if args.json:
        out = []
        for r in results:
            d = r.__dict__.copy()
            d["verdict"] = r.verdict(legacy=args.legacy)
            out.append(d)
        print(json.dumps(out, indent=2, ensure_ascii=False))
        return 0

    counts = {
        "NO_MEDIA_PRIMITIVE": 0, "MEDIA_RENDERED": 0,
        "NO_MEDIA_RENDERED": 0, "SCAN_ERROR": 0,
    }
    for r in results:
        counts[r.verdict(legacy=args.legacy)] += 1
    print(f"=== {repo.name} — {len(results)} notebooks ===")
    for verdict, n in counts.items():
        print(f"{verdict}: {n}")
    print()
    for r in results:
        if r.verdict(legacy=args.legacy) == "NO_MEDIA_RENDERED":
            print(f"  CANDIDAT: {r.path}  calls={r.primitive_calls}  noexec={r.noexec} errors={r.errors}")
    for r in results:
        if r.scan_error:
            print(f"  SCAN_ERROR: {r.path} — {r.scan_error}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
