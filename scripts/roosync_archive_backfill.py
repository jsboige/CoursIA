#!/usr/bin/env python3
"""Scan + backfill des archives RooSync sans resume LLM (#8889).

**Contexte (issue #8889)** :

Quand l'auto-condensation d'un dashboard RooSync ne peut pas joindre le LLM
de resume (vLLM localhost:5002), elle degrade en **truncation fallback** : les
messages sont archives verbatim, mais **sans resume**. Le dashboard vivant
garde alors un stub pour cette fenetre, et **rien ne repasse jamais** derriere
pour combler quand le LLM revient. Mesure : ~11.6% des archives (537/4615)
n'ont jamais recu de resume.

**Aucune perte de contenu** : les archives sont verbatim sur disque, le
format est `archive/workspace-<name>-<ISO>-fallback.md` avec frontmatter
`llmGenerated: false` + `fallbackTruncation: true`. Le probleme est
**lisibilite** du canal principal, pas integrite.

**Scope de cet outil** :

- `--list` : imprime un tableau (date, dashboard, taille, nb messages) pour
  toutes les archives fallback detectees
- `--report` : statistiques agregees par dashboard + export JSON
- `--backfill <path>` : marque une archive pour backfill manuel (sans appel
  LLM — pose juste un tag `markForBackfill: true` dans le frontmatter, le
  backfill reel reste a la charge d'un operateur humain ou d'un script
  dedie branchant vLLM)
- `--summarize` : passe de rattrapage bornee — pour chaque archive fallback
  de la fenetre (plus recentes d'abord), demande un resume a un endpoint
  OpenAI-compatible (`--base-url`, defaut vLLM:5002 ; sur lane Ollama :
  `--base-url http://localhost:11434/v1 --model <id>`), insere le bloc
  resume AVANT les messages verbatim, bascule `llmGenerated: true` /
  `fallbackTruncation: false` et ajoute une ligne de provenance
  `backfilledAt`/`backfillModel`. S'arrete au premier echec LLM (jamais
  dans le chemin d'un append : outil autonome, l'auto-condensation n'est
  pas touchee). `--dry-run` liste les candidates sans appel LLM.

**Hors scope** : toucher au dashboard vivant, modifier le format d'archive
existant, la stabilisation vLLM (deja portee par les watchdogs, cf #8889).

**§ SOTA** (cf. `.claude/rules/sota-not-workaround.md`) : l'outil s'appuie sur le format verbatim
existant (pas de workaround degrade), aucune reinvention du frontmatter,
lecture regex stricte. Le verdict de fallback (`llmGenerated: false` ET
`fallbackTruncation: true`) est implemente tel que documente dans le body
de #8889.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Iterable, Iterator

# --- Frontmatter parsing ------------------------------------------------------

# Le frontmatter RooSync est un mini-header YAML-like au debut du fichier
# archive. Exemple verbatim (cf #8889 body) :
#
# ---
# messageCount: 8
# llmGenerated: false
# fallbackTruncation: true
# ---
FRONTMATTER_RE = re.compile(
    r"^---\s*\n(?P<body>.*?)\n---\s*\n",
    re.DOTALL | re.MULTILINE,
)


@dataclass(frozen=True)
class ArchiveFrontmatter:
    """Frontmatter parse d'une archive RooSync."""
    message_count: int | None = None
    llm_generated: bool | None = None
    fallback_truncation: bool | None = None
    raw: dict[str, str] = field(default_factory=dict)


def parse_frontmatter(text: str) -> ArchiveFrontmatter:
    """Parse le frontmatter YAML-like. Tolerance : champs manquants = None."""
    match = FRONTMATTER_RE.match(text)
    if not match:
        return ArchiveFrontmatter(raw={})
    raw: dict[str, str] = {}
    for line in match.group("body").splitlines():
        line = line.strip()
        if not line or ":" not in line:
            continue
        key, _, value = line.partition(":")
        raw[key.strip()] = value.strip()

    def _int(key: str) -> int | None:
        v = raw.get(key)
        if v is None:
            return None
        try:
            return int(v)
        except ValueError:
            return None

    def _bool(key: str) -> bool | None:
        v = raw.get(key)
        if v is None:
            return None
        return v.strip().lower() == "true"

    return ArchiveFrontmatter(
        message_count=_int("messageCount"),
        llm_generated=_bool("llmGenerated"),
        fallback_truncation=_bool("fallbackTruncation"),
        raw=raw,
    )


# --- Detection des archives fallback ------------------------------------------

# Pattern de nommage documente dans #8889 : workspace-<name>-<ISO>-fallback.md
# Variante : peut contenir un workspace-prefix 'workspace-' ou pas.
FILENAME_FALLBACK_RE = re.compile(
    r"(?P<workspace>workspace-[A-Za-z0-9_-]+|[A-Za-z0-9_-]+)"
    r"-(?P<iso>\d{4}-\d{2}-\d{2}T\d{2}-\d{2}-\d{2})"
    r"-fallback\.md$",
)


@dataclass(frozen=True)
class ArchiveInfo:
    """Info extraite d'une archive fallback detectee."""
    path: Path
    workspace: str
    iso: str
    size_bytes: int
    message_count: int | None
    frontmatter: ArchiveFrontmatter


def is_fallback_archive(path: Path) -> bool:
    """Vrai si le nom de fichier matche le pattern documented fallback."""
    return bool(FILENAME_FALLBACK_RE.search(path.name))


def iter_archives(root: Path) -> Iterator[Path]:
    """Iterateur sur tous les fichiers *.md sous root."""
    return root.rglob("*.md")


def detect_fallback_archives(root: Path) -> list[ArchiveInfo]:
    """Detecte toutes les archives fallback sous root, avec frontmatter parse.

    Une archive est consideree "fallback reelle" si ET seulement si :
    - Le nom matche FILENAME_FALLBACK_RE
    - Le frontmatter porte `llmGenerated: false` ET `fallbackTruncation: true`
    """
    results: list[ArchiveInfo] = []
    if not root.exists():
        return results
    for path in iter_archives(root):
        if not is_fallback_archive(path):
            continue
        match = FILENAME_FALLBACK_RE.search(path.name)
        if not match:
            continue
        workspace = match.group("workspace")
        iso = match.group("iso")
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        fm = parse_frontmatter(text)
        if fm.llm_generated is False and fm.fallback_truncation is True:
            results.append(ArchiveInfo(
                path=path,
                workspace=workspace,
                iso=iso,
                size_bytes=path.stat().st_size,
                message_count=fm.message_count,
                frontmatter=fm,
            ))
    return results


# --- Modes : list / report / backfill ----------------------------------------

def cmd_list(archives: list[ArchiveInfo]) -> int:
    """Imprime un tableau : date, dashboard, taille, nb messages."""
    if not archives:
        print("[list] aucune archive fallback detectee.")
        return 0
    # Tri par date ISO descendante (plus recentes d'abord)
    archives_sorted = sorted(archives, key=lambda a: a.iso, reverse=True)
    print(f"{'ISO':<22} {'Workspace':<32} {'Messages':>8} {'Size (o)':>10}  Path")
    print("-" * 110)
    total_size = 0
    total_messages = 0
    for a in archives_sorted:
        msg = a.message_count if a.message_count is not None else "?"
        print(f"{a.iso:<22} {a.workspace:<32} {msg:>8} {a.size_bytes:>10}  {a.path}")
        total_size += a.size_bytes
        if a.message_count is not None:
            total_messages += a.message_count
    print("-" * 110)
    print(f"TOTAL : {len(archives)} archives, {total_messages} messages, {total_size} octets")
    return 0


def cmd_report(archives: list[ArchiveInfo], output_dir: Path) -> int:
    """Statistiques agregees par dashboard + export JSON."""
    if not archives:
        print("[report] aucune archive fallback a agreger.")
        return 0
    by_workspace: dict[str, list[ArchiveInfo]] = {}
    for a in archives:
        by_workspace.setdefault(a.workspace, []).append(a)

    summary = {
        "total_archives": len(archives),
        "total_size_bytes": sum(a.size_bytes for a in archives),
        "total_messages": sum(a.message_count or 0 for a in archives),
        "workspaces": {},
    }
    for ws, items in sorted(by_workspace.items()):
        summary["workspaces"][ws] = {
            "archive_count": len(items),
            "size_bytes": sum(a.size_bytes for a in items),
            "messages": sum(a.message_count or 0 for a in items),
            "oldest": min((a.iso for a in items), default=None),
            "newest": max((a.iso for a in items), default=None),
        }

    output_dir.mkdir(parents=True, exist_ok=True)
    json_path = output_dir / "roosync_archive_backfill_report.json"
    json_path.write_text(
        json.dumps(summary, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )
    print(f"[report] {len(archives)} archives, {len(by_workspace)} dashboards")
    print(f"[report] JSON ecrit : {json_path}")
    # Top dashboards par volume
    top = sorted(by_workspace.items(), key=lambda kv: -len(kv[1]))[:5]
    for ws, items in top:
        print(f"  - {ws}: {len(items)} archives")
    return 0


def cmd_backfill(target: Path, archives: list[ArchiveInfo]) -> int:
    """Marque l'archive cible pour backfill manuel (ajoute markForBackfill: true)."""
    target_resolved = target.resolve()
    matches = [a for a in archives if a.path.resolve() == target_resolved]
    if not matches:
        print(f"[backfill] ERREUR : {target} n'est pas une archive fallback detectee.")
        print(f"[backfill] Indication : relancer avec --list pour voir les chemins.")
        return 1
    info = matches[0]
    text = info.path.read_text(encoding="utf-8", errors="replace")
    if "markForBackfill:" in text:
        print(f"[backfill] DEJA MARQUEE : {info.path}")
        return 0
    # Insertion en fin du frontmatter, avant le fermant (---) : on reconstruit
    # proprement via m.group('body') au lieu de slicer m.group(0) (sinon le
    # marqueur colle au fermant et casse un parseur YAML strict).
    new_text = FRONTMATTER_RE.sub(
        lambda m: f"---\n{m.group('body')}\nmarkForBackfill: true\n---\n",
        text,
        count=1,
    )
    if new_text == text:
        print(f"[backfill] ERREUR : frontmatter absent ou mal forme dans {info.path}")
        return 1
    info.path.write_text(new_text, encoding="utf-8")
    print(f"[backfill] MARQUEE : {info.path}")
    return 0


# --- Resume LLM : passe de rattrapage (--summarize, #8889) ---------------------

DEFAULT_LLM_BASE_URL = "http://localhost:5002/v1"
DEFAULT_LLM_MODEL = "qwen3.6-35b-a3b"  # condenseur RooSync (body #8889)
DEFAULT_LLM_TIMEOUT_S = 120
DEFAULT_MAX_CHARS = 24000

# Titre du bloc insere — sert aussi de garde d'idempotence in-file.
SUMMARY_BLOCK_MARKER = "## Résumé (backfill) des"

SYSTEM_PROMPT = (
    "Tu résumes une fenêtre d'archive du canal de coordination RooSync "
    "(cluster d'agents IA). Réponds en markdown français, sans titre de "
    "niveau 1, en trois sections : « Thèmes principaux », « Actions et "
    "résultats », « En attente » (une puce par point). Commence directement "
    "par la première section : pas de préambule, tu ne t'adresses pas au "
    "lecteur. Sois factuel et concret : cite les noms de lanes, PRs, issues "
    "et machines quand ils apparaissent. Pas de commentaire sur la tâche "
    "elle-même."
)


class LlmUnavailableError(RuntimeError):
    """LLM de resume injoignable ou reponse inutilisable : la passe s'arrete."""


def request_summary(text: str, *, base_url: str, model: str,
                    timeout: int = DEFAULT_LLM_TIMEOUT_S,
                    max_chars: int = DEFAULT_MAX_CHARS) -> str:
    """Demande un resume a un endpoint OpenAI-compatible (vLLM, Ollama).

    Stdlib uniquement (urllib) : l'outil doit tourner hors venv sur les lanes.
    Le contenu est borne a `max_chars` (le resume de rattrapage n'a pas besoin
    du contexte integral, cf claim #8889 2026-10-01).
    """
    import urllib.error
    import urllib.request

    content = text[:max_chars]
    if len(text) > max_chars:
        content += "\n\n[... tronqué pour le résumé ...]"
    payload = {
        "model": model,
        "messages": [
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": content},
        ],
        "temperature": 0.2,
        "max_tokens": 700,
    }
    req = urllib.request.Request(
        f"{base_url.rstrip('/')}/chat/completions",
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            body = json.loads(resp.read().decode("utf-8"))
    except (urllib.error.URLError, TimeoutError, OSError) as exc:
        raise LlmUnavailableError(f"LLM injoignable ({base_url}): {exc}") from exc
    except json.JSONDecodeError as exc:
        raise LlmUnavailableError(f"réponse LLM non-JSON ({base_url}): {exc}") from exc
    try:
        summary = str(body["choices"][0]["message"]["content"]).strip()
    except (KeyError, IndexError, TypeError) as exc:
        raise LlmUnavailableError(f"réponse LLM sans contenu exploitable: {str(body)[:200]}") from exc
    if not summary:
        raise LlmUnavailableError("réponse LLM vide")
    return summary


def apply_summary_to_archive(text: str, summary: str, *, model: str,
                             now_iso: str) -> str:
    """Applique le rattrapage sur le contenu d'une archive fallback.

    - Frontmatter : `llmGenerated` false->true, `fallbackTruncation` true->false,
      plus une ligne de provenance `backfilledAt` / `backfillModel`.
    - Corps : insertion du bloc resume AVANT le premier separateur `---` qui
      suit l'en-tete — les messages verbatim ne bougent pas d'un octet
      (critere d'acceptance #8889).
    """
    if SUMMARY_BLOCK_MARKER in text:
        raise ValueError("archive déjà porteuse d'un résumé backfill")

    def _flip(m: re.Match) -> str:
        lines = []
        for line in m.group("body").splitlines():
            stripped = line.strip()
            if stripped == "llmGenerated: false":
                lines.append("llmGenerated: true")
            elif stripped == "fallbackTruncation: true":
                lines.append("fallbackTruncation: false")
            else:
                lines.append(line)
        lines.append(f"backfilledAt: '{now_iso}'")
        lines.append(f"backfillModel: {model}")
        return "---\n" + "\n".join(lines) + "\n---\n"

    new_text = FRONTMATTER_RE.sub(_flip, text, count=1)
    if new_text == text:
        raise ValueError("frontmatter introuvable ou déjà transformé")

    fm = parse_frontmatter(text)
    n = fm.message_count if fm.message_count is not None else "?"
    block = (
        f"{SUMMARY_BLOCK_MARKER} {n} messages archivés\n\n"
        f"{summary}\n\n"
        f"> Résumé généré rétroactivement le {now_iso} par `{model}` via "
        f"`scripts/roosync_archive_backfill.py --summarize` (fenêtre "
        f"initialement archivée sans résumé, cf #8889)."
    )

    fm_match = FRONTMATTER_RE.match(new_text)
    head, rest = new_text[:fm_match.end()], new_text[fm_match.end():]
    sep = rest.find("\n---\n")
    if sep == -1:
        return head + rest.rstrip("\n") + "\n\n" + block + "\n"
    return head + rest[:sep] + "\n\n" + block + rest[sep:]


def cmd_summarize(archives: list[ArchiveInfo], *, root: Path, limit: int,
                  days: int | None, base_url: str, model: str, timeout: int,
                  max_chars: int, dry_run: bool,
                  now: datetime | None = None) -> int:
    """Passe de rattrapage bornee : resume les archives fallback les plus
    recentes, s'arrete au premier echec LLM, idempotente par construction
    (les archives traitees sortent du predicat de detection)."""
    now = now or datetime.now(timezone.utc)
    if days is not None:
        cutoff = now - timedelta(days=days)

        def _in_window(a: ArchiveInfo) -> bool:
            try:
                ts = datetime.strptime(a.iso, "%Y-%m-%dT%H-%M-%S").replace(tzinfo=timezone.utc)
            except ValueError:
                return True  # ISO illisible : ne pas exclure silencieusement
            return ts >= cutoff

        archives = [a for a in archives if _in_window(a)]
    ordered = sorted(archives, key=lambda a: a.iso, reverse=True)[:limit]

    if dry_run:
        for a in ordered:
            print(f"[dry-run] {a.iso} {a.workspace} ({a.message_count} msg, {a.size_bytes} o) {a.path}")
        print(f"[dry-run] {len(ordered)} candidates / {len(archives)} fallback "
              f"detectees (limit={limit}, days={days}, base_url={base_url})")
        return 0

    processed = 0
    for a in ordered:
        try:
            text = a.path.read_text(encoding="utf-8", errors="replace")
        except OSError as exc:
            print(f"[summarize] SKIP lecture impossible {a.path.name}: {exc}")
            continue
        if SUMMARY_BLOCK_MARKER in text:
            print(f"[summarize] SKIP déjà pourvue {a.path.name}")
            continue
        print(f"[summarize] {a.iso} {a.workspace} ({a.message_count} msg) ...", flush=True)
        try:
            summary = request_summary(text, base_url=base_url, model=model,
                                      timeout=timeout, max_chars=max_chars)
        except LlmUnavailableError as exc:
            print(f"[summarize] ARRÊT au premier échec LLM : {exc}")
            if processed:
                print(f"[summarize] PARTIEL : {processed} résumée(s), la passe "
                      f"reprendra proprement (idempotente).")
                return 1
            print("[summarize] Aucune archive touchée. Relancer quand le LLM "
                  f"répond (base_url={base_url}).")
            return 2
        try:
            new_text = apply_summary_to_archive(
                text, summary, model=model,
                now_iso=now.strftime("%Y-%m-%dT%H:%M:%SZ"),
            )
        except ValueError as exc:
            print(f"[summarize] SKIP {a.path.name}: {exc}")
            continue
        a.path.write_text(new_text, encoding="utf-8")
        processed += 1
        print(f"[summarize] OK {a.path.name} ({len(summary)} car. de résumé)")
    print(f"[summarize] Passe terminée : {processed} résumée(s) / "
          f"{len(ordered)} candidates / {len(archives)} fallback dans la fenêtre.")
    return 0


# --- Main ---------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Detection + marquage des archives RooSync sans resume LLM (#8889)",
    )
    parser.add_argument("--root", type=Path, required=True,
                        help="Racine de scan (typiquement $ROOSYNC_SHARED_PATH/dashboards/archive)")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--list", action="store_true",
                       help="Lister toutes les archives fallback detectees")
    group.add_argument("--report", action="store_true",
                       help="Statistiques agregees par dashboard + JSON")
    group.add_argument("--backfill", type=Path, metavar="ARCHIVE_PATH",
                       help="Marquer une archive precise pour backfill manuel")
    group.add_argument("--summarize", action="store_true",
                       help="Passe de rattrapage LLM bornee (resume + bascule frontmatter)")
    parser.add_argument("--limit", type=int, default=10,
                        help="Nombre max d'archives resumees par passe (--summarize)")
    parser.add_argument("--days", type=int, default=30,
                        help="Fenetre en jours, plus recentes seulement (--summarize)")
    parser.add_argument("--base-url", default=DEFAULT_LLM_BASE_URL,
                        help="Endpoint OpenAI-compatible du LLM de resume (defaut : vLLM:5002)")
    parser.add_argument("--model", default=DEFAULT_LLM_MODEL,
                        help="Modele de resume (defaut : condenseur RooSync)")
    parser.add_argument("--timeout", type=int, default=DEFAULT_LLM_TIMEOUT_S,
                        help="Timeout HTTP par resume, en secondes")
    parser.add_argument("--max-chars", type=int, default=DEFAULT_MAX_CHARS,
                        help="Borne de contexte envoye au LLM par archive")
    parser.add_argument("--dry-run", action="store_true",
                        help="Avec --summarize : lister les candidates sans appel LLM ni ecriture")
    parser.add_argument("--output-dir", type=Path,
                        default=Path("scripts/results/roosync_archive_backfill"),
                        help="Repertoire de sortie pour les rapports JSON")
    args = parser.parse_args()

    archives = detect_fallback_archives(args.root)
    print(f"[scan] root={args.root} : {len(archives)} archives fallback detectees")

    if args.list:
        return cmd_list(archives)
    if args.report:
        return cmd_report(archives, args.output_dir)
    if args.backfill:
        return cmd_backfill(args.backfill, archives)
    if args.summarize:
        return cmd_summarize(
            archives, root=args.root, limit=args.limit, days=args.days,
            base_url=args.base_url, model=args.model, timeout=args.timeout,
            max_chars=args.max_chars, dry_run=args.dry_run,
        )
    return 1  # unreachable (mutually_exclusive_group required)


if __name__ == "__main__":
    sys.exit(main())
