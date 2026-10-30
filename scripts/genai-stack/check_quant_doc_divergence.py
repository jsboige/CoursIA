#!/usr/bin/env python3
"""Organe de confrontation doc <-> quantification réellement chargée.

La table « Quantization Settings per Service » de `docs/genai/genai-services.md`
annonçait `tts-fishaudio` en « BnB 4-bit NF4 ~5 GB » depuis le 2026-09-02, alors que
le service tournait en `--half` (fp16, 20,3 Go mesurés). Aucun organe ne confrontait
la table à ce que les services chargent : c'est le défaut que ce script ferme (#23252).

Trois règles de lecture, chacune payée par une mesure :

1. **La quantification effective se lit dans le bloc `command:` / `environment:` du
   compose, jamais dans le fichier entier.** `services/tts-fishaudio/docker-compose.yml`
   porte `NF4` et `bnb4` dans ses commentaires d'en-tête (l'ancienne image, le format
   maison des checkpoints) et `--half` dans la commande réelle : un grep du fichier
   entier rendrait le verdict inverse du bon sur le cas fondateur.
2. **On compare des classes de précision, pas des chaînes.** `--half` et `fp16` sont la
   même classe ; sans cela, `--half` face à « BnB 4-bit NF4 » ne produit aucun verdict.
3. **`UNKNOWN` par défaut, et `UNKNOWN` n'est jamais `OK`.** Sept services sur douze ne
   portent aucun jeton de quantification lisible dans leur compose ; leur état vit dans
   une variable d'environnement, un `Dockerfile` ou le défaut de la bibliothèque.
   `ORPHAN-ROW` ne se prononce pas non plus sur la seule absence de répertoire homonyme :
   `tts-kokoro` vit dans `services/tts-api/`, et un organe qui suppose une correspondance
   1:1 rend un faux orphelin.

Verdicts : `DIVERGENT-HEAVIER`, `DIVERGENT-LIGHTER`, `ORPHAN-ROW`, `ORPHAN-SERVICE`,
`UNKNOWN`. Sortie 1 sur `DIVERGENT-HEAVIER` et `ORPHAN-*` uniquement — `UNKNOWN` est
advisory, comme partout ailleurs dans ce dépôt (#14849).

Usage :
    python scripts/genai-stack/check_quant_doc_divergence.py
    python scripts/genai-stack/check_quant_doc_divergence.py --as-of c7b94f43bda --json
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

REPO_DEFAULT = Path(__file__).resolve().parents[2]
DOC_PATH = "docs/genai/genai-services.md"
SERVICES_PATH = "docker-configurations/services"
SECTION = "### Quantization Settings per Service"

# Classes de precision, du plus lourd au plus leger. `bf16` et `fp16` pesent pareil :
# la distinction n'a pas de sens pour un budget VRAM, qui est ce dont on parle ici.
LEVEL = {"fp32": 5, "fp16": 4, "bf16": 4, "int8": 3, "fp8": 2, "nf4": 1}

# L'ordre compte : `int8_float16` contient `float16`, `bfloat16` contient `float16`.
# Toute classe testee avant une autre la masque.
TOKENS: list[tuple[str, str]] = [
    ("nf4", r"\bnf4\b|\bbnb4\b|\bbnb-4bit\b|load_in_4bit|\b4-?bit\b"),
    ("fp8", r"\bfp8\b|\bfloat8\b"),
    ("int8", r"\bint8\b|\bint8_float16\b|\bint8_float32\b"),
    ("bf16", r"\bbfloat16\b|\bbf16\b"),
    ("fp32", r"\bfp32\b|\bfloat32\b"),
    ("fp16", r"\bfp16\b|\bfloat16\b|--half\b"),
]

GPU_MARKERS = re.compile(
    r"runtime:\s*nvidia|driver:\s*nvidia|capabilities:\s*\[?gpu|"
    r"NVIDIA_VISIBLE_DEVICES|nvidia\.com/gpu",
    re.IGNORECASE,
)


# --------------------------------------------------------------------------- io


class Loader:
    """Lit l'arbre de travail, ou une révision git quand `as_of` est fourni."""

    def __init__(self, repo: Path, as_of: str | None = None) -> None:
        self.repo = repo
        self.as_of = as_of

    def read(self, relpath: str) -> str | None:
        if self.as_of:
            proc = subprocess.run(
                ["git", "-C", str(self.repo), "show", f"{self.as_of}:{relpath}"],
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
            )
            return proc.stdout if proc.returncode == 0 else None
        path = self.repo / relpath
        if not path.is_file():
            return None
        return path.read_text(encoding="utf-8", errors="replace")

    def list_service_dirs(self) -> list[str]:
        if self.as_of:
            proc = subprocess.run(
                ["git", "-C", str(self.repo), "ls-tree", "-d", "--name-only",
                 f"{self.as_of}:{SERVICES_PATH}"],
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
            )
            return sorted(p.strip() for p in proc.stdout.splitlines() if p.strip())
        base = self.repo / SERVICES_PATH
        if not base.is_dir():
            return []
        return sorted(p.name for p in base.iterdir() if p.is_dir())

    def list_subdirs(self, owner: str) -> list[str]:
        """Les sous-répertoires d'un service — ce qui distingue « contient » de
        « mentionne » (`resolve_service`)."""
        rel = f"{SERVICES_PATH}/{owner}"
        if self.as_of:
            proc = subprocess.run(
                ["git", "-C", str(self.repo), "ls-tree", "-d", "--name-only",
                 f"{self.as_of}:{rel}"],
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
            )
            return sorted(p.strip() for p in proc.stdout.splitlines() if p.strip())
        base = self.repo / rel
        if not base.is_dir():
            return []
        # Meme precaution que `grep_services` : ne pas resoudre les liens.
        return sorted(p.name for p in base.iterdir()
                      if p.is_dir() and not p.is_symlink())

    def declares_service(self, owner: str, name: str) -> bool:
        """Un compose de `owner` **déclare-t-il** `name` comme clé de service ?

        C'est le signal d'appartenance autoritaire, et il se distingue d'une
        simple mention : `services/tts-api/docker-compose-hybrid.yml` parle de
        Kokoro dans un commentaire d'en-tête et dans `DEFAULT_TTS_MODEL=kokoro`,
        sans jamais déclarer de service `tts-kokoro:` ; `services/tts-multi/`
        le déclare (`docker-compose.yml:55`).

        L'ancre est l'**indentation de 2 espaces** : sous `services:`, une clé
        de service y est posée, alors qu'une occurrence plus profonde est une
        entrée de `depends_on:` (l.47 et l.152 du même fichier), qui nomme un
        service sans en être le propriétaire.
        """
        rx = re.compile(rf"^  {re.escape(name)}\s*:\s*(?:#.*)?$", re.MULTILINE)
        for fname in ("docker-compose.yml", "docker-compose.yaml",
                      "docker-compose-hybrid.yml"):
            text = self.read(f"{SERVICES_PATH}/{owner}/{fname}")
            if text and rx.search(text):
                return True
        return False

    def grep_services(self, pattern: str) -> list[str]:
        """Chemins (relatifs au dépôt) où `pattern` apparaît sous `services/`."""
        if self.as_of:
            proc = subprocess.run(
                ["git", "-C", str(self.repo), "grep", "-l", "-i", "-E", pattern,
                 self.as_of, "--", SERVICES_PATH],
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
            )
            out = []
            for line in proc.stdout.splitlines():
                _, _, path = line.partition(":")
                if path:
                    out.append(path)
            return sorted(set(out))
        hits = []
        base = self.repo / SERVICES_PATH
        if not base.is_dir():
            return []
        rx = re.compile(pattern, re.IGNORECASE)
        for path in base.rglob("*"):
            # Un venv de service contient des liens symboliques que Windows refuse de
            # suivre (WinError 1920) : on ne résout pas les liens, on les saute.
            try:
                if path.is_symlink() or not path.is_file():
                    continue
                if "venv" in path.parts or "node_modules" in path.parts:
                    continue
                if path.stat().st_size > 400_000:
                    continue
            except OSError:
                continue
            if path.suffix.lower() not in {".yml", ".yaml", ".env", ".py", ".md", ""}:
                continue
            try:
                text = path.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            if rx.search(text):
                hits.append(str(path.relative_to(self.repo)).replace("\\", "/"))
        return sorted(hits)


# ------------------------------------------------------------------- classement


def classify(text: str) -> tuple[str, str | None]:
    """Classe de précision d'un fragment, et le jeton qui l'a fait conclure.

    Le classement se fait par **position dans le texte**, pas par priorité de table :
    « bfloat16 (fp8 opt via ...) » annonce du bfloat16 dont le fp8 est une option, et
    une priorité de table y lirait `fp8` — donc une divergence qui n'existe pas.
    La position départage aussi les jetons composés : dans `int8_float16`, `int8` gagne
    (index 0) ; dans `bfloat16`, `bfloat16` gagne sur le `float16` qu'il contient.
    """
    best: tuple[int, int, str, str] | None = None
    for order, (label, pattern) in enumerate(TOKENS):
        m = re.search(pattern, text, re.IGNORECASE)
        if m is None:
            continue
        cand = (m.start(), order, label, m.group(0))
        if best is None or cand < best:
            best = cand
    return (best[2], best[3]) if best else ("unknown", None)


def strip_comments(compose: str) -> str:
    """Retire les commentaires YAML (ligne entière ou fin de ligne hors guillemets)."""
    out = []
    for line in compose.splitlines():
        stripped = line.lstrip()
        if stripped.startswith("#"):
            continue
        quote: str | None = None
        cut = len(line)
        for i, ch in enumerate(line):
            if quote:
                if ch == quote:
                    quote = None
            elif ch in "\"'":
                quote = ch
            elif ch == "#" and i > 0 and line[i - 1] in " \t":
                cut = i
                break
        out.append(line[:cut].rstrip())
    return "\n".join(out)


def effective_blocks(compose: str) -> str:
    """Concatène les seules lignes qui portent la charge réelle : command + environement.

    Les blocs sont repérés par leur clé de premier niveau et se terminent à la première
    ligne non indentée. C'est volontairement grossier : mieux vaut manquer un jeton et
    rendre `UNKNOWN` que lire un commentaire d'en-tête et rendre un verdict inversé.
    """
    kept: list[str] = []
    key_indent: int | None = None
    for raw in strip_comments(compose).splitlines():
        if not raw.strip():
            continue
        indent = len(raw) - len(raw.lstrip())
        stripped = raw.strip()
        # `command:` vit sous `services:` -> `<nom>:` : il est imbriqué, pas à la racine.
        if re.match(r"^(command|environment)\s*:", stripped):
            key_indent = indent
            kept.append(stripped)
            continue
        if key_indent is not None:
            if indent > key_indent:
                kept.append(stripped)
                continue
            key_indent = None
    return "\n".join(kept)


def read_effective(loader: Loader, service_dir: str) -> tuple[str, str | None, str | None]:
    """(classe, fragment, provenance) de la quantification effective d'un service."""
    for name in ("docker-compose.yml", "docker-compose.yaml",
                 "docker-compose-hybrid.yml"):
        rel = f"{SERVICES_PATH}/{service_dir}/{name}"
        text = loader.read(rel)
        if text is None:
            continue
        blocks = effective_blocks(text)
        cls, token = classify(blocks)
        if cls != "unknown":
            return cls, token, rel
    return "unknown", None, None


# ---------------------------------------------------------------------- doc


def parse_doc(text: str) -> list[dict[str, str]]:
    """Lignes de la table de quantification, dans l'ordre du document."""
    if SECTION not in text:
        return []
    body = text.split(SECTION, 1)[1]
    rows: list[dict[str, str]] = []
    seen_table = False
    for line in body.splitlines():
        stripped = line.strip()
        if stripped.startswith("### ") and seen_table:
            break
        if not stripped.startswith("|"):
            if seen_table and stripped:
                break
            continue
        cells = [c.strip() for c in stripped.strip("|").split("|")]
        if len(cells) < 5:
            continue
        if set(cells[0]) <= set("-: ") or cells[0].lower() == "service":
            seen_table = True
            continue
        seen_table = True
        rows.append(
            {
                "service": cells[0].strip("`"),
                "host": cells[1],
                "model": cells[2],
                "declared": cells[3],
                "idle_vram": cells[4],
            }
        )
    return rows


# ------------------------------------------------------------------ verdicts


def resolve_service(loader: Loader, name: str) -> tuple[str | None, str]:
    """Répertoire du service, et comment il a été résolu.

    `homonyme` : le répertoire porte le nom de la ligne.
    `appartenance` : le nom vit à l'intérieur d'un autre service — la
    correspondance ligne <-> répertoire n'est pas 1:1.

    **Mentionner n'est pas posséder** (#23343, revue du 2026-10-29). Le
    propriétaire est celui qui **porte un sous-répertoire du nom** ; à défaut
    seulement, un simple hit de `grep` fait candidat. La distinction n'est pas
    cosmétique : c'est le répertoire retenu dont `read_effective` lit la
    quantification. Sur l'arbre réel, `tts-kokoro` est **mentionné** par
    `services/tts-api/` (et par `tts-multi`), mais il **vit** dans
    `services/tts-multi/kokoro/` (`context: ./kokoro`,
    `tts-multi/docker-compose.yml:57`) : l'ancien `owners[0]` alphabétique
    rendait `tts-api` et faisait lire la quantification du mauvais service.
    """
    dirs = loader.list_service_dirs()
    if name in dirs:
        return name, "homonyme"
    hits = loader.grep_services(rf"\b{re.escape(name)}\b")
    owners = sorted({h.split("/")[2] for h in hits if h.startswith(SERVICES_PATH + "/")
                     and len(h.split("/")) > 3})
    if owners:
        proprietaire = owner_par_sous_repertoire(loader, owners, name)
        if proprietaire is not None:
            return proprietaire, f"appartenance ({proprietaire}, declare {name}:)"
        return owners[0], (f"appartenance ({', '.join(owners[:3])}) "
                           "— propriétaire non tranché (aucun sous-répertoire)")
    return None, "introuvable"


def owner_par_sous_repertoire(loader: Loader, owners: list[str],
                              name: str) -> str | None:
    """Le propriétaire du nom, par ordre de force décroissante.

    1. celui dont un compose **déclare la clé de service** `name:` — signal
       autoritaire : c'est ce fichier que `read_effective` lira ;
    2. celui qui **porte un sous-répertoire** du nom (utile quand le nom du
       dossier diffère de celui du service).

    « Mentionner » ne suffit pas : `services/tts-api/` ne contient que des
    commentaires et des variables d'environnement parlant de Kokoro, et
    pourtant `owners[0]` alphabétique le retenait.
    """
    for owner in owners:
        if loader.declares_service(owner, name):
            return owner
    for owner in owners:
        if name in loader.list_subdirs(owner):
            return owner
    return None



def evaluate(loader: Loader) -> list[dict[str, str]]:
    doc_text = loader.read(DOC_PATH)
    if doc_text is None:
        raise SystemExit(f"{DOC_PATH} introuvable (révision demandée ?)")
    rows = parse_doc(doc_text)
    findings: list[dict[str, str]] = []
    declared_names: set[str] = set()

    for row in rows:
        name = row["service"]
        declared_names.add(name)
        declared_cls, declared_token = classify(row["declared"])
        service_dir, resolution = resolve_service(loader, name)
        if service_dir is None:
            findings.append({
                "service": name, "verdict": "ORPHAN-ROW",
                "declared": row["declared"], "effective": "-",
                "source": f"aucun répertoire homonyme ni appartenance sous {SERVICES_PATH}/",
            })
            continue
        eff_cls, eff_token, source = read_effective(loader, service_dir)
        if eff_cls == "unknown" or declared_cls == "unknown":
            findings.append({
                "service": name, "verdict": "UNKNOWN",
                "declared": row["declared"],
                "effective": eff_token or "non lisible",
                "source": source or f"{SERVICES_PATH}/{service_dir}/ ({resolution})",
            })
            continue
        verdict = "OK"
        if LEVEL[eff_cls] > LEVEL[declared_cls]:
            verdict = "DIVERGENT-HEAVIER"
        elif LEVEL[eff_cls] < LEVEL[declared_cls]:
            verdict = "DIVERGENT-LIGHTER"
        findings.append({
            "service": name, "verdict": verdict,
            "declared": row["declared"],
            "effective": f"{eff_token} ({eff_cls})",
            "source": source or f"{SERVICES_PATH}/{service_dir}/",
        })

    # Un service GPU de l'arbre absent de la table est un trou de doc, pas un silence.
    for service_dir in loader.list_service_dirs():
        if service_dir in declared_names or service_dir == "shared":
            continue
        for name in ("docker-compose.yml", "docker-compose.yaml"):
            text = loader.read(f"{SERVICES_PATH}/{service_dir}/{name}")
            if text is None:
                continue
            if GPU_MARKERS.search(strip_comments(text)):
                findings.append({
                    "service": service_dir, "verdict": "ORPHAN-SERVICE",
                    "declared": "-", "effective": "-",
                    "source": f"{SERVICES_PATH}/{service_dir}/{name} (marqueur GPU)",
                })
            break
    return findings


FAILING = {"DIVERGENT-HEAVIER", "ORPHAN-ROW", "ORPHAN-SERVICE"}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", default=str(REPO_DEFAULT))
    parser.add_argument("--as-of", dest="as_of", default=None,
                        help="révision git : rejoue le contrôle sur un état passé")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args(argv)

    findings = evaluate(Loader(Path(args.repo), args.as_of))
    failing = [f for f in findings if f["verdict"] in FAILING]

    if args.json:
        print(json.dumps({"findings": findings, "failing": len(failing)}, indent=2,
                         ensure_ascii=False))
    elif not args.quiet:
        width = max(len(f["service"]) for f in findings) if findings else 10
        for f in findings:
            print(f"{f['service']:<{width}}  {f['verdict']:<18} "
                  f"annoncé={f['declared']:<22} effectif={f['effective']:<18} {f['source']}")
        counts: dict[str, int] = {}
        for f in findings:
            counts[f["verdict"]] = counts.get(f["verdict"], 0) + 1
        print("\n" + "  ".join(f"{k}={v}" for k, v in sorted(counts.items())))
        if failing:
            print(
                "\nCorrection attendue : aligner la doc SUR le service, ou reconfigurer "
                "le service SUR la doc — au choix documenté de la lane, jamais un silence."
            )
    return 1 if failing else 0


if __name__ == "__main__":
    sys.exit(main())
