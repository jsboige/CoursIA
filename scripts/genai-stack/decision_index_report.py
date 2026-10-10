#!/usr/bin/env python3
"""Classe les entrees de l'index public de decision par palier de taille servie.

Le Pli 1 de #18204 demande, par palier (<=1B, 2-4B, 9-12B, 26-35B quantifie), le
meilleur modele servable sur une carte de 24 Go, avec sa licence, la disponibilite
de ses poids et sa voie de service. L'index publie le score (`balanced_skill`) et
les coordonnees Hugging Face, mais **ni la licence ni le contrat servi** : ce
script produit le classement et les coordonnees, et releve les licences par
`--licenses` (appel a l'API Hugging Face, une requete par depot).

Usage :
    python scripts/genai-stack/decision_index_report.py
    python scripts/genai-stack/decision_index_report.py --licenses --top 5
    python scripts/genai-stack/decision_index_report.py --index /chemin/index.json --json
"""

from __future__ import annotations

import argparse
import json
import sys
import urllib.error
import urllib.request

INDEX_URL = (
    "https://huggingface.co/spaces/multimodalart/jev-decision-index"
    "/resolve/main/data/index.json"
)

# Paliers de taille servie, en milliards de parametres. Le dernier est le seul
# qui ne tient pas en precision pleine sur 24 Go : il suppose une quantification.
TIERS: list[tuple[str, float, float]] = [
    ("<=1B", 0.0, 1.2),
    ("2-4B", 1.2, 5.0),
    ("9-12B", 5.0, 15.0),
    ("26-35B", 15.0, 40.0),
]

# En dessous de cette taille, un modele dense tient en BF16 sur 24 Go sans
# quantification ; au-dessus, il faut quantifier pour le servir.
FULL_PRECISION_LIMIT_B = 10.0


def load_index(source: str) -> dict:
    """Charge l'index depuis une URL ou un chemin local."""
    if "://" in source:
        request = urllib.request.Request(source, headers={"User-Agent": "coursia-research/1.0"})
        with urllib.request.urlopen(request, timeout=120) as handle:
            return json.load(handle)
    with open(source, encoding="utf-8") as handle:
        return json.load(handle)


def weights_repo(meta: dict) -> str | None:
    """Depot Hugging Face des poids, ou None si l'index n'en publie pas."""
    return meta.get("weights_repo") or None


def repo_from_url(url: str | None) -> str | None:
    """Extrait `owner/name` d'une URL de modele Hugging Face."""
    if not url or "huggingface.co/" not in url:
        return None
    tail = url.split("huggingface.co/", 1)[1].strip("/")
    parts = [p for p in tail.split("/") if p]
    return "/".join(parts[:2]) if len(parts) >= 2 else None


def has_open_weights(meta: dict) -> bool:
    """Vrai si l'index atteste des poids telechargeables sans reservation."""
    if meta.get("weights_repo"):
        return True
    note = (meta.get("weights_note") or "").lower()
    if note and "coming soon" not in note and "closed" not in note:
        return True
    return bool(meta.get("model_url"))


def service_paths(params_b: float | None, gguf: bool) -> str:
    """Voie de service plausible d'apres la taille servie et le format publie."""
    if not params_b:
        return "?"
    if gguf:
        return "llama.cpp (GGUF), vLLM"
    if params_b <= FULL_PRECISION_LIMIT_B:
        return "vLLM, llama.cpp (quantifie)"
    return "vLLM (quantifie 4 bits obligatoire en 24 Go)"


def fetch_hf(repo: str) -> dict:
    """Licence et metadonnees d'un depot Hugging Face (donnee externe, lecture seule)."""
    url = "https://huggingface.co/api/models/" + repo
    request = urllib.request.Request(url, headers={"User-Agent": "coursia-research/1.0"})
    try:
        with urllib.request.urlopen(request, timeout=30) as handle:
            return json.load(handle)
    except urllib.error.HTTPError as exc:
        return {"_error": "HTTP %s" % exc.code}
    except Exception as exc:  # noqa: BLE001 - sonde de disponibilite : on rapporte l'echec
        return {"_error": str(exc)[:60]}


def license_of(payload: dict) -> str:
    """Licence declaree par la carte du modele, ou `-`."""
    if "_error" in payload:
        return payload["_error"]
    card = payload.get("cardData") or {}
    lic = card.get("license")
    if lic is None:
        for tag in payload.get("tags") or []:
            if tag.startswith("license:"):
                return tag.split(":", 1)[1]
    if isinstance(lic, list):
        return ",".join(lic)
    return lic or "-"


def is_gguf(payload: dict) -> bool:
    return "gguf" in (payload.get("tags") or [])


def build_rows(index: dict, with_license: bool, top: int) -> dict[str, list[dict]]:
    tiers: dict[str, list[dict]] = {label: [] for label, _, _ in TIERS}
    license_cache: dict[str, str] = {}
    gguf_cache: dict[str, bool] = {}

    for model in index.get("models", []):
        meta = model.get("meta") or {}
        params = meta.get("served_params")
        if not params:
            continue
        params_b = params / 1e9
        scores = model.get("scores") or {}
        repo = weights_repo(meta) or repo_from_url(meta.get("model_url"))
        row = {
            "name": model.get("name"),
            "params_b": round(params_b, 2),
            "balanced_skill": scores.get("balanced_skill"),
            "balanced_raw": scores.get("balanced_raw"),
            "coverage": model.get("coverage"),
            "median_latency": (model.get("latency") or {}).get("median"),
            "repo": repo,
            "base": repo_from_url(meta.get("base_url")) or meta.get("base_model"),
            "open_weights": has_open_weights(meta),
            "gguf": False,
            "license": None,
        }
        if with_license and repo:
            if repo not in license_cache:
                payload = fetch_hf(repo)
                license_cache[repo] = license_of(payload)
                gguf_cache[repo] = is_gguf(payload)
            row["license"] = license_cache[repo]
            row["gguf"] = gguf_cache.get(repo, False)
        for label, low, high in TIERS:
            if low <= params_b < high:
                row["tier"] = label
                tiers[label].append(row)
                break

    for label in tiers:
        tiers[label].sort(key=lambda r: -(r["balanced_skill"] or 0))
        tiers[label] = tiers[label][:top]
    return tiers


def render_markdown(tiers: dict[str, list[dict]], with_license: bool) -> str:
    out: list[str] = []
    for label, _, _ in TIERS:
        rows = tiers[label]
        out.append("### Palier %s (%d entrees retenues)" % (label, len(rows)))
        out.append("")
        header = "| Modele | Taille servie | `balanced_skill` | Depot des poids | Base |"
        sep = "|---|---:|---:|---|---|"
        if with_license:
            header += " Licence | Poids ouverts | Voie de service |"
            sep = "|---|---:|---:|---|---|---|---|---|"
        out.append(header)
        out.append(sep)
        for row in rows:
            line = "| %s | %.2f B | %s | %s | %s |" % (
                row["name"], row["params_b"],
                row["balanced_skill"] if row["balanced_skill"] is not None else "-",
                row["repo"] or "-", row["base"] or "-",
            )
            if with_license:
                line += " %s | %s | %s |" % (
                    row["license"] or "-",
                    "oui" if row["open_weights"] else "non",
                    service_paths(row["params_b"], row["gguf"]),
                )
            out.append(line)
        out.append("")
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--index", default=INDEX_URL,
                        help="URL ou chemin de data/index.json (defaut : espace HF public)")
    parser.add_argument("--top", type=int, default=8, help="entrees par palier (defaut : 8)")
    parser.add_argument("--licenses", action="store_true",
                        help="relever les licences par l'API Hugging Face (une requete par depot)")
    parser.add_argument("--json", action="store_true", help="sortie JSON au lieu de markdown")
    args = parser.parse_args(argv)

    index = load_index(args.index)
    suite = index.get("suite") or {}
    print("edition    : %s (base %s)" % (suite.get("label"), suite.get("base_edition")),
          file=sys.stderr)
    print("genere le  : %s" % index.get("generated_utc"), file=sys.stderr)
    print("entrees    : %d" % len(index.get("models", [])), file=sys.stderr)
    print("headline   : %s" % suite.get("headline"), file=sys.stderr)

    tiers = build_rows(index, args.licenses, args.top)
    if args.json:
        json.dump(tiers, sys.stdout, ensure_ascii=False, indent=1)
        sys.stdout.write("\n")
    else:
        print(render_markdown(tiers, args.licenses))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
