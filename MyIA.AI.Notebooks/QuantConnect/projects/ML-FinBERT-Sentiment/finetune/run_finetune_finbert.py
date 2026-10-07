"""Port local GPU du re-entrainement FinBERT du livre (06/19/02, HandsOnAITradingBook e025f21).

Le livre re-entraine `ProsusAI/finbert` DANS l'algorithme LEAN, a chaque
rebalancement mensuel (`_trade` : collecte des articles des 30 derniers jours,
etiquetage par la reaction du cours entre deux parutions consecutives,
classification en 3 classes, `model.fit(dataset, epochs=2)`). Ce harnais sort
le re-entrainement de l'algorithme pour l'executer sur un GPU local, et
compare modele de base et modele re-entraine hors echantillon :

  1. `--stage data` : constitue le corpus de titres financiers horodates
     (FNSPID, `All_external.csv`, CC BY-NC 4.0) filtre sur l'univers et la
     fenetre du harnais. Le corpus reste **hors depot** (cache local) : seules
     les mesures sont commitees (cf. `.claude/rules/bibliography-hygiene.md`).
  2. `--stage build` : applique la recette d'etiquetage du livre mois par mois
     (actif le plus volatil du top 10 liquidite, 30 derniers jours d'articles,
     label = reaction du cours a la parution, 3 classes au 25/75), puis separe
     entrainement et hors echantillon.
  3. `--stage finetune` : re-entraine un modele par graine (recette du livre :
     lr 3e-5, Adam, 2 epoques, entropie croisee sur les logits).
  4. `--stage eval` : exactitude de classification sur les mois hors
     echantillon, modele de base contre modele re-entraine, puis simulation
     locale de la strategie du livre (long 100 % / short 25 %) pour les deux
     bras.

Ecarts documentes vs le livre :
  - **Source des articles** : le livre lit Tiingo News sur QC Cloud. Le harnais
    lit FNSPID (corpus public horodate, meme forme : date + ticker + titre).
    La contrepartie hors ligne d'une source de donnees QC est l'ecart que le
    portage Chronos a deja documente (univers fixe, cloture yfinance).
  - **Resolution du prix et fenetre de reaction** : le livre mesure la reaction
    du cours entre **deux parutions consecutives**, sur des clotures a la
    SECONDE pres (`Resolution.SECOND`). A resolution quotidienne, cette regle
    s'effondre : deux parutions de la meme seance n'ont **aucune** reaction
    resolvable et rendent un label exactement nul. Mesure sur le corpus du
    harnais (2015-2019, 24 grandes caps) : **410 des 680 paires consecutives
    (60 %) tombent dans la meme seance**, donc **429 labels (63 %) sont nuls
    exactement** — ce qui fabrique une classe neutre majoritaire (75 % des
    echantillons) que le livre ne connait pas. Le harnais mesure donc la
    reaction **a la parution** : le rendement de la premiere seance dont la
    cloture suit l'instant de parution, rapporte a la cloture precedente. Sur
    le meme corpus, cette regle ne rend que 0,9 % de nuls exacts et une
    distribution etalee (q10 -1,46 %, q25 -0,62 %, mediane +0,06 %, q75
    +0,75 %, q90 +1,58 %), donc les proportions de classes que le livre vise
    (37,5 % / 25 % / 37,5 %). L'intention du livre — « quelle a ete la
    reaction du marche a cette nouvelle » — est preservee ; c'est sa
    mecanique de mesure qui est adaptee a la resolution disponible.
  - **Selecteur d'actif, et la couverture du corpus** : le livre retient le plus
    volatil des 10 valeurs les plus liquides, sur un marche ou la couverture
    d'actualite est **universelle** (Tiingo News). Hors ligne la couverture de
    FNSPID est **partielle**, et le selecteur du livre y choisit regulierement un
    titre sans actualite observable : mesure sur le corpus partiel, la tete de
    classement est AMD (le plus volatil de l'univers) avec **14 articles sur cinq
    ans**, ce qui ecartait **37 des 60 mois** pour une raison de **couverture**,
    pas de strategie (703 echantillons seulement). Le harnais descend donc d'un
    rang quand le candidat n'est pas observable, et retient le premier candidat
    couvert par au moins `MIN_SAMPLES + 1` articles dans la fenetre. **Quand le
    premier choix du livre est couvert, il reste retenu a l'identique** ; la
    meme mesure passe alors a **1 948 echantillons sur 59 des 60 mois**, avec des
    proportions de classes de 32,5 / 28,4 / 39,1 (le livre vise 37,5 / 25 / 37,5).
  - **TensorFlow -> PyTorch** : le livre utilise `TFBertForSequenceClassification` ;
    le harnais utilise `AutoModelForSequenceClassification` (memes poids, meme
    tokenizer). C'est le meme ecart que le portage de base 06/19/01, deja
    documente dans `main.py`.
  - **`max_length`** : le livre laisse la valeur par defaut du tokenizer (512)
    avec `padding='max_length'`. Les titres font ~15 jetons ; le harnais passe
    `max_length=128`, qui les contient tous avec une marge large et divise le
    temps de calcul.
  - **Separation entrainement / hors echantillon** : le livre n'en a **aucune**
    — il re-entraine et predit sur les memes 100 echantillons du mois. Le
    harnais ajoute la separation que l'issue demande (critere 2) : les
    `--holdout-months` derniers mois sont retires de l'entrainement.

Usage :
    set CUDA_VISIBLE_DEVICES=1   # enumeration torch par defaut : 1 = 3080 Ti (libre)
    python run_finetune_finbert.py --stage all --seeds 1 2 3 42 --run-dir D:\\Dev\\CoursIA-18962-finbert-run
"""

from __future__ import annotations

import argparse
import csv
import json
import logging
import random
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd

FINETUNE_DIR = Path(__file__).resolve().parent

#: Modele du livre.
BOOK_MODEL = "ProsusAI/finbert"

#: Univers du harnais. Le livre selectionne dynamiquement « top 10 liquidite
#: -> le plus volatil » sur l'ensemble du marche ; hors QC, le harnais fige une
#: liste de 24 grandes capitalisations **hors Mag7** (l'univers du livre n'est
#: pas accessible hors ligne, et le §C interdit une revendication BEATS sur
#: l'univers Mag7 — aucun BEATS n'est revendique ici, mais l'univers l'ecarte
#: par construction). Le selecteur du livre (top 10 dollar-volume -> le plus
#: volatil a 365 j) est ensuite applique **dans** cette liste.
UNIVERSE = [
    "JPM", "BAC", "WMT", "XOM", "CVX", "JNJ", "PFE", "UNH", "HD", "DIS",
    "BA", "CAT", "KO", "PEP", "PG", "T", "VZ", "CSCO", "INTC", "AMD",
    "MU", "GS", "MS", "ABT",
]

#: Fenetre du corpus et des mesures. Le fichier `Stock_news/All_external.csv`
#: de FNSPID couvre 2004-2020 (mesure par sondage de plages, cf. en-tete) :
#: la fenetre du harnais est choisie **dans** cette couverture, et non sur les
#: annees du livre (2022-2023), qui vivent dans `nasdaq_exteral_data.csv`
#: (23 Go, places NASDAQ seulement).
DATE_MIN = "2015-01-01"
DATE_MAX = "2019-12-31"
PRICE_START = "2014-01-01"

#: Recette du livre.
LAST_N_SAMPLES = 100
MIN_SAMPLES = 10
PERCENT_SIGNED = 0.75

#: Convention de classes **apres re-etiquetage du livre** (cf. `_classify3`).
LABELS3 = ["negative", "neutral", "positive"]
ORDER3 = {"negative": 0, "neutral": 1, "positive": 2}

DEFAULT_SEEDS = [1, 2, 3, 42]
HOLDOUT_MONTHS = 6
MAX_LEN = 128
EPOCHS = 2
LR = 3e-5
BATCH = 16

log = logging.getLogger("finbert-finetune")


def _setup_log():
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s %(message)s",
        datefmt="%H:%M:%S",
    )
    # Le telechargement par plages Xet journalise chaque requete HTTP : sans
    # ce filtre, le journal de l'etape `data` fait des dizaines de Mo.
    for name in ("httpx", "httpcore", "urllib3", "filelock", "datasets"):
        logging.getLogger(name).setLevel(logging.WARNING)


# --------------------------------------------------------------------------
# Etape 1 -- corpus
# --------------------------------------------------------------------------

def stage_data(run_dir: Path, force: bool = False) -> Path:
    """Filtre FNSPID sur l'univers et la fenetre, et cache le resultat.

    Le fichier source fait 5,7 Go et ~10 M de lignes : il est **streame**
    depuis le Hub, jamais telecharge en entier. Le cache local ne contient que
    les colonnes utiles (date, ticker, titre) du sous-ensemble vise.
    """
    out = run_dir / "data" / "fnspid_news.csv"
    if out.exists() and not force:
        n = sum(1 for _ in open(out, encoding="utf-8")) - 1
        log.info("corpus deja present : %s (%d lignes)", out, n)
        return out

    from datasets import load_dataset

    out.parent.mkdir(parents=True, exist_ok=True)
    log.info("streaming FNSPID Stock_news/All_external.csv (5,7 Go, ~10 M lignes)")
    ds = load_dataset(
        "Zihan1004/FNSPID",
        data_files="Stock_news/All_external.csv",
        split="train",
        streaming=True,
    )

    keep = set(UNIVERSE)
    seen = 0
    kept = 0
    per_symbol: dict[str, int] = {}
    t0 = time.time()
    with open(out, "w", encoding="utf-8", newline="") as fh:
        writer = csv.writer(fh)
        writer.writerow(["date", "symbol", "title"])
        for row in ds:
            seen += 1
            if seen % 500_000 == 0:
                log.info(
                    "  %d lignes lues, %d retenues (%.0f s)",
                    seen, kept, time.time() - t0,
                )
            symbol = (row.get("Stock_symbol") or "").strip().upper()
            if symbol not in keep:
                continue
            date = (row.get("Date") or "").strip()
            if len(date) < 10 or not (DATE_MIN <= date[:10] <= DATE_MAX):
                continue
            title = (row.get("Article_title") or "").strip()
            if not title:
                continue
            writer.writerow([date, symbol, title])
            kept += 1
            per_symbol[symbol] = per_symbol.get(symbol, 0) + 1

    log.info(
        "corpus ecrit : %s -- %d lignes lues, %d retenues, %d tickers (%.0f s)",
        out, seen, kept, len(per_symbol), time.time() - t0,
    )
    meta = {
        "source": "Zihan1004/FNSPID Stock_news/All_external.csv",
        "licence": "CC BY-NC 4.0",
        "lignes_lues": seen,
        "lignes_retenues": kept,
        "par_ticker": dict(sorted(per_symbol.items(), key=lambda kv: -kv[1])),
        "fenetre": [DATE_MIN, DATE_MAX],
    }
    (run_dir / "data" / "fnspid_meta.json").write_text(
        json.dumps(meta, indent=2, ensure_ascii=False), encoding="utf-8"
    )
    return out


# --------------------------------------------------------------------------
# Prix
# --------------------------------------------------------------------------

def load_closes(run_dir: Path, tickers: list[str]) -> tuple[pd.DataFrame, pd.DataFrame]:
    """Clotures et volumes quotidiens ajustes, cache local (yfinance)."""
    cache = run_dir / "data" / "closes.csv"
    vol_cache = run_dir / "data" / "volumes.csv"
    if cache.exists() and vol_cache.exists():
        closes = pd.read_csv(cache, index_col=0, parse_dates=True)
        volumes = pd.read_csv(vol_cache, index_col=0, parse_dates=True)
        if all(t in closes.columns for t in tickers) and all(
            t in volumes.columns for t in tickers
        ):
            return closes, volumes
        log.info("cache de prix incomplet, rechargement")

    import yfinance as yf

    log.info("telechargement yfinance : %d tickers, %s -> %s", len(tickers), PRICE_START, DATE_MAX)
    raw = yf.download(
        tickers, start=PRICE_START, end=DATE_MAX, auto_adjust=True,
        progress=False, group_by="column",
    )
    closes = raw["Close"].copy()
    volumes = raw["Volume"].copy()
    closes.index = pd.to_datetime(closes.index).tz_localize(None)
    volumes.index = pd.to_datetime(volumes.index).tz_localize(None)
    closes.to_csv(cache)
    volumes.to_csv(vol_cache)
    return closes, volumes


def _price_grid(closes: pd.DataFrame) -> pd.DataFrame:
    """Clotures reindexees sur les seances, valeurs reportees avant."""
    grid = closes.copy()
    grid.index = pd.to_datetime(grid.index).tz_localize(None).normalize()
    return grid[~grid.index.duplicated(keep="last")].sort_index().ffill()


#: Heure UTC de la cloture des actions US, borne basse : 16:00 ET = 20:00 UTC
#: en heure d'ete, 21:00 UTC en heure d'hiver. Une parution posterieure a ce
#: seuil est traitee comme anterieure a la premiere seance suivante.
CLOTURE_US_UTC = 20


def _session_returns(grid: pd.DataFrame) -> pd.DataFrame:
    """Rendement de chaque seance par rapport a la cloture precedente."""
    return grid / grid.shift(1) - 1.0


def _reaction_label(returns: pd.DataFrame, symbol: str, ts: pd.Timestamp):
    """Reaction du cours a une parution : premiere cloture qui la suit.

    Le livre mesure la reaction entre deux parutions consecutives, sur des
    prix a la **seconde** (cf. en-tete). A resolution quotidienne, deux
    parutions de la meme seance n'ont aucune reaction resolvable : mesure sur
    le corpus, 63 % des paires consecutives tombent dans ce cas et rendraient
    un label exactement nul, fabriquant une classe neutre majoritaire
    artificielle. Le harnais mesure donc la reaction **a la parution** : le
    rendement de la premiere seance dont la cloture suit l'instant de
    parution, rapporte a la cloture precedente.
    """
    if symbol not in returns.columns:
        return None
    col = returns[symbol].dropna()
    if col.empty:
        return None
    ts_naif = ts.tz_localize(None) if ts.tzinfo is not None else ts
    cible = ts_naif.normalize()
    if ts_naif.hour >= CLOTURE_US_UTC:
        cible = cible + pd.Timedelta(days=1)
    pos = col.index.searchsorted(cible)
    if pos >= len(col):
        return None
    valeur = float(col.iloc[pos])
    return valeur if np.isfinite(valeur) else None


# --------------------------------------------------------------------------
# Etape 2 -- echantillons etiquetes (recette du livre)
# --------------------------------------------------------------------------

def _rank_assets(
    grid: pd.DataFrame, volumes: pd.DataFrame, month: pd.Timestamp
) -> list[str]:
    """Classement du livre : top 10 liquidite, ordonne par volatilite decroissante.

    Le livre retient le **premier** de ce classement (`_book_selector`). Le
    harnais expose la liste entiere, parce qu'hors ligne la couverture
    d'actualite est partielle : le premier choix peut n'avoir **aucune**
    actualite observable sur la fenetre, et un selecteur qui l'ignore ecarte le
    mois pour une raison de **couverture**, pas de strategie (mesure : 37 des 60
    mois du corpus partiel etaient ecartes pour ce seul motif, la tete de
    classement etant AMD avec 14 articles sur cinq ans). Le harnais descend donc
    d'un rang quand le candidat n'est pas observable ; quand le premier choix
    **est** couvert, il est retenu exactement comme dans le livre.

    Le livre lit `fundamental.dollar_volume` ; le harnais l'approche par la
    moyenne `cloture x volume` des 60 seances precedentes.
    """
    hist_v = volumes.loc[:month].tail(60)
    hist_c = grid.loc[:month].tail(60)
    if hist_c.empty or hist_v.empty:
        return []
    common = [c for c in hist_c.columns if c in hist_v.columns]
    dollar = (hist_c[common] * hist_v[common]).mean().dropna()
    if dollar.empty:
        return []
    top = list(dollar.sort_values().tail(10).index)

    year = grid.loc[:month].tail(365)[top]
    if len(year) < 60:
        return []
    vol = year.pct_change().iloc[1:].std().dropna()
    return [str(s) for s in vol.sort_values(ascending=False).index]


def _classify3(samples: pd.DataFrame) -> pd.DataFrame:
    """Trois classes au 25/75 -- logique du livre, recopiee telle quelle.

    75 % des labels les plus negatifs -> classe 0, 75 % des plus positifs ->
    classe 2, le reste -> classe 1. La classe **0 est negative, 2 positive** :
    c'est la convention du livre *apres* re-etiquetage, et elle differe de
    `id2label` du modele de base (cf. `_base_predictions`).
    """
    s = samples.sort_values(by="label", ascending=False).reset_index(drop=True)
    positive_cutoff = int(PERCENT_SIGNED * len(s[s.label > 0]))
    negative_cutoff = len(s) - int(PERCENT_SIGNED * len(s[s.label < 0]))
    s.loc[list(range(negative_cutoff, len(s))), "label3"] = 0
    s.loc[list(range(positive_cutoff, negative_cutoff)), "label3"] = 1
    s.loc[list(range(0, positive_cutoff)), "label3"] = 2
    s["label3"] = s["label3"].astype(int)
    return s


def build_samples(run_dir: Path, news: pd.DataFrame) -> pd.DataFrame:
    """Construit un jeu (mois, actif, texte, label3) par la recette du livre."""
    closes, volumes = load_closes(run_dir, UNIVERSE)
    grid = _price_grid(closes)
    returns = _session_returns(grid)

    news = news.copy()
    news["dt"] = pd.to_datetime(news["date"], utc=True, errors="coerce")
    news = news.dropna(subset=["dt"]).sort_values("dt")

    months = pd.date_range(DATE_MIN, DATE_MAX, freq="MS", tz="UTC")
    rows = []
    skipped = []
    for month in months:
        window_start = month - pd.Timedelta(days=30)
        ranked = _rank_assets(grid, volumes, month.tz_localize(None))
        if not ranked:
            skipped.append((month.strftime("%Y-%m"), "selecteur: aucune donnee"))
            continue
        symbol, art = None, None
        for candidat in ranked:
            fenetre = news[
                (news.symbol == candidat) & (news.dt >= window_start) & (news.dt < month)
            ]
            if len(fenetre) >= MIN_SAMPLES + 1:
                symbol, art = candidat, fenetre
                break
        if symbol is None:
            tete = news[
                (news.symbol == ranked[0]) & (news.dt >= window_start) & (news.dt < month)
            ]
            skipped.append(
                (
                    month.strftime("%Y-%m"),
                    f"aucun candidat couvert sur {len(ranked)} "
                    f"(tete {ranked[0]}: {len(tete)} articles)",
                )
            )
            continue
        raw = [_reaction_label(returns, symbol, ts) for ts in art.dt]
        labels = [np.nan if v is None else v for v in raw]
        samples = pd.DataFrame(
            {"text": art.title.values, "label": labels}
        ).dropna()
        samples = samples.iloc[-LAST_N_SAMPLES:]
        if len(samples) < MIN_SAMPLES:
            skipped.append((month.strftime("%Y-%m"), f"{symbol}: {len(samples)} echantillons"))
            continue
        samples = _classify3(samples)
        samples["month"] = month.strftime("%Y-%m")
        samples["symbol"] = symbol
        rows.append(samples)

    if not rows:
        raise RuntimeError("aucun mois exploitable : corpus ou prix insuffisants")
    full = pd.concat(rows, ignore_index=True)
    log.info(
        "echantillons : %d lignes sur %d mois, %d mois ecartes",
        len(full), full.month.nunique(), len(skipped),
    )
    for month, reason in skipped:
        log.info("  mois ecarte %s -- %s", month, reason)
    return full


# --------------------------------------------------------------------------
# Etape 3 -- re-entrainement
# --------------------------------------------------------------------------

def _torch():
    import torch

    return torch


def finetune_one(train: pd.DataFrame, seed: int, device: str):
    """Re-entraine un modele par la recette du livre, et rend (modele, tokenizer)."""
    torch = _torch()
    from torch.utils.data import DataLoader, TensorDataset
    from transformers import AutoModelForSequenceClassification, AutoTokenizer

    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    if device.startswith("cuda"):
        torch.cuda.manual_seed_all(seed)

    tokenizer = AutoTokenizer.from_pretrained(BOOK_MODEL)
    model = AutoModelForSequenceClassification.from_pretrained(
        BOOK_MODEL, num_labels=3
    ).to(device)

    enc = tokenizer(
        list(train.text),
        padding="max_length",
        truncation=True,
        max_length=MAX_LEN,
        return_tensors="pt",
    )
    labels = torch.tensor(train.label3.values, dtype=torch.long)
    loader = DataLoader(
        TensorDataset(enc["input_ids"], enc["attention_mask"], labels),
        batch_size=BATCH,
        shuffle=True,
    )
    optimizer = torch.optim.AdamW(model.parameters(), lr=LR)
    loss_fn = torch.nn.CrossEntropyLoss()

    model.train()
    for epoch in range(EPOCHS):
        total, seen = 0.0, 0
        for ids, mask, target in loader:
            ids, mask, target = ids.to(device), mask.to(device), target.to(device)
            optimizer.zero_grad()
            out = model(input_ids=ids, attention_mask=mask)
            loss = loss_fn(out.logits, target)
            loss.backward()
            optimizer.step()
            total += float(loss.detach()) * len(target)
            seen += len(target)
        log.info("    epoque %d/%d -- perte %.4f", epoch + 1, EPOCHS, total / max(seen, 1))
    model.eval()
    return model, tokenizer


def _probabilities(model, tokenizer, texts: list[str], device: str) -> np.ndarray:
    """Probabilites par classe, dans l'ordre des indices du modele."""
    torch = _torch()

    enc = tokenizer(
        texts, padding=True, truncation=True, max_length=MAX_LEN, return_tensors="pt"
    )
    enc = {k: v.to(device) for k, v in enc.items()}
    with torch.no_grad():
        logits = model(**enc).logits
    return torch.nn.functional.softmax(logits, dim=-1).cpu().numpy()


def _base_predictions(texts: list[str], device: str) -> tuple[np.ndarray, dict]:
    """Predictions du modele **de base**, ramenees dans la convention du livre.

    `ProsusAI/finbert` expose `id2label = {0: positive, 1: negative, 2: neutral}`
    (mesure sur le noeud QC, cf. note n5 de `main.py`). Le re-etiquetage du
    livre, lui, pose 0 = negative et 2 = positive. Comparer les `argmax` bruts
    comparerait deux conventions differentes : le harnais lit `id2label` sur le
    modele charge et **reordonne** les colonnes de probabilite, si bien que les
    deux bras parlent la meme langue et que seule la tete entrainee differe.
    """
    from transformers import AutoModelForSequenceClassification, AutoTokenizer

    tokenizer = AutoTokenizer.from_pretrained(BOOK_MODEL)
    model = AutoModelForSequenceClassification.from_pretrained(
        BOOK_MODEL, num_labels=3
    ).to(device)
    model.eval()
    id2label = {int(k): v for k, v in model.config.id2label.items()}
    probs = _probabilities(model, tokenizer, texts, device)

    columns = {}
    for index, name in id2label.items():
        key = str(name).strip().lower()
        if key in ORDER3:
            columns[ORDER3[key]] = probs[:, index]
    if len(columns) != 3:
        raise RuntimeError(f"id2label inattendu : {id2label}")
    return np.column_stack([columns[0], columns[1], columns[2]]), id2label


# --------------------------------------------------------------------------
# Etape 4 -- evaluation
# --------------------------------------------------------------------------

def _mcnemar(base_correct: np.ndarray, ft_correct: np.ndarray) -> dict:
    """Test exact de McNemar sur les predictions appariees du meme echantillon."""
    b = int(np.sum(base_correct & ~ft_correct))
    c = int(np.sum(~base_correct & ft_correct))
    n = b + c
    if n == 0:
        return {"b": b, "c": c, "n": 0, "p_value": 1.0}
    from math import comb

    k = min(b, c)
    p = sum(comb(n, i) for i in range(0, k + 1)) / (2 ** n) * 2
    return {"b": b, "c": c, "n": n, "p_value": float(min(1.0, p))}


def _strategy_returns(
    probs_mois: np.ndarray, rendement_mois: pd.Series, symbol: str
) -> float:
    """Regle du livre : long 100 % si `scores[2] > scores[0]`, sinon short 25 %.

    `probs_mois` porte les probabilites agregees du mois pour les deux bras,
    dans la convention du livre (0 = negative, 2 = positive).
    """
    if symbol not in rendement_mois.index:
        return float("nan")
    rendement = rendement_mois.loc[symbol]
    if not np.isfinite(rendement):
        return float("nan")
    weight = 1.0 if probs_mois[2] > probs_mois[0] else -0.25
    return float(weight * rendement)


def _aggregate(scores: np.ndarray) -> np.ndarray:
    """Agregation a poids exponentiels du livre."""
    n = scores.shape[0]
    weights = np.exp(np.linspace(0, 1, n))
    weights /= weights.sum()
    return (scores * weights[:, None]).sum(axis=0)


def _monthly_forward_returns(grid: pd.DataFrame, horizon: int = 21) -> dict:
    """Rendement forward sur ~`horizon` seances, indexe par mois d'entree.

    La cle est le mois de la **premiere seance** : c'est la date a laquelle le
    livre entre en position apres son rebalancement de debut de mois.
    """
    forward = grid.pct_change().shift(-horizon)
    rows: dict[str, pd.Series] = {}
    for timestamp, row in forward.iterrows():
        rows.setdefault(timestamp.strftime("%Y-%m"), row)
    return rows


def evaluate(run_dir: Path, data: pd.DataFrame, seeds: list[int], device: str) -> dict:
    months = sorted(data.month.unique())
    if len(months) <= HOLDOUT_MONTHS:
        raise RuntimeError("pas assez de mois pour un hors echantillon")
    test_months = months[-HOLDOUT_MONTHS:]
    train_months = months[:-HOLDOUT_MONTHS]
    train = data[data.month.isin(train_months)].reset_index(drop=True)
    test = data[data.month.isin(test_months)].reset_index(drop=True)
    log.info(
        "entrainement : %d echantillons / %d mois -- hors echantillon : %d / %d mois",
        len(train), len(train_months), len(test), len(test_months),
    )

    test_texts = list(test.text)
    base_probs, id2label = _base_predictions(test_texts, device)
    base_labels = base_probs.argmax(axis=1)
    base_correct = base_labels == test.label3.values
    log.info("modele de base : exactitude %.4f sur %d echantillons", base_correct.mean(), len(test))

    grid = _price_grid(load_closes(run_dir, UNIVERSE)[0])
    month_returns = _monthly_forward_returns(grid)

    per_seed = []
    for seed in seeds:
        log.info("graine %s", seed)
        model, tokenizer = finetune_one(train, seed, device)
        ft_probs = _probabilities(model, tokenizer, test_texts, device)
        ft_labels = ft_probs.argmax(axis=1)
        ft_correct = ft_labels == test.label3.values
        stats = _mcnemar(base_correct, ft_correct)
        par_mois = {}
        for month, group in test.groupby("month"):
            symbol = str(group.symbol.iloc[0])
            rendement = month_returns.get(month, pd.Series(dtype=float))
            r_base = _strategy_returns(
                _aggregate(base_probs[group.index]), rendement, symbol
            )
            r_ft = _strategy_returns(
                _aggregate(ft_probs[group.index]), rendement, symbol
            )
            par_mois[month] = {
                "n": int(len(group)),
                "symbole": symbol,
                "exactitude_base": float(base_correct[group.index].mean()),
                "exactitude_finetuned": float(ft_correct[group.index].mean()),
                "retour_base": r_base,
                "retour_finetuned": r_ft,
            }
        per_seed.append(
            {
                "seed": seed,
                "accuracy_base": float(base_correct.mean()),
                "accuracy_finetuned": float(ft_correct.mean()),
                "delta": float(ft_correct.mean() - base_correct.mean()),
                "mcnemar": stats,
                # Histogramme des classes PREDITES : sans lui, une exactitude
                # basse ne se distingue pas d'un modele qui repond toujours la
                # meme chose. C'est la mesure qui separe « il se trompe » de
                # « il a effondre sa sortie sur une classe ».
                "pred_base": np.bincount(base_labels, minlength=3).tolist(),
                "pred_finetuned": np.bincount(ft_labels, minlength=3).tolist(),
                "vrai": np.bincount(test.label3.values, minlength=3).tolist(),
                "par_mois": par_mois,
            }
        )
        log.info(
            "  exactitude base %.4f -> re-entraine %.4f (delta %+.4f, McNemar p=%.4f)",
            per_seed[-1]["accuracy_base"], per_seed[-1]["accuracy_finetuned"],
            per_seed[-1]["delta"], stats["p_value"],
        )
        log.info(
            "    classes predites [neg,neu,pos] : re-entraine %s | base %s | vrai %s",
            per_seed[-1]["pred_finetuned"], per_seed[-1]["pred_base"],
            per_seed[-1]["vrai"],
        )
        del model
        _torch().cuda.empty_cache()

    deltas = np.array([s["delta"] for s in per_seed])
    edge = float(deltas.mean() / deltas.std(ddof=1)) if len(deltas) > 1 and deltas.std(ddof=1) > 0 else float("nan")

    # Strategie : meme test, regle du livre, par mois. Le bras de base ne
    # depend pas de la graine ; le bras re-entraine, si.
    strategie = []
    for month in test_months:
        ref = per_seed[0]["par_mois"][month]
        retours_ft = np.array(
            [s["par_mois"][month]["retour_finetuned"] for s in per_seed], dtype=float
        )
        strategie.append(
            {
                "month": month,
                "symbol": ref["symbole"],
                "retour_base": ref["retour_base"],
                "retour_finetuned_moyenne": (
                    float(np.nanmean(retours_ft))
                    if np.isfinite(retours_ft).any()
                    else float("nan")
                ),
            }
        )
    cumul_base = float(np.nansum([s["retour_base"] for s in strategie]))
    cumul_ft = float(np.nansum([s["retour_finetuned_moyenne"] for s in strategie]))

    result = {
        "modele": BOOK_MODEL,
        "graines": seeds,
        "mois_entrainement": train_months,
        "mois_hors_echantillon": test_months,
        "n_entrainement": int(len(train)),
        "n_hors_echantillon": int(len(test)),
        "id2label_base": {str(k): v for k, v in id2label.items()},
        "accuracy_base": float(base_correct.mean()),
        "accuracy_finetuned_moyenne": float(np.mean([s["accuracy_finetuned"] for s in per_seed])),
        "delta_moyen": float(deltas.mean()),
        "delta_ecart_type": float(deltas.std(ddof=1)) if len(deltas) > 1 else 0.0,
        "edge_sigma": edge,
        "graines_gagnantes": int(np.sum(deltas > 0)),
        "par_graine": per_seed,
        "strategie_par_mois": strategie,
        "strategie_cumul_base": cumul_base,
        "strategie_cumul_finetuned": cumul_ft,
    }
    return result


# --------------------------------------------------------------------------
# Orchestration
# --------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    _setup_log()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", default="all",
                        choices=["data", "build", "finetune", "eval", "all"])
    parser.add_argument("--seeds", type=int, nargs="+", default=DEFAULT_SEEDS)
    parser.add_argument("--run-dir", required=True)
    parser.add_argument("--force-data", action="store_true")
    parser.add_argument("--device", default=None)
    args = parser.parse_args(argv)

    run_dir = Path(args.run_dir)
    (run_dir / "data").mkdir(parents=True, exist_ok=True)
    (run_dir / "results").mkdir(parents=True, exist_ok=True)

    torch = _torch()
    device = args.device or ("cuda" if torch.cuda.is_available() else "cpu")
    # Le nom de la carte est journalise, pas seulement l'index : sur une machine a
    # deux GPU, `cuda:0` ne dit pas laquelle a travaille. C'est la sonde qui fait
    # foi, et elle est recopiee dans les mesures committeees.
    device_name = (
        torch.cuda.get_device_name(device) if device.startswith("cuda") else "cpu"
    )
    log.info("device %s = %s (torch %s)", device, device_name, torch.__version__)

    if args.stage in ("data", "all"):
        stage_data(run_dir, force=args.force_data)
        # `all` poursuit ; seul `data` s'arrete ici. Le `return 0` inconditionnel
        # qui vivait ici faisait de `--stage all` un synonyme de `--stage data` :
        # le chemin par defaut n'entrainait jamais le modele.
        if args.stage == "data":
            return 0

    news = pd.read_csv(run_dir / "data" / "fnspid_news.csv")
    if news.empty:
        log.error("corpus vide -- relancer --stage data")
        return 2

    samples = build_samples(run_dir, news)
    samples.to_csv(run_dir / "data" / "samples.csv", index=False)
    log.info("echantillons ecrits : %s", run_dir / "data" / "samples.csv")

    if args.stage in ("build",):
        return 0

    result = evaluate(run_dir, samples, args.seeds, device)
    result["device"] = device_name
    result["torch"] = torch.__version__
    measures = FINETUNE_DIR / "measures"
    measures.mkdir(parents=True, exist_ok=True)
    for graine in result["par_graine"]:
        fichier = measures / f"seed-{graine['seed']}.json"
        fichier.write_text(
            json.dumps(graine, indent=2, ensure_ascii=False), encoding="utf-8"
        )
        log.info("mesures ecrites : %s", fichier)
    out = measures / "summary.json"
    out.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
    log.info("mesures ecrites : %s", out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
