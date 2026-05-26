"""
ESGF 2026 - Notation collegiale Trading Algorithmique
Compile teacher grades + peer evals -> final grades with redressement.

Usage:
    python scripts/compile_esgf_2026.py

Output:
    G:/Mon Drive/MyIA/Formation/ESGF/2026/Notes_Finales_ESGF_2026_Compilation.xlsx
"""
import pandas as pd
import numpy as np
from pathlib import Path

# === PATHS ===
BASE = Path(r"G:\Mon Drive\MyIA\Formation\ESGF\2026")
COMP_FILE = BASE / "Présentation trading 4 BD 2025-2026.xlsx"
REVIEW_FILE = BASE / "SOUTENANCE_2026-05-19_REVIEW.md"
GFORM_FILE = BASE / (
    "ESG - 2026 - 5ESGF-5BD1 - Trading Algorithmique - "
    "Evaluations (réponses) - Réponses au formulaire 1.csv"
)
OUTPUT_FILE = BASE / "Notes_Finales_ESGF_2026_Compilation.xlsx"

# === PARAMS ===
TEACHER_WEIGHT = 0.5   # 50% teacher / 50% peer where peer data available
TARGET_MEAN = 13.0
TARGET_STD = 2.5
MAX_NOTE = 20.0
MIN_NOTE = 0.0

# === TEACHER GRADES (from REVIEW - SUGGESTION DE NOTATION) ===
# Format: group_key -> (Presentation/10, Theorique/10, Technique/10)
TEACHER_GRADES = {
    "Gr01": (7, 7, 7),       # EMA Cross - Fane/Fomene/Mayuma
    "Gr02": (4, 4, 4),       # Dzolevo+Morel - MarkovRegime+MultiTimeframe
    "Gr03": (7, 7, 7),       # El Hajji - LLM Sentiment (provisional)
    "Gr04": (7, 6, 6),       # Bayiha/Diallo/Ekoue-Bla - AdaptativeAssetAllocation
    "Gr05": (9, 9, 9),       # Keita/Gbemetounou/Photo Ngumba - DualMomentum
    "Gr06": (6, 6, 6),       # Wefang/Mahmoud/Kemdeng - SectorMomentum 11 ETFs
    "HL_Gueye": (8, 6, 6),   # Gueye/Gnire/Kora/Yoneba - SectorMomentumETF
    "HL_ZScore": (7, 7, 8),  # Bensaid/Zarrouk/Bourich - Z-Score Fondamentale
    "HL_Wheel": (7, 7, 4),   # Kadid/Ayivi/Ngassaki/Kabli - WheelTechSimple
    "HL_RiskParity": (7.5, 8, 7),  # Lidoh/El Ghali/Samer - RiskParityV5
}

# === QC BACKTEST STATS (from REVIEW) ===
BACKTEST_STATS = {
    "Gr01": {"project": "EMA-Cross-Stocks", "cloud_id": 31663164, "sharpe": 1.206, "cagr": 50.7, "maxdd": 43.1, "originalite": "PLAGIAT"},
    "Gr02a": {"project": "MultiTimeframeTrend", "cloud_id": 31864806, "sharpe": -0.282, "cagr": 1.8, "maxdd": 5.0, "originalite": "ORIGINAL"},
    "Gr02b": {"project": "MarkovRegimeDetection", "cloud_id": 31871247, "sharpe": None, "cagr": None, "maxdd": None, "originalite": "TRES_HAUTE"},
    "Gr03": {"project": "LLM Sentiment", "cloud_id": 31819357, "sharpe": 0.571, "cagr": 11.4, "maxdd": 19.6, "originalite": "HAUTE"},
    "Gr04a": {"project": "AAA iter2c", "cloud_id": 31781187, "sharpe": 0.527, "cagr": 8.1, "maxdd": 18.9, "originalite": "HAUTE"},
    "Gr04b": {"project": "Clone AAA 2", "cloud_id": 31851153, "sharpe": 0.466, "cagr": 7.6, "maxdd": 19.7, "originalite": "VARIANTE"},
    "Gr05": {"project": "DualMomentum", "cloud_id": 31798582, "sharpe": 0.620, "cagr": 10.4, "maxdd": 14.1, "originalite": "HAUTE"},
    "Gr06": {"project": "SECTOMOMENTUM 11 ETFS", "cloud_id": 31872194, "sharpe": 0.201, "cagr": 5.9, "maxdd": 21.6, "originalite": "SIMPLIFIEE"},
    "HL_Gueye": {"project": "SectorMomentum v4", "cloud_id": 31842772, "sharpe": 0.473, "cagr": 9.7, "maxdd": 37.3, "originalite": "HAUTE"},
    "HL_Gnire": {"project": "Projet Trading", "cloud_id": 31784813, "sharpe": 0.473, "cagr": 9.675, "maxdd": 37.3, "originalite": "MEME_GROUPE"},
    "HL_ZScore": {"project": "Z-Score Fondamentale", "cloud_id": 31932810, "sharpe": 0.225, "cagr": 6.35, "maxdd": 37.7, "originalite": "ORIGINAL"},
    "HL_Wheel": {"project": "WheelTechSimple", "cloud_id": 31846074, "sharpe": -0.510, "cagr": -104.0, "maxdd": 103.5, "originalite": "ORIGINAL"},
    "HL_RiskParity": {"project": "RiskParityV5", "cloud_id": 31872286, "sharpe": 0.514, "cagr": 9.26, "maxdd": 20.7, "originalite": "HAUTE"},
}

# === GForm group name -> internal key mapping ===
GFORM_GROUP_MAP = {
    "EMA-Cross-Stocks": "Gr01",
    "MarkovRegimeDetection": "Gr02",
    "projet ilias el hajji": "Gr03",
    "AdaptativeAssetAllocation": "Gr04",
    "DualMomentum": "Gr05",
    "Sector momentum 11 ETFs": "Gr06",
    "SectorMomentum - Kora - Gueye - Yonaba": "HL_Gueye",
    "Z-scode fondamentaux - Bensaid - Zarrouk - Bourich": "HL_ZScore",
    "OptionWheel - Kadid - Ayivi - Kabli- NGassaki": "HL_Wheel",
    "Risk-Parity - Lidoh - El Ghali": "HL_RiskParity",
}

# Fake groups to exclude from peer evals
FAKE_GROUPS = {"Upgraded Red-Orange Elephant"}

TEACHER_EMAIL = "jsboige@gmail.com"


def parse_composition():
    """Parse group composition from XLSX."""
    df = pd.read_excel(COMP_FILE, sheet_name="Feuil1")
    df.columns = ["Groupe", "Projet_QC", "Nom", "Prenom", "User_QC"]
    df["Groupe"] = df["Groupe"].ffill()
    df["Projet_QC"] = df["Projet_QC"].ffill()
    df = df[df["Nom"] != "Nom"].reset_index(drop=True)

    groups = {}
    for _, row in df.iterrows():
        if pd.isna(row["Groupe"]):
            continue
        g = int(row["Groupe"])
        if g not in groups:
            groups[g] = {"projet": row["Projet_QC"], "membres": []}
        groups[g]["membres"].append(f"{row['Prenom']} {row['Nom']}")
    return groups


def parse_peer_evals():
    """Parse peer evaluations from GForm CSV.

    Returns dict: group_key -> {p_mean, t_mean, tech_mean, n_peers}
    Excludes teacher row and fake groups.
    """
    df = pd.read_csv(GFORM_FILE, encoding="utf-8")
    # Normalize column names
    col_map = {}
    for c in df.columns:
        cl = c.lower().strip()
        if "qualité" in cl and "présentation" in cl:
            col_map[c] = "p_note"
        elif "qualité" in cl and "théorique" in cl:
            col_map[c] = "t_note"
        elif "qualité" in cl and "technique" in cl:
            col_map[c] = "tech_note"
        elif "groupe" in cl and "évaluer" in cl:
            col_map[c] = "group_name"
        elif "e-mail" in cl or "email" in cl:
            col_map[c] = "email"
    df = df.rename(columns=col_map)

    # Filter out teacher and fake groups
    mask_peer = (
        (df["email"] != TEACHER_EMAIL)
        & (~df["group_name"].isin(FAKE_GROUPS))
        & (df["group_name"].notna())
    )
    peers = df[mask_peer]

    # Map to internal keys
    peers["key"] = peers["group_name"].map(GFORM_GROUP_MAP)
    peers = peers[peers["key"].notna()]

    # Aggregate per group
    result = {}
    for key, grp in peers.groupby("key"):
        result[key] = {
            "p_mean": grp["p_note"].mean(),
            "t_mean": grp["t_note"].mean(),
            "tech_mean": grp["tech_note"].mean(),
            "n_peers": len(grp),
        }
    return result


def compute_note(p, t, tech):
    """Convert P/T/Tech (each /10) to /20."""
    return (p + t + tech) / 30.0 * 20.0


def apply_redressement(notes, target_mean=TARGET_MEAN, target_std=TARGET_STD):
    """Linear redressement to target mean and std."""
    current_mean = np.mean(notes)
    current_std = np.std(notes, ddof=0)

    if current_std < 0.01:
        return np.clip(np.full_like(notes, target_mean), MIN_NOTE, MAX_NOTE)

    scaled = (notes - current_mean) / current_std * target_std + target_mean
    return np.clip(scaled, MIN_NOTE, MAX_NOTE)


def main():
    groups = parse_composition()
    peer_evals = parse_peer_evals()

    rows = []
    for key, (tp, tt, ttech) in TEACHER_GRADES.items():
        teacher_note = compute_note(tp, tt, ttech)

        # Peer data
        peer = peer_evals.get(key)
        if peer and peer["n_peers"] >= 1:
            peer_note = compute_note(peer["p_mean"], peer["t_mean"], peer["tech_mean"])
            # Collegiale: 50/50 teacher/peer
            collegiale_note = TEACHER_WEIGHT * teacher_note + (1 - TEACHER_WEIGHT) * peer_note
            source = f"50/50 (n={peer['n_peers']})"
        else:
            collegiale_note = teacher_note
            peer_note = None
            source = "teacher-only"

        if key.startswith("HL_"):
            label = key
            membres = "—"
            projet = BACKTEST_STATS.get(key, {}).get("project", "?")
            cloud_id = BACKTEST_STATS.get(key, {}).get("cloud_id", "?")
            sharpe = BACKTEST_STATS.get(key, {}).get("sharpe", "?")
        else:
            gnum = int(key.replace("Gr", ""))
            gdata = groups.get(gnum, {"membres": ["?"], "projet": "?"})
            label = f"Gr{gnum:02d}"
            membres = ", ".join(gdata["membres"])
            projet = gdata["projet"]
            cloud_id = BACKTEST_STATS.get(key, {}).get("cloud_id", "?")
            sharpe = BACKTEST_STATS.get(key, {}).get("sharpe", "?")

        rows.append({
            "Groupe": label,
            "Membres": membres,
            "Projet_QC": projet,
            "Cloud_ID": cloud_id,
            "Sharpe": sharpe,
            "Teacher_P/10": tp,
            "Teacher_T/10": tt,
            "Teacher_Tech/10": ttech,
            "Teacher/20": round(teacher_note, 2),
            "Peer_P/10": round(peer["p_mean"], 2) if peer else None,
            "Peer_T/10": round(peer["t_mean"], 2) if peer else None,
            "Peer_Tech/10": round(peer["tech_mean"], 2) if peer else None,
            "Peer/20": round(peer_note, 2) if peer else None,
            "N_Peers": peer["n_peers"] if peer else 0,
            "Source": source,
            "Collegiale/20": round(collegiale_note, 2),
        })

    df = pd.DataFrame(rows)

    # Redressement on collegiale notes
    coll_notes = df["Collegiale/20"].values.astype(float)
    redressed = apply_redressement(coll_notes)
    df["Redressee/20"] = np.round(redressed, 2)
    df["Note_Finale/20"] = df["Redressee/20"].apply(
        lambda x: round(min(MAX_NOTE, max(MIN_NOTE, x)), 1)
    )

    # Sort
    df = df.sort_values("Groupe").reset_index(drop=True)

    # Summary stats
    print("=== NOTES COLLEGIALES (avant redressement) ===")
    print(df[["Groupe", "Teacher/20", "Peer/20", "Collegiale/20", "N_Peers", "Source"]].to_string(index=False))
    print(f"\nMean collegiale: {coll_notes.mean():.2f}, Std: {np.std(coll_notes):.2f}")
    print(f"\n=== NOTES FINALES (redressement target={TARGET_MEAN}/{TARGET_STD}) ===")
    print(df[["Groupe", "Collegiale/20", "Redressee/20", "Note_Finale/20"]].to_string(index=False))
    final = df["Note_Finale/20"].values
    print(f"\nMean finale: {final.mean():.2f}, Std finale: {final.std():.2f}")

    # Write to Excel
    with pd.ExcelWriter(OUTPUT_FILE, engine="openpyxl") as writer:
        df.to_excel(writer, sheet_name="Notes", index=False)

        # Summary sheet
        summary = pd.DataFrame({
            "Parametre": [
                "TEACHER_WEIGHT", "PEER_WEIGHT", "TARGET_MEAN", "TARGET_STD",
                "N_groupes", "Mean_collegiale", "Std_collegiale",
                "Mean_finale", "Std_finale", "Date_compilation"
            ],
            "Valeur": [
                TEACHER_WEIGHT, 1 - TEACHER_WEIGHT, TARGET_MEAN, TARGET_STD,
                len(df), round(float(coll_notes.mean()), 2), round(float(np.std(coll_notes)), 2),
                round(float(final.mean()), 2), round(float(final.std()), 2),
                pd.Timestamp.now().strftime("%Y-%m-%d %H:%M")
            ]
        })
        summary.to_excel(writer, sheet_name="Params", index=False)

        # Peer detail sheet
        peer_rows = []
        for key, peer in peer_evals.items():
            tp, tt, ttech = TEACHER_GRADES.get(key, (0, 0, 0))
            peer_rows.append({
                "Groupe": key,
                "N_Peers": peer["n_peers"],
                "Teacher_P": tp, "Teacher_T": tt, "Teacher_Tech": ttech,
                "Peer_P_mean": round(peer["p_mean"], 2),
                "Peer_T_mean": round(peer["t_mean"], 2),
                "Peer_Tech_mean": round(peer["tech_mean"], 2),
                "Delta_P": round(peer["p_mean"] - tp, 2),
                "Delta_T": round(peer["t_mean"] - tt, 2),
                "Delta_Tech": round(peer["tech_mean"] - ttech, 2),
            })
        pd.DataFrame(peer_rows).to_excel(writer, sheet_name="Peer_Detail", index=False)

    print(f"\nXLSX saved: {OUTPUT_FILE}")
    return df


if __name__ == "__main__":
    main()
