"""
EPITA 2026 - Notation collegiale PrCon (Programmation par Contraintes)
Compile teacher grades + peer evals -> final grades with redressement.
4 criteria: Presentation/10, Theorique/10, Technique/10, Organisation/10
Note/20 = (P+T+Tech+Org) / 40 * 20

Usage:
    python scripts/compile_epita_prcon_2026.py

Output:
    G:/Mon Drive/MyIA/Formation/Epita/2026/Notes_Finales_PrCon_2026.xlsx
"""
import pandas as pd
import numpy as np
from pathlib import Path

# === PATHS ===
BASE = Path(r"G:\Mon Drive\MyIA\Formation\Epita\2026")
GFORM_FILE = BASE / (
    "Epita - 2026 - PrCon - Evaluations (réponses) - "
    "Réponses au formulaire 1.csv"
)
GROUP_FILE = BASE / "Groupe Programmation Par Contrainte - Feuille 1.csv"
OUTPUT_FILE = BASE / "Notes_Finales_PrCon_2026.xlsx"

# === PARAMS ===
TEACHER_WEIGHT = 0.5   # 50% teacher / 50% peer
TARGET_MEAN = 13.0
TARGET_STD = 2.5
MAX_NOTE = 20.0
MIN_NOTE = 0.0

TEACHER_EMAIL = "jsboige@gmail.com"


def parse_groups():
    """Parse group composition from CSV."""
    df = pd.read_csv(GROUP_FILE, encoding="utf-8")
    # Columns may vary, return raw for inspection
    return df


def compute_note(p, t, tech, org):
    """Convert P/T/Tech/Org (each /10) to /20."""
    return (p + t + tech + org) / 40.0 * 20.0


def apply_redressement(notes, target_mean=TARGET_MEAN, target_std=TARGET_STD):
    """Linear redressement to target mean and std."""
    current_mean = np.mean(notes)
    current_std = np.std(notes, ddof=0)

    if current_std < 0.01:
        return np.clip(np.full_like(notes, target_mean), MIN_NOTE, MAX_NOTE)

    scaled = (notes - current_mean) / current_std * target_std + target_mean
    return np.clip(scaled, MIN_NOTE, MAX_NOTE)


def main():
    # Load GForm data
    df = pd.read_csv(GFORM_FILE, encoding="utf-8")

    # Identify columns by position
    col_group = df.columns[4]
    col_p = df.columns[6]
    col_t = df.columns[7]
    col_tech = df.columns[8]
    col_org = df.columns[9]
    col_email = df.columns[1]

    # Separate teacher and peer
    teacher_df = df[df[col_email] == TEACHER_EMAIL]
    peer_df = df[df[col_email] != TEACHER_EMAIL]

    # Build teacher grades dict: group_name -> (p, t, tech, org)
    teacher_grades = {}
    for _, row in teacher_df.iterrows():
        grp = row[col_group]
        teacher_grades[grp] = {
            "p": float(row[col_p]),
            "t": float(row[col_t]),
            "tech": float(row[col_tech]),
            "org": float(row[col_org]),
        }

    # Aggregate peer evals per group
    peer_agg = {}
    for grp_name, grp_df in peer_df.groupby(col_group):
        peer_agg[grp_name] = {
            "p_mean": grp_df[col_p].mean(),
            "t_mean": grp_df[col_t].mean(),
            "tech_mean": grp_df[col_tech].mean(),
            "org_mean": grp_df[col_org].mean(),
            "n_peers": len(grp_df),
        }

    # Build grading table
    rows = []
    for grp_name in sorted(teacher_grades.keys()):
        tg = teacher_grades[grp_name]
        teacher_note = compute_note(tg["p"], tg["t"], tg["tech"], tg["org"])

        # Extract short label (before parenthesis)
        label = grp_name.split(" (")[0].strip() if " (" in grp_name else grp_name
        # Extract members
        membres = ""
        if "(" in grp_name and ")" in grp_name:
            membres = grp_name[grp_name.index("(")+1:grp_name.index(")")]

        # Peer data
        peer = peer_agg.get(grp_name)
        if peer and peer["n_peers"] >= 1:
            peer_note = compute_note(
                peer["p_mean"], peer["t_mean"],
                peer["tech_mean"], peer["org_mean"]
            )
            coll_note = TEACHER_WEIGHT * teacher_note + (1 - TEACHER_WEIGHT) * peer_note
            source = f"50/50 (n={peer['n_peers']})"
        else:
            peer_note = None
            coll_note = teacher_note
            source = "teacher-only"

        rows.append({
            "Groupe": label,
            "Membres": membres,
            "Teacher_P/10": tg["p"],
            "Teacher_T/10": tg["t"],
            "Teacher_Tech/10": tg["tech"],
            "Teacher_Org/10": tg["org"],
            "Teacher/20": round(teacher_note, 2),
            "Peer_P/10": round(peer["p_mean"], 2) if peer else None,
            "Peer_T/10": round(peer["t_mean"], 2) if peer else None,
            "Peer_Tech/10": round(peer["tech_mean"], 2) if peer else None,
            "Peer_Org/10": round(peer["org_mean"], 2) if peer else None,
            "Peer/20": round(peer_note, 2) if peer else None,
            "N_Peers": peer["n_peers"] if peer else 0,
            "Source": source,
            "Collegiale/20": round(coll_note, 2),
        })

    result = pd.DataFrame(rows)

    # Redressement
    coll_notes = result["Collegiale/20"].values.astype(float)
    redressed = apply_redressement(coll_notes)
    result["Redressee/20"] = np.round(redressed, 2)
    result["Note_Finale/20"] = result["Redressee/20"].apply(
        lambda x: round(min(MAX_NOTE, max(MIN_NOTE, x)), 1)
    )

    # Sort
    result = result.sort_values("Groupe").reset_index(drop=True)

    # Summary
    print(f"=== EPITA PrCon 2026 — {len(result)} groupes ===")
    print(f"Teacher rows: {len(teacher_df)}, Peer rows: {len(peer_df)}")
    print(f"\nMean collegiale: {coll_notes.mean():.2f}, Std: {np.std(coll_notes):.2f}")
    print(f"\n=== TOP 5 ===")
    top5 = result.nlargest(5, "Note_Finale/20")
    print(top5[["Groupe", "Membres", "Teacher/20", "Peer/20", "Note_Finale/20"]].to_string(index=False))
    print(f"\n=== BOTTOM 5 ===")
    bot5 = result.nsmallest(5, "Note_Finale/20")
    print(bot5[["Groupe", "Membres", "Teacher/20", "Peer/20", "Note_Finale/20"]].to_string(index=False))

    final = result["Note_Finale/20"].values
    print(f"\nMean finale: {final.mean():.2f}, Std finale: {final.std():.2f}")

    # Write Excel
    with pd.ExcelWriter(OUTPUT_FILE, engine="openpyxl") as writer:
        result.to_excel(writer, sheet_name="Notes", index=False)

        # Full detail
        summary = pd.DataFrame({
            "Parametre": [
                "TEACHER_WEIGHT", "PEER_WEIGHT", "TARGET_MEAN", "TARGET_STD",
                "N_groupes", "Mean_collegiale", "Std_collegiale",
                "Mean_finale", "Std_finale", "Date_compilation"
            ],
            "Valeur": [
                TEACHER_WEIGHT, 1 - TEACHER_WEIGHT, TARGET_MEAN, TARGET_STD,
                len(result), round(float(coll_notes.mean()), 2),
                round(float(np.std(coll_notes)), 2),
                round(float(final.mean()), 2), round(float(final.std()), 2),
                pd.Timestamp.now().strftime("%Y-%m-%d %H:%M")
            ]
        })
        summary.to_excel(writer, sheet_name="Params", index=False)

    print(f"\nXLSX saved: {OUTPUT_FILE}")
    return result


if __name__ == "__main__":
    main()
