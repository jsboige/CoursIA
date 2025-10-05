import pandas as pd
import numpy as np
import os
import glob
import re
from unidecode import unidecode
import openpyxl
from rapidfuzz import fuzz

# --- Paramètres globaux ---
number_of_projects = 2
nb_eval_fields_per_project = [3, 3]
professor_email = "jsboige@gmail.com"
PROFESSOR_FULL_NAME = "Jean-Sylvain Boige"
SIMILARITY_THRESHOLD = 80 # Seuil pour le fuzzy matching
TEACHER_WEIGHT = 1.0 # Poids de la note du professeur. 1.0 = 50% du total.

# --- Structures de données ---

class StudentRecord:
    def __init__(self, prenom, nom, sujet_projet_1, sujet_projet_2=None):
        self.prenom = prenom
        self.nom = nom
        self.sujets = [sujet_projet_1]
        if sujet_projet_2:
            self.sujets.append(sujet_projet_2)
        self.notes = []

    @property
    def moyenne(self):
        return np.mean(self.notes) if self.notes else 0

class EvaluationRecord:
    def __init__(self, date, email, nom, prenom, groupe, sujet_libre, notes_dict,
                 points_positifs, points_negatifs, recommandations):
        self.date = pd.to_datetime(date, dayfirst=True, errors='coerce')
        self.email = email
        self.nom = nom
        self.prenom = prenom
        self.groupe = str(groupe) if pd.notna(groupe) else ""
        self.sujet_libre = sujet_libre
        self.notes = {k: int(v) for k, v in notes_dict.items() if pd.notna(v) and str(v).strip()}
        self.points_positifs = points_positifs
        self.points_negatifs = points_negatifs
        self.recommandations = recommandations
        self.is_teacher = False

    @property
    def note(self):
        if not self.notes:
            return 0
        total_notes = sum(self.notes.values())
        nb_eval_fields = len(self.notes)
        # Each criterion is out of 10. We normalize to a score out of 20.
        # (total_score / (num_fields * 10)) * 20  which simplifies to (total_score * 2) / num_fields
        return (total_notes * 2) / nb_eval_fields if nb_eval_fields > 0 else 0

class GroupEvaluation:
    def __init__(self, groupe, evaluations, group_members):
        self.groupe = groupe
        self.evaluations = evaluations
        self.group_members = group_members
        self.note_rectifiee = 0

    @property
    def moyenne(self):
        student_evals = [e.note for e in self.evaluations if not e.is_teacher]
        teacher_evals = [e.note for e in self.evaluations if e.is_teacher]

        student_avg = np.mean(student_evals) if student_evals else 0
        teacher_avg = np.mean(teacher_evals) if teacher_evals else 0
        
        # Si pas de notes étudiantes, on retourne la note du prof directement
        if not student_evals:
            return teacher_avg

        # Si pas de note prof, on retourne la moyenne étudiante
        if not teacher_evals:
            return student_avg
            
        # Logique de pondération du notebook original
        # Note: avec TEACHER_WEIGHT = 1.0, la note du prof pèse 50% de la note finale
        # peu importe le nombre d'évaluations étudiantes.
        numerator = student_avg + (teacher_avg * TEACHER_WEIGHT)
        denominator = 1 + TEACHER_WEIGHT
        
        return numerator / denominator if denominator > 0 else 0

    @property
    def ecart_type(self):
        all_notes = [e.note for e in self.evaluations]
        if len(all_notes) < 2:
            return 0
        return np.std(all_notes)

    @property
    def date(self):
        return self.evaluations[len(self.evaluations) // 2].date if self.evaluations else None


class ProjectEvaluation:
    def __init__(self, professor_email, student_records):
        self.professor_email = professor_email
        self.student_records = student_records
        self.grouped_evaluations = []

    @staticmethod
    def fold_accents(text):
        return unidecode(text)

    def project_name(self, name):
        if not isinstance(name, str):
            return ""
        first_name = name.split(" ")[0].split("-")[0]
        first_name = first_name[:5]
        return self.fold_accents(first_name.lower().strip())

    def match_names(self, student_or_eval1, eval2):
        name1 = student_or_eval1.nom
        prenom1 = student_or_eval1.prenom
        
        name2 = eval2.nom
        prenom2 = eval2.prenom

        return (self.project_name(name1) == self.project_name(name2) and self.project_name(prenom1) == self.project_name(prenom2)) or \
               (self.project_name(prenom1) == self.project_name(name2) and self.project_name(name1) == self.project_name(prenom2))

    def is_valid_evaluation(self, group_evaluation, eval_record, seen_evaluators):
        # Règle 1: Rejeter les notes invalides
        # Le professeur peut mettre 20, mais pas les étudiants (limités à 19.999...)
        is_student_perfect_score = not eval_record.is_teacher and eval_record.note >= 20
        if is_student_perfect_score or eval_record.note < 1:
            print(f"AVERTISSEMENT: Note invalide ({eval_record.note}) pour le groupe {group_evaluation.groupe} par {eval_record.prenom} {eval_record.nom}. Evaluation écartée.")
            return False

        # Règle 2: Rejeter les dates incohérentes
        if group_evaluation.date and abs((group_evaluation.date - eval_record.date).total_seconds()) > 5 * 3600:
            print(f"AVERTISSEMENT: Date d'évaluation incohérente pour le groupe {group_evaluation.groupe} par {eval_record.prenom} {eval_record.nom}. Evaluation écartée.")
            return False

        # Règle 3: Rejeter les évaluateurs non-inscrits (sauf le professeur)
        if not eval_record.is_teacher:
            is_registered = any(self.match_names(student, eval_record) for student in self.student_records)
            if not is_registered:
                print(f"AVERTISSEMENT: L'évaluateur {eval_record.prenom} {eval_record.nom} n'est pas inscrit au cours. Evaluation pour {group_evaluation.groupe} écartée.")
                return False

        # Règle 4: Rejeter les auto-évaluations
        is_member = any(self.match_names(member, eval_record) for member in group_evaluation.group_members)
        if is_member:
            print(f"AVERTISSEMENT: Auto-évaluation par {eval_record.prenom} {eval_record.nom} pour son propre groupe {group_evaluation.groupe}. Evaluation écartée.")
            return False

        # Règle 5: Rejeter les évaluations en double
        evaluator_id = eval_record.email
        if evaluator_id in seen_evaluators:
            print(f"AVERTISSEMENT: Evaluation double par {eval_record.prenom} {eval_record.nom} pour le groupe {group_evaluation.groupe}. Evaluation écartée.")
            return False

        return True

    def filter_evaluations(self):
        for group_eval in self.grouped_evaluations:
            valid_evaluations = []
            seen_evaluators = set()
            # Trier les évaluations par date pour que la première évaluation valide serve de référence temporelle
            sorted_evaluations = sorted(group_eval.evaluations, key=lambda e: e.date)
            for evaluation in sorted_evaluations:
                if self.is_valid_evaluation(group_eval, evaluation, seen_evaluators):
                    valid_evaluations.append(evaluation)
                    seen_evaluators.add(evaluation.email)
            group_eval.evaluations = valid_evaluations

    @property
    def moyenne(self):
        if not self.grouped_evaluations: return 0
        notes = [ge.moyenne * len(ge.group_members) for ge in self.grouped_evaluations if ge.group_members]
        counts = [len(ge.group_members) for ge in self.grouped_evaluations if ge.group_members]
        return np.sum(notes) / np.sum(counts) if np.sum(counts) > 0 else 0

    @property
    def ecart_type(self):
        if not self.grouped_evaluations: return 0
        mean = self.moyenne
        squared_diffs = [((ge.moyenne - mean) ** 2) * len(ge.group_members) for ge in self.grouped_evaluations if ge.group_members]
        counts = [len(ge.group_members) for ge in self.grouped_evaluations if ge.group_members]
        return np.sqrt(np.sum(squared_diffs) / np.sum(counts)) if np.sum(counts) > 0 else 0

# --- Fonctions de traitement ---

def load_student_records(file_path):
    df = pd.read_csv(file_path, delimiter=',')
    
    # Dictionnaire de renommage plus robuste pour les variations de colonnes
    column_mapping = {
        # Variations pour le prénom
        "Prénom": "prenom",
        "Prenom": "prenom",
        # Variations pour le nom
        "Nom": "nom",
        # Variations pour le sujet du projet
        "Sujet IA Symbolique": "sujet_projet_1",
        "Sujet Projet de Programmation par Contrainte": "sujet_projet_1"
    }
    df = df.rename(columns=column_mapping)
    
    students = []
    # Vérifier que les colonnes nécessaires existent après renommage
    required_cols = ['prenom', 'nom', 'sujet_projet_1']
    if not all(col in df.columns for col in required_cols):
        missing_cols = [col for col in required_cols if col not in df.columns]
        raise ValueError(f"Colonnes manquantes dans {file_path} après renommage : {missing_cols}. Colonnes disponibles : {df.columns.tolist()}")

    for _, row in df.iterrows():
        # Vérification de la validité des données avant de créer l'objet
        prenom = row.get('prenom')
        nom = row.get('nom')
        if pd.isna(prenom) or not str(prenom).strip() or pd.isna(nom) or not str(nom).strip():
            print(f"AVERTISSEMENT: Ligne ignorée dans {file_path} car le nom ou le prénom est manquant : Ligne { _ + 2 }")
            continue
        students.append(StudentRecord(prenom, nom, row['sujet_projet_1']))
    return students


def load_grades_from_file(file_path, correct_prof_name, correct_prof_email, threshold=80):
    """
    Charge les évaluations depuis un fichier CSV, identifie le professeur avec une logique de fuzzy matching
    et retourne une liste d'objets EvaluationRecord enrichis.
    """
    df = pd.read_csv(file_path, delimiter=',')
    column_mapping = {
        "Horodateur": "date", "Adresse e-mail": "email", "Votre nom": "nom", "Votre prénom": "prenom",
        "Groupe à évaluer": "groupe", "Sujet de la présentation": "sujet_libre",
        "Qualité de la présentation (communication, la forme)": "note_communication",
        "Qualité théorique (principes utilisés, classe d'algorithmes, contexte et explications des performances et des problèmes, histoire etc.)": "note_theorique",
        "Qualité technique (livrables, commits, qualité du code, démos, résultats, perspectives)": "note_technique",
        "Organisation (planning, répartition des tâches, collaboration, intégration au projet Github)": "note_organisation",
        "Points positifs de la présentation": "points_positifs",
        "Points négatifs de la présentation": "points_negatifs",
        "Recommandations pour s'améliorer": "recommandations"
    }
    df.rename(columns=column_mapping, inplace=True)

    df['nom_complet'] = df['prenom'].astype(str).str.strip() + " " + df['nom'].astype(str).str.strip()

    def normalize_name(name):
        return unidecode(name).lower().strip()

    normalized_prof_name = normalize_name(correct_prof_name)

    evaluations = []
    note_cols = [col for col in ["note_communication", "note_theorique", "note_technique", "note_organisation"] if col in df.columns]

    for _, row in df.iterrows():
        if not any(pd.notna(row.get(col)) and str(row.get(col)).strip() for col in note_cols):
            continue

        evaluator_name = row['nom_complet']
        normalized_evaluator = normalize_name(evaluator_name)
        similarity = fuzz.ratio(normalized_prof_name, normalized_evaluator)
        
        is_teacher = False
        if similarity >= threshold:
            is_teacher = True
            if row['email'] and row['email'].strip() != correct_prof_email:
                print(f"AVERTISSEMENT : L'évaluateur '{evaluator_name}' identifié comme le professeur a une adresse email potentiellement incorrecte: '{row['email']}'")

        notes_dict = {col: row.get(col) for col in note_cols}
        record = EvaluationRecord(
            row.get('date'), row.get('email'), row.get('nom'), row.get('prenom'),
            row.get('groupe'), row.get('sujet_libre'), notes_dict,
            row.get('points_positifs'), row.get('points_negatifs'), row.get('recommandations')
        )
        record.is_teacher = is_teacher
        evaluations.append(record)

    return evaluations


def adjust_grade(original_grade, group_mean, group_std_dev, target_mean=10, target_std_dev=2):
    if group_std_dev == 0:
        return target_mean
    adjusted_grade = ((original_grade - group_mean) / group_std_dev) * target_std_dev + target_mean
    return np.clip(adjusted_grade, 0, 20)


group_size_adjustments = {1: 3.0, 2: 1.0, 3: 0.0, 4: -1.0}

def palier_group_size_adjustment(group_size):
    # Malus par défaut de -2 pour les tailles de groupe non définies (ex: 5, 6...)
    return group_size_adjustments.get(group_size, -2.0)


def generate_workbook(project_evaluations, students, output_path):
    """
    Génère un classeur Excel contenant le rapport de notes détaillé.
    """
    if not project_evaluations:
        print(f"ERREUR: Aucune donnée à traiter pour le rapport : {output_path}")
        return

    # On suppose qu'on traite un projet à la fois
    project_evaluation = project_evaluations[0]

    report_data = []
    for group_eval in project_evaluation.grouped_evaluations:
        members = ", ".join([f"{s.prenom} {s.nom}" for s in group_eval.group_members])
        report_data.append({
            "Groupe (Sujet)": group_eval.groupe,
            "Membres": members,
            "Taille du Groupe": len(group_eval.group_members),
            "Moyenne Brute": group_eval.moyenne,
            "Note Intermédiaire (avec bonus/malus)": getattr(group_eval, 'intermediate_grade', 'N/A'),
            "Note Finale Ajustée": group_eval.note_rectifiee
        })

    if not report_data:
        print(f"AVERTISSEMENT: Aucune donnée de groupe à écrire dans le rapport {output_path}.")
        # Créer un DataFrame vide avec les en-têtes pour éviter l'échec de la vérification
        df = pd.DataFrame(columns=["Groupe (Sujet)", "Membres", "Taille du Groupe", "Moyenne Brute", "Note Intermédiaire (avec bonus/malus)", "Note Finale Ajustée"])
    else:
        df = pd.DataFrame(report_data)

    try:
        # Utilisation de pandas pour écrire facilement le fichier Excel
        df.to_excel(output_path, sheet_name='Rapport de Notes', index=False, engine='openpyxl')
        print(f"Classeur généré avec succès à : {output_path}")
    except Exception as e:
        print(f"ERREUR CRITIQUE: Impossible de sauvegarder le fichier Excel à {output_path}. Exception: {e}")


def fuzzy_match_group(eval_group_name, student_project_string):
    """
    Tente de faire correspondre un nom de groupe d'évaluation (potentiellement simple)
    avec une chaîne de projet d'étudiant (potentiellement plus descriptive).
    """
    if not isinstance(eval_group_name, str) or not isinstance(student_project_string, str):
        return False

    # Normalisation : minuscules, suppression des espaces superflus
    eval_norm = eval_group_name.lower().strip()
    student_norm = student_project_string.lower().strip()

    # Cas 1: Correspondance directe (pour les noms simples comme "Quoridor")
    if eval_norm == student_norm:
        return True

    # Cas 2: Si l'un est contenu dans l'autre (ex: "groupe 1" et "1")
    if eval_norm in student_norm or student_norm in eval_norm:
        return True

    # Cas 3: Extraction de tous les numéros et comparaison des ensembles
    eval_nums = set(re.findall(r'\d+', eval_norm))
    student_nums = set(re.findall(r'\d+', student_norm))

    # Si les deux chaînes contiennent des numéros et qu'ils ont au moins un numéro en commun
    if eval_nums and student_nums and eval_nums.intersection(student_nums):
        return True

    return False

def process_grades(registration_file, evaluation_file, output_dir, class_name, all_students):
    """
    Traite les notes pour une classe donnée à partir des fichiers d'inscription et d'évaluation.
    """
    # --- Chargement des données ---
    # `student_records` contient uniquement les étudiants de la classe en cours, pour former les groupes.
    student_records = load_student_records(registration_file)
    project_evals = load_grades_from_file(evaluation_file, PROFESSOR_FULL_NAME, professor_email, SIMILARITY_THRESHOLD)
    
    # --- Traitement ---
    # `project_evaluation` utilise `all_students` (toutes classes confondues) pour la validation des évaluateurs.
    project_evaluation = ProjectEvaluation(professor_email, all_students)
    
    df = pd.DataFrame([vars(e) for e in project_evals])
    # Group by the 'groupe' field, converting to string to be safe
    grouped = df.groupby(df['groupe'].astype(str))

    group_evals = []
    for name, group_df in grouped:
        evals_indices = group_df.index
        evals = [e for i, e in enumerate(project_evals) if i in evals_indices]
        
        # Utiliser la logique de correspondance floue pour trouver les membres
        members = [s for s in student_records for s_sujet in s.sujets if fuzzy_match_group(name, s_sujet)]
        group_evals.append(GroupEvaluation(name, evals, members))
    
    project_evaluation.grouped_evaluations = group_evals
    project_evaluation.filter_evaluations()

    # --- Points de contrôle post-filtrage ---
    validated_group_evals = []
    for group_eval in project_evaluation.grouped_evaluations:
        # Vérification 1: Le groupe ne doit pas être vide. Sinon, on l'ignore.
        if not group_eval.group_members:
            print(f"AVERTISSEMENT CRITIQUE: Le groupe '{group_eval.groupe}' n'a aucun membre inscrit et sera ignoré.")
            continue

        # Vérification 2: Présence de l'évaluation du professeur (maintenant bloquant)
        if not any(e.is_teacher for e in group_eval.evaluations):
            raise ValueError(f"Erreur critique : L'évaluation du professeur est manquante pour le groupe '{group_eval.groupe}'.")
        
        validated_group_evals.append(group_eval)
    project_evaluation.grouped_evaluations = validated_group_evals

    # --- Rectification des notes en deux passes ---
    target_mean, target_stdev = (15.5, 2.0)

    # Passe 1: Calcul des notes intermédiaires avec bonus/malus
    intermediate_grades = []
    for group_eval in project_evaluation.grouped_evaluations:
        raw_avg = group_eval.moyenne
        bonus_malus = palier_group_size_adjustment(len(group_eval.group_members))
        intermediate_grade = np.clip(raw_avg + bonus_malus, 0, 20)
        # Stockage temporaire de la note intermédiaire pour la passe 2
        group_eval.intermediate_grade = intermediate_grade
        intermediate_grades.append(intermediate_grade)

    # Passe 2: Normalisation basée sur les statistiques des notes intermédiaires
    if not intermediate_grades:
        # Gérer le cas où il n'y a aucune note à traiter
        project_mean = target_mean
        project_stdev = 0
    else:
        # Calcul des nouvelles statistiques basées sur les notes intermédiaires
        project_mean = np.mean(intermediate_grades)
        project_stdev = np.std(intermediate_grades)

    for group_eval in project_evaluation.grouped_evaluations:
        # Utilisation de la note intermédiaire stockée pour la normalisation
        current_grade = group_eval.intermediate_grade
        final_grade = adjust_grade(current_grade, project_mean, project_stdev, target_mean, target_stdev)
        group_eval.note_rectifiee = np.clip(final_grade, 14, 20)

    # --- Génération du fichier Excel ---
    output_filename = f"rapport_notes_{class_name}.xlsx"
    output_path = os.path.join(output_dir, output_filename)
    
    # La fonction generate_workbook attend une liste de projets, nous l'encapsulons
    generate_workbook([project_evaluation], student_records, output_path)
    print(f"Le traitement pour la classe {class_name} est terminé. Fichier de résultats : {output_path.replace('//', '/')}")

    # Retourner l'objet traité pour l'analyse qualitative
    return project_evaluation

def generate_qualitative_summary(project_evaluation, class_name):
    """
    Affiche un résumé qualitatif des résultats de la notation pour une classe.
    """
    print(f"\n--- Résumé Qualitatif pour la classe : {class_name} ---")
    
    if not project_evaluation or not project_evaluation.grouped_evaluations:
        print("Aucune donnée d'évaluation à analyser.")
        return

    # Trier les groupes par note finale
    sorted_groups = sorted(project_evaluation.grouped_evaluations, key=lambda g: g.note_rectifiee, reverse=True)
    
    if not sorted_groups:
        print("Aucun groupe validé à analyser.")
        return

    # 1. Meilleur et moins bon groupe
    best_group = sorted_groups[0]
    worst_group = sorted_groups[-1]
    print(f"\n🏆 Meilleur Groupe : '{best_group.groupe}' (Note: {best_group.note_rectifiee:.2f})")
    print(f"📉 Moins bon Groupe : '{worst_group.groupe}' (Note: {worst_group.note_rectifiee:.2f})")

    # 2. Moyenne et Écart-type globaux
    overall_mean = project_evaluation.moyenne
    overall_std = project_evaluation.ecart_type
    print(f"\n📊 Statistiques Globales (basées sur les moyennes brutes de groupe pondérées) :")
    print(f"   - Moyenne de la classe : {overall_mean:.2f}")
    print(f"   - Écart-type de la classe : {overall_std:.2f}")

    # 3. Forme de la distribution
    final_notes = [g.note_rectifiee for g in sorted_groups]
    final_mean = np.mean(final_notes)
    final_median = np.median(final_notes)
    
    distribution_shape = "plutôt symétrique"
    if final_mean > final_median + 0.2:
        distribution_shape = "étirée vers la droite (quelques très bonnes notes)"
    elif final_mean < final_median - 0.2:
        distribution_shape = "étirée vers la gauche (quelques très mauvaises notes)"
        
    print(f"\n📈 Distribution des Notes Finales :")
    print(f"   - Moyenne : {final_mean:.2f}")
    print(f"   - Médiane : {final_median:.2f}")
    print(f"   - Forme : La distribution est {distribution_shape}.")

    # 4. Liste des sujets et résultats
    print("\n📋 Détail des notes par groupe (trié par note finale) :")
    print("-" * 60)
    print(f"{'Groupe (Sujet)':<40} {'Note Finale':>15}")
    print("-" * 60)
    for group in sorted_groups:
        print(f"{str(group.groupe):<40} {group.note_rectifiee:>15.2f}")
    print("-" * 60)