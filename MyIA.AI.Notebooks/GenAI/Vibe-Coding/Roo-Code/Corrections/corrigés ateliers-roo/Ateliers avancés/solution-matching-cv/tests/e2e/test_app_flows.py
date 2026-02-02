import pytest
import os
from playwright.sync_api import expect

@pytest.mark.parametrize(
    "algo_id, algo_name, timeout",
    [
        ("simple", "SIMPLE", 5000),
        ("best_score_semantic", "BEST_SCORE_SEMANTIC", 8000),
        ("stable_semantic", "STABLE_SEMANTIC", 8000),
    ],
)
def test_app_matching_flows(page, flask_server, app_dir, algo_id, algo_name, timeout):
    """
    Teste le parcours complet pour chaque algorithme de matching.
    """
    page.goto(flask_server)

    try:
        print(f"[{algo_name}] Page chargée. Test avec les données pré-chargées.")
        
        print(f"[{algo_name}] Sélection de l'algorithme...")
        page.locator(f'input[name="matching_algorithm"][value="{algo_id}"]').click()

        print(f"[{algo_name}] Clic sur le bouton de soumission...")
        page.locator('button[type="submit"]').click()

        print(f"[{algo_name}] Attente de la visibilité du tableau de résultats (timeout: {timeout}ms)...")
        expect(page.locator("table")).to_be_visible(timeout=timeout)

        # Vérification approfondie du contenu du tableau
        rows = page.locator("table tr").all()
        assert len(rows) > 1, f"Le tableau devrait contenir au moins une ligne de données."
        
        # Vérifier les en-têtes
        headers = [header.inner_text() for header in rows[0].locator("th").all()]
        print(f"[{algo_name}] En-têtes trouvés: {headers}")
        assert "job_title" in headers, "La colonne 'job_title' est manquante."
        assert "consultant_name" in headers, "La colonne 'consultant_name' est manquante."

        # Vérifier le contenu des lignes de données
        for i, row in enumerate(rows[1:], 1): # Ignorer l'en-tête
            cells = row.locator("td").all()
            consultant_name = cells[headers.index("consultant_name")].inner_text()
            
            assert consultant_name is not None, f"La cellule du nom du consultant est nulle à la ligne {i}."
            assert consultant_name.strip() != "", f"La cellule du nom du consultant est vide à la ligne {i}."
            assert "NaN" not in consultant_name, f"La cellule du nom du consultant contient 'NaN' à la ligne {i}."

        print(f"[{algo_name}] Test du matching et de la validité des données réussi pour {len(rows) - 1} lignes.")

    except Exception as e:
        screenshot_path = f"screenshot_error_{algo_name}.png"
        page.screenshot(path=screenshot_path)
        pytest.fail(
            f"Test {algo_name} échoué : {e}\nScreenshot capturé : {screenshot_path}"
        )