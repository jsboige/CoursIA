"""Banc typé « décisions système 1 » partagé par la série GenAI/Texte.

Ce que ce module est
--------------------
L'organe natif du **banc typé** de la série : le contrat des questions typées
(`choice` / `noul` / `score`), les 48 tickets de support en français (12 par
classe) et leur découpage déterministe en train / calibration / test.

Pourquoi il est extrait
-----------------------
Le banc vivait en cellules inline dans `03b_Typed_Decisions_System1.ipynb`
(§1 contrat, §2 banc). Le carnet `03e-DecisionAutoregressive` (Pli 2 de #18204)
doit mesurer des modèles autoregressifs 4-9B **sur le même banc**, sans le
ré-déclarer : l'extraire ici rend le banc et le contrat **importables** par tous
les carnets de la série, au lieu d'une copie pédagogique qui dériverait.

Ce que ce module fournit
------------------------
- `CLASSES` / `TICKETS` : les 4 classes et les 48 tickets (données byte-fidèles
  à 03b §2).
- `Question` : le contrat — un état + un espace de réponses fermé ; `decide()`
  ramène un vecteur de scores à une distribution (03b §1).
- `load_bench()` : le découpage déterministe 6/3/3 par classe (train=24,
  calibration=12, test=12), sans graine aléatoire.

Provenance
----------
Extraction byte-fidèle des cellules 4 et 7 de `03b_Typed_Decisions_System1.ipynb`
(contrat `Question` + banc `TICKETS`/split). Aucune donnée n'est modifiée ; le
découpage est identique. Le scoring (Brier / ECE) n'est **pas** ici : il est
porté par `decision_local_check.py` (organe du Pli 1), que les carnets importent.
"""
from __future__ import annotations

import numpy as np

# --- Contrat (03b §1) --------------------------------------------------------

CHOICE, NOUL, SCORE = "choice", "noul", "score"


class Question:
    """Une question typée : un état soumis au modèle + un espace de réponses déclaré."""

    def __init__(self, kind: str, state: str, options: tuple[str, ...]):
        assert kind in (CHOICE, NOUL, SCORE)
        assert len(options) >= 2
        self.kind = kind
        self.state = state
        self.options = tuple(options)

    def decide(self, scores, temperature: float = 1.0) -> np.ndarray:
        """Ramène n'importe quel vecteur de scores à une distribution sur les options.

        C'est tout le contrat : quoi que produise un moteur, la réponse vit dans
        l'espace fermé des options déclarées.
        """
        s = np.asarray(scores, dtype=float)
        z = (s - s.max()) / temperature
        p = np.exp(z)
        return p / p.sum()


# --- Banc (03b §2) ----------------------------------------------------------

CLASSES = ("compte", "facturation", "livraison", "technique")  # ordre alphabetique, stable

TICKETS: dict[str, list[str]] = {
    "compte": [
        "Je n'arrive pas a me connecter a mon compte depuis ce matin",
        "Mon mot de passe est refuse alors que je suis sur de lui",
        "Comment reinitialiser l'acces a mon profil ?",
        "Mon compte a ete bloque sans explication",
        "Je veux changer l'adresse email associee a mon compte",
        "La double authentification n'envoie plus de code",
        "J'ai oublie mon identifiant de connexion",
        "Mon profil affiche les donnees d'une autre personne",
        "Je souhaite fermer mon compte definitivement",
        "Le lien d'activation recu par mail est expire",
        "Deux comptes ont ete crees avec mon adresse, je veux fusionner",
        "Ma session se deconnecte toutes les cinq minutes",
    ],
    "facturation": [
        "J'ai ete preleve deux fois pour le meme abonnement",
        "Ma facture de mars comporte une ligne inconnue",
        "Comment obtenir un remboursement du dernier paiement ?",
        "Le tarif applique ne correspond pas a l'offre souscrite",
        "Je veux un duplicata de ma facture de janvier",
        "Ma carte a ete debitee alors que j'ai annule",
        "Les frais annuels apparaissent alors que l'offre dit mensuel",
        "Puis-je changer de moyen de paiement pour les prelevements ?",
        "Le total facture ne correspond pas au panier commande",
        "Une remise promise n'apparait pas sur la facture",
        "Je conteste un montant preleve sur mon relevé",
        "Comment passer a l'offre etudiante avec le tarif reduit ?",
    ],
    "livraison": [
        "Mon colis est marque livre mais je ne l'ai pas recu",
        "La livraison prevue hier n'a pas eu lieu",
        "Comment suivre mon colis apres expedition ?",
        "Le colis est arrive endommage, que faire ?",
        "Il manque un article dans le carton recu",
        "Je veux changer l'adresse de livraison en cours de route",
        "Le transporteur affiche une adresse erronnee",
        "Ma commande est bloquee en entrepot depuis une semaine",
        "Puis-je faire livrer au point relais du quartier ?",
        "Le suivi n'a pas bouge depuis trois jours",
        "Le livreur n'a laisse aucun avis de passage",
        "Je souhaite reporter la date de creneau de livraison",
    ],
    "technique": [
        "L'application plante a l'ouverture de la page de paiement",
        "Les pages mettent une minute a charger depuis la mise a jour",
        "Le bouton de validation ne reagit pas au clic",
        "J'ai une erreur 500 sur mon espace client",
        "Les notifications push n'arrivent plus sur mon telephone",
        "L'export de mes donnees produit un fichier corrompu",
        "La recherche ne renvoie aucun resultat",
        "Les pieces jointes ne se telechargent plus",
        "Le site affiche mal le texte sur ma tablette",
        "L'application se ferme seule apres quelques secondes",
        "Impossible de televerser une photo de profil",
        "Le mode sombre ne s'applique qu'a moitie de l'interface",
    ],
}


def load_bench() -> dict[str, object]:
    """Décompose le banc en train / calibration / test (déterministe, 6/3/3 par classe).

    Retourne un dict : `X_train`/`X_cal`/`X_test` (listes de str), `y_train`/
    `y_cal`/`y_test` (listes de str = classe) et `y_train_idx`/`y_cal_idx`/
    `y_test_idx` (np.array d'ints, position dans `CLASSES`).
    """
    assert set(TICKETS) == set(CLASSES)
    assert all(len(v) == 12 for v in TICKETS.values())
    out: dict[str, object] = {}
    for k, (a, b) in (("train", (0, 6)), ("cal", (6, 9)), ("test", (9, 12))):
        xs: list[str] = []
        ys: list[str] = []
        for c in CLASSES:
            xs += TICKETS[c][a:b]
            ys += [c] * (b - a)
        out[f"X_{k}"] = xs
        out[f"y_{k}"] = ys
        out[f"y_{k}_idx"] = np.array([CLASSES.index(c) for c in ys])
    return out


if __name__ == "__main__":
    b = load_bench()
    print(f"classes={len(CLASSES)}  tickets={sum(len(v) for v in TICKETS.values())}")
    print(f"train={len(b['X_train'])}  calibration={len(b['X_cal'])}  test={len(b['X_test'])}")
    print("exemple test :", b["X_test"][0], "->", b["y_test"][0])
    q = Question(CHOICE, "Ma carte bleue a ete refusee trois fois ce matin", CLASSES)
    d = q.decide([0.05, 0.10, 0.80, 0.05])
    print("contrat OK : distribution", dict(zip(q.options, d.round(3))))
