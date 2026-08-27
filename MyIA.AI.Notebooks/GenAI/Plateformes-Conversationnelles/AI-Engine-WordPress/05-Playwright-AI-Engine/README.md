# Playwright-AI-Engine — ce que l'API ne voit pas

[← AI-Engine (WordPress)](../README.md) | [Tour de la plateforme](../00-Tour-Plateforme/README.md) | [QA Playwright-OWUI](../../Open-WebUI/Playwright-OWUI/README.md)

Pendant « assurance qualité » du dossier AI-Engine, symétrique de
[`Playwright-OWUI/`](../../Open-WebUI/Playwright-OWUI/README.md) côté
Open WebUI.

---

## Pourquoi ce dossier ?

La série « AI Engine par son API » mesure le plugin par ses interfaces
machine : l'API REST `mwai/v1` en administrateur, `mwai-ui/v1` en
visiteur, le serveur MCP en agent. Six notebooks, six faces — et un
angle mort commun : **aucun d'eux ne charge l'application React de
l'administration**.

Or cette application n'est pas un afficheur passif. Elle écrit. Sur
cette instance, une valeur posée par l'API REST peut être défaite par le
seul fait qu'un humain ouvre une page de réglages, sans cliquer sur quoi
que ce soit — et le résultat n'est pas stable d'une fois sur l'autre.

C'est la matière de ce dossier : les constats qui exigent un vrai
navigateur, et les pièges de méthode qui vont avec.

---

## Structure

```
05-Playwright-AI-Engine/
├── README.md                        # ce fichier
└── 00-Parcours-QA-AI-Engine.ipynb   # parcours fondateur, exécuté sur l'instance jetable
```

Le dossier s'ouvre avec un seul parcours. Le pendant Open WebUI en
compte six, organisés par thème ; l'équivalent se construira ici au fil
des constats, pas par symétrie d'arborescence.

---

## Le parcours — ce qu'il mesure

[`00-Parcours-QA-AI-Engine.ipynb`](00-Parcours-QA-AI-Engine.ipynb) suit
un escalier de quatre paliers sur un indicateur témoin,
`module_workspace` :

| Palier | Ce qu'on fait | Ce qu'on observe |
|--------|---------------|------------------|
| 0 | Lire l'état par l'API | Le serveur répond, sans ambiguïté |
| 1 | Écrire `True` par l'API | `200`, relecture concordante — un test REST s'arrête ici, au vert |
| 2 | Ouvrir une page de réglages, ne toucher à rien | La page émet **deux** `POST settings/update` : `True`, puis `False` |
| 3 | Relire | L'une des deux a gagné — et pas toujours la même |

Les trois constats du parcours :

1. **Le verrou est côté client.** Le serveur accepte ces modules ; c'est
   l'application d'administration qui rabat une liste d'indicateurs à
   `False` au montage et la renvoie. Le parcours reconstitue cette liste
   sans lire une ligne de code source, uniquement d'après ce qui passe
   sur le réseau.
2. **Aucune sonde d'API ne pouvait le voir.** Le désaccord n'existe qu'à
   l'instant où un navigateur charge la page. Une suite de tests REST
   reste verte pendant que la fonctionnalité est éteinte côté interface.
3. **Une sonde de navigateur ne suffit pas non plus si elle
   n'échantillonne qu'une fois.** Les deux écritures partent à quelques
   dizaines de millisecondes d'intervalle et se croisent côté serveur :
   c'est un *lost update*, et son issue varie. À l'exécution commitée,
   l'écriture de l'API survit 3 fois sur 5. Observer une fois ne rapporte
   pas l'état du système, cela rapporte un tirage.

La conclusion pratique est un déplacement du critère : la contre-mesure
n'est pas une meilleure assertion sur un tour, c'est un **taux**.
Répéter, compter, publier la proportion. Un test qui rend « 3 fois sur
5 » dit quelque chose de vrai ; un test qui rend « OK » ne dit rien tant
qu'on ignore combien de fois il a regardé.

Le parcours se termine sur une observation qu'on n'attendait pas : le
script d'installation de l'instance déclare six modules actifs, dont
quatre figurent dans la liste que l'interface rabat. **L'état documenté
de l'instance n'est donc pas un état stable** — il suffit d'aller
consulter les réglages pour qu'il commence à s'en écarter.

---

## Exécuter le parcours

**Prérequis**

1. l'instance jetable « Maison Valmont » démarrée — voir
   [`../instance-jetable/README.md`](../instance-jetable/README.md) ;
2. `../instance-jetable/.env` renseigné (jamais commité) ;
3. `pip install requests python-dotenv playwright` puis
   `playwright install chromium`.

```bash
cd 05-Playwright-AI-Engine
python -m nbconvert --execute --to notebook --inplace 00-Parcours-QA-AI-Engine.ipynb
```

Le parcours pilote un vrai processus navigateur. Dans un noyau Jupyter,
qui tourne déjà dans une boucle asyncio, ce pilotage est confié à un fil
dédié : le helper `en_arriere_plan()` de la cellule de configuration s'en
charge, et rend la politique de boucle d'origine en sortant.

**Ce que le parcours modifie, et rend.** Il bascule des indicateurs
`module_*`. La dernière cellule les remet à l'état que
`../instance-jetable/seed-valmont.php` déclare, et le vérifie par l'API.
Aucun contenu, aucun utilisateur, aucun chatbot n'est touché.

---

## Périmètre publiable

Ce dépôt est public. Le parcours respecte les mêmes règles que le reste
du dossier :

- **cible unique** : l'instance jetable locale, corpus 100 % synthétique
  (« Maison Valmont »). Jamais une instance réelle, jamais de données
  réelles ;
- **aucune valeur sensible dans les fichiers commités** : URL,
  identifiants et clés viennent de `../instance-jetable/.env`, qui est
  gitignoré. Seul `../instance-jetable/.env.example` documente les
  variables attendues ;
- **sorties committées telles qu'exécutées** : elles ne contiennent que
  des noms d'indicateurs, des dates en millisecondes et des booléens.
  Aucune n'est retouchée à la main.

Vérification rapide avant toute contribution à ce dossier :

```bash
# le .env ne doit jamais entrer dans l'index
git check-ignore -v ../instance-jetable/.env

# aucune valeur sensible dans le notebook
grep -nE "Bearer |password|localhost:80(8|9)[0-9]" 00-Parcours-QA-AI-Engine.ipynb
```

---

## Voir aussi

- [`../00-Tour-Plateforme/README.md`](../00-Tour-Plateforme/README.md) —
  le tour guidé de l'interface, où ce comportement a été rencontré pour
  la première fois, au détour d'une capture
- [`../parler-au-chatbot-en-visiteur-par-l-api.ipynb`](../parler-au-chatbot-en-visiteur-par-l-api.ipynb)
  — dernier grain de la série « par son API », qui épuisait les faces
  atteignables sans navigateur
- [`../../Open-WebUI/Playwright-OWUI/README.md`](../../Open-WebUI/Playwright-OWUI/README.md)
  — le dossier symétrique côté Open WebUI, six modules de tests E2E
- [`verification-verte-systeme-casse.md`](../../../../../docs/reference/verification-verte-systeme-casse.md)
  — l'étude de cas sur les vérifications vertes qui ne prouvent rien ; ce
  parcours la prolonge du côté de l'échantillonnage
