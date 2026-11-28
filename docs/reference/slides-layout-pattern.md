# Slidev — motif de mise en page des decks de cours

> REFERENCE — vivante — dernière révision 2026-11-28

Cible : les decks `slides/**` portes par la campagne **#10950**. Ecrit apres qu'un diagnostic « les grilles sont impossibles dans Slidev » ait bloque trois iterations de reparation sur un deck. Le constat qui l'a produit etait vrai ; la conclusion ne l'etait pas.

## La baseline, c'est le PPTX du user

Mandat user (2026-08-20) : *« la baseline, ce sont les render de mes pptx [...] si c'est encore plus moche, alors pas la peine d'aller plus loin »*. Et sur la composition : *« La baseline pptx n'est pas bicolonne. Certains slides ont LE TEXTE en bicolonnes [...] mais les images ont toujours ete positionnees a la main. »*

D'ou les trois regles ci-dessous. Elles ne sont pas un style-guide : ce sont les contraintes qui reproduisent le rendu de reference.

## Les trois regles

1. **Layout `default`, `h1` pleine largeur.** Ne **jamais** utiliser `two-cols` pour un titre + deux colonnes de texte : le theme pose `h1 { border-bottom: 2px solid var(--color-accent) }` ([`slides/theme-ia101/styles/index.css`](../../slides/theme-ia101/styles/index.css)), donc sous `two-cols` le filet suit la colonne et **la barre de titre est coupee en deux**. C'est le defaut visuel que le user a explicitement demande de supprimer.

2. **Le texte bicolonne va dans un `<div class="grid grid-cols-2 gap-10">` au niveau du corps, sous le titre.** Pas dans un layout, pas autour du titre.

3. **Chaque image est placee a la main, en absolu** : `class="absolute top-[Npx] left-[Npx]"` (ou `right-[Npx]`). **Jamais dans le flot.** Une image en flot se centre, pousse le texte, et laisse la moitie de la slide vide — c'est exactement ce que la bicolonne avait ete introduite pour eviter, et qu'elle n'a pas evite.

## Le piege qui fait croire les grilles impossibles

Mettre une liste markdown dans un `<div class="grid">` fait rendre a Vue :

```
Element is missing end tag
```

**Cause : la regle HTML-block de markdown-it.** Un bloc HTML se ferme sur une **ligne vide**, et le parsing markdown ne reprend qu'**apres** cette ligne vide. Sans elle, la liste est avalee dans le HTML brut et le fragment devient invalide.

Le remede n'est donc pas d'abandonner la grille : c'est une ligne vide.

```markdown
<div class="grid grid-cols-2 gap-10">
<div>

**Titre de colonne**

- premiere puce
- seconde puce

</div>
<div>

**Autre colonne**

- ...

</div>
</div>
```

**Les lignes vides apres chaque `<div>` ouvrant et avant chaque `</div>` fermant ne sont pas cosmetiques — elles sont le mecanisme.** Les retirer casse le rendu.

**La regle vaut pour TOUT bloc HTML, pas seulement les grilles de colonnes.** Un wrapper d'animation `<div v-click="N">`, une classe de densite `<div class="dense-list">`, n'importe quelle ouverture seule sur sa ligne : si la ligne suivante porte une syntaxe markdown de bloc (`**gras**`, liste a tirets, heading `##`, tableau `|`, citation `>`, liste ordonnee), sans ligne vide elle est **avalee dans le HTML brut** et rend en litteral — asterisques comprises, hierarchie de liste aplatie en prose a tirets (#13216 : 49 blocs ainsi avals sur main, dont une liste a trois niveaux effondree). Le defaut est invisible aux gates de composition (le texte litteral reste dans le canvas) : il ne se voit qu'en rendu. Contrairement, la prose HTML inline apres un `<div class="text-sm...">` qui ne porte AUCUNE syntaxe markdown rend correctement sans ligne vide — ne pas sur-corriger.

Contre-exemple deja present dans le depot avant que le diagnostic « impossible » soit pose : [`slides/S3-acculturation/deck-executif.md:39-41`](../../slides/S3-acculturation/deck-executif.md#L39-L41) — un `grid grid-cols-3` qui construit, et qui porte la ligne vide.

## Generalisation : tout wrapper HTML sur sa ligne ouvre un bloc

La regle precedent, portee sur le diagnostic « les grilles sont impossibles », cache une regle plus large : **tout** tag ouvrant HTML seul sur sa ligne ouvre un bloc HTML, et tout markdown de bloc place sur la ligne suivante est avale. Les coupables recurrents sur les decks du depot :

- **`<div class="grid grid-cols-N ...">`** : layout en grille (cf regle 2).
- **`<div v-click="N">`** : wrapper d'animation incremental Slidev, omnipresent
  dans `slides/06-apprentissage` (~30 occurrences sur ce seul deck).
- **`<div class="dense-list">`**, `<div class="columns">`, `<div class="...">`
  utilitaires de mise en page.

**Compte rendu main, 2026-08-27 (avant fix #13216) : 49 emplacements sur 36 decks, repartis :**

| Deck | markdown avale |
|---|---|
| `slides/01-introduction/slides.md` | 1 |
| `slides/06-apprentissage/slides.md` | 39 |
| `slides/S8-semantic-web/slides.md` | 9 |

**Le defaut est invisible aux scanners de composition** : `scan_slidev_composition.py` mesure debordement de canvas, chevauchement de glyphes et occupation -- des asterisques litteraux et une liste aplatie sont du texte A L'INTERIEUR du canvas. Le detecteur dedie `scan_slides_html_block_markdown.py` (PR #13218) a ete pose pour le rendu honnete de cette grandeur.

**Regle praticienne a toute nouvelle tranche : apres avoir pose un `<div>` ouvrant seul sur sa ligne, poser systematiquement une ligne vide avant la premiere ligne markdown suivante.** La grille, le wrapper `v-click` ou la classe dense-list n'echappent pas a la regle.

## Geometrie du canvas — 980 x 552, et le facteur d'echelle

Sans `canvasWidth` / `aspectRatio` / `canvasHeight` dans le headmatter, Slidev applique son defaut : **980 x 552**. Verifier le headmatter avant d'ecrire le moindre `top-[Npx]` — un deck calcule contre une autre constante produit des positions fausses **partout**, et l'erreur se propage a chaque reparation suivante.

**`getBoundingClientRect` rend des px MIS A L'ECHELLE**, pas des px CSS. Diviser par `scaler.width / 980` avant toute comparaison a une utilitaire `top-[Npx]` / `max-h-[Npx]`. Facteur mesure sur un viewport 1280 : **1,3061**. Sans cette division on lit « 391 px » sur un element a `max-h-[300px]` et on diagnostique un debordement qui n'existe pas.

## Mesurer un deck servi — l'instrument doit nommer ce qu'il mesure

Le DOM d'un deck Slidev contient **une `.slidev-layout` par slide** (82 sur le deck S3-acculturation), et **une seule est visible** : toutes les autres ont une bounding box de taille **0**. Un `document.querySelector('.slidev-layout')` attrape la premiere, donc une cachee, donc `width = 0` — et tout calcul divise par ce zero rend `null` **sans erreur**.

Selectionner la visible par aire maximale, et **faire rendre a l'instrument l'identite de ce qu'il vient de mesurer** (le `h1` de la slide) a cote de la valeur. C'est ce qui distingue « mesure d'une slide vide » de « mesure de la bonne slide ».

## Ce qu'une mesure de debordement ne dit pas

Un controle `bottom > canvasHeight` est necessaire et **tres insuffisant** : il **certifie implicitement tout ce qu'il ne teste pas**. Une slide dont la moitie droite est vide, dont les images sont centrees dans le flot et dont une note orpheline chevauche le pied de page peut passer ce controle sans broncher.

**Directive user (2026-08-20) : sur une composition, le plancher mecanisable n'est jamais le critere d'acceptation.** Un `slidev build` EXIT=0 prouve que le deck *construit*, rien de son rendu. L'acceptation reste un jugement visuel, porte par une lane qui **voit** (cf [`cluster-agents.md` §Capacite vision](cluster-agents.md)). Une estimation arithmetique de hauteur de contenu ne remplace pas non plus le regard : mesuree une fois a **224 px** d'ecart avec le rendu reel.

## Rendre la mesure reproductible — `--pin-fonts`

Les compteurs du scanner dérivent des largeurs de glyphes et des hauteurs de ligne, donc des polices **système** de la machine qui rend le deck. Sans pin, deux machines ne mesurent pas dans les mêmes conditions — mesuré sur [`S8-semantic-web`](../../slides/S8-semantic-web/slides.md) (30 slides, même Chromium 156.0.8078.4) :

| Sans pin | Windows 11 | conteneur ubuntu 24.04 |
|---|---|---|
| pile du thème `"Segoe UI", Calibri, Arial, sans-serif` | Segoe UI, Calibri et Arial résolues | Arial seule (`fc-match` : alias de Liberation Sans) |
| `line-height: normal` sur cette pile, à 16 px | 21 px | 18 px |
| échantillon monospace | Consolas, 373,87 px | Liberation Mono, 408,07 px |
| compteurs hors-canvas / chevauchement / éteints / recouvrement / occupation | 0 / 0 / 8 / 0 / 0 | 0 / 0 / 0 / 0 / 0 |
| `font_signature` | `d26d62ef2e341fc7` | `9f62c747e2c82100` |

Les quatre compteurs de constat tombent à zéro des deux côtés : c'est une propriété de ce deck (il ne déborde pas), pas une preuve de comparabilité. Le cinquième les départage. `n_chevauchements_eteints` compte les paires éteintes par la confirmation élément — les plages de texte de deux éléments se chevauchent d'un ou deux pixels alors que leurs boîtes sont disjointes, rien à l'écran : 8 sur Windows, 0 dans le conteneur. Sur cette machine, le rapport ne distingue plus « aucun effleurement » de « la porte de confirmation a disparu ». **Un compte n'est opposable qu'entre conditions égales.**

`scan_slidev_composition.py --pin-fonts` égalise les conditions ([`slidev_font_pin.py`](../../scripts/notebook_tools/slidev_font_pin.py)) :

- **Masquage** — 41 noms de familles (15 sans, 18 monospace, 8 serif) sont servis par des polices **livrées** (`scripts/notebook_tools/fonts/`, OFL 1.1 et licence DejaVu) sous des faces `@font-face` portant le même nom : une face déclarée sous le nom d'une famille installée gagne sur la police locale. Toute famille sans se rend avec Selawik (repli DejaVu Sans), toute monospace avec DejaVu Sans Mono, toute serif avec Gelasio (repli DejaVu Serif) — un texte déclaré en Arial ou en Verdana mesure comme Segoe UI. 144 faces ; la face principale porte le cmap exact de sa police en `unicode-range`.
- **Métriques** — `ascent-override` / `descent-override` / `line-gap-override` (et `size-adjust` pour le monospace) reproduisent la boîte de ligne de la référence Windows : Segoe UI 24/19, Cascadia Code 21/17, Georgia 21/17 à 18 px.
- **Génériques** — `sans-serif`, `monospace`, `system-ui`… ne sont masquables ni par `@font-face` ni par CDP `Page.setFontFamilies` (les deux essayés, inertes). Ils sont réparés par style inline, élément par élément, quand ils décident la police d'une pile. Slidev garde le deck entier dans `#slide-content` (`#slideshow` → un `.slidev-page` par slide, une seule affichée) : le premier passage répare tout le deck, les suivants ne rattrapent que ce que le deck a recréé.
- **Sans hinting** — le navigateur est lancé avec `--font-render-hinting=none`. Sous Linux, Chromium arrondit les avancées au pixel : une même police livrée s'écarte de Windows de −2,14 % à +8,74 % selon la taille (18 chaînes mesurées, 13 au-delà de 1 %). Avec l'argument, l'écart résiduel est de 0,06 % au plus (0,14 px), les hauteurs de ligne sont égales dans les quatre conditions, et sur Windows l'argument est sans effet (18 largeurs identiques). Les arguments entrent dans l'empreinte du pin.

### Ce que le rapport garantit

- **Vérifié avant de mesurer** — octets des polices contre un verrou sha256, feuille adoptée, 144 faces chargées. Pin inapplicable → **exit 3**, sans ouvrir de navigateur : pas de mesure « à peu près ».
- **Le document du deck n'est jamais intercepté** — la feuille entre par `adoptedStyleSheets`, posée par un script d'initialisation : elle existe avant le premier script du deck (Mermaid mesure son texte à l'insertion). Un document renvoyé par une route Playwright perd son espace d'adressage et Chromium refuse ses scripts de module (« blocked by CORS policy… more-private address space `local` ») dès que l'origine n'est pas un contexte sûr — mesuré : rc 2 sur un deck servi sur `172.24.240.1`, le même deck passant sur `localhost`. Seules les URL des polices passent par une route.
- **Ce qui a échappé est nommé** — après la mesure, CDP relit la police de chaque glyphe rendu : un glyphe servi par une police système est listé dans `font_pin.escaped` (slide, famille, nombre) et `font_pin.verified` vaut `false`. Cela ne change pas le code retour du deck.
- **Trois empreintes se comparent entre rapports** — `font_pin.signature` (feuille, octets des polices, arguments de lancement), `font_signature` (environnement d'un élément de texte et d'un bloc de code), `rendering_conditions.signature` (polices rendues par slide, navigateur, canvas). Sous pin leur égalité est opposable ; sans pin, elle ne prouve rien.

Mesuré sous pin sur ce deck, siège Windows contre conteneur ubuntu : compteurs égaux (0 / 0 / 8 / 0 / 0), trois empreintes égales (`font_pin.signature` `6d567a59d85c45f3…`, `font_signature` `2ab11e9914976424`, `rendering_conditions.signature` `2dac48aac909a1f4…`), 14 348 glyphes épinglés, aucun échappé. Huit feuilles du rapport diffèrent encore, toutes hors compteur : le générique `monospace` nu (373,87 contre 409,39 px — il reste système par construction), les largeurs de l'échantillon monospace (398,34 contre 398,20 px), et l'étendue horizontale d'un chevauchement éteint de la slide 12 (362 contre 361 px). `font_pin.repaired_by_slide` attribue chaque générique réparé à sa page ; `font_pin.escaped` liste les glyphes hors couverture des polices livrées. Deux passages du même code sur le même siège rendent le rapport à l'identique, octet pour octet (mesuré : deux passages consécutifs sur le siège Windows).

### Ce que le pin ne restitue pas

Il égalise les machines, il ne rend pas Windows : pas de crénage (Segoe UI crène 8 292 paires, Selawik aucune — un texte créné est plus large sous le pin) ; pas de face italique (le navigateur incline) ; les génériques hors de `#slide-content` (le conteneur de mesure de Mermaid est rattaché au corps) ne sont pas réparés. Une famille qu'aucune face ne masque reste système des deux côtés : c'est une liste (`SANS_NAMES` / `MONO_NAMES` / `SERIF_NAMES`) à étendre, pas une empreinte à rétrécir. Toute police ajoutée exige de refaire le verrou sha256 et `python scripts/notebook_tools/slidev_font_pin.py --rebuild-ranges` (fonttools).

L'[advisory CI](../../.github/workflows/slides-composition-advisory.yml) passe `--pin-fonts` sur ses deux invocations : un compte pris localement sans le drapeau ne se lui compare pas.

## Images en pied de colonne d'une grille convertie — contrat de compression

La migration `two-cols` -> `grid grid-cols-2` (campagne **#10950**, tranches 1-10) met certaines images illustratives **en flux dans la cellule**, sous le texte de colonne (ex. `img_070`, `img_125/126`). Le layout `default` etant **block**, `flex`/`max-height` y est inerte : la rangee de grille grandit avec son contenu et l'image de pied **sort du canvas** (mesure `scan_slidev_composition.py`, 2026-08-26 : 6 slides HORS_CANVAS, +4 a +124 px sur [S3-acculturation](../../slides/S3-acculturation/slides.md)).

**Contrat** porte par [`slides/S3-acculturation/style.css`](../../slides/S3-acculturation/style.css) (regle 6) : layout `default` = flex borné (héritage du contrat `two-cols` d'origine — « les images cedent l'espace au texte »), grille `gap-5` = `grid-template-rows: 1fr`, cellule = flex vertical `min-height:0` → toute `<img>`. `flex: 0 1 auto` compressible. **Ne pas retirer ce bloc pour ajuster une slide** : reparer la slide, pas la contrainte. Sur un deck qui n'a pas ce bloc, une `<img>` nue en pied de cellule sans `.img-grid*` ni `absolute` est un debordement en attente.

## Fond du theme

`.slidev-layout` porte `background-color` ; sans hauteur, la boite est dimensionnee par son contenu et **toute slide courte laisse une bande blanche** en bas du canvas (mesure : pale s'arretant a 436 px et 393 px sur deux slides d'un canvas de 552). Corrige par `min-height: 100%` + `box-sizing: border-box` — le padding `28px 40px` etant deja sur cette boite. C'est **du theme**, donc tous les decks du theme en heritent : ne pas le recorriger deck par deck.

## Voir aussi

- **#10950** — campagne de refonte des decks
- **#24171** — mesure de débordement reproductible d'une machine à l'autre : `--pin-fonts` (section « Rendre la mesure reproductible », ci-dessus)
- [`cluster-agents.md`](cluster-agents.md) — routage du QA visuel vers une lane qui voit
- [`slide-analyzer-sk-agent.md`](slide-analyzer-sk-agent.md) — analyse de deck par vision

## Composer à partir des relations texte-image

La position absolue est un moyen technique, pas une méthode de composition. Une image peut rester lisible tout en étant placée sans rapport avec le propos. Une bande basse uniforme reproduit ce défaut aussi sûrement qu'une colonne droite systématique.

### Lire l'intention avant les coordonnées

1. Ouvrir le rendu PNG du PPTX et identifier chaque image par son contenu réel. Ne pas déduire son identité du numéro du fichier ou d'un logo supposé.
2. Associer chaque figure au paragraphe qui l'introduit : concept illustré, fonction explicative, étape de la démonstration. Une image décorative et un schéma d'architecture ne demandent pas la même surface.
3. Relever la relation spatiale : face au paragraphe, sous une introduction, entre deux blocs, ou étage d'une séquence. Les coordonnées estimées depuis un PNG ne sont pas des métadonnées PPTX exactes.
4. Recomposer cette relation après découpage ou enrichissement du texte. Conserver l'intention du PPTX, pas ses coordonnées au pixel près dans un contenu devenu différent.

### Réserver l'espace correspondant au propos

Le titre reste pleine largeur. Pour une slide illustrée, utiliser le layout `image-overlay` et des classes locales au deck. Le texte demeure au-dessus des overlays. Adapter la largeur des paragraphes concernés et leur hauteur réservée, puis centrer la figure dans l'espace qui leur répond. Les paragraphes suivants peuvent retrouver la pleine largeur.

Exemples de décisions, à adapter plutôt qu'à recopier :

- Tokenizer et embeddings : deux figures étagées face aux deux explications respectives.
- Réseau et attention : respecter les rapports portrait/paysage, sans imposer une taille identique aux rectangles réellement peints.
- Architecture Transformer : une grande figure verticale face aux étapes, plutôt qu'une miniature en pied de slide.
- Usages sectoriels : chaque illustration à hauteur du secteur qu'elle représente.
- Écosystème : séparer les catégories trop chargées avant de distribuer les logos.

`object-fit: contain` conserve les proportions. La boîte de l'élément `img` n'est pas nécessairement le rectangle de l'image peinte : examiner les deux avant de conclure à une collision ou à un espace perdu. Vérifier aussi le contenant de positionnement des overlays ; une règle `position: relative` héritée peut déplacer leur origine. Corriger localement, sans modifier le thème partagé pour un seul deck.

### Faire coïncider apparition et explication

Attribuer un indice de clic explicite au paragraphe et à sa figure. Avec `<v-clicks at="1">`, garder une liste comme seul contenu direct du wrapper quand on veut une progression par élément. Une référence placée après la liste reçoit son propre clic. Une image explicative permanente en frontmatter ne respecte pas cette synchronisation.

Lorsqu'un paragraphe est ajouté ou déplacé, revérifier les indices des figures et références. Pour une hiérarchie enrichie, distinguer le concept, son mécanisme, puis un exemple ou une limite. Le troisième niveau n'est pas une obligation sur chaque puce : scinder la slide si le rendu devient trop dense. Vérifier l'ordre réel des apparitions plutôt que supposer la sémantique d'une liste imbriquée.

### Contrôler le rendu, pas seulement le code

- Produire d'abord quelques échantillons contrastés, puis déléguer des lots bornés avec vision et chemins précis. Conserver la décision d'intégration au principal.
- Comparer le PPTX et Slidev pour les associations et le placement. Lire chaque slide modifiée au dernier clic, puis vérifier les états intermédiaires pour la synchronisation.
- Naviguer par URL `/<slide>?clicks=<indice>`, attendre le titre de la bonne slide, les polices, les images et l'opacité finale. Ne pas assigner un état de navigation readonly.
- Mesurer les rectangles dans les coordonnées normalisées du canvas. Contrôler débordement, intersection avec les glyphes et séparation des paragraphes suivants.
- Utiliser le scanner de composition comme plancher advisory. Son occupation compare les images au canvas entier : une zone sans image peut contenir le texte. Un avertissement doit être qualifié, pas supprimé en étirant une image jusqu'à satisfaire un seuil.
- Confronter les conclusions des agents au rendu et aux mesures. Un compte, un titre de capture ou une interprétation de logo peut être erroné même dans une revue apparemment précise.

L'export est un contrôle distinct. Un exit code nul et un fichier PDF présent ne prouvent pas que toutes les slides ont été imprimées. Vérifier le nombre de pages et leur contenu. En cas de timeout tardif, l'export natif `--per-slide --range` permet des plages bornées, ensuite assemblées sans réinterpréter le contenu. La vérification structurelle du PDF ne remplace pas son contrôle visuel.

### Actualiser sans remplacer le cours par un catalogue

Lire les cellules sources des notebooks, pas seulement leurs titres ou dates de modification. Extraire un mécanisme, une expérience et sa limite ; citer le notebook dans la slide correspondante. Pour une affirmation de fraîcheur, compléter avec une source primaire datée du modèle ou de la technique. Distinguer un exemple historique toujours pédagogique d'une prétention à représenter l'état actuel. Un nouveau schéma doit expliquer une relation absente, pas seulement ajouter de la décoration.
