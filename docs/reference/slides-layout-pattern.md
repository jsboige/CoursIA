# Slidev — motif de mise en page des decks de cours

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

Contre-exemple deja present dans le depot avant que le diagnostic « impossible » soit pose : [`slides/S3-acculturation/deck-executif.md:39-41`](../../slides/S3-acculturation/deck-executif.md#L39-L41) — un `grid grid-cols-3` qui construit, et qui porte la ligne vide.

## Geometrie du canvas — 980 x 552, et le facteur d'echelle

Sans `canvasWidth` / `aspectRatio` / `canvasHeight` dans le headmatter, Slidev applique son defaut : **980 x 552**. Verifier le headmatter avant d'ecrire le moindre `top-[Npx]` — un deck calcule contre une autre constante produit des positions fausses **partout**, et l'erreur se propage a chaque reparation suivante.

**`getBoundingClientRect` rend des px MIS A L'ECHELLE**, pas des px CSS. Diviser par `scaler.width / 980` avant toute comparaison a une utilitaire `top-[Npx]` / `max-h-[Npx]`. Facteur mesure sur un viewport 1280 : **1,3061**. Sans cette division on lit « 391 px » sur un element a `max-h-[300px]` et on diagnostique un debordement qui n'existe pas.

## Mesurer un deck servi — l'instrument doit nommer ce qu'il mesure

Le DOM d'un deck Slidev contient **une `.slidev-layout` par slide** (82 sur le deck S3-acculturation), et **une seule est visible** : toutes les autres ont une bounding box de taille **0**. Un `document.querySelector('.slidev-layout')` attrape la premiere, donc une cachee, donc `width = 0` — et tout calcul divise par ce zero rend `null` **sans erreur**.

Selectionner la visible par aire maximale, et **faire rendre a l'instrument l'identite de ce qu'il vient de mesurer** (le `h1` de la slide) a cote de la valeur. C'est ce qui distingue « mesure d'une slide vide » de « mesure de la bonne slide ».

## Ce qu'une mesure de debordement ne dit pas

Un controle `bottom > canvasHeight` est necessaire et **tres insuffisant** : il **certifie implicitement tout ce qu'il ne teste pas**. Une slide dont la moitie droite est vide, dont les images sont centrees dans le flot et dont une note orpheline chevauche le pied de page peut passer ce controle sans broncher.

**Directive user (2026-08-20) : sur une composition, le plancher mecanisable n'est jamais le critere d'acceptation.** Un `slidev build` EXIT=0 prouve que le deck *construit*, rien de son rendu. L'acceptation reste un jugement visuel, porte par une lane qui **voit** (cf [`cluster-agents.md` §Capacite vision](cluster-agents.md)). Une estimation arithmetique de hauteur de contenu ne remplace pas non plus le regard : mesuree une fois a **224 px** d'ecart avec le rendu reel.

## Images en pied de colonne d'une grille convertie — contrat de compression

La migration `two-cols` -> `grid grid-cols-2` (campagne **#10950**, tranches 1-10) met certaines images illustratives **en flux dans la cellule**, sous le texte de colonne (ex. `img_070`, `img_125/126`). Le layout `default` etant **block**, `flex`/`max-height` y est inerte : la rangee de grille grandit avec son contenu et l'image de pied **sort du canvas** (mesure `scan_slidev_composition.py`, 2026-08-26 : 6 slides HORS_CANVAS, +4 a +124 px sur [S3-acculturation](../../slides/S3-acculturation/slides.md)).

**Contrat** porte par [`slides/S3-acculturation/style.css`](../../slides/S3-acculturation/style.css) (regle 6) : layout `default` = flex borné (héritage du contrat `two-cols` d'origine — « les images cedent l'espace au texte »), grille `gap-5` = `grid-template-rows: 1fr`, cellule = flex vertical `min-height:0` → toute `<img>`. `flex: 0 1 auto` compressible. **Ne pas retirer ce bloc pour ajuster une slide** : reparer la slide, pas la contrainte. Sur un deck qui n'a pas ce bloc, une `<img>` nue en pied de cellule sans `.img-grid*` ni `absolute` est un debordement en attente.

## Fond du theme

`.slidev-layout` porte `background-color` ; sans hauteur, la boite est dimensionnee par son contenu et **toute slide courte laisse une bande blanche** en bas du canvas (mesure : pale s'arretant a 436 px et 393 px sur deux slides d'un canvas de 552). Corrige par `min-height: 100%` + `box-sizing: border-box` — le padding `28px 40px` etant deja sur cette boite. C'est **du theme**, donc les 19 decks en heritent : ne pas le recorriger deck par deck.

## Voir aussi

- **#10950** — campagne de refonte des decks
- [`cluster-agents.md`](cluster-agents.md) — routage du QA visuel vers une lane qui voit
- [`slide-analyzer-sk-agent.md`](slide-analyzer-sk-agent.md) — analyse de deck par vision
