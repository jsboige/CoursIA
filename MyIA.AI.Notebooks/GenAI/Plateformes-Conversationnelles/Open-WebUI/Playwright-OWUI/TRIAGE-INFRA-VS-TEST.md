# Triage — un test rouge n'est pas toujours un bug

[← Retour Playwright-OWUI](./README.md)

> **Pour qui ?** Étudiants du parcours QA-OWUI, à partir du module 03. Ce guide
> répond à la question que se pose tout QA Engineer devant une suite qui rougit :
> **« est-ce l'application, mon test, ou la machine ? »**
>
> Les trois cas d'étude ci-dessous sont des incidents **réels** survenus sur la
> flotte multi-tenant qui sert de terrain à cette série. Aucun n'est inventé pour
> l'exercice — c'est justement ce qui les rend instructifs.

## Le réflexe à acquérir

Un test qui échoue vous dit **qu'une attente n'a pas été satisfaite**. Il ne vous
dit pas *pourquoi*. Trois causes très différentes produisent exactement le même
rouge dans le rapport :

| Cause | Ce qui a changé | Qui doit corriger |
|-------|-----------------|-------------------|
| **Régression applicative** | Le code de l'app | L'équipe de dev |
| **Dérive de test** | L'UI a bougé, le test non (sélecteur obsolète) | Vous, le QA |
| **Panne d'infrastructure** | Ni l'app ni le test : la machine, le réseau, un service | L'équipe ops |

Confondre les trois coûte cher : on « corrige » un sélecteur qui n'avait rien,
on ouvre un bug chez les devs pour une panne réseau, ou — le pire — on
désactive un test qui avait raison.

**Règle : on ne conclut pas sans avoir mesuré la couche du dessous.**

---

## Cas d'étude 1 — « Le site est mort » alors que l'application va bien

**Symptôme.** Le site public renvoie `502 Bad Gateway`. Six instances sur sept
sont injoignables. Toute la suite E2E échoue dès l'authentification.

**Le réflexe naïf.** « L'application est plantée, il faut la redémarrer / prévenir
les devs. »

**Ce que dit la mesure.** En interrogeant chaque couche séparément :

```
/health DANS le conteneur ......... 200   ← l'application va parfaitement bien
port de l'hôte (localhost:3010) ... 000   ← rien n'écoute côté hôte
URL publique (via reverse proxy) .. 502   ← le proxy ne trouve personne
```

**Diagnostic.** L'application était saine du début à la fin. C'est la
**redirection de port** entre l'hôte et le conteneur qui était morte (bug connu
de Docker Desktop sous Windows). Le `502` du proxy n'était que l'écho de ce trou.

**Leçon transposable.** Une requête traverse une pile :

```
test → DNS → reverse proxy → port de l'hôte → conteneur → application → base
```

Un échec vous donne le résultat **de bout en bout**. Pour localiser la panne,
interrogez les couches **une par une, en partant du bas**. Le premier maillon
vert en partant de l'application désigne le coupable juste au-dessus.

---

## Cas d'étude 2 — 22 tests rouges, et pourtant aucun bug

**Symptôme.** Une exécution de la suite rend **22 échecs / 19 succès**. Les
messages accusent tous un sélecteur : le bouton du sélecteur de modèles serait
introuvable.

**Le réflexe naïf.** « L'UI a changé, le sélecteur est obsolète, je le corrige. »

**Ce que dit la preuve.** Playwright joint à chaque échec un instantané du DOM
(`error-context.md`). En l'ouvrant, on y lit :

```
button "Modèle sélectionné : Samantha" [ref=e131]
```

Le bouton que le test « ne trouve pas » **est présent dans la capture prise au
moment de l'échec**. Un sélecteur cassé ne se comporte pas ainsi : il produit un
DOM où l'élément est *absent* ou *différent*.

**Diagnostic.** La suite avait été lancée pendant qu'un téléchargement de 17 Go
saturait le réseau et le disque de la même machine. Les pages mettaient plus
longtemps à devenir interactives que le délai d'attente des tests. Les échecs
étaient des **expirations de délai**, pas des erreurs d'assertion.

**Leçon transposable.** Apprenez à lire la **nature** de l'erreur :

| Indice | Interprétation probable |
|--------|-------------------------|
| `TimeoutError` + élément présent dans la capture | Environnement lent, pas dérive |
| `TimeoutError` + élément absent de la capture | Vraie dérive de sélecteur, ou page non chargée |
| Erreur d'**assertion** (`expect(...)` reçoit une autre valeur) | Régression applicative probable |
| Échecs **massifs et simultanés** sur des tests sans rapport | Cause commune → suspectez l'infra |
| Un seul test rouge, ciblé, reproductible | Suspectez le code ou le test |

Le dernier critère est le plus discriminant : **une cause commune produit des
symptômes communs**. Quand vingt tests indépendants tombent ensemble, ce n'est
presque jamais vingt bugs.

> ⚠️ **L'erreur que ce cas illustre vraiment** : la suite avait été lancée
> *sciemment* pendant une opération lourde sur la même machine. Un résultat de
> test obtenu dans des conditions non maîtrisées n'est pas un résultat — c'est
> du bruit. Il fallait relancer au calme avant toute conclusion.

---

## Cas d'étude 3 — Mesurer avant d'accuser

**Symptôme.** Des téléchargements qui « se bloquent » sans jamais échouer :
aucune erreur, aucun octet, pas de fin.

**Ce que dit la mesure.** Trois commandes suffisent à trancher :

```bash
# Débit réel vers un CDN rapide
curl -o /dev/null -w 'debit=%{speed_download}o/s\n' --max-time 60 \
  "https://speed.cloudflare.com/__down?bytes=25000000"

# Latence
ping 1.1.1.1
```

Relevé effectué pendant l'incident : **~140 Ko/s** de débit et une latence
moyenne de **671 ms** (contre quelques millisecondes attendues). À ce régime,
n'importe quelle attente de 30 secondes expire, et un transfert d'un gigaoctet
demande des heures.

**Diagnostic.** Rien n'était « bloqué » : tout était simplement **trop lent d'un
facteur cent**. Un blocage et une lenteur extrême se ressemblent beaucoup vus
d'en haut — seule la mesure les distingue.

**Leçon transposable.** Avant d'écrire « c'est bloqué » dans un rapport de bug,
produisez un **chiffre**. « Le pull ne fonctionne pas » n'est pas exploitable ;
« 0 octet reçu en 240 s alors que le lien plafonne à 140 Ko/s » l'est.

---

## Mettre le triage dans le code

Le meilleur triage est celui que la suite fait **toute seule**. Plutôt que de
laisser vingt tests rougir parce qu'un service est absent, vérifiez l'infra une
fois et signalez-le clairement.

```typescript
import { test, expect, request } from '@playwright/test';

// Sonde d'infrastructure : si la plateforme ne repond pas, on ne fait pas
// rougir la suite — on l'ignore avec un motif explicite. Un test rouge doit
// vouloir dire "l'application a un probleme", jamais "la machine est absente".
test.beforeAll(async ({ baseURL }) => {
  const ctx = await request.newContext();
  let healthy = false;
  try {
    const res = await ctx.get(`${baseURL}/health`, { timeout: 10_000 });
    healthy = res.ok();
  } catch {
    healthy = false;            // DNS, refus de connexion, expiration...
  } finally {
    await ctx.dispose();
  }
  test.skip(!healthy, `Instance injoignable sur ${baseURL} — panne d'infrastructure, pas un echec de test`);
});
```

Deux principes valables bien au-delà de Playwright :

1. **Distinguer « en échec » de « non exécutable ».** Un test ignoré avec un
   motif lisible informe ; un test rouge sans cause informe mal.
2. **Ne jamais masquer un vrai échec.** Cette sonde ne doit couvrir que
   l'indisponibilité *de la plateforme*, jamais une fonctionnalité qu'on teste.
   Sinon on transforme un bug en silence — l'inverse du but recherché.

Le module 03 applique déjà cette idée aux modèles indisponibles (« skip
gracieux ») et le module 06 à la détection de fonctionnalité. Ce guide en donne
la règle générale.

## Checklist de triage

Avant de conclure quoi que ce soit sur une suite rouge :

- [ ] Les échecs sont-ils **massifs et simultanés** ? (→ cause commune)
- [ ] L'erreur est-elle une **expiration** ou une **assertion** ?
- [ ] L'élément « introuvable » figure-t-il dans la **capture jointe** ?
- [ ] La machine était-elle **occupée** pendant l'exécution ?
- [ ] Le débit et la latence ont-ils été **mesurés**, pas supposés ?
- [ ] La pile a-t-elle été interrogée **couche par couche** ?
- [ ] Une **relance au calme** reproduit-elle le résultat ?

Tant que la dernière case n'est pas cochée, vous n'avez pas de verdict : vous
avez une hypothèse.

---

*Guide transversal — cas d'étude issus d'incidents réels de la flotte multi-tenant, août 2026.*
