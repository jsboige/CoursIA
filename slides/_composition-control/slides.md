---
theme: ../theme-ia101
title: "Contrôle positif composition (fixture CI #15545)"
---

# Fixture de contrôle positif — slide propre

Cette slide ne porte aucun défaut. Elle existe pour que les défauts
délibérés portent des numéros de slide stables : **2** (HORS_CANVAS)
et **3** (CHEVAUCHEMENT).

---

# Slide baseline — défaut HORS_CANVAS déterministe

Le paragraphe ci-dessous est positionné en absolu à 600 px du haut du
canvas (552 px) : il déborde par le bas quelle que soit la fonte ou le
thème. Un scanner vivant DOIT le signaler (HORS_CANVAS, tag P).

<p style="position:absolute; top:600px; left:0; width:240px; height:40px;">élément contrôle hors canvas</p>

---

# Slide contrôle — CHEVAUCHEMENT réel déterministe

Les deux paragraphes ci-dessous sont en absolu et se recouvrent de
20 px en vertical et 220 px en horizontal, bien au-delà du seuil
`> 1` : un scanner vivant DOIT les rapporter même après la passe de
confirmation par boîtes éléments (#15695) — les `getBoundingClientRect()`
des deux P se chevauchent aussi.

<p style="position:absolute; top:300px; left:0; width:260px; height:30px;">bloc contrôle chevauchement A</p>

<p style="position:absolute; top:310px; left:40px; width:260px; height:30px;">bloc contrôle chevauchement B</p>
