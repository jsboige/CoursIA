---
theme: ../theme-ia101
title: "Contrôle positif composition (fixture CI #15545)"
---

# Fixture de contrôle positif — slide propre

Cette slide ne porte aucun défaut. Elle existe pour que le défaut
délibéré porte un numéro de slide stable : **2**.

---

# Slide baseline — défaut HORS_CANVAS déterministe

Le paragraphe ci-dessous est positionné en absolu à 600 px du haut du
canvas (552 px) : il déborde par le bas quelle que soit la fonte ou le
thème. Un scanner vivant DOIT le signaler (HORS_CANVAS, tag P).

<p style="position:absolute; top:600px; left:0; width:240px; height:40px;">élément contrôle hors canvas</p>
