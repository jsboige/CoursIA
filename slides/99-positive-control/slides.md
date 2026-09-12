---
theme: default
title: [unclosed-15835
---

# Positive control #15835

Ce deck n'existe que pour prouver que le gate de build **rougit**.

Il porte deux defauts fatals INDEPENDANTS, pour que le controle positif ne
depende pas d'un seul chemin d'echec :

1. un frontmatter YAML invalide (`title: [unclosed-15835`) ;
2. une erreur de syntaxe JavaScript dans le bloc `script setup`.

La PR qui porte ce fichier doit produire un check-run **rouge** attribue a
cette PR. Elle est jetable : fermee et sa branche supprimee une fois le
verdict observe.

<script setup>
const = ;
</script>
