<script setup lang="ts">
withDefaults(defineProps<{
  placement?: 'start' | 'end' | 'below'
  size?: 'sm' | 'md' | 'lg'
}>(), {
  placement: 'end',
  size: 'md',
})
</script>

<template>
  <div class="ts" :data-placement="placement" :data-size="size">
    <div class="ts-copy"><slot /></div>
    <div class="ts-visual"><slot name="visual" /></div>
  </div>
</template>

<!--
  Doctrine de composition #15048 : le groupe pedagogique comme brique.
  Racine DOM unique en CSS Grid ; la figure reste attachee a SON groupe
  (jamais de coordonnees absolues au niveau diapo). Les tailles sont
  bornees par token (sm/md/lg) -- les valeurs px ne vivent qu'ici.
-->
<style scoped>
.ts {
  --ts-gap: 1.25rem;
  --ts-visual-w: 380px;
  display: grid;
  gap: var(--ts-gap);
  min-width: 0;
  align-content: start;
  height: 100%;
}
.ts[data-size='sm'] {
  --ts-visual-w: 280px;
}
.ts[data-size='md'] {
  --ts-visual-w: 380px;
}
.ts[data-size='lg'] {
  --ts-visual-w: 480px;
}
.ts[data-placement='end'] {
  grid-template-areas: 'copy visual';
  grid-template-columns: minmax(0, 1fr) minmax(0, var(--ts-visual-w));
}
.ts[data-placement='start'] {
  grid-template-areas: 'visual copy';
  grid-template-columns: minmax(0, var(--ts-visual-w)) minmax(0, 1fr);
}
.ts[data-placement='below'] {
  grid-template-areas: 'copy' 'visual';
  /* la rangee visuelle prend le RESTE de la hauteur du groupe (bornee),
   * pas la hauteur de l'image -- sinon une figure haute pousse le groupe
   * hors de sa zone. */
  grid-template-rows: auto minmax(0, 1fr);
}
.ts[data-placement='below'] .ts-visual {
  justify-self: center;
  width: min(100%, var(--ts-visual-w));
}
.ts-copy {
  grid-area: copy;
  min-width: 0;
}
.ts-visual {
  grid-area: visual;
  min-width: 0;
  /* #15048 : la boite visuelle est BORNEE a la hauteur de son groupe
     (stretch), l'image s'y contient -- sinon une figure plus haute que sa
     moitie de diapo deborde sur le groupe voisin (mesure pilote 08 :
     overlap [0,1] + 62px d'overflow vertical avant ce correctif). */
  min-height: 0;
  align-self: stretch;
  display: flex;
  align-items: center;
  justify-content: center;
  overflow: hidden;
}
.ts-visual :deep(img) {
  width: 100%;
  height: auto;
  max-height: 100%;
  object-fit: contain;
}
</style>
