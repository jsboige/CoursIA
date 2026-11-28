<script setup lang="ts">
const props = defineProps<{ file: string; alt: string }>()

// Les URL d’images doivent être résolues par Vite, aussi dans le build statique.
const figures = import.meta.glob('../images/*.png', {
  eager: true,
  import: 'default',
  query: '?url',
}) as Record<string, string>
</script>

<template>
  <img :src="figures[`../images/${props.file}`]" :alt="props.alt">
</template>
