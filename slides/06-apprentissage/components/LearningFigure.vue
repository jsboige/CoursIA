<script setup lang="ts">
const { file, alt } = defineProps<{ file: string; alt: string }>()

// Vite résout ces URL aussi dans l’export statique du support.
const figures = import.meta.glob('../images/*.{png,jpg}', {
  eager: true,
  import: 'default',
  query: '?url',
}) as Record<string, string>
</script>

<template>
  <img :src="figures[`../images/${file}`]" :alt="alt">
</template>
