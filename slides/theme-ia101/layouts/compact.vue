<script setup lang="ts">
import { default as ia101Styles } from '../styles/index.css'
</script>

<template>
  <div class="slidev-layout compact">
    <slot />
  </div>
</template>

<style scoped>
.compact {
  @apply px-8 py-6;
}
</style>
