<script setup lang="ts">
import { default as ia101Styles } from '../styles/index.css'
</script>

<template>
  <div class="slidev-layout default">
    <slot />
  </div>
</template>

<style scoped>
.default {
  @apply px-12 py-8;
}
</style>
