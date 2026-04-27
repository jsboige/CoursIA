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
  font-size: 16px !important;
  padding: 14px 36px !important;
}

.compact ul > li {
  margin-bottom: 4px;
}

.compact ul ul > li {
  margin-bottom: 2px;
}

.compact h1 {
  font-size: 1.4em;
  margin-bottom: 8px;
}
</style>
