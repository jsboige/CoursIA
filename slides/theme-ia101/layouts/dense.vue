<template>
  <div class="slidev-layout dense">
    <slot />
  </div>
</template>

<style scoped>
.dense {
  font-size: 15px !important;
  padding: 14px 36px !important;
}

.dense ul > li {
  margin-bottom: 1px;
}

.dense h1 {
  font-size: 1.4em;
  margin-bottom: 6px;
}

.dense table {
  font-size: 0.95em;
}

.dense table th,
.dense table td {
  padding: 4px 8px;
}
</style>
