<template>
  <div class="slidev-layout dense">
    <slot />
  </div>
</template>

<style scoped>
.dense {
  padding: 24px 48px !important;
}

.dense ul > li {
  margin-bottom: 4px;
}

.dense h1 {
  margin-bottom: 12px;
}
</style>
