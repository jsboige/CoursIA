<template>
  <div class="slidev-layout dense">
    <slot />
  </div>
</template>

<style scoped>
.dense {
  font-size: 18px !important;
  padding: 20px 40px !important;
}

.dense ul > li {
  margin-bottom: 2px;
}

.dense h1 {
  margin-bottom: 8px;
}
</style>
