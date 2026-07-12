<template>
  <div class="slidev-layout image-grid">
    <slot />
  </div>
</template>

<style scoped>
.image-grid {
  display: flex;
  flex-direction: column;
}

.image-grid :deep(.image-grid) {
  display: grid;
  grid-template-columns: repeat(auto-fill, minmax(85px, 1fr));
  gap: 8px;
  margin-top: 12px;
  justify-items: center;
}

.image-grid :deep(.image-grid img) {
  max-height: 50px;
  max-width: 85px;
  object-fit: contain;
}
</style>
