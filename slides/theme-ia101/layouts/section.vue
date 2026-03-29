<template>
  <div class="slidev-layout section">
    <div class="content">
      <slot />
    </div>
  </div>
</template>

<style scoped>
.section {
  background: linear-gradient(135deg, #34495E 0%, #2C3E50 100%);
  color: #F5F5F5;
  display: flex;
  flex-direction: column;
  justify-content: center;
  align-items: center;
  text-align: center;
  height: 100%;
}

.section :deep(h1),
.section :deep(h2),
.section :deep(h3) {
  color: #F5F5F5;
  border-bottom: none;
}

.section :deep(h1) {
  font-size: 2em;
}
</style>
