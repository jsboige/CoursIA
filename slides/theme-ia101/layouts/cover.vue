<template>
  <div class="slidev-layout cover">
    <div class="content">
      <slot />
    </div>
  </div>
</template>

<style scoped>
.cover {
  display: flex;
  flex-direction: column;
  justify-content: center;
  align-items: center;
  text-align: center;
  height: 100%;
  background: linear-gradient(180deg, #FFFFFF 0%, #F0F0F0 45%, #DDE3E8 100%);
}

.cover :deep(h1) {
  font-size: 1.8em;
  border-bottom: none;
  margin-bottom: 16px;
  color: var(--color-accent);
  padding-bottom: 16px;
}

.cover :deep(p) {
  margin: 4px 0;
  color: var(--color-text);
  font-size: 0.95em;
}

.cover :deep(strong) {
  font-size: 1.15em;
  letter-spacing: 0.05em;
}

.cover :deep(ul) {
  text-align: center;
  margin-top: 8px;
}

.cover :deep(ul > li) {
  padding-left: 0;
  margin-bottom: 4px;
}

.cover :deep(ul > li)::before {
  content: '\2022';
  color: var(--color-teal);
  position: relative;
  margin-right: 8px;
  left: auto;
}
</style>
