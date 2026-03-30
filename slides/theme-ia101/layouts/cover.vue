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
  background: linear-gradient(135deg, #F5F5F5 0%, #E8E8E8 100%);
}

.cover h1 {
  font-size: 2.2em;
  border-bottom: none;
  margin-bottom: 24px;
  color: var(--color-accent);
}
</style>
