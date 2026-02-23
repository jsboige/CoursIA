<script setup lang="ts">
const props = defineProps<{
  image?: string
}>()
</script>

<template>
  <div class="slidev-layout image-right">
    <div class="left">
      <slot />
    </div>
    <div class="right">
      <img v-if="image" :src="image" alt="" />
      <slot name="right" />
    </div>
  </div>
</template>

<style scoped>
.image-right {
  display: flex;
  gap: 40px;
  align-items: start;
}

.left {
  flex: 1.2;
  flex-shrink: 0;
}

.right {
  flex: 1;
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
}

.right img {
  max-width: 100%;
  max-height: 70vh;
  object-fit: contain;
}
</style>
