<script setup lang="ts">
const props = defineProps<{
  image?: string
  imageClass?: string
}>()
</script>

<template>
  <div class="slidev-layout image-overlay">
    <slot />
    <img
      v-if="image"
      :src="image"
      :class="['overlay-img', imageClass]"
      alt=""
    />
  </div>
</template>

<style scoped>
.image-overlay {
  position: relative;
}

.overlay-img {
  position: absolute;
  top: 40px;
  right: 60px;
  max-width: 30%;
  max-height: 40%;
  object-fit: contain;
  z-index: 1;
}

/* Utility classes for positioning */
.overlay-img.top-right {
  top: 40px;
  right: 60px;
}

.overlay-img.mid-right {
  top: 50%;
  right: 60px;
  transform: translateY(-50%);
}

.overlay-img.bottom-right {
  bottom: 60px;
  top: auto;
  right: 60px;
}

.overlay-img.small {
  max-width: 20%;
  max-height: 30%;
}

.overlay-img.large {
  max-width: 40%;
  max-height: 50%;
}
</style>
