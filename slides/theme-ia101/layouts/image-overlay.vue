<script setup lang="ts">
const props = defineProps<{
  image?: string
  imageClass?: string
}>()
</script>

<template>
  <div class="slidev-layout image-overlay">
    <div :class="['overlay-content', { 'has-image': !!image }]">
      <slot />
    </div>
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

.overlay-content {
  width: 100%;
  position: relative;
  z-index: 2;
}

.overlay-img {
  position: absolute;
  top: 50%;
  right: 30px;
  transform: translateY(-50%);
  max-width: 35%;
  max-height: 70%;
  object-fit: contain;
  z-index: 1;
  opacity: 0.15;
}

/* Utility classes for positioning */
.overlay-img.top-right {
  top: 40px;
  transform: none;
}

.overlay-img.mid-right {
  top: 50%;
  right: 30px;
  transform: translateY(-50%);
}

.overlay-img.bottom-right {
  bottom: 40px;
  top: auto;
  right: 30px;
  transform: none;
}

.overlay-img.small {
  max-width: 25%;
  max-height: 50%;
}

.overlay-img.large {
  max-width: 45%;
  max-height: 80%;
}

/* Higher opacity variant for images that need more visibility */
.overlay-img.visible {
  opacity: 0.3;
}
</style>
