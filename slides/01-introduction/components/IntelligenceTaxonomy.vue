<template>
  <div class="taxonomy-grid">
    <div v-for="(row, i) in rows" :key="i" class="t-row">
      <div class="t-label">{{ row.label }}</div>
      <div class="t-items">
        <span
          v-for="item in row.items"
          :key="item"
          class="t-pill"
          :class="{ highlight: i === 0 }"
        >{{ item }}</span>
      </div>
    </div>
  </div>
</template>

<script setup>
defineProps({
  rows: {
    type: Array,
    required: true
  }
})
</script>

<style scoped>
.taxonomy-grid {
  display: flex;
  flex-direction: column;
  gap: 5px;
  padding: 10px 14px;
  background: #F2E8E3;
  border-radius: 12px;
  font-size: 0.70em;
  margin-top: 6px;
}

.t-row {
  display: flex;
  align-items: center;
  gap: 14px;
  background: #EDD8D0;
  border-radius: 8px;
  padding: 5px 12px;
  min-height: 38px;
}

.t-label {
  font-size: 1.25em;
  font-weight: 600;
  color: #4a5568;
  min-width: 130px;
  font-family: Georgia, serif;
  flex-shrink: 0;
}

.t-items {
  display: flex;
  flex-wrap: wrap;
  gap: 5px;
}

.t-pill {
  background: #C17B5F;
  color: white;
  padding: 3px 9px;
  border-radius: 6px;
  font-size: 0.88em;
  white-space: nowrap;
  border: 1.5px dashed #9B5B3F;
}

.t-pill.highlight {
  background: #8B3A1A;
  border: 1.5px solid #8B3A1A;
  font-weight: 600;
  font-size: 0.95em;
}
</style>
