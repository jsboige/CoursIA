<template>
  <div class="slidev-layout two-cols">
    <div class="col-left">
      <slot />
    </div>
    <div class="col-right">
      <slot name="right" />
    </div>
  </div>
</template>

<style scoped>
.two-cols {
  display: flex;
  gap: 30px;
}

.col-left {
  flex: 1.2;
  flex-shrink: 0;
}

.col-right {
  flex: 1;
  flex-shrink: 0;
}
</style>
