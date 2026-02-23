import { defineTheme } from '@slidev/cli'
import animations from '@slidev/theme-default/animations'

export default defineTheme({
  name: 'ia101',
  layouts: {
    default: () => import('./layouts/default.vue'),
    cover: () => import('./layouts/cover.vue'),
    section: () => import('./layouts/section.vue'),
    'image-right': () => import('./layouts/image-right.vue'),
    'two-cols': () => import('./layouts/two-cols.vue'),
    dense: () => import('./layouts/dense.vue'),
  },
  // Include default animations
  animations,
})
