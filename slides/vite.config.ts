import { defineConfig } from 'vite'

// Slidev build with esbuild CSS minify to bypass lightningcss 1.30.2 regression
// on the unocss output `color: rgb(... / var(--un-text-opacity))` pattern
// (incident 2026-10-08: lightningcss raises "Invalid token in pseudo element:
// Dimension { value: 1.5, unit: 'rem' }" and 19 decks fail).
// See PR #19798 / commit history.
export default defineConfig({
  build: {
    cssMinify: 'esbuild'
  }
})
