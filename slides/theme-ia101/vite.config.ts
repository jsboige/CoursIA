import { defineConfig } from 'vite'

// Minification CSS desactivee : sans cela les 19 decks echouent au build
// (#19727). Le declencheur est le couple @slidev/cli 53 + vite 8, qui minifie
// le CSS avec lightningcss la ou vite 6 utilisait esbuild.
//
// lightningcss refuse un CSS que Slidev emet lui-meme. L'expansion de la
// directive `--uno` de node_modules/@slidev/client/styles/code.css:122 perd son
// selecteur sur un chunk et laisse des declarations nues, suivies de `.dark …` :
//
//   .katex :before { border-color: currentColor; }
//   margin-right:1.5rem;width:1rem;...;.dark .slidev-code-line-numbers …::before{…}
//
// D'ou « Invalid token in pseudo element: Dimension 1.5rem ». La source est un
// fichier de Slidev, pas le theme ni les decks : le defaut est amont, et la
// seule reparation locale qui ne depende pas d'un correctif amont est de
// desactiver la minification. Cout assume : CSS non minifie dans le site
// construit.
//
// `cssMinify: 'esbuild'` est exclu : vite 8 ne livre plus esbuild.
//
// Ce fichier vit dans le theme, et non dans slides/, parce que Slidev ne lit un
// vite.config.* que dans ses racines (theme + addons + racine du deck) -- un
// slides/vite.config.ts est ignore. Une seule config couvre donc les 19 decks,
// dont les 19 portent `theme: ../theme-ia101`.
export default defineConfig({
  build: { cssMinify: false },
})
