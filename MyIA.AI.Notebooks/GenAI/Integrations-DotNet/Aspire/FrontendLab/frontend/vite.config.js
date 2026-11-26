import { defineConfig } from 'vite';

// Port strict 5173 : l'AppHost declare un endpoint fixe, le dev-server doit
// ecouter exactement la ou Aspire l'attend (strictPort evite le glissement
// 5173 -> 5174 qui laisserait la sonde HTTP sur un port mort).
export default defineConfig({
  server: {
    host: '127.0.0.1',
    port: 5173,
    strictPort: true,
  },
});
