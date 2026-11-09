// Frontend minimal : le grain porte l'orchestration Aspire, pas la richesse du
// front. La page affiche un plateau servi par le dev-server Vite et expose un
// point d'API simul cote client (le contenu servi, pas la logique, fait la preuve).
const state = {
  app: 'FrontendLab',
  orchestrateur: 'Aspire AppHost',
  gestionnaire: 'pnpm',
  démarrages: Number(sessionStorage.getItem('visites') || 0) + 1,
};
sessionStorage.setItem('visites', String(state.démarrages));

document.querySelector('#app').innerHTML = `
  <main>
    <h1>${state.app}</h1>
    <p>Ressource frontend servie par le dev-server Vite, orchestr&eacute;e par ${state.orchestrateur} (paquets ${state.gestionnaire}).</p>
    <p>Chargements de session&nbsp;: <span id="visites">${state.démarrages}</span></p>
  </main>
`;
