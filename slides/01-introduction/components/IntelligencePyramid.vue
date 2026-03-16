<script setup>
import imgProcedurale from '../images/img_022.jpg'
import imgExploratoire from '../images/img_024.jpg'
import imgProbabiliste from '../images/img_023.png'
</script>

<template>
  <div class="pyramid-container">
    <div class="layer layer-1">
      <div class="layer-header">Procedurale</div>
      <div class="layer-images">
        <img :src="imgProcedurale" alt="Procedurale" />
      </div>
      <div class="layer-items">
        <span class="item">Automates</span>
        <span class="item">Algorithmes</span>
      </div>
      <div class="layer layer-2">
        <div class="layer-header">Exploratoire</div>
        <div class="layer-images">
          <img :src="imgExploratoire" alt="Exploratoire" />
        </div>
        <div class="layer-items">
          <span class="item">Recherche de chemin</span>
          <span class="item">Escalades</span>
          <span class="item">Arbres de jeux</span>
          <span class="item">Satisfaction de contraintes</span>
        </div>
        <div class="layer layer-3">
          <div class="layer-header">Symbolique</div>
          <div class="layer-items">
            <span class="item">Raisonnement</span>
            <span class="item">Bases de connaissances</span>
            <span class="item">Solveurs</span>
            <span class="item">Planificateurs</span>
            <span class="item">Smart-contracts</span>
          </div>
          <div class="layer layer-4">
            <div class="layer-header">Probabiliste</div>
            <div class="layer-images">
              <img :src="imgProbabiliste" alt="Probabiliste" />
            </div>
            <div class="layer-items">
              <span class="item">Modeles graphiques</span>
              <span class="item">Reseaux de decision</span>
              <span class="item highlight">Politiques Markoviennes</span>
              <span class="item highlight">Theorie des jeux</span>
            </div>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<style scoped>
.pyramid-container {
  width: 100%;
  height: 100%;
  display: flex;
  align-items: center;
  justify-content: center;
  padding: 0;
}

.layer {
  position: relative;
  border: 2.5px solid #8B1A1A;
  border-radius: 18px;
  padding: 6px 8px 8px 8px;
  background: rgba(139, 26, 26, 0.06);
}

.layer-1 {
  width: 100%;
  padding: 8px 10px 10px 10px;
  background: rgba(139, 26, 26, 0.10);
}

.layer-2 {
  margin-top: 4px;
  background: rgba(139, 26, 26, 0.08);
}

.layer-3 {
  margin-top: 4px;
  background: rgba(139, 26, 26, 0.05);
}

.layer-4 {
  margin-top: 4px;
  background: rgba(245, 245, 245, 0.9);
}

.layer-header {
  font-size: 1.15em;
  font-weight: bold;
  color: #8B1A1A;
  margin-bottom: 2px;
}

.layer-1 > .layer-header {
  font-size: 1.4em;
}

.layer-2 > .layer-header {
  font-size: 1.2em;
}

.layer-3 > .layer-header {
  font-size: 1.1em;
}

.layer-4 > .layer-header {
  font-size: 1.0em;
}

.layer-images {
  float: right;
  margin: 0 0 4px 8px;
}

.layer-images img {
  display: block;
  max-height: 60px;
  max-width: 80px;
  object-fit: contain;
  border-radius: 4px;
}

.layer-1 > .layer-images img {
  max-height: 65px;
  max-width: 90px;
}

.layer-items {
  display: flex;
  flex-wrap: wrap;
  gap: 3px 6px;
  margin-bottom: 4px;
}

.item {
  display: inline-block;
  background: #C17B5F;
  color: white;
  padding: 2px 8px;
  border-radius: 6px;
  font-size: 0.7em;
  white-space: nowrap;
}

.item.highlight {
  background: #FF6B6B;
  font-weight: bold;
}
</style>
