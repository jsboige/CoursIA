<template>
  <div class="colored-table-container">
    <table class="colored-table">
      <thead><tr>
        <td class="header-cell"></td>
        <td class="header-cell">Comme l'homme</td>
        <td class="header-cell">De facon rationnelle</td>
      </tr></thead>
      <tbody><tr>
        <td class="header-cell">Penser</td>
        <td class="content-cell">Sciences cognitives</td>
        <td class="content-cell">Logique formelle</td>
      </tr>
      <tr>
        <td class="header-cell">Agir</td>
        <td class="content-cell">Test de Turing</td>
        <td class="content-cell highlight">Agents rationnels</td>
      </tr></tbody>
    </table>
  </div>
</template>

<style scoped>
.colored-table-container {
  margin: 20px 0;
}

.colored-table {
  width: 100%;
  border-collapse: separate;
  border-spacing: 4px;
}

.header-cell {
  background-color: #8B1A1A !important;
  color: #ffffff !important;
  padding: 14px 20px;
  text-align: center;
  font-weight: bold;
  border-radius: 4px;
}

.content-cell {
  background-color: #9B4F2A !important;
  color: #ffffff !important;
  padding: 14px 20px;
  text-align: center;
  border-radius: 4px;
  font-weight: 600;
}

.content-cell.highlight {
  background-color: #C0392B !important;
  color: #ffffff !important;
  font-weight: bold;
}
</style>
