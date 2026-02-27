<template>
  <div class="colored-table-container">
    <table class="colored-table">
      <tr>
        <td class="header-cell"></td>
        <td class="header-cell">Comme l'homme</td>
        <td class="header-cell">De facon rationnelle</td>
      </tr>
      <tr>
        <td class="header-cell">Penser</td>
        <td class="content-cell">Sciences cognitives</td>
        <td class="content-cell">Logique formelle</td>
      </tr>
      <tr>
        <td class="header-cell">Agir</td>
        <td class="content-cell">Test de Turing</td>
        <td class="content-cell highlight">Agents rationnels</td>
      </tr>
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
  background-color: #8B1A1A;
  color: white;
  padding: 14px 20px;
  text-align: center;
  font-weight: bold;
  border-radius: 4px;
}

.content-cell {
  background-color: #C17B5F;
  color: white;
  padding: 14px 20px;
  text-align: center;
  border-radius: 4px;
}

.content-cell.highlight {
  background-color: #FF6B6B;
  font-weight: bold;
}
</style>
