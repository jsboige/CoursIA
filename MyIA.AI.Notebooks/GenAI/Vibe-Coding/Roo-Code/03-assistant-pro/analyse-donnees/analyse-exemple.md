# Exemple d'analyse de données avec Roo

## Objectif de l'analyse

Analyser les données de ventes par région et par catégorie pour identifier les tendances et les opportunités d'optimisation des ventes.

## Chargement et exploration des données

```python
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
import numpy as np

# Chargement des données
df = pd.read_csv('exemple-dataset.csv')

# Affichage des premières lignes
print(df.head())

# Informations sur le dataset
print(df.info())

# Statistiques descriptives
print(df.describe())
```

### Résultat de l'exploration

```
         date region    categorie  ventes  clients  prix_moyen
0  2024-01-15   Nord  Electronique   12500       78      160.26
1  2024-01-15    Sud  Electronique    9800       62      158.06
2  2024-01-15    Est  Electronique    7600       45      168.89
3  2024-01-15  Ouest  Electronique   11200       70      160.00
4  2024-02-15   Nord  Electronique   11800       74      159.46

<class 'pandas.core.frame.DataFrame'>
RangeIndex: 16 entries, 0 to 15
Data columns (total 6 columns):
 #   Column       Non-Null Count  Dtype  
---  ------       --------------  -----  
 0   date         16 non-null     object 
 1   region       16 non-null     object 
 2   categorie    16 non-null     object 
 3   ventes       16 non-null     int64  
 4   clients      16 non-null     int64  
 5   prix_moyen   16 non-null     float64
dtypes: float64(1), int64(2), object(3)
memory usage: 896.0+ bytes

            ventes      clients  prix_moyen
count     16.000000    16.000000   16.000000
mean    9143.750000    48.375000  203.519375
std     2142.539237    19.553534   45.256241
min     5400.000000    22.000000  156.920000
25%     7650.000000    33.000000  160.000000
50%     9000.000000    44.500000  168.820000
75%    10750.000000    67.250000  245.892500
max    12500.000000    78.000000  248.570000
```

## Analyse des ventes par région et catégorie

```python
# Analyse des ventes par région
ventes_par_region = df.groupby('region')['ventes'].sum().reset_index()
print(ventes_par_region.sort_values('ventes', ascending=False))

# Analyse des ventes par catégorie
ventes_par_categorie = df.groupby('categorie')['ventes'].sum().reset_index()
print(ventes_par_categorie)

# Analyse croisée région x catégorie
ventes_croisees = df.groupby(['region', 'categorie'])['ventes'].sum().reset_index()
ventes_pivot = ventes_croisees.pivot(index='region', columns='categorie', values='ventes')
print(ventes_pivot)
```

### Résultats de l'analyse

```
  region  ventes
0   Nord   42200
3  Ouest   42100
1    Sud   35000
2    Est   27000

   categorie  ventes
0  Electronique   73200
1     Mobilier   53800

categorie  Electronique  Mobilier
region                          
Est              15700      11300
Nord             24300      17900
Ouest            23200      18900
Sud              20000      15000
```

## Visualisation des données

### 1. Comparaison des ventes par région

```python
plt.figure(figsize=(10, 6))
sns.barplot(x='region', y='ventes', data=ventes_par_region, palette='viridis')
plt.title('Ventes totales par région', fontsize=15)
plt.xlabel('Région')
plt.ylabel('Ventes (€)')
plt.grid(axis='y', linestyle='--', alpha=0.7)
plt.xticks(rotation=0)
plt.tight_layout()
plt.savefig('ventes_par_region.png')
plt.show()
```

![Ventes par région](https://i.imgur.com/example1.png)

### 2. Évolution des ventes par catégorie et par mois

```python
# Conversion de la colonne date en datetime
df['date'] = pd.to_datetime(df['date'])
df['mois'] = df['date'].dt.strftime('%Y-%m')

# Agrégation par mois et catégorie
ventes_mensuelles = df.groupby(['mois', 'categorie'])['ventes'].sum().reset_index()

plt.figure(figsize=(12, 7))
sns.lineplot(x='mois', y='ventes', hue='categorie', data=ventes_mensuelles, 
             marker='o', linewidth=2.5, markersize=10)
plt.title('Évolution des ventes par catégorie', fontsize=15)
plt.xlabel('Mois')
plt.ylabel('Ventes (€)')
plt.grid(linestyle='--', alpha=0.7)
plt.xticks(rotation=0)
plt.legend(title='Catégorie')
plt.tight_layout()
plt.savefig('evolution_ventes.png')
plt.show()
```

![Évolution des ventes](https://i.imgur.com/example2.png)

### 3. Heatmap des ventes par région et catégorie

```python
plt.figure(figsize=(10, 8))
sns.heatmap(ventes_pivot, annot=True, fmt='.0f', cmap='YlGnBu', linewidths=.5)
plt.title('Heatmap des ventes par région et catégorie', fontsize=15)
plt.tight_layout()
plt.savefig('heatmap_ventes.png')
plt.show()
```

![Heatmap des ventes](https://i.imgur.com/example3.png)

## Analyse du prix moyen et du nombre de clients

```python
# Relation entre le nombre de clients et les ventes
plt.figure(figsize=(10, 6))
sns.scatterplot(x='clients', y='ventes', hue='categorie', size='prix_moyen',
                sizes=(50, 200), data=df, palette='Set2')
plt.title('Relation entre clients, ventes et prix moyen', fontsize=15)
plt.xlabel('Nombre de clients')
plt.ylabel('Ventes (€)')
plt.grid(linestyle='--', alpha=0.7)
plt.legend(title='Catégorie')
plt.tight_layout()
plt.savefig('relation_clients_ventes.png')
plt.show()
```

![Relation clients-ventes](https://i.imgur.com/example4.png)

## Conclusions et recommandations

### Principales observations

1. **Performance par région**:
   - Les régions Nord et Ouest génèrent les ventes les plus élevées
   - La région Est présente les ventes les plus faibles

2. **Performance par catégorie**:
   - La catégorie Électronique représente environ 58% des ventes totales
   - La catégorie Mobilier a un prix moyen plus élevé mais moins de clients

3. **Évolution mensuelle**:
   - Légère augmentation des ventes d'Électronique en février
   - Augmentation plus marquée des ventes de Mobilier en février

### Recommandations

1. **Optimisation régionale**:
   - Analyser les stratégies commerciales réussies dans les régions Nord et Ouest pour les appliquer à l'Est
   - Envisager des campagnes marketing ciblées dans la région Est pour stimuler les ventes

2. **Stratégie par catégorie**:
   - Pour l'Électronique: se concentrer sur l'augmentation du volume de clients
   - Pour le Mobilier: explorer des opportunités d'augmenter le panier moyen

3. **Actions à court terme**:
   - Lancer une promotion croisée Électronique + Mobilier dans la région Est
   - Analyser plus en détail les facteurs de conversion dans les régions performantes

## Prochaines étapes d'analyse

- Collecter des données sur une période plus longue pour identifier les tendances saisonnières
- Intégrer des données démographiques pour mieux comprendre les différences régionales
- Analyser les coûts pour calculer la rentabilité par catégorie et par région
- Segmenter les clients pour des stratégies marketing plus ciblées