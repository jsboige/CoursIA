# Fixture : blocs mermaid `fill:` sans `color:` (pattern #15022)

Fixture de test POSITIF du detecteur `detect_mermaid_fill_without_color.py`.
Ce fichier porte volontairement les formes fautives pour piner le contrat —
il est allowlisté par chemin dans le detecteur (`ALLOWED`), un scan fleet ne
doit donc jamais le remonter comme finding.

## Bloc fautif (classDef sans color:)

```mermaid
flowchart LR
    A --> B
    classDef dist fill:#d1ecf1,stroke:#0c5460,stroke-width:2px;
    class A,B dist;
```

## Bloc corrige (classDef avec color:)

```mermaid
flowchart LR
    A --> B
    classDef dist fill:#d1ecf1,stroke:#0c5460,stroke-width:2px,color:#0c5460;
    class A,B dist;
```

## Forme style (fautive)

```mermaid
flowchart TD
    X --> Y
    style X fill:#fff3cd,stroke:#856404;
    style Y fill:#fff3cd,stroke:#856404,color:#856404;
```

## Fence NON mermaid (doit etre ignoree)

```
classDef dist fill:#d1ecf1,stroke:#0c5460;
style X fill:#fff3cd;
```

## Commentaire %% portant le mot fill (doit etre ignore)

```mermaid
flowchart LR
    A --> B
    %% color: explicite -- une regle fill: sans color: serait un finding
    classDef ok fill:#d1ecf1,color:#0c5460;
```
