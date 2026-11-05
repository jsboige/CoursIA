using System;
using System.Collections.Generic;
using System.Linq;

namespace MyIA.AI.Shared.Search.Probability;

/// <summary>
/// Reseau bayesien discret (AIMA ch. 12-13), tel que le decrit la tranche 2a de #21909 :
/// des variables finies, une structure de parents declaree avant les enfants, et une table
/// de probabilite conditionnelle par noeud.
/// </summary>
/// <remarks>
/// Les parents doivent etre declares avant leurs enfants. Cette regle n'est pas cosmetique :
/// elle rend le graphe acyclique par construction, si bien qu'aucune detection de cycle n'est
/// necessaire a l'execution, et qu'une structure cyclique echoue a la construction.
///
/// L'inference offerte ici est l'enumeration exacte (AIMA, algorithme <c>ENUMERATE-ALL</c>) :
/// elle est correcte par construction et volontairement non optimisee. L'elimination de
/// variables viendra si un consommateur en a besoin.
/// </remarks>
public sealed class BayesianNetwork
{
    private const double Tolerance = 1e-9;

    private readonly string[] _names;
    private readonly string[][] _domains;
    private readonly int[][] _parentIndices;
    private readonly double[][] _cpt;
    private readonly Dictionary<string, int> _indices;

    /// <summary>Declare un noeud du reseau : son nom, son domaine, ses parents et sa table.</summary>
    /// <param name="Name">Nom de la variable, unique dans le reseau.</param>
    /// <param name="Domain">Valeurs possibles, dans l'ordre ou la table les enumere.</param>
    /// <param name="Parents">Noms des parents, deja declares.</param>
    /// <param name="Cpt">
    /// Table de probabilite conditionnelle, aplatie : pour chaque combinaison des valeurs des
    /// parents (ordre lexicographique sur <paramref name="Parents"/>, le dernier parent variant
    /// le plus vite), les probabilites de chaque valeur du domaine se suivent.
    /// </param>
    public sealed record Node(
        string Name,
        IReadOnlyList<string> Domain,
        IReadOnlyList<string> Parents,
        IReadOnlyList<double> Cpt);

    /// <summary>Construit le reseau et valide toute sa structure avant le premier calcul.</summary>
    /// <exception cref="ArgumentException">Structure ou table invalide.</exception>
    public BayesianNetwork(IReadOnlyList<Node> nodes)
    {
        ArgumentNullException.ThrowIfNull(nodes);
        if (nodes.Count == 0)
        {
            throw new ArgumentException("Un reseau bayesien doit porter au moins une variable.", nameof(nodes));
        }

        _names = new string[nodes.Count];
        _domains = new string[nodes.Count][];
        _parentIndices = new int[nodes.Count][];
        _cpt = new double[nodes.Count][];

        var indices = new Dictionary<string, int>(StringComparer.Ordinal);

        for (int node = 0; node < nodes.Count; node++)
        {
            Node declaration = nodes[node] ?? throw new ArgumentException($"Le noeud {node} est nul.", nameof(nodes));

            string name = string.IsNullOrWhiteSpace(declaration.Name)
                ? throw new ArgumentException($"Le noeud {node} n'a pas de nom.", nameof(nodes))
                : declaration.Name;

            if (indices.ContainsKey(name))
            {
                throw new ArgumentException($"La variable '{name}' est declaree deux fois.", nameof(nodes));
            }

            string[] domain = ValidateDomain(name, declaration.Domain);

            int[] parents = new int[declaration.Parents?.Count ?? 0];
            for (int position = 0; position < parents.Length; position++)
            {
                string parentName = declaration.Parents![position];
                if (!indices.TryGetValue(parentName, out int parentIndex))
                {
                    throw new ArgumentException(
                        $"Le parent '{parentName}' de '{name}' n'est pas declare avant elle : "
                        + "un parent doit preceder son enfant, ce qui rend le graphe acyclique par construction.",
                        nameof(nodes));
                }

                if (Array.IndexOf(parents, parentIndex, 0, position) >= 0)
                {
                    throw new ArgumentException($"Le parent '{parentName}' est declare deux fois pour '{name}'.", nameof(nodes));
                }

                parents[position] = parentIndex;
            }

            int combinations = 1;
            foreach (int parent in parents)
            {
                combinations = checked(combinations * _domains[parent].Length);
            }

            int expected = checked(combinations * domain.Length);
            if (declaration.Cpt is null || declaration.Cpt.Count != expected)
            {
                throw new ArgumentException(
                    $"La table de '{name}' porte {declaration.Cpt?.Count ?? 0} valeurs, "
                    + $"or {combinations} combinaison(s) de parents x {domain.Length} valeur(s) = {expected} sont attendues.",
                    nameof(nodes));
            }

            double[] cpt = declaration.Cpt.ToArray();
            for (int start = 0; start < cpt.Length; start += domain.Length)
            {
                double sum = 0;
                for (int offset = 0; offset < domain.Length; offset++)
                {
                    double value = cpt[start + offset];
                    if (double.IsNaN(value) || value < 0 || value > 1)
                    {
                        throw new ArgumentException(
                            $"La table de '{name}' porte la probabilite hors de [0,1] : {value}.",
                            nameof(nodes));
                    }

                    sum += value;
                }

                if (Math.Abs(sum - 1.0) > Tolerance)
                {
                    throw new ArgumentException(
                        $"La table de '{name}' ne somme pas a 1 pour la combinaison {start / domain.Length} : {sum}.",
                        nameof(nodes));
                }
            }

            indices.Add(name, node);
            _names[node] = name;
            _domains[node] = domain;
            _parentIndices[node] = parents;
            _cpt[node] = cpt;
        }

        _indices = indices;
    }

    /// <summary>Nombre de variables du reseau.</summary>
    public int NodeCount => _names.Length;

    /// <summary>Indice de la variable nommee, ou une exception si elle n'existe pas.</summary>
    public int IndexOf(string name)
    {
        ArgumentNullException.ThrowIfNull(name);
        return _indices.TryGetValue(name, out int index)
            ? index
            : throw new ArgumentException($"La variable '{name}' n'existe pas dans ce reseau.", nameof(name));
    }

    /// <summary>Nom de la variable d'indice <paramref name="node"/>.</summary>
    public string NameOf(int node)
    {
        RequireNode(node);
        return _names[node];
    }

    /// <summary>Domaine de la variable, dans l'ordre ou la table l'enumere.</summary>
    public IReadOnlyList<string> DomainOf(int node)
    {
        RequireNode(node);
        return _domains[node];
    }

    /// <summary>
    /// Probabilite jointe d'une affectation <b>complete</b> : produit des tables de chaque
    /// variable, conditionnee par les valeurs de ses parents dans la meme affectation.
    /// </summary>
    public double JointProbability(IReadOnlyDictionary<string, string> assignment)
    {
        ArgumentNullException.ThrowIfNull(assignment);

        var values = new int[_names.Length];
        for (int node = 0; node < _names.Length; node++)
        {
            if (!assignment.TryGetValue(_names[node], out string? value))
            {
                throw new ArgumentException(
                    $"L'affectation ne donne pas de valeur a '{_names[node]}' : une probabilite jointe exige l'affectation complete.",
                    nameof(assignment));
            }

            values[node] = IndexOfValue(node, value, nameof(assignment));
        }

        double product = 1.0;
        for (int node = 0; node < _names.Length; node++)
        {
            product *= Parameter(node, values);
        }

        return product;
    }

    /// <summary>
    /// Distribution a posteriori de la variable <paramref name="query"/> sachant
    /// <paramref name="evidence"/>, par enumeration exacte des affectations coherentes.
    /// </summary>
    /// <exception cref="InvalidOperationException">L'evidence n'est compatible avec aucune affectation.</exception>
    public double[] Posterior(int query, IReadOnlyDictionary<string, string> evidence)
    {
        RequireNode(query);
        ArgumentNullException.ThrowIfNull(evidence);

        var fixedValues = new int?[_names.Length];
        foreach (KeyValuePair<string, string> entry in evidence)
        {
            int node = IndexOf(entry.Key);
            fixedValues[node] = IndexOfValue(node, entry.Value, nameof(evidence));
        }

        var assignment = new int[_names.Length];
        var mass = new double[_domains[query].Length];
        double total = 0;

        void Walk(int node, double weight)
        {
            if (node == _names.Length)
            {
                mass[assignment[query]] += weight;
                total += weight;
                return;
            }

            if (fixedValues[node] is int fixedValue)
            {
                assignment[node] = fixedValue;
                Walk(node + 1, weight * Parameter(node, assignment));
                return;
            }

            for (int value = 0; value < _domains[node].Length; value++)
            {
                assignment[node] = value;
                Walk(node + 1, weight * Parameter(node, assignment));
            }
        }

        Walk(0, 1.0);

        if (total <= 0)
        {
            throw new InvalidOperationException(
                "L'evidence fournie n'est compatible avec aucune affectation : sa probabilite est nulle, "
                + "il n'existe donc pas de distribution a posteriori a rendre.");
        }

        for (int value = 0; value < mass.Length; value++)
        {
            mass[value] /= total;
        }

        return mass;
    }

    private double Parameter(int node, IReadOnlyList<int> assignment)
    {
        int[] parents = _parentIndices[node];
        int size = _domains[node].Length;

        int combination = 0;
        for (int position = 0; position < parents.Length; position++)
        {
            combination = (combination * _domains[parents[position]].Length) + assignment[parents[position]];
        }

        return _cpt[node][(combination * size) + assignment[node]];
    }

    private int IndexOfValue(int node, string value, string parameterName)
    {
        int index = Array.IndexOf(_domains[node], value);
        return index >= 0
            ? index
            : throw new ArgumentException(
                $"La valeur '{value}' n'appartient pas au domaine de '{_names[node]}'.",
                parameterName);
    }

    private void RequireNode(int node)
    {
        if (node < 0 || node >= _names.Length)
        {
            throw new ArgumentOutOfRangeException(nameof(node), node, $"Indice de variable hors du reseau (0..{_names.Length - 1}).");
        }
    }

    private static string[] ValidateDomain(string name, IReadOnlyList<string>? domain)
    {
        if (domain is null || domain.Count < 2)
        {
            throw new ArgumentException($"Le domaine de '{name}' doit porter au moins deux valeurs.");
        }

        var values = domain.ToArray();
        for (int index = 0; index < values.Length; index++)
        {
            if (string.IsNullOrEmpty(values[index]))
            {
                throw new ArgumentException($"Le domaine de '{name}' porte une valeur vide.");
            }

            if (Array.IndexOf(values, values[index], 0, index) >= 0)
            {
                throw new ArgumentException($"Le domaine de '{name}' repete la valeur '{values[index]}'.");
            }
        }

        return values;
    }
}
