using System;
using System.Collections.Generic;
using System.Linq;

namespace MyIA.AI.Shared.Search.Csp;

/// <summary>
/// Recherche par backtracking sur un <see cref="CspProblem"/>, avec choix de
/// variable (ordre par defaut ou MRV) et inference (aucune, forward checking, AC-3).
/// </summary>
/// <remarks>
/// <para>
/// Port du noyau CSP d'AIMA (EPIC #7265, pepite B1), recupere du patrimoine
/// Aricie : la version d'origine (<c>aima.core.search.csp.BacktrackingStrategy</c>)
/// n'etait atteignable qu'a travers un wrapper DNN + IKVM ; celle-ci est du C#
/// nu, sans dependance DNN ni Java.
/// </para>
/// <para>
/// Le solveur compte ses <see cref="NodeCount"/> et <see cref="BacktrackCount"/> :
/// ce sont les deux mesures qui rendent une heuristique falsifiable plutot que
/// decorative (MRV et AC-3 doivent reduire le nombre de noeuds explores).
/// </para>
/// </remarks>
public sealed class BacktrackingSolver
{
    /// <summary>Heuristique de choix de variable ; ordre de declaration par defaut.</summary>
    public VariableSelection Selection { get; init; } = VariableSelection.DefaultOrder;

    /// <summary>Inference appliquee apres chaque affectation ; aucune par defaut.</summary>
    public InferenceStrategy Inference { get; init; } = InferenceStrategy.None;

    /// <summary>Noeuds explores lors du dernier <see cref="Solve"/> (une affectation etendue = un noeud).</summary>
    public int NodeCount { get; private set; }

    /// <summary>Retours arriere effectues lors du dernier <see cref="Solve"/>.</summary>
    public int BacktrackCount { get; private set; }

    /// <summary>
    /// Cherche une affectation complete et coherente.
    /// Rend <c>null</c> quand le probleme est insatisfiable.
    /// </summary>
    public Assignment? Solve(CspProblem problem)
    {
        ArgumentNullException.ThrowIfNull(problem);

        NodeCount = 0;
        BacktrackCount = 0;

        Assignment assignment = new();
        Dictionary<Variable, Domain> domains = problem.Variables.ToDictionary(variable => variable, variable => variable.Domain.Copy());

        return Search(problem, assignment, domains) ? assignment : null;
    }

    private bool Search(CspProblem problem, Assignment assignment, Dictionary<Variable, Domain> domains)
    {
        NodeCount++;

        if (assignment.IsComplete(problem.Variables))
        {
            return true;
        }

        Variable variable = SelectUnassignedVariable(problem, assignment, domains);

        foreach (object? value in domains[variable].Values.ToList())
        {
            assignment.Add(variable, value);

            Dictionary<Variable, Domain>? restore = null;
            if (assignment.IsConsistent(problem.GetConstraints(variable)))
            {
                restore = Inference == InferenceStrategy.None ? null : Snapshot(domains);
                if (Inference == InferenceStrategy.None || ApplyInference(problem, assignment, domains, variable, value))
                {
                    if (Search(problem, assignment, domains))
                    {
                        return true;
                    }
                }
            }

            if (restore != null)
            {
                Restore(domains, restore);
            }

            assignment.Remove(variable);
            BacktrackCount++;
        }

        return false;
    }

    private Variable SelectUnassignedVariable(
        CspProblem problem,
        Assignment assignment,
        Dictionary<Variable, Domain> domains)
    {
        List<Variable> unassigned = problem.Variables.Where(variable => !assignment.Contains(variable)).ToList();

        return Selection switch
        {
            VariableSelection.DefaultOrder => unassigned[0],
            VariableSelection.MinimumRemainingValues => unassigned
                .OrderBy(variable => domains[variable].Size)
                .First(),
            VariableSelection.MinimumRemainingValuesDegree => unassigned
                .OrderBy(variable => domains[variable].Size)
                .ThenByDescending(variable => problem.GetNeighbors(variable).Count())
                .First(),
            _ => throw new ArgumentOutOfRangeException(nameof(Selection), Selection, "Heuristique de selection inconnue."),
        };
    }

    private bool ApplyInference(
        CspProblem problem,
        Assignment assignment,
        Dictionary<Variable, Domain> domains,
        Variable assigned,
        object? assignedValue)
    {
        return Inference switch
        {
            InferenceStrategy.ForwardChecking => ForwardCheck(problem, domains, assigned, assignedValue),
            InferenceStrategy.Ac3 => Ac3(problem, assignment, domains, assigned, assignedValue),
            _ => true,
        };
    }

    /// <summary>
    /// Forward checking : retire des domaines voisins les valeurs incompatibles
    /// avec l'affectation courante. Rend <c>false</c> des qu'un domaine se vide.
    /// </summary>
    private static bool ForwardCheck(
        CspProblem problem,
        Dictionary<Variable, Domain> domains,
        Variable assigned,
        object? assignedValue)
    {
        foreach (Variable neighbor in problem.GetNeighbors(assigned))
        {
            foreach (BinaryConstraint constraint in problem.GetBinaryConstraints(assigned, neighbor))
            {
                if (!PruneNeighborDomain(constraint, assigned, neighbor, domains, assignedValue))
                {
                    return false;
                }
            }
        }

        return true;
    }

    private static bool PruneNeighborDomain(
        BinaryConstraint constraint,
        Variable assigned,
        Variable neighbor,
        Dictionary<Variable, Domain> domains,
        object? assignedValue)
    {
        Domain neighborDomain = domains[neighbor];
        List<object?> toRemove = new();

        foreach (object? candidate in neighborDomain.Values)
        {
            bool compatible = ReferenceEquals(constraint.Left, assigned)
                ? constraint.IsSatisfiedByValues(assignedValue, candidate)
                : constraint.IsSatisfiedByValues(candidate, assignedValue);

            if (!compatible)
            {
                toRemove.Add(candidate);
            }
        }

        foreach (object? value in toRemove)
        {
            neighborDomain.Remove(value);
        }

        return !neighborDomain.IsEmpty;
    }

    /// <summary>
    /// AC-3 : revise les arcs binaires jusqu'a point fixe. Un arc (Xi, Xj) est
    /// revise en retirant de Xi les valeurs sans support dans Xj.
    /// </summary>
    /// <remarks>
    /// La variable qui vient d'etre affectee est un singleton : ses voisins sont
    /// d'abord filtres contre sa valeur (meme geste que le forward checking),
    /// puis AC-3 propage la coherence d'arc sur le reste du reseau. Sans ce
    /// premier filtrage, les arcs touches par l'affectation ne seraient pas
    /// revises et la propagation laisserait passer des valeurs incoherentes.
    /// </remarks>
    private static bool Ac3(
        CspProblem problem,
        Assignment assignment,
        Dictionary<Variable, Domain> domains,
        Variable assigned,
        object? assignedValue)
    {
        if (!ForwardCheck(problem, domains, assigned, assignedValue))
        {
            return false;
        }

        Queue<(Variable Xi, Variable Xj)> queue = new();

        foreach (Variable variable in problem.Variables.Where(variable => !assignment.Contains(variable)))
        {
            foreach (Variable neighbor in problem.GetNeighbors(variable).Where(neighbor => !assignment.Contains(neighbor)))
            {
                if (problem.GetBinaryConstraints(variable, neighbor).Any())
                {
                    queue.Enqueue((variable, neighbor));
                    queue.Enqueue((neighbor, variable));
                }
            }
        }

        while (queue.Count > 0)
        {
            (Variable xi, Variable xj) = queue.Dequeue();

            bool revised = false;
            foreach (BinaryConstraint constraint in problem.GetBinaryConstraints(xi, xj))
            {
                revised |= Revise(constraint, xi, xj, domains);
            }

            if (!revised)
            {
                continue;
            }

            if (domains[xi].IsEmpty)
            {
                return false;
            }

            foreach (Variable neighbor in problem.GetNeighbors(xi).Where(neighbor => !assignment.Contains(neighbor) && !ReferenceEquals(neighbor, xj)))
            {
                if (problem.GetBinaryConstraints(neighbor, xi).Any())
                {
                    queue.Enqueue((neighbor, xi));
                }
            }
        }

        return true;
    }

    private static bool Revise(
        BinaryConstraint constraint,
        Variable xi,
        Variable xj,
        Dictionary<Variable, Domain> domains)
    {
        Domain domainI = domains[xi];
        Domain domainJ = domains[xj];
        List<object?> toRemove = new();

        foreach (object? valueI in domainI.Values)
        {
            bool hasSupport = domainJ.Values.Any(valueJ =>
                ReferenceEquals(constraint.Left, xi)
                    ? constraint.IsSatisfiedByValues(valueI, valueJ)
                    : constraint.IsSatisfiedByValues(valueJ, valueI));

            if (!hasSupport)
            {
                toRemove.Add(valueI);
            }
        }

        foreach (object? value in toRemove)
        {
            domainI.Remove(value);
        }

        return toRemove.Count > 0;
    }

    private static Dictionary<Variable, Domain> Snapshot(Dictionary<Variable, Domain> domains) =>
        domains.ToDictionary(entry => entry.Key, entry => entry.Value.Copy());

    private static void Restore(Dictionary<Variable, Domain> domains, Dictionary<Variable, Domain> snapshot)
    {
        foreach (KeyValuePair<Variable, Domain> entry in snapshot)
        {
            domains[entry.Key] = entry.Value.Copy();
        }
    }
}
