// Faux positif pour AGENTGUARD005 : un awaiter personnalise peut exposer
// une methode `GetResult()` qui n'a rien a voir avec la machine a etats
// d'une Task. L'analyseur doit ignorer ce cas (le filtre semantique
// verifie que le receiver du `GetAwaiter()` est bien de type
// `System.Threading.Tasks.Task` ou `Task<T>` ; ici il est de type
// `MonAwaitable`, donc on laisse passer).
//
// Verdict attendu : PROPRE (aucun diagnostic AGENTGUARD005).

using System;
using System.Runtime.CompilerServices;

namespace AwaiterCustom;

public readonly struct MonAwaitable
{
    private readonly int _valeur;
    public MonAwaitable(int valeur) => _valeur = valeur;

    public MonAwaiter GetAwaiter() => new MonAwaiter(_valeur);
}

public readonly struct MonAwaiter : INotifyCompletion
{
    private readonly int _valeur;
    public MonAwaiter(int valeur) => _valeur = valeur;

    public bool IsCompleted => true;
    public int GetResult() => _valeur;
    public void OnCompleted(Action continuation) => continuation();
}

public static class AgentAwaiterPersonnalise
{
    // Le code appelle `.GetAwaiter().GetResult()` mais sur un type qui
    // n'est PAS `System.Threading.Tasks.Task`. L'analyseur ne doit PAS
    // signaler -- un awaiter custom peut etre synchrone-par-construction.
    public static int LireValeur()
    {
        MonAwaitable a = new MonAwaitable(7);
        return a.GetAwaiter().GetResult();
    }
}
