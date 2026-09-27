# Release notes

## 1.3.0

- AGENTGUARD005 : `GetAwaiter().GetResult()` sur une expression de type `Task` ou `Task<T>` (analyse semantique du receiver ; exemption : la tache n'est pas `System.Threading.Tasks.Task`, donc les awaiters personnalises sont exempts)

## 1.2.0

- AGENTGUARD004 : `CancellationToken` disponible mais omis lors d'un appel dont la signature cible expose explicitement ce type (analyse semantique ; exemptions : token deja passe, aucune cible annulable, aucun token disponible, homonyme)

## 1.1.0

- AGENTGUARD002 : methode async void hors gestionnaire d'evenement (avec exemption semantique handler)
- AGENTGUARD003 : invocation nue de `Task.Run(...)` comme ExpressionStatement (tache non observee ; exempt : await, affectation, discard, return, homonyme)

## 1.0.0

- Initial release
- AGENTGUARD001
