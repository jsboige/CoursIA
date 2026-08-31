# Release notes

## 1.2.0

- AGENTGUARD004 : `CancellationToken` disponible mais omis lors d'un appel dont la signature cible expose explicitement ce type (analyse semantique ; exemptions : token deja passe, aucune cible annulable, aucun token disponible, homonyme)

## 1.1.0

- AGENTGUARD002 : methode async void hors gestionnaire d'evenement (avec exemption semantique handler)
- AGENTGUARD003 : invocation nue de `Task.Run(...)` comme ExpressionStatement (tache non observee ; exempt : await, affectation, discard, return, homonyme)

## 1.0.0

- Initial release
- AGENTGUARD001
