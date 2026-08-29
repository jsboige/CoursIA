# Release notes

## 1.1.0

- AGENTGUARD002 : methode async void hors gestionnaire d'evenement (avec exemption semantique handler)
- AGENTGUARD003 : invocation nue de `Task.Run(...)` comme ExpressionStatement (tache non observee ; exempt : await, affectation, discard, return, homonyme)

## 1.0.0

- Initial release
- AGENTGUARD001
