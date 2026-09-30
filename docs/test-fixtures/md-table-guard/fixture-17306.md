# Fixture md-table-guard #17306

Fixture d'exercice pour la jambe advisory du garde markdown-table : un fichier
`.md` change par la PR met le workflow sur le chemin COUNT > 0, donc sur la
materielisation sparse des fichiers changes (`git sparse-checkout set --no-cone
--stdin`, fix #17306) que cette PR corrige. Contenu volontairement sans
tableau ni pipe : le scanner doit rendre Clean et le job exit 0.

Ce fichier n'est consomme par aucun autre organe ; il ne sert qu'a rendre la
branche fixee de la garde executable sur la PR elle-meme.
