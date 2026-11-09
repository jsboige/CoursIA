# Programme jq du step "Post signal comments" de runner-variance-guard.yml
# (#15574 item 4). Vit dans un fichier et s'invoque par `jq -r -f` : un
# programme entre apostrophes dans un `run:` du workflow ferme la chaine
# bash des qu'il contient une apostrophe echappee (relecture ai-01
# e04d4e3f3b, bash -n : unexpected EOF) -- le fichier elimine la classe
# entiere, pas seulement l'occurrence.
#
# Entree : le verdict JSON de check_runner_variance.py ; seuls les
# signaux NOUVEAUX (compte croissant depuis le dernier passage) y
# figurent sous .signals.
#
# Sortie : un bloc par signal -- en-tete UNE fois, puis la liste des
# instances join("\n") (l'ancienne forme emettait l'en-tete complet par
# instance).

.signals[] |
"## SIGNAL \(.runner) (hote \(.host))

\(.hit_count) instances >= 3x la mediane du pool sur 24 h :
" + ([.hits[] | "- \(.ts) -- \(.job) : \(.duration_minutes) min vs mediane \(.pool_median_minutes) min (x\(.ratio), conclusion: \(.conclusion))"] | join("\n")) + "

Garde advisory (#15574 item 4) : aucun retrait automatique -- le retrait reste au proprietaire de lhote."
