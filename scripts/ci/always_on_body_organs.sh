#!/usr/bin/env bash
# Organes always-on qui lisent le BODY de la PR (Grain tag, prev:, close-keyword,
# genre diversity, closing-ref vs claim). Extrait de always-on-guards.yml pour
# qu'un job dedie (workflow always-on-guards-body.yml, evenement `edited`) les
# rejoue sans re-declencher les organes de contenu.
#
# Le corps de chaque organe est repris VERBATIM du workflow d'origine. Env
# attendu : GH_TOKEN, GH_REPO, PR_NUMBER, PR_BODY, PR_AUTHOR, IS_FORK, HEAD_REF.
# `set -e` reproduit le shell des steps GitHub (`bash -e {0}`) ; chaque organe
# tourne dans un SUBSHELL, donc son `exit 0/1` d'origine sort de l'organe et
# pas du script -- l'agregat voit tous les organes, comme aujourd'hui.
set -eo pipefail

FAILED=""

run_organ() {
  case "$1" in
    tag_required) organ_tag_required ;;
    prev_guard) organ_prev_guard ;;
    close_keyword) organ_close_keyword ;;
    adjacency) organ_adjacency ;;
    lane_claim) organ_lane_claim ;;
  esac
}

# ---------------------------------------------------------------------------
# tag_required -- Require Grain tag (block on absent, #10045)
# if: github.event_name == 'pull_request'
organ_tag_required() (
set -uo pipefail

case "$PR_AUTHOR" in
  *"[bot]") echo "Auteur bot ($PR_AUTHOR) : hors scope."; exit 0 ;;
esac
if [ "$IS_FORK" = "true" ]; then
  echo "PR issue d'un fork : hors scope (PR etudiante, cf student-pr-reviews.md)."
  exit 0
fi

printf '%s' "${PR_BODY:-}" > /tmp/pr_body.txt

# #17713 -- exemption : une PR dont la branche commence par `claude/`
# ET dont le body porte "Hors flotte" est une session cloud du
# mainteneur, exempte du tag Grain: par `CLAUDE.md` ('A qui ce fichier
# s'adresse'). On passe HEAD_REF au script qui applique l'exemption
# (les DEUX conditions doivent etre reunies -- un renommage de
# branche seul ne suffit pas).
HEAD_REF="${HEAD_REF:-}"

# Capturer le RC via &&/|| (exempt d'errexit) -- jamais une
# commande suivie d'un RC=$? en ligne separee : sous bash -e elle
# meurt au block path meme, avant l'affectation.
python3 scripts/ci/variation_tag_required.py \
  --body-file /tmp/pr_body.txt --head-ref "$HEAD_REF" > /tmp/verdict.json 2>/tmp/verdict.err && RC=0 || RC=$?

if [ -s /tmp/verdict.err ]; then
  echo "--- helper stderr ---"
  cat /tmp/verdict.err
fi
echo "--- verdict ---"
cat /tmp/verdict.json

OVERRIDDEN=$(python3 -c "import json; print(json.load(open('/tmp/verdict.json')).get('overridden'))" 2>/dev/null || echo "None")
if [ "$OVERRIDDEN" = "True" ]; then
  echo "::notice::Adjacence G-VAR-3 REELLE, levee par le coordinateur (clause 24h, section 3). Le grain suivant de la lane change de genre."
fi

if [ "$RC" -eq 0 ]; then
  # #15372 : un run vert LEVE le commentaire bloquant precedent en place
  # (s'il existe). No-op silencieux sinon -- un vert sur une PR jamais
  # bloquee ne fabrique pas de bruit.
  if ! GH_TOKEN="${GH_TOKEN}" python3 scripts/ci/guard_comment_upsert.py \
    --pr "$PR_NUMBER" \
    --marker '<!-- vtr-required-block -->' \
    --lift --note "Grain tag + lane presents au re-passage." \
    >/dev/null 2>&1; then
    echo "::warning::tag_required lift failed (commentaire bloquant possiblement perime)"
  fi
  echo "Grain tag + lane present -- job passes."
  exit 0
fi

REASON=$(python3 -c "import json; print(json.load(open('/tmp/verdict.json')).get('reason','unknown'))" 2>/dev/null || echo "unknown")
echo "::error::Grain tag ou lane manquant : $REASON"

# #15372 : upsert -- EDITE le commentaire bot existant (marqueur + auteur
# github-actions) au lieu d'en cumuler un nouveau par run rouge : un re-run
# du workflow (recuperation #9858) ne doit pas doubler le poste.
cat > /tmp/tag_required_blocked.md <<EOF
<!-- vtr-required-block -->
**Grain tag obligatoire (#10045, bloquant).**

\`${REASON}\`.

Pour passer ce gate, le body doit porter en tete une ligne de la forme :

\`\`\`
Grain: <DEEP|MED|LIGHT>/<genre> -- lane <machine:workspace> -- prev: <TIER>/<GENRE> #<PR>
\`\`\`

Le \`<genre>\` doit figurer dans l'enumeration §1 de \`variation-protocol.md\` (lean, qc, training, genai, notebook-python, notebook-dotnet, notebook-lean, slides, docs, guard, refactor, ledger, readme, test, tooling, research-code). Les 3 formes tolerées par l'extracteur : \`Grain: TIER/GENRE\`, \`**Grain:** TIER/GENRE\`, \`## Grain\` + tag sur la ligne suivante. La lane doit suivre le format \`<machine>:<workspace>\` (cf. \`lane-claim-protocol.md\`).
EOF
if ! GH_TOKEN="${GH_TOKEN}" python3 scripts/ci/guard_comment_upsert.py \
  --pr "$PR_NUMBER" \
  --marker '<!-- vtr-required-block -->' \
  --body-file /tmp/tag_required_blocked.md \
  >/dev/null 2>&1; then
  # #15374 : le gate est deja rouge (exit 1 ensuite), mais l'echec d'upsert
  # ne doit pas passer inapercu -- il ne sera jamais presente comme une
  # ecriture reussie.
  echo "::warning::tag_required upsert failed (commentaire bloquant non pose)"
fi

exit 1
)

# ---------------------------------------------------------------------------
# prev_guard -- Require prev: non-closing (block on close-keyword genre, #10093)
# if: github.event_name == 'pull_request'
organ_prev_guard() (
set -uo pipefail

case "$PR_AUTHOR" in
  *"[bot]") echo "Auteur bot ($PR_AUTHOR) : hors scope."; exit 0 ;;
esac
if [ "$IS_FORK" = "true" ]; then
  echo "PR issue d'un fork : hors scope (PR etudiante, cf student-pr-reviews.md)."
  exit 0
fi

printf '%s' "${PR_BODY:-}" > /tmp/pr_body.txt

# Commit messages : messageBody = ce que GitHub parse pour
# l'auto-close. Echec de fetch LOGGE, non masque (#10953).
if ! gh pr view "$PR_NUMBER" --json commits --jq '[.commits[].messageBody]' \
    > /tmp/commits.json; then
  echo "::warning::gh pr view --json commits a echoue — scan des commits vide, body seul couvert (#10953)"
  printf '[]' > /tmp/commits.json
fi

# PREV-INVALID metadata (#13475) : la resolution de chaque
# `prev: ... #N` (PR mergee / PR ouverte / issue) vit desormais
# dans le module, sous test -- cf `resolve_prev_targets`. Elle
# etait ici, en heredoc, hors de portee de tout test, et elle
# etait fausse : elle demandait `gh pr view --json state,merged`,
# or `merged` n'est pas un champ de ce `gh`, donc l'appel echouait
# pour CHAQUE cible, retombait sur `gh issue view` (qui repond
# aussi pour les PRs) et classait toute PR en issue. `prev-not-pr`
# rougissait sur 100 % des PRs -- dont celle qui livrait le garde.
# Echec de resolution -> cible absente -> le gate s'abstient
# (contrat FN-safety inchange).

python3 scripts/ci/variation_prev_guard.py \
  --body-file /tmp/pr_body.txt \
  --commits-file /tmp/commits.json \
  --current-pr "$PR_NUMBER" \
  --resolve-targets > /tmp/verdict.json 2>/tmp/verdict.err && RC=0 || RC=$?

if [ -s /tmp/verdict.err ]; then
  echo "--- helper stderr ---"
  cat /tmp/verdict.err
fi
echo "--- verdict ---"
cat /tmp/verdict.json

if [ "$RC" -eq 0 ]; then
  echo "No \`prev:\` close-keyword genre in body or commits -- job passes."
  # #15372 : un run vert LEVE le commentaire bloquant precedent
  # en place (s'il existe). No-op silencieux sinon -- un vert
  # sur une PR jamais bloquee ne fabrique pas de bruit. Un mur
  # qui ne se ferme jamais n'est pas un signal.
  PREVS=$(python3 -c "import json; print(', '.join('#%s' % n for n in json.load(open('/tmp/verdict.json')).get('prev_targets_accepted', [])))" 2>/dev/null || echo "")
  if ! GH_TOKEN="${GH_TOKEN}" python3 scripts/ci/guard_comment_upsert.py \
    --pr "$PR_NUMBER" \
    --marker '<!-- vtr-prev-close-keyword -->' \
    --lift --note "aucun genre mots-clé fermant dans le body ni les commits ; prev: accepté(s) : ${PREVS:-aucun}" \
    >/dev/null 2>&1; then
    # #15374 : le gate reste vert (run prev: propre), mais un
    # lift qui echoue (quota, reseau, permissions) doit rester
    # OBSERVABLE -- sinon le commentaire bloquant survit faux
    # en silence.
    echo "::warning::prev-guard lift failed (commentaire bloquant possiblement perime)"
  fi
  exit 0
fi

REASON=$(python3 -c "import json; print(json.load(open('/tmp/verdict.json')).get('reason','unknown'))" 2>/dev/null || echo "unknown")
echo "::error::prev: close-keyword genre detected: $REASON"

# #15372 : upsert -- EDITE le commentaire bot existant (marqueur
# + auteur github-actions) au lieu d'en cumuler un nouveau par
# run rouge (19 faux bloquants mesures sur 4 PRs le 09/09).
cat > /tmp/prev_blocked_body.md <<EOF
<!-- vtr-prev-close-keyword -->
**\`prev:\` genre mots-clé fermant -- bloquant (#10093).**

${REASON}

Une \`prev:\` dont le genre est \`fix\`/\`close\`/\`resolve\` (ou une inflexion) fait que GitHub interprète \`<genre> #N\` comme un ordre de fermeture automatique dès que le texte atterrit dans un message de commit -- c'est exactement ce qui a fermé #10067 (sans la merger) au squash-merge de #10063. Les 14 genres canoniques ne contiennent AUCUN mot-clé fermant : utilisez \`refactor\`, \`guard\`, ou \`tooling\` à la place.

Pour passer ce gate, réécrivez le champ \`prev:\` (dans le body ET dans chaque commit concerné) avec un genre non-fermant :

\`\`\`
Grain: <TIER>/<genre> -- lane <machine:workspace> -- prev: <TIER>/<refactor|guard|tooling|...> #<PR>
\`\`\`
EOF
if ! GH_TOKEN="${GH_TOKEN}" python3 scripts/ci/guard_comment_upsert.py \
  --pr "$PR_NUMBER" \
  --marker '<!-- vtr-prev-close-keyword -->' \
  --body-file /tmp/prev_blocked_body.md \
  >/dev/null 2>&1; then
  # #15374 : le gate est deja rouge (exit 1 ensuite), mais
  # l'echec d'upsert ne doit pas passer inapercu -- il ne sera
  # jamais presente comme une ecriture reussie.
  echo "::warning::prev-guard upsert failed (commentaire bloquant non pose)"
fi

exit 1
)

# ---------------------------------------------------------------------------
# close_keyword -- Require no close-keyword + PR-number (block on auto-close of a PR, #10101)
# if: github.event_name == 'pull_request'
organ_close_keyword() (
set -uo pipefail

case "$PR_AUTHOR" in
  *"[bot]") echo "Auteur bot ($PR_AUTHOR) : hors scope."; exit 0 ;;
esac
if [ "$IS_FORK" = "true" ]; then
  echo "PR issue d'un fork : hors scope (PR etudiante, cf student-pr-reviews.md)."
  exit 0
fi

printf '%s' "${PR_BODY:-}" > /tmp/pr_body.txt

if ! gh pr view "$PR_NUMBER" --json commits --jq '[.commits[].messageBody]' \
    > /tmp/commits.json; then
  echo "::warning::gh pr view --json commits a echoue — scan des commits vide, body seul couvert (#10953)"
  printf '[]' > /tmp/commits.json
fi

python3 scripts/ci/pr_close_keyword_guard.py \
  --body-file /tmp/pr_body.txt \
  --commits-file /tmp/commits.json > /tmp/verdict.json 2>/tmp/verdict.err && RC=0 || RC=$?

if [ -s /tmp/verdict.err ]; then
  echo "--- helper stderr ---"
  cat /tmp/verdict.err
fi
echo "--- verdict ---"
cat /tmp/verdict.json

# Warnings fail-open (refs perimees, blips) surfaces meme en pass.
python3 -c "import json; [print('::warning::'+w) for w in json.load(open('/tmp/verdict.json')).get('warnings',[])]" 2>/dev/null || true

if [ "$RC" -eq 0 ]; then
  # #15372 : un run vert LEVE le commentaire bloquant precedent en place.
  if ! GH_TOKEN="${GH_TOKEN}" python3 scripts/ci/guard_comment_upsert.py \
    --pr "$PR_NUMBER" \
    --marker '<!-- vtr-close-keyword-pr-ref -->' \
    --lift --note "aucun mot-cle fermant sur un numero de PR au re-passage." \
    >/dev/null 2>&1; then
    echo "::warning::close_keyword lift failed (commentaire bloquant possiblement perime)"
  fi
  echo "No closing-keyword + PR-number reference in body or commits -- job passes."
  exit 0
fi

REASON=$(python3 -c "import json; print(json.load(open('/tmp/verdict.json')).get('reason','unknown'))" 2>/dev/null || echo "unknown")
echo "::error::closing-keyword + PR-number reference detected: $REASON"

# #15372 : upsert -- pas de mur de verdicts perimes (re-run compris).
cat > /tmp/close_keyword_blocked.md <<EOF
<!-- vtr-close-keyword-pr-ref -->
**\`<mot-clé fermant> #N\` où N est une PR -- bloquant (#10101).**

${REASON}

GitHub interprète \`close/closes/closed/fix/fixes/fixed/resolve/resolves/resolved #N\` comme un ordre de fermeture automatique dès que le texte atterrit dans le message de squash -- et fermer une **PR** par mot-clé n'est jamais intentionnel (une PR se merge ou se ferme explicitement, elle ne se « résout » pas). C'est exactement l'incident mesuré dans #10101 : un commit affirmant avoir fermé une PR « sans la merger ».

Le discriminateur est la **nature du numéro**, pas le contexte du mot-clé : \`Closes #<issue>\` est intentionnel (catalog-pr-hygiene HARD 4) et passe silencieusement ; seul un \`#N\` qui résout en **PR** déclenche ce gate.

Pour passer ce gate :
- **retirez le mot-clé fermant** devant le numéro, ou
- **écrivez le numéro SANS le \`#\`** (un nombre nu n'est pas un auto-close).
EOF
if ! GH_TOKEN="${GH_TOKEN}" python3 scripts/ci/guard_comment_upsert.py \
  --pr "$PR_NUMBER" \
  --marker '<!-- vtr-close-keyword-pr-ref -->' \
  --body-file /tmp/close_keyword_blocked.md \
  >/dev/null 2>&1; then
  echo "::warning::close_keyword upsert failed (commentaire bloquant non pose)"
fi

exit 1
)

# ---------------------------------------------------------------------------
# adjacency -- Require genre diversity vs prev (required, block on LIGHT adjacency, #11170)
# if: github.event_name == 'pull_request'
organ_adjacency() (
set -uo pipefail

case "$PR_AUTHOR" in
  *"[bot]") echo "Auteur bot ($PR_AUTHOR) : hors scope."; exit 0 ;;
esac
if [ "$IS_FORK" = "true" ]; then
  echo "PR issue d'un fork : hors scope (PR etudiante, cf student-pr-reviews.md)."
  exit 0
fi

printf '%s' "${PR_BODY:-}" > /tmp/pr_body.txt

# Comments, pour le marqueur [G-VAR-3 OVERRIDE] (#11708).
gh pr view "$PR_NUMBER" --json comments \
  --jq '[.comments[] | {author: .author.login, body: .body}]' \
  > /tmp/pr_comments.json 2>/dev/null || rm -f /tmp/pr_comments.json

COMMENTS_ARG=""
if [ -s /tmp/pr_comments.json ]; then
  COMMENTS_ARG="--comments-file /tmp/pr_comments.json"
fi

# Merged PRs pour le VRAI predecesseur de la lane (#12095) :
# fenetre merge-time DECOUPEE EN TRANCHES DE DATES via fetch_merged_prs_since.py
# (#12636 : --limit 100 est creation-capped ; le cap de recherche a 1000
#  impose le decoupage -- une seule requete ne couvre pas 21 j).
python3 scripts/ci/fetch_merged_prs_since.py --days 21 \
  > /tmp/merged_prs.json 2>/tmp/merged_fetch.err || rm -f /tmp/merged_prs.json

MERGED_ARG=""
if [ -s /tmp/merged_prs.json ]; then
  MERGED_ARG="--merged-prs-file /tmp/merged_prs.json"
else
  # Sans ce warning l'echec est INVISIBLE : le garde continue de
  # passer et de bloquer, mais sur le champ prev: DECLARE que le
  # worker ecrit lui-meme, pas sur ce qui a reellement merge. C'est
  # ainsi que l'option inexistante --page a fait tourner l'adjacence
  # sur le mauvais axe repo-wide pendant toute la vie du script,
  # sans qu'aucun run ne le dise (mesure 2026-08-29, 5/5 PRs).
  echo "::warning::G-VAR-3 : fenetre de merges NON recuperee -- l'adjacence retombe sur le champ prev: DECLARE (ecrit par le worker), pas sur la sequence reelle. Le verdict ci-dessous ne mesure pas ce qui a merge."
  if [ -s /tmp/merged_fetch.err ]; then
    echo "--- fetch stderr ---"
    sed 's/^/  /' /tmp/merged_fetch.err
  fi
fi

# shellcheck disable=SC2086  # COMMENTS_ARG/MERGED_ARG are deliberate 0-or-2 token splits
python3 scripts/ci/variation_adjacency_guard.py \
  --body-file /tmp/pr_body.txt --pr-number "$PR_NUMBER" \
  $COMMENTS_ARG $MERGED_ARG \
  > /tmp/verdict.json 2>/tmp/verdict.err && RC=0 || RC=$?

if [ -s /tmp/verdict.err ]; then
  echo "--- helper stderr ---"
  cat /tmp/verdict.err
fi
echo "--- verdict ---"
cat /tmp/verdict.json

ADJACENT=$(python3 -c "import json; print(json.load(open('/tmp/verdict.json')).get('adjacent'))" 2>/dev/null || echo "False")

# Label advisory pour l'adjacence DEEP/MED (jugement coord).
gh label create variation-adjacency-deep-med \
  --description "Adjacence DEEP/MED hors LIGHT : §2 l'autorise si substance distincte (coordinateur)" \
  --color FEF2C0 --force || true
if [ "$ADJACENT" = "True" ]; then
  gh pr edit "$PR_NUMBER" --add-label variation-adjacency-deep-med 2>/dev/null || true
else
  gh pr edit "$PR_NUMBER" --remove-label variation-adjacency-deep-med 2>/dev/null || true
fi

if [ "$RC" -eq 0 ]; then
  # #15372 : un run vert LEVE le commentaire bloquant precedent en place.
  if ! GH_TOKEN="${GH_TOKEN}" python3 scripts/ci/guard_comment_upsert.py \
    --pr "$PR_NUMBER" \
    --marker '<!-- vtr-adjacency-block -->' \
    --lift --note "pas d'adjacence LIGHT de meme genre au re-passage." \
    >/dev/null 2>&1; then
    echo "::warning::adjacency lift failed (commentaire bloquant possiblement perime)"
  fi
  echo "No LIGHT-genre adjacency vs prev: -- job passes."
  exit 0
fi

REASON=$(python3 -c "import json; print(json.load(open('/tmp/verdict.json')).get('reason','unknown'))" 2>/dev/null || echo "unknown")
# L'axe fait partie du verdict : un blocage calcule sur 'declared'
# et un blocage calcule sur 'merged-sequence' n'ont pas la meme
# valeur probante, et rien ne les distinguait dans la sortie.
PREV_SRC=$(python3 -c "import json; print(json.load(open('/tmp/verdict.json')).get('prev_source','?'))" 2>/dev/null || echo "?")
# #15739 : le REFERENTIEL complet du verdict -- contre quoi il a
# conclu. Un rouge d'adjacence est une fonction de la sequence de
# merges AU MOMENT du check ; des qu'une autre PR de la lane merge,
# le rouge affiche devient perime sans que rien ne le re-tourne. Le
# referential rend la peremption VISIBLE (prev #N + genre + source +
# horodatage de la sequence) et la commande de recalcul est DANS le
# message, pas dans une doc a retrouver.
PREV_PR=$(python3 -c "import json; print(json.load(open('/tmp/verdict.json')).get('prev_pr','?'))" 2>/dev/null || echo "?")
PREV_GENRE=$(python3 -c "import json; print(json.load(open('/tmp/verdict.json')).get('prev_genre','?'))" 2>/dev/null || echo "?")
SEQ_AS_OF=$(python3 -c "import json; print(json.load(open('/tmp/verdict.json')).get('sequence_as_of') or 'n/a')" 2>/dev/null || echo "n/a")
echo "::error::G-VAR-3 LIGHT-genre adjacency [prev: #${PREV_PR} ${PREV_GENRE} via ${PREV_SRC} ; sequence de merges au ${SEQ_AS_OF}]: $REASON"

# #15372 : upsert -- pas de mur de verdicts perimes (re-run compris).
cat > /tmp/adjacency_blocked.md <<EOF
<!-- vtr-adjacency-block -->
**G-VAR-3 : deux grains LIGHT du meme genre consecutifs -- bloquant (#11170).**

${REASON}

**Referentiel du verdict (#15739)** -- ce verdict a ete calcule contre : predecesseur \#${PREV_PR} (\`${PREV_GENRE}\`, source \`${PREV_SRC}\`), sequence de merges arretee au \`${SEQ_AS_OF}\`. Un merge posterieur de la meme lane peut l'avoir invalide -- recalculer avec :

\`\`\`bash
python scripts/ci/variation_adjacency_guard.py --pr-number ${PR_NUMBER}
\`\`\`

variation-protocol.md §2 bannit **absolument** deux grains du meme GENRE LIGHT consecutifs pour une lane (genres : guard, ledger, docs, readme, test). Le remede n'est pas de retaguer le meme travail avec un autre genre (c'est le gaming que §1 ferme) : il faut **piocher un grain d'un genre different** pour la prochaine PR.

Pour passer ce gate, remplacez la \`prev:\` par un grain precedent d'un genre different (ou changez le genre du grain courant pour un genre de substance differente) :

\`\`\`
Grain: <TIER>/<genre> -- lane <machine:workspace> -- prev: <TIER>/<genre-different> #<PR>
\`\`\`
EOF
if ! GH_TOKEN="${GH_TOKEN}" python3 scripts/ci/guard_comment_upsert.py \
  --pr "$PR_NUMBER" \
  --marker '<!-- vtr-adjacency-block -->' \
  --body-file /tmp/adjacency_blocked.md \
  >/dev/null 2>&1; then
  echo "::warning::adjacency upsert failed (commentaire bloquant non pose)"
fi

exit 1
)

# ---------------------------------------------------------------------------
# lane_claim -- Require no closing-ref against another lane active claim (block on lane collision, #10223)
# if: github.event_name == 'pull_request'
organ_lane_claim() (
set -uo pipefail

case "$PR_AUTHOR" in
  *"[bot]") echo "Auteur bot ($PR_AUTHOR) : hors scope."; exit 0 ;;
esac
if [ "$IS_FORK" = "true" ]; then
  echo "PR issue d'un fork : hors scope (PR etudiante, cf student-pr-reviews.md)."
  exit 0
fi

printf '%s' "${PR_BODY:-}" > /tmp/pr_body.txt

# #10323: GitHub-authoritative closing refs.
if PR_CLOSING_REFS=$(gh pr view "$PR_NUMBER" \
    --json closingIssuesReferences \
    --jq '[.closingIssuesReferences[].number] | join(",")' 2>/dev/null); then
  PR_CREFS_ARG=(--pr-closing-refs "$PR_CLOSING_REFS")
else
  PR_CREFS_ARG=()
  echo "::warning::closingIssuesReferences fetch failed; falling back to regex finder (#10323)."
fi

# Le shell par defaut du runner est `bash -e -o pipefail` ; le
# `set -uo pipefail` ci-dessus n'y retire PAS -e. Sans le guard
# `&& RC=0 || RC=$?` (la convention des gardes freres
# variation_prev_guard / variation_adjacency_guard ci-dessus), un
# exit non nul du helper (1 = BLOCK legitime, 2 = caller error)
# tuait le step AVANT l'affichage du verdict et le commentaire de
# resolution (RELEASED/OVERRIDE/48 h) : blocage muet, diagnostique
# a la main sur #15846.
python3 scripts/ci/lane_claim_required.py \
  --body-file /tmp/pr_body.txt "${PR_CREFS_ARG[@]}" \
  > /tmp/verdict.json 2>/tmp/verdict.err && RC=0 || RC=$?

if [ -s /tmp/verdict.err ]; then
  echo "--- helper stderr ---"
  cat /tmp/verdict.err
fi
echo "--- verdict ---"
cat /tmp/verdict.json

python3 -c "import json; [print('::warning::'+w) for w in json.load(open('/tmp/verdict.json')).get('warnings',[])]" 2>/dev/null || true

if [ "$RC" -eq 0 ]; then
  # #15372 : un run vert LEVE le commentaire bloquant precedent en place.
  if ! GH_TOKEN="${GH_TOKEN}" python3 scripts/ci/guard_comment_upsert.py \
    --pr "$PR_NUMBER" \
    --marker '<!-- lane-claim-conflict -->' \
    --lift --note "aucun claim frais d'une autre lane sur un renvoi fermant au re-passage." \
    >/dev/null 2>&1; then
    echo "::warning::lane_claim lift failed (commentaire bloquant possiblement perime)"
  fi
  echo "Aucun claim frais d'une autre lane sur un renvoi fermant -- job passes."
  exit 0
fi

REASON=$(python3 -c "import json; print(json.load(open('/tmp/verdict.json')).get('reason','unknown'))" 2>/dev/null || echo "unknown")
echo "::error::collision de lane sur une reference fermante: $REASON"

# #15372 : upsert -- pas de mur de verdicts perimes (re-run compris).
cat > /tmp/lane_claim_blocked.md <<EOF
<!-- lane-claim-conflict -->
**Collision de lane sur une reference fermante (#10223).**

${REASON}

Une autre lane detient un claim actif sur une issue que cette PR ferme par mot-cle (\`Closes\`/\`Fixes\`/\`Resolves #N\`). Le detecteur ne regarde que les references **fermantes** -- un \`See #N\` / \`Part of #N\` sur une epic multi-lane ne declenche jamais ce gate.

Les **trois sorties** pour passer ce gate :
- la lane detenrice **relache** son claim (\`[RELEASED] lane <machine:workspace>\` sur l'issue concernee), ou
- le **coordinateur ecrit** un arbitrage (\`[OVERRIDE] lane <cette lane>\` -- c'est la trace qui rend l'override mecaniquement traçable, #10223 Tache 2), ou
- le claim atteint **48 h** de peremption (le protocole re-arbitre les claims d'une lane inactive).

Voir #10223 et \`lane-claim-protocol.md\`.
EOF
if ! GH_TOKEN="${GH_TOKEN}" python3 scripts/ci/guard_comment_upsert.py \
  --pr "$PR_NUMBER" \
  --marker '<!-- lane-claim-conflict -->' \
  --body-file /tmp/lane_claim_blocked.md \
  >/dev/null 2>&1; then
  echo "::warning::lane_claim upsert failed (commentaire bloquant non pose)"
fi

exit 1
)

main() {
  local rc=0
  for id in tag_required prev_guard close_keyword adjacency lane_claim; do
    echo "::group::organe $id"
    rc=0
    run_organ "$id" || rc=$?
    echo "::endgroup::"
    if [ "$rc" -ne 0 ]; then
      FAILED="$FAILED $id"
    fi
  done
  if [ -n "$FAILED" ]; then
    echo "::error::Organes de body bloquants en echec :$FAILED"
    exit 1
  fi
  echo "Organes de body: tous verts."
}

main
