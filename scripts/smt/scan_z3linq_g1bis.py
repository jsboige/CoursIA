#!/usr/bin/env python3
"""
scan_z3linq_g1bis.py -- verdict ferme G1-bis pour 18 PRs endjin/Z3.Linq TBD.

Sortie : tableau JSON par PR avec verdict ferme + chemins du fork concernes
(`solutions/Z3.Linq/*.cs` au pin `e09dae6` du submodule
`MyIntelligenceAgency/Z3.Linq`). Le verdict definitif (REDONDANT/DIVERGENT/
NOUVEAU-POUR-NOUS) demande une lecture du diff et du code fork -- ce script
ENCODE les verdicts (la lecture est faite main, l'automation rejoue pour audit).

EPIC parent : #14169 (Z3.Linq amont se remet en mouvement)
Sous-grain   : #16053 (G1-bis trancher REDONDANT/DIVERGENT/NOUVEAU-POUR-NOUS)
Lane         : myia-po-2027:CoursIA-2
Fork pinné   : MyIntelligenceAgency/Z3.Linq @ e09dae6 (cf body issue #16053)
               ; le submodule CoursIA pointe sur 20984bfd (post-fix DateTime #14445)
               ; G1-bis mesure contre e09dae6 strictement, l'ecart note.

Trois verdicts possibles (capacites) + un verdict de perimetre :
  REDONDANT       -- la capacite existe deja dans le fork e09dae6.
  DIVERGENT       -- la capacite existe avec une semantique differente
                      (amont a evolue au-dela, ou notre bug latent).
  NOUVEAU-POUR-NOUS -- l'amont livre une capacite qu'on n'a pas.
  HORS-SCOPE      -- la PR ne touche pas de capacite applicative (packaging,
                      doc XML, infra) ; ne releve pas de la posture de fork.

Usage :
    python scripts/smt/scan_z3linq_g1bis.py --out JSON

Rapport G1-bis depose au dashboard RooSync workspace CoursIA-2
(harness-hygiene.md : rapports = dashboard, jamais dans l'arbre).
"""
import argparse
import json
import sys
from pathlib import Path


# 18 PRs TBD du scanner G1 (PR #16052)
# Bloc modernisation-build : 2 (#47, #94)
# Bloc marshalling-sortes : 12 (#73, #77, #79, #80, #81, #84, #88, #90, #91, #92, #93, #95)
# Bloc resolution-semantique : 4 (#86, #96, #98, #99)
TBD_PRS = [47, 94, 73, 77, 79, 80, 81, 84, 88, 90, 91, 92, 93, 95, 86, 96, 98, 99]


# Verdicts first-hand (lecture diff amont + grep fork e09dae6)
# Cle : PR number amont endjin/Z3.Linq
# Valeur : dict avec verdict, fichiers fork concernes (path:ligne), note courte
#   e09dae6_str : reference SHA du submodule fork (note d'ecart avec 20984bfd)
VERDICTS = {
    # -- Bloc modernisation-build --
    47: {
        "verdict": "REDONDANT",
        "fork_paths": ["solutions/Z3.Linq/ExpressionVisitor.cs:215-235"],
        "note": (
            "PR #47 = bump MiaPlaza.ExpressionUtils 1.2.0 -> 1.3.1 et adaptation "
            "au breaking de PartialEval(Expression). Notre fork a aussi besoin du bump "
            "(cf c.8924, le submodule CoursIA pointe sur 1.2.0 actuellement). "
            "Adaptation `Expression.Lambda(...).Body` : memes 11 lignes sur la meme "
            "methode VisitCall/PartialEval. A l'identique, pas de port necessaire."
        ),
        "sub_issue_action": "Aucune. Le bump de la dep est une action tierce ; notre port s'applique quand on bumpe.",
    },
    94: {
        "verdict": "HORS-SCOPE",
        "fork_paths": ["solutions/Directory.Build.props", "solutions/Z3.Linq/*.csproj"],
        "note": (
            "PR #94 = generation et validation de la doc XML (+165 / -25 sur 13 fichiers, "
            "mesure API 2026-09-13). Les fichiers touches sont Directory.Build.props, les "
            "*.csproj, et des fichiers d'attributs (TheoremGlobalRewriterAttribute, "
            "TheoremVariableTypeMappingAttribute, etc.) : aucun fichier de capacite "
            "applicatif (Theorem.cs/ExpressionVisitor.cs ne sont touches que pour des "
            "commentaires XML doc, pas du code). C'est du packaging projet, pas une "
            "capacite de la lib. Capacite absente = HORS-SCOPE, distinct du REDONDANT "
            "(qui suppose une capacite deja portee)."
        ),
        "sub_issue_action": "Aucune. Packaging projet, hors scope fonctionnel ; ne releve pas de la posture de fork de l'EPIC #14169.",
    },
    # -- Bloc marshalling-sortes --
    73: {
        "verdict": "DIVERGENT",
        "fork_paths": ["solutions/Z3.Linq/Theorem.cs:507", "solutions/Z3.Linq/Theorem.cs:516"],
        "note": (
            "PR #73 = peupler les symboles que le solveur laisse non-interpretes "
            "(Model.Eval avec completion). 4 sites d'evaluation remontes dans un helper "
            "EvaluateWithCompletion. Notre fork (e09dae6) evalue sans completion : "
            "le cas `where t.X1 == t.X1` leve InvalidCastException, le cas "
            "`where t.X1 > 0 || t.X1 <= 0` aussi (mesure ai-01 #14444 body §3). "
            "A e09dae6 strictement : DIVERGENT, fix non applique. "
            "A 20984bfd (post-fix DateTime) : fix DateTime applique mais pas le "
            "EvaluateWithCompletion -- DIVERGENT maintenu pour le fix #73. "
            "Test mesure reproduit le defaut : `t.X1 == t.X1` -> crash."
        ),
        "sub_issue_action": (
            "Sous-issue G3-merger PR #73 (cherry-pick ou re-implementation selon "
            "le diff a appliquer a Theorem.cs sites 445/471/507/634)."
        ),
    },
    77: {
        "verdict": "REDONDANT",
        "fork_paths": ["solutions/Z3.Linq/ExpressionVisitor.cs:866"],
        "note": (
            "PR #77 = MkReal rendu avec InvariantCulture (cite leur #52). "
            "Notre fork (e09dae6) a DEJA `Convert.ToString(val, "
            "CultureInfo.InvariantCulture)` a ExpressionVisitor.cs:866, "
            "cite par notre #4616 (convergence independante sans contact, "
            "signalee par ai-01 dans le G1 historique #14444 body §3.2). "
            "Aucune action requise, mais voir note."
        ),
        "sub_issue_action": "Aucune. Capacite deja portee (cf #4616).",
    },
    79: {
        "verdict": "DIVERGENT",
        "fork_paths": ["solutions/Z3.Linq/Theorem.cs:445"],
        "note": (
            "PR #79 = lire la valeur d'un champ de collection. 5 +/- 2 sur Theorem.cs. "
            "A e09dae6 le site 445 lit un element de tableau mais ne distingue pas "
            "champ scalaire vs champ collection (PR #79 specialise ce cas). "
            "DIVERGENT -- l'amont specialise la lecture par kind ; notre fork a un seul "
            "code path qui marche pour les 2 cas simples."
        ),
        "sub_issue_action": (
            "Sous-issue G3-merger PR #79 (specialisation du read-back par kind)."
        ),
    },
    80: {
        "verdict": "DIVERGENT",
        "fork_paths": ["solutions/Z3.Linq/Theorem.cs:898"],
        "note": (
            "PR #80 = lire un symbole float comme un float. 2 +/- 2 sur Theorem.cs. "
            "A e09dae6 le site 898 gere TypeCode.Single via RealExpr->RatNum "
            "(pattern identique a double/decimal). Le fix PR #80 specialises "
            "pour eviter un ArgumentException sur float. DIVERGENT mineur."
        ),
        "sub_issue_action": (
            "Sous-issue G3-investigation (lit-on vraiment float via ce path ?)."
        ),
    },
    81: {
        "verdict": "DIVERGENT",
        "fork_paths": ["solutions/Z3.Linq/Theorem.cs:471"],
        "note": (
            "PR #81 = lire l'element decimal que la boucle a selectionne. "
            "A e09dae6 le site 471 fait l'evaluation du tableau ENTIER, pas de "
            "l'element selectionne (cite par PR #73 -- site sans couverture test). "
            "DIVERGENT -- bug reconnu cote amont #55."
        ),
        "sub_issue_action": (
            "Sous-issue G3-merger PR #81 (correction du site 471 + tests)."
        ),
    },
    84: {
        "verdict": "DIVERGENT",
        "fork_paths": ["solutions/Z3.Linq/Theorem.cs:668", "solutions/Z3.Linq/Theorem.cs:904"],
        "note": (
            "PR #84 = lire un DateTime en UTC. A e09dae6, Theorem.cs:668 et :904 "
            "appellent `DateTime.FromFileTime` qui rend une date LOCALE (Kind=Local) "
            "pour un input UTC. Mesure ai-01 #14444 body §3.3 : input 12:00Z ressort "
            "13:00+01:00 (instant preserve mais Ticks decales du fuseau). "
            "Bug latent a e09dae6. CORRIGE dans 20984bfd (cf notre PR #27 fix #14445). "
            "DIVERGENT : deja partiellement absorbe par notre fix DateTime, "
            "reste a verifier que la lecture est bien UTC post-fix."
        ),
        "sub_issue_action": (
            "Sous-issue G5-verification post-bump (relancer notebooks Z3-Linq2Z3 "
            "sur 20984bfd pour verifier que l'aller-retour DateTime est OK)."
        ),
    },
    88: {
        "verdict": "DIVERGENT",
        "fork_paths": ["solutions/Z3.Linq/Theorem.cs:437", "solutions/Z3.Linq/Theorem.cs:496", "solutions/Z3.Linq/Theorem.cs:591", "solutions/Z3.Linq/Theorem.cs:660", "solutions/Z3.Linq/Theorem.cs:898"],
        "note": (
            "PR #88 = faire marcher les symboles short et enum. "
            "A e09dae6, Theorem.cs a 5 sites qui gerent TypeCode.Int16 (437/496/591/660/898). "
            "Mais le PR #88 signale que ces sites ne couvrent pas tous les cas "
            "(enum notamment). DIVERGENT mineur."
        ),
        "sub_issue_action": (
            "Sous-issue G3-investigation (les sites Int16 du fork couvrent-ils les enum ?)."
        ),
    },
    90: {
        "verdict": "DIVERGENT",
        "fork_paths": ["solutions/Z3.Linq/Theorem.cs:205-235", "solutions/Z3.Linq/Theorem.cs:448"],
        "note": (
            "PR #90 = donner aux collections les memes sortes qu'aux scalaires "
            "(passage d'un mapping de collection a une sharing des sorts). "
            "A e09dae6, Theorem.cs:205-235 declare chaque collection avec son "
            "propre domain/range sort (mapping par element type) ; le PR #90 "
            "partage le sort avec le mapping scalaire. 61 +/- 115 sur Theorem.cs, "
            "refactor structurel. DIVERGENT -- comportement peut changer sur "
            "contraintes inter-arrays."
        ),
        "sub_issue_action": (
            "Sous-issue G3-merger PR #90 (refactor + validation notebooks 17/18)."
        ),
    },
    91: {
        "verdict": "DIVERGENT",
        "fork_paths": ["solutions/Z3.Linq/Theorem.cs:300-330"],
        "note": (
            "PR #91 = marshaler les environnements anonymes comme les autres formes. "
            "A e09dae6, les environments anonymes passent par un chemin distinct "
            "(Theorem.cs:300-330). Le PR #91 specialise le marshalling pour les "
            "rendre compatibles avec les autres formes. 28 +/- 26 sur Theorem.cs. "
            "DIVERGENT -- marshalling partiellement equivalent."
        ),
        "sub_issue_action": (
            "Sous-issue G3-investigation (les envs anonymes passent dans nos usages ?)."
        ),
    },
    92: {
        "verdict": "DIVERGENT",
        "fork_paths": ["solutions/Z3.Linq/ExpressionVisitor.cs:255-270"],
        "note": (
            "PR #92 = choisir les conversions numeriques par sort, pas par type cible. "
            "A e09dae6, ExpressionVisitor.cs:255-270 fait des conversions par type "
            "(int -> IntNum, decimal -> RatNum). Le PR #92 inverse la logique : "
            "regarder le sort Z3 d'abord. 28 +/- 14 sur ExpressionVisitor.cs. "
            "DIVERGENT -- changement de politique de conversion."
        ),
        "sub_issue_action": (
            "Sous-issue G3-investigation (nos usages beneficient-ils du tri par sort ?)."
        ),
    },
    93: {
        "verdict": "DIVERGENT",
        "fork_paths": ["solutions/Z3.Linq/Z3Context.cs:155-185", "solutions/Z3.Linq/Theorem.cs"],
        "note": (
            "PR #93 = dimensionner les collections depuis l'instance passee a NewTheorem. "
            "A e09dae6, le code prend la Count() de l'instance mais pas systematiquement "
            "(certains envs ne pre-size pas). 65 +/- 31 sur Theorem.cs + 24 +/- 8 sur "
            "Z3Context.cs. DIVERGENT -- comportement partiellement couvert."
        ),
        "sub_issue_action": (
            "Sous-issue G3-investigation (nos envs sont-ils tous pre-sized ?)."
        ),
    },
    95: {
        "verdict": "REDONDANT",
        "fork_paths": ["solutions/Z3.Linq/ExpressionVisitor.cs:868"],
        "note": (
            "PR #95 = encoder un DateTime en ticks (pas en FileTimeUtc). "
            "Notre fork a e09dae6 utilise `MkInt(((DateTime)val).ToFileTimeUtc())` "
            "(l.868) -- c'est le bug #14445. Le fix PR #95 encode en ticks. "
            "A 20984bfd (post-fix DateTime) : notre PR #27 a absorbe le fix "
            "PR #95 (cite dans le commit `f0da578 merge: DateTime round-trip via "
            "UTC ticks (port endjin#95)`). REDONDANT -- deja absorbe."
        ),
        "sub_issue_action": "Aucune. Capacite absorbee par #27 / #14445.",
    },
    # -- Bloc resolution-semantique --
    86: {
        "verdict": "REDONDANT",
        "fork_paths": ["solutions/Z3.Linq/Explanation.cs", "solutions/Z3.Linq/Theorem.cs:377-400"],
        "note": (
            "PR #86 = rapporter la satisfiabilite separement de la solution. "
            "Notre fork a DEJA `Explanation(SolveStatus, core)` dans Explanation.cs "
            "avec 4 statuts (Unsatisfiable/Satisfiable/Unknown/Timeout) et "
            "l'UNSAT-core deja livre (cf #13995 -- port deja fait en aval). "
            "Cite par ai-01 dans le G1 historique #14444 body §2 (et #14444 "
            "merge). REDONDANT -- capacite deja portee."
        ),
        "sub_issue_action": "Aucune. Capacite deja portee (cf #13995 et #14444 body).",
    },
    96: {
        "verdict": "NOUVEAU-POUR-NOUS",
        "fork_paths": [],
        "note": (
            "PR #96 = borner un solve et dire 'Z3 n'a pas pu decider'. "
            "A e09dae6 Theorem.cs:455 (solver check), pas de notion de SolveLimit, "
            "pas de TheoremUndecidedException.cs (le fichier est cree par PR #96). "
            "Pas de timeout/limite expose dans l'API publique. NOUVEAU-POUR-NOUS "
            "-- capacite absente, port souhaitable pour les solveurs longs."
        ),
        "sub_issue_action": (
            "Sous-issue G4-port PR #96 (ajouter TheoremUndecidedException, "
            "parametre timeout au solve, integration dans ISolveable + "
            "SolveableExtensions)."
        ),
    },
    98: {
        "verdict": "DIVERGENT",
        "fork_paths": ["solutions/Z3.Linq/Theorem.cs:428"],
        "note": (
            "PR #98 = borner chaque symbole entier au range de son type "
            "(e.g. int -> -2^31..2^31-1). 110 +/- 11 sur Theorem.cs. "
            "A e09dae6, Theorem.cs:428 declare les int en Int (pas de bornes). "
            "Le PR #98 ajoute des assertions de bornes par type. "
            "DIVERGENT -- politique de declaration, peut affecter les perfs."
        ),
        "sub_issue_action": (
            "Sous-issue G3-investigation (les bornes sont-elles desirees pour nos usages ?)."
        ),
    },
    99: {
        "verdict": "DIVERGENT",
        "fork_paths": ["solutions/Z3.Linq/ExpressionVisitor.cs"],
        "note": (
            "PR #99 = traduire les ternaires + arreter de crasher sur bitwise "
            "et modulo reel. 79 +/- 31 sur ExpressionVisitor.cs. "
            "A e09dae6, pas de traduction des expressions ternaires "
            "(C# `condition ? a : b`), bitwise (`a & b`) et modulo reel. "
            "Couvert par ai-01 dans le G1 historique #14444 (lecture profonde). "
            "DIVERGENT -- 3 patterns non traduits actuellement."
        ),
        "sub_issue_action": (
            "Sous-issue G3-merger PR #99 (3 patterns de traduction + tests)."
        ),
    },
}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", type=Path, default=None, help="Output JSON path (default: stdout)")
    args = ap.parse_args()

    rows = []
    for n in TBD_PRS:
        if n not in VERDICTS:
            print(f"# PR #{n} : verdict missing", file=sys.stderr)
            sys.exit(1)
        v = VERDICTS[n]
        rows.append({
            "number": n,
            "verdict": v["verdict"],
            "fork_paths": v["fork_paths"],
            "note": v["note"],
            "sub_issue_action": v["sub_issue_action"],
        })

    summary = {
        "REDONDANT": sum(1 for r in rows if r["verdict"] == "REDONDANT"),
        "DIVERGENT": sum(1 for r in rows if r["verdict"] == "DIVERGENT"),
        "NOUVEAU-POUR-NOUS": sum(1 for r in rows if r["verdict"] == "NOUVEAU-POUR-NOUS"),
        "HORS-SCOPE": sum(1 for r in rows if r["verdict"] == "HORS-SCOPE"),
    }

    out = {
        "epic": "#14169",
        "sub_grain": "#16053 (G1-bis)",
        "lane": "myia-po-2027:CoursIA-2",
        "fork_pinned_target": "MyIntelligenceAgency/Z3.Linq @ e09dae6",
        "fork_pinned_submodule": "20984bfd (post-fix DateTime #14445)",
        "reading_method": (
            "Verdicts first-hand : lecture `gh pr diff --repo endjin/Z3.Linq <N>` "
            "+ grep `solutions/Z3.Linq/*.cs` au pin e09dae6 (submodule checkoute "
            "temporairement a e09dae6, pas committe). G1 historique #14444 "
            "(MERGED 2026-09-03) couvre 4 PRs en lecture profonde (#77, #86, "
            "#95, #99) -- coherence verifiee."
        ),
        "prs_total": len(rows),
        "verdict_summary": summary,
        "rows": rows,
    }

    if args.out:
        args.out.write_text(json.dumps(out, indent=2, ensure_ascii=False))
        print(f"Wrote {len(rows)} rows to {args.out}", file=sys.stderr)
    else:
        print(json.dumps(out, indent=2, ensure_ascii=False))

    return 0


if __name__ == "__main__":
    sys.exit(main())
