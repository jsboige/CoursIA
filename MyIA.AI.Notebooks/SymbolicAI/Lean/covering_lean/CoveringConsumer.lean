import Covering

-- Audit d'axiomes du certificat de borne inferieure, execute par le
-- consommateur local. Le carnet Lean-43 lit cette sortie : elle est la preuve
-- que la preuve importee ne repose sur aucun axiome hors de la liste autorisee
-- par le comparateur amont (propext, Quot.sound, Classical.choice).
#print axioms Covering.covering_24_14_4
#print axioms Covering.covering_25_15_5
