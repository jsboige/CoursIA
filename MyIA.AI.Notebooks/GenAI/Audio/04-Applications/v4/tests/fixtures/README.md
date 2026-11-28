# Fixtures du harnais v4

Ces fichiers sont des **captures**, pas des charges inventées. Leur forme est la
preuve : un test écrit contre une charge synthétique ne voit pas la dérive d'un
contrat de service.

## `zonos3_controls_studio_mect60k_x10.json`

Réponse de `GET /v2/controls` du service `tts-zonos3`, capturée le
**2026-11-27 à 17:34:44 UTC**.

| --- | --- |
|---|---|
| Capture | `GET http://127.0.0.1:1919/v2/controls`, conteneur `tts-zonos3` |
| Bundle servi | `studio_mect60k_x10` |
| Runtime (code) | `github.com/Zyphra/ZONOS3-Mini` @ `a50e14117d99181ba7f28047b451ba03ba1a09a9` |
| Poids | `huggingface.co/Zyphra/ZONOS3-Mini` @ `2921b8821772b0bd10a04456863d21abf9d2f283` |
| Taille | 38 969 octets |
| SHA-256 | `4191632b182d5188656f4824a3412cb460dc2d96a2585296a09bffaaff813ad8` |
| Forme | 65 `directions`, 14 `sets`, 25 `ui.controls`, `embedding_dim` 192, `steer_release` `null` |

Les vecteurs sont retirés : chaque entrée de `directions` garde `kind`, `norm`,
`set` et `space`, mais perd sa clé `vector` (192 flottants par direction, sans
usage dans les tests et sans valeur de preuve). Le reste de la charge est
**inchangé** ; les clés sont simplement triées à l'écriture.

### Pourquoi ces champs comptent

- `ui.controls` porte la correspondance publiée entre un contrôle nommé et les
  directions qu'il dose (`map`), sa fenêtre d'usage (`range`) et sa fenêtre
  sûre (`safe`). `v4.zonos3_steering` en tire `span` (demi-largeur du côté
  visé) et `unit` (multiplicateur du `map`) : c'est ce qui a remplacé une
  symétrie supposée sur le jeu `mood`.
- `sets.<jeu>.calibration` porte la dose neutre d'un jeu. Seul `mood` en publie
  une ; les treize autres jeux rendent `null`, donc un neutre de `0.0` — et non
  la valeur de `mood` (4.0).
- `directions` liste ce que le bundle **sert** réellement. Une direction
  déclarée par la table de correspondance mais absente d'ici dégrade l'axe au
  lieu de l'envoyer.

### Régénérer

Le service doit tourner (`docker compose up -d` dans
`docker-configurations/services/tts-zonos3`), puis :

```python
import json
from pathlib import Path

import requests

raw = requests.get("http://127.0.0.1:1919/v2/controls", timeout=30).json()
for entry in raw.get("directions", {}).values():
    if isinstance(entry, dict):
        entry.pop("vector", None)
out = Path("tests/fixtures/zonos3_controls_studio_mect60k_x10.json")
out.write_text(
    json.dumps(raw, indent=1, ensure_ascii=False, sort_keys=True) + "\n",
    encoding="utf-8",
)
```

**Une régénération qui change le SHA-256 est un fait, pas un détail de
plomberie** : le bundle, le runtime ou les poids ont bougé. Relire alors
`v4.zonos3_steering.AXIS_MAPPINGS` contre la nouvelle charge avant de mettre la
fixture à jour — c'est exactement le test
`test_axis_mapping_uses_the_windows_the_studio_publishes` qui doit rougir le
premier si la correspondance ne tient plus.

Le nom du fichier porte le bundle : un nouveau bundle se capture dans un
**nouveau** fichier, il n'écrase pas celui-ci.

## `a0c_controls.json`

Charge du banc A0C (`#19695`, `#17586`) : le texte de référence de *Boule de
Suif* (Maupassant, 1880, domaine public) et quatre rendus, chacun avec les
trois hypothèses ASR du banc (`tiny`, `large-v3`, `large-v3-turbo`). Il fixe
les comptes de spans manquants par modèle pour
`v4/p7_verify.py::_voted_missing_spans`. Aucune capture réseau ici : c'est un
relevé de banc conservé tel quel.
