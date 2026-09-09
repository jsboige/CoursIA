# Audit job deaths (issue #15055)

Jobs morts non-skips analyses : **252** | morts infrastructurelles : **6** (NO_RUNNER_ACQUIRED=4, RUNNER_LOST_COMM=2) | REAL_STEP_FAILURE=38 | AUTRES=208

| Run | Workflow | Job | Classe | Runner | Steps | Duree | SHA |
|---|---|---|---|---|---|---|---|
| [34168702151](https://github.com/jsboige/CoursIA/actions/runs/34168702151) | Quarto Pages Deploy | Build Quarto site | **REAL_STEP_FAILURE** | myia-ai-01-linux-docker-4 | 9/15 | 16m38s | 9754c8ce25 |
| [34068931097](https://github.com/jsboige/CoursIA/actions/runs/34068931097) | Notebook Validation | validate-notebooks | **RUNNER_LOST_COMM** | myia-po-2024-linux-docker-5 | 4/8 | 10m01s | 501a30a06e |
| [34066220916](https://github.com/jsboige/CoursIA/actions/runs/34066220916) | Secret Scan | Gitleaks secret scanner | **NO_RUNNER_ACQUIRED** | (none) | 0/0 | 3m03s | 612448b8e8 |
| [34059521648](https://github.com/jsboige/CoursIA/actions/runs/34059521648) | Scripts & Notebook-Tools Tests | Scripts Tests (CPU) | **NO_RUNNER_ACQUIRED** | (none) | 0/0 | 3m02s | 6af1fe07f0 |
| [34043004719](https://github.com/jsboige/CoursIA/actions/runs/34043004719) | Quarto Pages Deploy | Build Quarto site | **RUNNER_LOST_COMM** | myia-ai-01-wsl-6 | 6/12 | 52m18s | 766a9100de |
| [34023579011](https://github.com/jsboige/CoursIA/actions/runs/34023579011) | Quarto Pages Deploy | Build Quarto site | **REAL_STEP_FAILURE** | myia-ai-01-wsl-7 | 0/1 | 10m27s | b8ebe6dd83 |
| [34023578975](https://github.com/jsboige/CoursIA/actions/runs/34023578975) | Notebook Validation | validate-notebooks | **REAL_STEP_FAILURE** | myia-ai-01-wsl-5 | 0/1 | 9m57s | b8ebe6dd83 |
| [34023579059](https://github.com/jsboige/CoursIA/actions/runs/34023579059) | markdown-rendering-guard | markdown-rendering guard (main-repo notebooks) | **REAL_STEP_FAILURE** | myia-po-2024-linux-docker-6 | 0/1 | 7m26s | b8ebe6dd83 |
| [34023578962](https://github.com/jsboige/CoursIA/actions/runs/34023578962) | banner-guard | probeAddresses banner guard (main-repo notebooks) | **REAL_STEP_FAILURE** | myia-ai-01-linux-docker-2 | 0/1 | 10m00s | b8ebe6dd83 |
| [34023578993](https://github.com/jsboige/CoursIA/actions/runs/34023578993) | Validation Matrix | validate | **NO_RUNNER_ACQUIRED** | (none) | 0/0 | 3m03s | b8ebe6dd83 |
| [34023578952](https://github.com/jsboige/CoursIA/actions/runs/34023578952) | Secret Scan | Gitleaks secret scanner | **NO_RUNNER_ACQUIRED** | (none) | 0/0 | 3m02s | b8ebe6dd83 |
| [34023578952](https://github.com/jsboige/CoursIA/actions/runs/34023578952) | Secret Scan | Gitleaks positive controls (#10143) | **REAL_STEP_FAILURE** | myia-ai-01-wsl-3 | 0/1 | 7m00s | b8ebe6dd83 |
| [34023327143](https://github.com/jsboige/CoursIA/actions/runs/34023327143) | Secret Scan | Gitleaks positive controls (#10143) | **REAL_STEP_FAILURE** | myia-ai-01-linux-docker-7 | 0/1 | 9m58s | c5dc1efc00 |
| [34023327156](https://github.com/jsboige/CoursIA/actions/runs/34023327156) | Validation Matrix | validate | **REAL_STEP_FAILURE** | myia-ai-01-linux-docker-4 | 0/1 | 8m02s | c5dc1efc00 |
| [34023327163](https://github.com/jsboige/CoursIA/actions/runs/34023327163) | Notebook Validation | validate-notebooks | **REAL_STEP_FAILURE** | myia-ai-01-linux-docker-4 | 0/1 | 7m56s | c5dc1efc00 |
| [34023327146](https://github.com/jsboige/CoursIA/actions/runs/34023327146) | banner-guard | probeAddresses banner guard (main-repo notebooks) | **REAL_STEP_FAILURE** | myia-ai-01-wsl-4 | 0/1 | 7m57s | c5dc1efc00 |
| [34020364713](https://github.com/jsboige/CoursIA/actions/runs/34020364713) | Secret Scan | Gitleaks positive controls (#10143) | **REAL_STEP_FAILURE** | myia-ai-01-linux-docker-2 | 0/1 | 8m14s | d0cd74fc89 |
| [34020275355](https://github.com/jsboige/CoursIA/actions/runs/34020275355) | Quarto Pages Deploy | Build Quarto site | **REAL_STEP_FAILURE** | myia-ai-01-linux-docker-1 | 0/1 | 8m16s | 51922bf6a9 |
| [34020275365](https://github.com/jsboige/CoursIA/actions/runs/34020275365) | Scripts & Notebook-Tools Tests | Scripts Tests (CPU) | **REAL_STEP_FAILURE** | myia-ai-01-wsl-8 | 0/1 | 7m45s | 51922bf6a9 |
| [34020239674](https://github.com/jsboige/CoursIA/actions/runs/34020239674) | Lean Conway CI | conway target-coverage | **REAL_STEP_FAILURE** | myia-ai-01-linux-docker-4 | 0/1 | 8m23s | 0ea8acb2b9 |
| [34020183456](https://github.com/jsboige/CoursIA/actions/runs/34020183456) | Scripts & Notebook-Tools Tests | Scripts Tests (CPU) | **REAL_STEP_FAILURE** | myia-ai-01-linux-docker-4 | 0/1 | 6m48s | 4389ca45d8 |
| [34020183502](https://github.com/jsboige/CoursIA/actions/runs/34020183502) | Secret Scan | Gitleaks positive controls (#10143) | **REAL_STEP_FAILURE** | myia-po-2024-linux-docker-7 | 0/1 | 10m32s | 4389ca45d8 |
| [34010936295](https://github.com/jsboige/CoursIA/actions/runs/34010936295) | Secret Scan | Gitleaks positive controls (#10143) | **REAL_STEP_FAILURE** | myia-ai-01-linux-docker-4 | 0/1 | 9m48s | 7a90f326db |
| [34006683871](https://github.com/jsboige/CoursIA/actions/runs/34006683871) | Secret Scan | Gitleaks positive controls (#10143) | **REAL_STEP_FAILURE** | myia-ai-01-linux-docker-6 | 0/1 | 7m29s | 251d43b83b |
| [34006683851](https://github.com/jsboige/CoursIA/actions/runs/34006683851) | markdown-rendering-guard | markdown-rendering guard (main-repo notebooks) | **REAL_STEP_FAILURE** | myia-ai-01-linux-docker-8 | 0/1 | 7m21s | 251d43b83b |
| [34006683843](https://github.com/jsboige/CoursIA/actions/runs/34006683843) | Notebook Validation | validate-notebooks | **REAL_STEP_FAILURE** | myia-po-2024-linux-docker-4 | 0/1 | 7m19s | 251d43b83b |
| [34006683845](https://github.com/jsboige/CoursIA/actions/runs/34006683845) | Quarto Pages Deploy | Build Quarto site | **REAL_STEP_FAILURE** | myia-ai-01-linux-docker-5 | 0/1 | 10m09s | 251d43b83b |
| [34006683839](https://github.com/jsboige/CoursIA/actions/runs/34006683839) | banner-guard | probeAddresses banner guard (main-repo notebooks) | **REAL_STEP_FAILURE** | myia-ai-01-wsl-2 | 0/1 | 7m18s | 251d43b83b |
| [34006683874](https://github.com/jsboige/CoursIA/actions/runs/34006683874) | Validation Matrix | validate | **REAL_STEP_FAILURE** | myia-ai-01-linux-docker-4 | 0/1 | 8m18s | 251d43b83b |
| [34006318693](https://github.com/jsboige/CoursIA/actions/runs/34006318693) | Scripts & Notebook-Tools Tests | Scripts Tests (CPU) | **REAL_STEP_FAILURE** | myia-ai-01-linux-docker-6 | 0/1 | 8m31s | 1a51d65513 |
| [34005835628](https://github.com/jsboige/CoursIA/actions/runs/34005835628) | banner-guard | probeAddresses banner guard (main-repo notebooks) | **REAL_STEP_FAILURE** | myia-ai-01-wsl-7 | 0/1 | 7m45s | dd91b3a820 |
| [34005835629](https://github.com/jsboige/CoursIA/actions/runs/34005835629) | Notebook Validation | validate-notebooks | **REAL_STEP_FAILURE** | myia-po-2024-linux-docker-8 | 0/1 | 7m55s | dd91b3a820 |
| [34005835653](https://github.com/jsboige/CoursIA/actions/runs/34005835653) | markdown-rendering-guard | markdown-rendering guard (main-repo notebooks) | **REAL_STEP_FAILURE** | myia-ai-01-wsl-5 | 0/1 | 9m53s | dd91b3a820 |
| [34005835618](https://github.com/jsboige/CoursIA/actions/runs/34005835618) | Validation Matrix | validate | **REAL_STEP_FAILURE** | myia-po-2024-linux-docker-1 | 0/1 | 7m41s | dd91b3a820 |
| [34004704691](https://github.com/jsboige/CoursIA/actions/runs/34004704691) | Scripts & Notebook-Tools Tests | Scripts Tests (CPU) | **REAL_STEP_FAILURE** | myia-po-2024-linux-docker-4 | 0/1 | 7m24s | eddd68e4bf |
| [34004704682](https://github.com/jsboige/CoursIA/actions/runs/34004704682) | Secret Scan | Gitleaks positive controls (#10143) | **REAL_STEP_FAILURE** | myia-ai-01-wsl-5 | 0/1 | 9m32s | eddd68e4bf |
| [34004704669](https://github.com/jsboige/CoursIA/actions/runs/34004704669) | ML & Prover Tests | ML Pipeline Tests (CPU) | **REAL_STEP_FAILURE** | myia-po-2024-linux-docker-7 | 0/1 | 8m32s | eddd68e4bf |
| [34004548493](https://github.com/jsboige/CoursIA/actions/runs/34004548493) | Quarto Pages Deploy | Build Quarto site | **REAL_STEP_FAILURE** | myia-ai-01-wsl-7 | 0/1 | 7m34s | e568f782b7 |
| [34004548450](https://github.com/jsboige/CoursIA/actions/runs/34004548450) | markdown-rendering-guard | markdown-rendering guard (main-repo notebooks) | **REAL_STEP_FAILURE** | myia-ai-01-linux-docker-8 | 0/1 | 7m51s | e568f782b7 |
| [34004548438](https://github.com/jsboige/CoursIA/actions/runs/34004548438) | Notebook Validation | validate-notebooks | **REAL_STEP_FAILURE** | myia-ai-01-wsl-1 | 0/1 | 7m59s | e568f782b7 |
| [34004548423](https://github.com/jsboige/CoursIA/actions/runs/34004548423) | Validation Matrix | validate | **REAL_STEP_FAILURE** | myia-po-2024-linux-docker-1 | 0/1 | 8m09s | e568f782b7 |
| [34004548426](https://github.com/jsboige/CoursIA/actions/runs/34004548426) | banner-guard | probeAddresses banner guard (main-repo notebooks) | **REAL_STEP_FAILURE** | myia-po-2024-linux-docker-4 | 0/1 | 8m15s | e568f782b7 |
| [34004401512](https://github.com/jsboige/CoursIA/actions/runs/34004401512) | Secret Scan | Gitleaks positive controls (#10143) | **REAL_STEP_FAILURE** | myia-ai-01-wsl-8 | 0/1 | 7m57s | 6c11c12d2a |
| [34004401558](https://github.com/jsboige/CoursIA/actions/runs/34004401558) | Scripts & Notebook-Tools Tests | Scripts Tests (CPU) | **REAL_STEP_FAILURE** | myia-ai-01-wsl-7 | 0/1 | 9m15s | 6c11c12d2a |
| [34168791762](https://github.com/jsboige/CoursIA/actions/runs/34168791762) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 9m19s | ae7fe3b8a3 |
| [34168702080](https://github.com/jsboige/CoursIA/actions/runs/34168702080) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 1m35s | 9754c8ce25 |
| [34168684272](https://github.com/jsboige/CoursIA/actions/runs/34168684272) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m22s | f5b4603016 |
| [34168684318](https://github.com/jsboige/CoursIA/actions/runs/34168684318) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m22s | f5b4603016 |
| [34168684265](https://github.com/jsboige/CoursIA/actions/runs/34168684265) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m22s | f5b4603016 |
| [34168684228](https://github.com/jsboige/CoursIA/actions/runs/34168684228) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | (none) | 0/0 | 0m20s | f5b4603016 |
| [34168684228](https://github.com/jsboige/CoursIA/actions/runs/34168684228) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | f5b4603016 |
| [34168684252](https://github.com/jsboige/CoursIA/actions/runs/34168684252) | Validation Matrix | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m22s | f5b4603016 |
| [34168680724](https://github.com/jsboige/CoursIA/actions/runs/34168680724) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | b4fba1f31a |
| [34168677933](https://github.com/jsboige/CoursIA/actions/runs/34168677933) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | (none) | 0/0 | 0m05s | dff1f52626 |
| [34168677933](https://github.com/jsboige/CoursIA/actions/runs/34168677933) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | dff1f52626 |
| [34168677909](https://github.com/jsboige/CoursIA/actions/runs/34168677909) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m03s | dff1f52626 |
| [34168674097](https://github.com/jsboige/CoursIA/actions/runs/34168674097) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m11s | 65c79023b0 |
| [34168674025](https://github.com/jsboige/CoursIA/actions/runs/34168674025) | Validation Matrix | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m11s | 65c79023b0 |
| [34168674106](https://github.com/jsboige/CoursIA/actions/runs/34168674106) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | (none) | 0/0 | 0m03s | 65c79023b0 |
| [34168674106](https://github.com/jsboige/CoursIA/actions/runs/34168674106) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 65c79023b0 |
| [34168674075](https://github.com/jsboige/CoursIA/actions/runs/34168674075) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | 65c79023b0 |
| [34168674118](https://github.com/jsboige/CoursIA/actions/runs/34168674118) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m11s | 65c79023b0 |
| [34168671000](https://github.com/jsboige/CoursIA/actions/runs/34168671000) | Validation Matrix | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m04s | 8a40928748 |
| [34168670974](https://github.com/jsboige/CoursIA/actions/runs/34168670974) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m04s | 8a40928748 |
| [34168670994](https://github.com/jsboige/CoursIA/actions/runs/34168670994) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m04s | 8a40928748 |
| [34168670977](https://github.com/jsboige/CoursIA/actions/runs/34168670977) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | (none) | 0/0 | 0m02s | 8a40928748 |
| [34168670977](https://github.com/jsboige/CoursIA/actions/runs/34168670977) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 8a40928748 |
| [34168668065](https://github.com/jsboige/CoursIA/actions/runs/34168668065) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m04s | 045936278a |
| [34159466805](https://github.com/jsboige/CoursIA/actions/runs/34159466805) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 155m00s | 96a9ad68c4 |
| [34159466778](https://github.com/jsboige/CoursIA/actions/runs/34159466778) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | (none) | 0/0 | 155m01s | 96a9ad68c4 |
| [34159466778](https://github.com/jsboige/CoursIA/actions/runs/34159466778) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 96a9ad68c4 |
| [34159466779](https://github.com/jsboige/CoursIA/actions/runs/34159466779) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 155m03s | 96a9ad68c4 |
| [34159466787](https://github.com/jsboige/CoursIA/actions/runs/34159466787) | Validation Matrix | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 155m03s | 96a9ad68c4 |
| [34159428555](https://github.com/jsboige/CoursIA/actions/runs/34159428555) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m39s | 2d3401c34c |
| [34159428494](https://github.com/jsboige/CoursIA/actions/runs/34159428494) | Validation Matrix | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m39s | 2d3401c34c |
| [34159428482](https://github.com/jsboige/CoursIA/actions/runs/34159428482) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m39s | 2d3401c34c |
| [34159428547](https://github.com/jsboige/CoursIA/actions/runs/34159428547) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | (none) | 0/0 | 0m37s | 2d3401c34c |
| [34159428547](https://github.com/jsboige/CoursIA/actions/runs/34159428547) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | 2d3401c34c |
| [34159390758](https://github.com/jsboige/CoursIA/actions/runs/34159390758) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | (none) | 0/0 | 0m36s | 90ba0fc085 |
| [34159390758](https://github.com/jsboige/CoursIA/actions/runs/34159390758) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 90ba0fc085 |
| [34131473202](https://github.com/jsboige/CoursIA/actions/runs/34131473202) | Quarto Pages Deploy | Build Quarto site | **TIMEOUT** | myia-ai-01-linux-docker-3 | 9/15 | 61m04s | b646b2fca0 |
| [34131465607](https://github.com/jsboige/CoursIA/actions/runs/34131465607) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m06s | 12604d2084 |
| [34131465602](https://github.com/jsboige/CoursIA/actions/runs/34131465602) | Validation Matrix | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m06s | 12604d2084 |
| [34131465624](https://github.com/jsboige/CoursIA/actions/runs/34131465624) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m06s | 12604d2084 |
| [34131465591](https://github.com/jsboige/CoursIA/actions/runs/34131465591) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m06s | 12604d2084 |
| [34131465619](https://github.com/jsboige/CoursIA/actions/runs/34131465619) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | (none) | 0/0 | 0m04s | 12604d2084 |
| [34131465619](https://github.com/jsboige/CoursIA/actions/runs/34131465619) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 12604d2084 |
| [34131459595](https://github.com/jsboige/CoursIA/actions/runs/34131459595) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m04s | dce1ac5ecc |
| [34131459551](https://github.com/jsboige/CoursIA/actions/runs/34131459551) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | (none) | 0/0 | 0m02s | dce1ac5ecc |
| [34131459551](https://github.com/jsboige/CoursIA/actions/runs/34131459551) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | dce1ac5ecc |
| [34131459720](https://github.com/jsboige/CoursIA/actions/runs/34131459720) | Validation Matrix | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m04s | dce1ac5ecc |
| [34131459561](https://github.com/jsboige/CoursIA/actions/runs/34131459561) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m04s | dce1ac5ecc |
| [34131459549](https://github.com/jsboige/CoursIA/actions/runs/34131459549) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m04s | dce1ac5ecc |
| [34131454698](https://github.com/jsboige/CoursIA/actions/runs/34131454698) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m04s | 0acff955f2 |
| [34131454729](https://github.com/jsboige/CoursIA/actions/runs/34131454729) | Validation Matrix | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m04s | 0acff955f2 |
| [34131454680](https://github.com/jsboige/CoursIA/actions/runs/34131454680) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m04s | 0acff955f2 |
| [34131454638](https://github.com/jsboige/CoursIA/actions/runs/34131454638) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m04s | 0acff955f2 |
| [34131454721](https://github.com/jsboige/CoursIA/actions/runs/34131454721) | Quarto Pages Deploy | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m04s | 0acff955f2 |
| [34131447463](https://github.com/jsboige/CoursIA/actions/runs/34131447463) | Validation Matrix | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | d594705848 |
| [34131447405](https://github.com/jsboige/CoursIA/actions/runs/34131447405) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m06s | d594705848 |
| [34131447402](https://github.com/jsboige/CoursIA/actions/runs/34131447402) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m06s | d594705848 |
| [34131447385](https://github.com/jsboige/CoursIA/actions/runs/34131447385) | Quarto Pages Deploy | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m06s | d594705848 |
| [34131447355](https://github.com/jsboige/CoursIA/actions/runs/34131447355) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m06s | d594705848 |
| [34131442177](https://github.com/jsboige/CoursIA/actions/runs/34131442177) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | 48a01fd9fb |
| [34131437189](https://github.com/jsboige/CoursIA/actions/runs/34131437189) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | 9c2f472165 |
| [34131430965](https://github.com/jsboige/CoursIA/actions/runs/34131430965) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m12s | b4e0dcf30d |
| [34131430973](https://github.com/jsboige/CoursIA/actions/runs/34131430973) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | b4e0dcf30d |
| [34131425337](https://github.com/jsboige/CoursIA/actions/runs/34131425337) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-1 | 5/15 | 0m19s | b85c3d6ddc |
| [34131425337](https://github.com/jsboige/CoursIA/actions/runs/34131425337) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | b85c3d6ddc |
| [34131425291](https://github.com/jsboige/CoursIA/actions/runs/34131425291) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | b85c3d6ddc |
| [34114810850](https://github.com/jsboige/CoursIA/actions/runs/34114810850) | Quarto Pages Deploy | Build Quarto site | **TIMEOUT** | myia-ai-01-linux-docker-5 | 9/15 | 60m27s | eec8365c5b |
| [34112443460](https://github.com/jsboige/CoursIA/actions/runs/34112443460) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-4 | 9/15 | 28m01s | f750d83bc8 |
| [34112443460](https://github.com/jsboige/CoursIA/actions/runs/34112443460) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | f750d83bc8 |
| [34112362053](https://github.com/jsboige/CoursIA/actions/runs/34112362053) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-linux-docker-1 | 8/15 | 1m02s | 50b6fb0379 |
| [34112362053](https://github.com/jsboige/CoursIA/actions/runs/34112362053) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 50b6fb0379 |
| [34104001092](https://github.com/jsboige/CoursIA/actions/runs/34104001092) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-linux-docker-7 | 9/15 | 10m12s | 777a7a378f |
| [34104001092](https://github.com/jsboige/CoursIA/actions/runs/34104001092) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 777a7a378f |
| [34096591142](https://github.com/jsboige/CoursIA/actions/runs/34096591142) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m06s | dca8734784 |
| [34096591348](https://github.com/jsboige/CoursIA/actions/runs/34096591348) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m07s | dca8734784 |
| [34096582466](https://github.com/jsboige/CoursIA/actions/runs/34096582466) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m07s | 69c1c469ee |
| [34078561070](https://github.com/jsboige/CoursIA/actions/runs/34078561070) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-linux-docker-6 | 8/14 | 17m09s | 0678a3fcb5 |
| [34078561070](https://github.com/jsboige/CoursIA/actions/runs/34078561070) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 0678a3fcb5 |
| [34077500719](https://github.com/jsboige/CoursIA/actions/runs/34077500719) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-2 | 8/13 | 18m58s | 2b766abf62 |
| [34077500719](https://github.com/jsboige/CoursIA/actions/runs/34077500719) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | 2b766abf62 |
| [34077012949](https://github.com/jsboige/CoursIA/actions/runs/34077012949) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-linux-docker-5 | 8/13 | 9m01s | 3cd24e354c |
| [34077012949](https://github.com/jsboige/CoursIA/actions/runs/34077012949) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 3cd24e354c |
| [34075548674](https://github.com/jsboige/CoursIA/actions/runs/34075548674) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m03s | 401ed7de7f |
| [34074797095](https://github.com/jsboige/CoursIA/actions/runs/34074797095) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-linux-docker-1 | 8/13 | 11m54s | 8e5e000b02 |
| [34074797095](https://github.com/jsboige/CoursIA/actions/runs/34074797095) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 8e5e000b02 |
| [34073831422](https://github.com/jsboige/CoursIA/actions/runs/34073831422) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-4 | 8/13 | 18m20s | 6835098043 |
| [34073831422](https://github.com/jsboige/CoursIA/actions/runs/34073831422) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | 6835098043 |
| [34073735130](https://github.com/jsboige/CoursIA/actions/runs/34073735130) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-8 | 4/13 | 1m47s | 7693bc1a48 |
| [34073735130](https://github.com/jsboige/CoursIA/actions/runs/34073735130) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | 7693bc1a48 |
| [34073699616](https://github.com/jsboige/CoursIA/actions/runs/34073699616) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-1 | 7/13 | 0m33s | 95f15758d6 |
| [34073699616](https://github.com/jsboige/CoursIA/actions/runs/34073699616) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | 95f15758d6 |
| [34072508667](https://github.com/jsboige/CoursIA/actions/runs/34072508667) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-4 | 8/13 | 22m33s | e0f3c62d49 |
| [34072508667](https://github.com/jsboige/CoursIA/actions/runs/34072508667) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | e0f3c62d49 |
| [34071353699](https://github.com/jsboige/CoursIA/actions/runs/34071353699) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | GitHub Actions 1000477971 | 2/3 | 0m13s | 62c4ad79c5 |
| [34068931074](https://github.com/jsboige/CoursIA/actions/runs/34068931074) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-po-2024-linux-docker-4 | 2/12 | 8m38s | 501a30a06e |
| [34068931074](https://github.com/jsboige/CoursIA/actions/runs/34068931074) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 501a30a06e |
| [34068146904](https://github.com/jsboige/CoursIA/actions/runs/34068146904) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-linux-docker-7 | 8/13 | 16m16s | 35be38facc |
| [34068146904](https://github.com/jsboige/CoursIA/actions/runs/34068146904) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 35be38facc |
| [34067752142](https://github.com/jsboige/CoursIA/actions/runs/34067752142) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-4 | 8/13 | 8m37s | 9269289049 |
| [34067752142](https://github.com/jsboige/CoursIA/actions/runs/34067752142) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | 9269289049 |
| [34066837555](https://github.com/jsboige/CoursIA/actions/runs/34066837555) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-5 | 8/13 | 19m46s | 6a663a7713 |
| [34066837555](https://github.com/jsboige/CoursIA/actions/runs/34066837555) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 6a663a7713 |
| [34066241678](https://github.com/jsboige/CoursIA/actions/runs/34066241678) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-2 | 8/13 | 12m22s | 19a6158c3e |
| [34066241678](https://github.com/jsboige/CoursIA/actions/runs/34066241678) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | 19a6158c3e |
| [34066241740](https://github.com/jsboige/CoursIA/actions/runs/34066241740) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m19s | 19a6158c3e |
| [34066090924](https://github.com/jsboige/CoursIA/actions/runs/34066090924) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m16s | 84ce2b0e5e |
| [34066090950](https://github.com/jsboige/CoursIA/actions/runs/34066090950) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-3 | 8/13 | 3m05s | 84ce2b0e5e |
| [34066090950](https://github.com/jsboige/CoursIA/actions/runs/34066090950) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 84ce2b0e5e |
| [34066088495](https://github.com/jsboige/CoursIA/actions/runs/34066088495) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | 4021837702 |
| [34066088445](https://github.com/jsboige/CoursIA/actions/runs/34066088445) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | 4021837702 |
| [34066041731](https://github.com/jsboige/CoursIA/actions/runs/34066041731) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 1m02s | e47be88917 |
| [34066041752](https://github.com/jsboige/CoursIA/actions/runs/34066041752) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-8 | 7/13 | 1m12s | e47be88917 |
| [34066041752](https://github.com/jsboige/CoursIA/actions/runs/34066041752) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | e47be88917 |
| [34066030435](https://github.com/jsboige/CoursIA/actions/runs/34066030435) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m16s | d6416bdc7a |
| [34066030453](https://github.com/jsboige/CoursIA/actions/runs/34066030453) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m16s | d6416bdc7a |
| [34066030446](https://github.com/jsboige/CoursIA/actions/runs/34066030446) | Quarto Pages Deploy | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m16s | d6416bdc7a |
| [34066027168](https://github.com/jsboige/CoursIA/actions/runs/34066027168) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | 066adb645d |
| [34065952716](https://github.com/jsboige/CoursIA/actions/runs/34065952716) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m48s | ed41ff0b2b |
| [34065952690](https://github.com/jsboige/CoursIA/actions/runs/34065952690) | Scripts & Notebook-Tools Tests | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 5m34s | ed41ff0b2b |
| [34065948173](https://github.com/jsboige/CoursIA/actions/runs/34065948173) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-2 | 8/13 | 2m00s | a159674ffc |
| [34065948173](https://github.com/jsboige/CoursIA/actions/runs/34065948173) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | a159674ffc |
| [34060400936](https://github.com/jsboige/CoursIA/actions/runs/34060400936) | Quarto Pages Deploy | Build Quarto site | **TIMEOUT** | myia-po-2024-linux-docker-3 | 8/13 | 60m21s | 036a7a5644 |
| [34059521630](https://github.com/jsboige/CoursIA/actions/runs/34059521630) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-linux-docker-8 | 8/13 | 16m47s | 6af1fe07f0 |
| [34059521630](https://github.com/jsboige/CoursIA/actions/runs/34059521630) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 6af1fe07f0 |
| [34059063019](https://github.com/jsboige/CoursIA/actions/runs/34059063019) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-po-2024-linux-docker-5 | 8/13 | 9m40s | cdd8e1b116 |
| [34059063019](https://github.com/jsboige/CoursIA/actions/runs/34059063019) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | cdd8e1b116 |
| [34055842579](https://github.com/jsboige/CoursIA/actions/runs/34055842579) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m10s | 07d0e76477 |
| [34055835653](https://github.com/jsboige/CoursIA/actions/runs/34055835653) | Scripts & Notebook-Tools Tests | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m10s | df524f5f8c |
| [34055835606](https://github.com/jsboige/CoursIA/actions/runs/34055835606) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m10s | df524f5f8c |
| [34055827934](https://github.com/jsboige/CoursIA/actions/runs/34055827934) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m10s | f7255716e9 |
| [34055827933](https://github.com/jsboige/CoursIA/actions/runs/34055827933) | Scripts & Notebook-Tools Tests | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m10s | f7255716e9 |
| [34055819669](https://github.com/jsboige/CoursIA/actions/runs/34055819669) | Scripts & Notebook-Tools Tests | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m11s | 1d331860fd |
| [34055819639](https://github.com/jsboige/CoursIA/actions/runs/34055819639) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m11s | 1d331860fd |
| [34055819671](https://github.com/jsboige/CoursIA/actions/runs/34055819671) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m29s | 1d331860fd |
| [34055819648](https://github.com/jsboige/CoursIA/actions/runs/34055819648) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m29s | 1d331860fd |
| [34055819691](https://github.com/jsboige/CoursIA/actions/runs/34055819691) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-po-2024-linux-docker-3 | 6/13 | 1m05s | 1d331860fd |
| [34055819691](https://github.com/jsboige/CoursIA/actions/runs/34055819691) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 1d331860fd |
| [34055811935](https://github.com/jsboige/CoursIA/actions/runs/34055811935) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m10s | 4d810ed07d |
| [34055811983](https://github.com/jsboige/CoursIA/actions/runs/34055811983) | Validation Matrix | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m10s | 4d810ed07d |
| [34055811925](https://github.com/jsboige/CoursIA/actions/runs/34055811925) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | (none) | 0/0 | 0m01s | 4d810ed07d |
| [34055811925](https://github.com/jsboige/CoursIA/actions/runs/34055811925) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | 4d810ed07d |
| [34055811827](https://github.com/jsboige/CoursIA/actions/runs/34055811827) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m11s | 4d810ed07d |
| [34055811902](https://github.com/jsboige/CoursIA/actions/runs/34055811902) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m11s | 4d810ed07d |
| [34055805410](https://github.com/jsboige/CoursIA/actions/runs/34055805410) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m10s | b5a48ef5eb |
| [34055799626](https://github.com/jsboige/CoursIA/actions/runs/34055799626) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m09s | 91d264a0b7 |
| [34055799560](https://github.com/jsboige/CoursIA/actions/runs/34055799560) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m18s | 91d264a0b7 |
| [34055799594](https://github.com/jsboige/CoursIA/actions/runs/34055799594) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-7 | 4/13 | 0m16s | 91d264a0b7 |
| [34055799594](https://github.com/jsboige/CoursIA/actions/runs/34055799594) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | 91d264a0b7 |
| [34055799570](https://github.com/jsboige/CoursIA/actions/runs/34055799570) | Scripts & Notebook-Tools Tests | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m27s | 91d264a0b7 |
| [34055791201](https://github.com/jsboige/CoursIA/actions/runs/34055791201) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m11s | b5687ac2a9 |
| [34055791228](https://github.com/jsboige/CoursIA/actions/runs/34055791228) | Quarto Pages Deploy | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m11s | b5687ac2a9 |
| [34055768753](https://github.com/jsboige/CoursIA/actions/runs/34055768753) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-linux-docker-5 | 4/13 | 0m42s | 667416efa1 |
| [34055768753](https://github.com/jsboige/CoursIA/actions/runs/34055768753) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | 667416efa1 |
| [34042844976](https://github.com/jsboige/CoursIA/actions/runs/34042844976) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-linux-docker-8 | 4/13 | 2m59s | 706ab6d572 |
| [34042844976](https://github.com/jsboige/CoursIA/actions/runs/34042844976) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | 706ab6d572 |
| [34041252177](https://github.com/jsboige/CoursIA/actions/runs/34041252177) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-7 | 8/13 | 30m13s | a0cf4d9a2f |
| [34041252177](https://github.com/jsboige/CoursIA/actions/runs/34041252177) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | a0cf4d9a2f |
| [34040411236](https://github.com/jsboige/CoursIA/actions/runs/34040411236) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-linux-docker-7 | 8/13 | 16m04s | 8ef9f347c1 |
| [34040411236](https://github.com/jsboige/CoursIA/actions/runs/34040411236) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | 8ef9f347c1 |
| [34039294101](https://github.com/jsboige/CoursIA/actions/runs/34039294101) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-linux-docker-4 | 8/13 | 20m10s | 6f0c723fee |
| [34039294101](https://github.com/jsboige/CoursIA/actions/runs/34039294101) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 6f0c723fee |
| [34037735395](https://github.com/jsboige/CoursIA/actions/runs/34037735395) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-6 | 8/13 | 29m47s | d2eab6dc70 |
| [34037735395](https://github.com/jsboige/CoursIA/actions/runs/34037735395) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | d2eab6dc70 |
| [34036828375](https://github.com/jsboige/CoursIA/actions/runs/34036828375) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-po-2024-linux-docker-5 | 8/13 | 18m09s | 707d91d81d |
| [34036828375](https://github.com/jsboige/CoursIA/actions/runs/34036828375) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | 707d91d81d |
| [34036401970](https://github.com/jsboige/CoursIA/actions/runs/34036401970) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-2 | 8/13 | 7m59s | c808dc0603 |
| [34036401970](https://github.com/jsboige/CoursIA/actions/runs/34036401970) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | c808dc0603 |
| [34035862550](https://github.com/jsboige/CoursIA/actions/runs/34035862550) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-linux-docker-6 | 8/13 | 10m20s | 9b60d6b890 |
| [34035862550](https://github.com/jsboige/CoursIA/actions/runs/34035862550) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 9b60d6b890 |
| [34035424982](https://github.com/jsboige/CoursIA/actions/runs/34035424982) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-4 | 8/13 | 8m35s | 8c70dd66d5 |
| [34035424982](https://github.com/jsboige/CoursIA/actions/runs/34035424982) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 8c70dd66d5 |
| [34035058195](https://github.com/jsboige/CoursIA/actions/runs/34035058195) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-po-2024-linux-docker-6 | 8/13 | 7m16s | 5dc0b16358 |
| [34035058195](https://github.com/jsboige/CoursIA/actions/runs/34035058195) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | 5dc0b16358 |
| [34035055374](https://github.com/jsboige/CoursIA/actions/runs/34035055374) | Quarto Pages Deploy | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | ee04898c7b |
| [34034259788](https://github.com/jsboige/CoursIA/actions/runs/34034259788) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-6 | 8/13 | 16m21s | 241156a6dd |
| [34034259788](https://github.com/jsboige/CoursIA/actions/runs/34034259788) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | 241156a6dd |
| [34034178686](https://github.com/jsboige/CoursIA/actions/runs/34034178686) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-wsl-3 | 7/13 | 1m21s | 72654baa69 |
| [34034178686](https://github.com/jsboige/CoursIA/actions/runs/34034178686) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 72654baa69 |
| [34032418437](https://github.com/jsboige/CoursIA/actions/runs/34032418437) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-po-2024-linux-docker-6 | 8/13 | 35m34s | fc68de988b |
| [34032418437](https://github.com/jsboige/CoursIA/actions/runs/34032418437) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | fc68de988b |
| [34032418442](https://github.com/jsboige/CoursIA/actions/runs/34032418442) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m45s | fc68de988b |
| [34032418409](https://github.com/jsboige/CoursIA/actions/runs/34032418409) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 1m09s | fc68de988b |
| [34032415130](https://github.com/jsboige/CoursIA/actions/runs/34032415130) | Validation Matrix | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m04s | 77d666246a |
| [34032415137](https://github.com/jsboige/CoursIA/actions/runs/34032415137) | Quarto Pages Deploy | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m04s | 77d666246a |
| [34032415142](https://github.com/jsboige/CoursIA/actions/runs/34032415142) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m04s | 77d666246a |
| [34032283738](https://github.com/jsboige/CoursIA/actions/runs/34032283738) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | myia-ai-01-linux-docker-1 | 4/13 | 2m39s | 42d9202aca |
| [34032283738](https://github.com/jsboige/CoursIA/actions/runs/34032283738) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | 0m00s | 42d9202aca |
| [34032283725](https://github.com/jsboige/CoursIA/actions/runs/34032283725) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 2m43s | 42d9202aca |
| [34032280909](https://github.com/jsboige/CoursIA/actions/runs/34032280909) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | 63b9cdf8df |
| [34032277330](https://github.com/jsboige/CoursIA/actions/runs/34032277330) | Validation Matrix | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m09s | 177239f527 |
| [34032277324](https://github.com/jsboige/CoursIA/actions/runs/34032277324) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m09s | 177239f527 |
| [34032277348](https://github.com/jsboige/CoursIA/actions/runs/34032277348) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m09s | 177239f527 |
| [34032277349](https://github.com/jsboige/CoursIA/actions/runs/34032277349) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | (none) | 0/0 | 0m07s | 177239f527 |
| [34032277349](https://github.com/jsboige/CoursIA/actions/runs/34032277349) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 177239f527 |
| [34032277328](https://github.com/jsboige/CoursIA/actions/runs/34032277328) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | 177239f527 |
| [34032274482](https://github.com/jsboige/CoursIA/actions/runs/34032274482) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | 841fafde25 |
| [34032274483](https://github.com/jsboige/CoursIA/actions/runs/34032274483) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | 841fafde25 |
| [34032274387](https://github.com/jsboige/CoursIA/actions/runs/34032274387) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | 841fafde25 |
| [34032274394](https://github.com/jsboige/CoursIA/actions/runs/34032274394) | Validation Matrix | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | 841fafde25 |
| [34032274384](https://github.com/jsboige/CoursIA/actions/runs/34032274384) | Quarto Pages Deploy | Build Quarto site | **CANCELLED_OTHER** | (none) | 0/0 | 0m01s | 841fafde25 |
| [34032274384](https://github.com/jsboige/CoursIA/actions/runs/34032274384) | Quarto Pages Deploy | Deploy to GitHub Pages | **CANCELLED_OTHER** | (none) | 0/0 | -1m59s | 841fafde25 |
| [34032270440](https://github.com/jsboige/CoursIA/actions/runs/34032270440) | Notebook Validation | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m06s | 9c636673f6 |
| [34032270398](https://github.com/jsboige/CoursIA/actions/runs/34032270398) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m06s | 9c636673f6 |
| [34032270395](https://github.com/jsboige/CoursIA/actions/runs/34032270395) | Validation Matrix | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m06s | 9c636673f6 |
| [34032270432](https://github.com/jsboige/CoursIA/actions/runs/34032270432) | Quarto Pages Deploy | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m06s | 9c636673f6 |
| [34032270394](https://github.com/jsboige/CoursIA/actions/runs/34032270394) | Pedagogy Density Advisory | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m06s | 9c636673f6 |
| [34032267142](https://github.com/jsboige/CoursIA/actions/runs/34032267142) | Secret Scan | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | 46676e61e3 |
| [34032267103](https://github.com/jsboige/CoursIA/actions/runs/34032267103) | Quarto Pages Deploy | (no jobs created) | **RUN_CANCELLED_NO_JOBS** | (none) | - | 0m05s | 46676e61e3 |
