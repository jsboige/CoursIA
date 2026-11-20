# CSharpRepl — attaché à un process .NET vivant

Carnet : [`CSharpRepl-Live-Patching.ipynb`](CSharpRepl-Live-Patching.ipynb) — CSharpRepl
attaché à une application .NET réelle, hot-patch à chaud (`#replace` / `#wrap` / `#patches` /
`#revert`) sur le process vivant, vs `pdb` / `%autoreload` IPython (axes
[#10802](https://github.com/jsboige/CoursIA/issues/10802) et
[#10971](https://github.com/jsboige/CoursIA/issues/10971), PR
[#10806](https://github.com/jsboige/CoursIA/pull/10806)).

Le carnet exécute `csharprepl-demo/` (application compagnon `LiveOrderApp`) → le binding
garde son dossier, conformément à la règle de rangement du
[hub](../README.md). Relocalisé depuis `Vibe-Coding/docs/` (#27237) pour vivre avec les
carnets C#/.NET de GenAI.
