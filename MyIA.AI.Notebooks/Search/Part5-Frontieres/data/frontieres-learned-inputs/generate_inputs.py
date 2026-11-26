import json, ast, pathlib, math, random, time
from dataclasses import dataclass,field
from collections import deque
from typing import Callable
import numpy as np
p=pathlib.Path('MyIA.AI.Notebooks/Search/Part5-Frontieres');n=json.loads((p/'Frontieres-06-LearningToBranch-Generalization-Audit-Python.ipynb').read_text());env=globals()
exec(''.join(n['cells'][4]['source']),env);exec(''.join(n['cells'][6]['source']),env)
instances=[]
for c in build_instances():
 edges=[]
 for left,right in c.relations:
  if left<right:edges.append([left,right])
 instances.append({'family':c.family,'id':c.instance_id,'domains':{k:sorted(v) for k,v in c.domains.items()},'edges':edges})
output=p/'data/frontieres-learned-inputs';output.mkdir(parents=True,exist_ok=True)
(output/'csp-instances.json').write_text(json.dumps({'source':'Frontieres-06 Python make_queens/make_coloring/make_latin, 12 per family','instances':instances},ensure_ascii=False,separators=(',',':'))+'\n')
n=json.loads((p/'Frontieres-10-NeuralDiving-Coloration-Python.ipynb').read_text());NV,KMAX,DEG=60,6,3
for i,name in [(2,'make_graph'),(9,'cover_matrix')]:
 code=ast.parse(''.join(n['cells'][i]['source']));fn=next(x for x in code.body if isinstance(x,ast.FunctionDef) and x.name==name);exec(compile(ast.Module(body=[fn],type_ignores=[]),'<fixture>','exec'),env)
seeds=list(range(5000,5060))+list(range(6000,6025));graphs={}
for s in seeds:
 a=make_graph(s);graphs[str(s)]=[[v,u] for v in range(NV) for u in range(v+1,NV) if a[v,u]]
covers={}
for label,m,nc,d in [('presolve',45,60,.10),('branching',90,60,.20)]:
 covers[label]={}
 for seed in range(4001,4021):
  mat=cover_matrix(m,nc,d,seed);covers[label][str(seed)]=[[int(j) for j in np.flatnonzero(row)] for row in mat]
r=np.random.default_rng(4001);w=r.integers(10,50,size=(5,40));profits=w.sum(axis=0)+r.integers(-2,3,size=40)
(output/'neural-inputs.json').write_text(json.dumps({'source':'Frontieres-10 Python make_graph/cover_matrix RNG inputs only','graphs':graphs,'covers':covers,'knapsack':{'weights':w.tolist(),'profits':profits.tolist()},'permutation_123':np.random.default_rng(123).permutation(KMAX).tolist()},separators=(',',':'))+'\n')
print('CSP',len(instances),'graphs',len(graphs),'covers',sum(len(x) for x in covers.values()))
