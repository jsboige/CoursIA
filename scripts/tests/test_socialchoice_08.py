import pytest
pytest.importorskip("z3")
pytest.importorskip("numpy")

def test_socialchoice_algorithms_against_exhaustive_oracles():
    import collections, contextlib, io, itertools, json
    from pathlib import Path
    p=Path(__file__).resolve().parents[2] / 'MyIA.AI.Notebooks/GameTheory/SocialChoice/08-Kemeny-RankedPairs-Dodgson.ipynb'
    n=json.loads(p.read_text()); d={}
    with contextlib.redirect_stdout(io.StringIO()):
     for i in (2,5,7,10,16,18): exec(''.join(n['cells'][i]['source']),d)
    a=('A','B','C'); rankings=list(itertools.permutations(a))
    def score(order,profile):
     return sum(1 for v in profile for x,y in itertools.combinations(order,2) if v.index(x)<v.index(y))
    def oracle_rp(profile):
     edges=[]
     for x,y in itertools.permutations(a,2):
      margin=sum((v.index(x)<v.index(y))-(v.index(y)<v.index(x)) for v in profile)
      if margin>0: edges.append((-margin,x,y))
     locked=set()
     for _,x,y in sorted(edges):
      # Independent exhaustive reachability through all simple paths.
      def reaches(u,t,path):
       return u==t or any(reaches(v,t,path|{v}) for v in a if (u,v) in locked and v not in path)
      if not reaches(y,x,{y}): locked.add((x,y))
     return {x for x in a if not any(v==x for _,v in locked)},locked
    count=0
    for voters in (1,2,3):
     for profile in itertools.product(rankings,repeat=voters):
      vals={r:score(r,profile) for r in rankings}; best=max(vals.values()); winners={r[0] for r,s in vals.items() if s==best}
      b=d['kemeny_bruteforce'](profile,a); z=d['kemeny_z3'](profile,a)
      assert b[0]==best and b[2]==winners
      assert z[0]=='OPTIMAL' and z[1]==best and z[3]==winners and vals[tuple(z[2])]==best
      order,rpw=d['ranked_pairs'](profile,a); expected,locked=oracle_rp(profile)
      assert rpw==expected and all(order.index(x)<order.index(y) for x,y in locked)
      count+=1
    print(f'{count} profils exhaustifs (1-3 votants, 3 candidats) : Kemeny brut et Z3, Ranked Pairs OK')
    graph=collections.defaultdict(set, {'A':{'B'},'B':{'C'}})
    assert d['creates_cycle'](graph,'C','A',a) and not d['creates_cycle'](graph,'A','C',a)
    print('Cycle et orientation inversée : OK')
    with contextlib.redirect_stdout(io.StringIO()): exec(''.join(n['cells'][13]['source']),d)
    def bfs(profile,candidate):
     queue=collections.deque([(tuple(profile),0)]); seen={tuple(profile)}
     while queue:
      p,cost=queue.popleft()
      if all(sum(v.index(candidate)<v.index(o) for v in p)>len(p)//2 for o in a if o!=candidate): return cost
      for i,v in enumerate(p):
       for j in range(len(a)-1):
        w=list(v); w[j],w[j+1]=w[j+1],w[j]; q=p[:i]+(tuple(w),)+p[i+1:]
        if q not in seen: seen.add(q); queue.append((q,cost+1))
    for count_voters in (1,2,3):
     for profile in itertools.product(rankings,repeat=count_voters):
      for candidate in a:
       assert d['dodgson_score'](candidate,profile,a)==bfs(profile,candidate), (profile,candidate)
    assert d['dodgson_score']('C',[('A','B','C')]*3,a)==4
    print('Dodgson : 774 couples profil/candidat contre BFS, temoin 4 swaps OK')
