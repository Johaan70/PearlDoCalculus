"""Regel 3 for mengder (rule3_complete_chaincopy_set, set_gap_core, v3.9).

For alle DAG-er med 2 til 5 noder og alle valg av X, W, Y, Z med |Z| >= 2 der
betingelsen i regel 3 svikter: enten er et par d-forbundet i G_{X̄Z̄}
(rule3_complete_set_root), eller vi velger y, z, w1 og en korteste kjede slik
at z når w1 og ikke y utenom X ∪ W ∪ Z, og w1 ikke er kollider. Modellen er
kjede-kopi-modellen med do(Z): z = 1, resten av Z = 0. Punktet
(y = 0, w1 = 1, resten av X ∪ W = 0) skal gi LHS > 0 og RHS = 0.

Resultat (2026-11-11):
  svikter: 260118, rot: 252806, gap: 7312, dekket: 7312, feil: 0.
"""
import itertools

def anc(edges, S):
    res = set(S); ch = True
    while ch:
        ch = False
        for a, b in edges:
            if b in res and a not in res:
                res.add(a); ch = True
    return res

def dsep(edges, x, y, Z):
    A = anc(edges, {x, y} | set(Z))
    E = [(a, b) for a, b in edges if a in A and b in A]
    adj = {v: set() for v in A}
    for a, b in E:
        adj[a].add(b); adj[b].add(a)
    for v in A:
        pa = [a for a, b in E if b == v]
        for i in pa:
            for j in pa:
                if i != j: adj[i].add(j)
    seen = {x}; st = [x]
    while st:
        u = st.pop()
        for w in adj[u]:
            if w in Z or w in seen: continue
            seen.add(w); st.append(w)
    return y not in seen

def ra(edges, S, s):
    seen = {s}; st = [s]
    while st:
        u = st.pop()
        for a, b in edges:
            if a == u and b not in seen and b not in S:
                seen.add(b); st.append(b)
    return seen

def rz(edges, S, s, w):
    R = ra(edges, S, s)
    return any(a in R for a, b in edges if b == w)

def m(J, a):
    return sum(p for k, p in J.items() if all(k[i] == x for i, x in a.items()))

def find_chain(H,S,y,z,banned):
    srcs=[s for s in set(v for e in H for v in e)|{y,z} if s not in S]
    start=[s for s in srcs if y in ra(H,S,s)]
    prev={s:None for s in start}; q=list(start)
    cols=[c for c in S if c not in banned]
    while q:
        s=q.pop(0)
        if z in ra(H,S,s):
            ch=[];cs=[]
            while s is not None:
                ch.append(s); p=prev[s]
                if p is not None: cs.append(p[1]); s=p[0]
                else: s=None
            return ch[::-1],cs[::-1]
        for c in cols:
            if not rz(H,S,s,c): continue
            for t in srcs:
                if t not in prev and rz(H,S,t,c):
                    prev[t]=(s,c); q.append(t)
    return None
def joint(n,H,S,ch,cs,w1,do):
    k=len(ch)-1; out={}
    for bits in itertools.product([0,1],repeat=k+1):
        val={}
        for v in range(n):
            if v in do: val[v]=do[v]; continue
            orp=tuple(int(any(val[a][i] for a,c in H if c==v and a not in S)) for i in range(k+1))
            if v==w1: val[v]=(orp[k],)*(k+1)
            elif v in S:
                if v in cs: j=cs.index(v)+1; val[v]=(orp[j-1]^orp[j],)*(k+1)
                else: val[v]=(0,)*(k+1)
            else: val[v]=tuple(bits[i] if ch[i]==v else orp[i] for i in range(k+1))
        key=tuple(val[v] for v in range(n)); out[key]=out.get(key,0)+0.5**(k+1)
    return out
N=5
fail=root=gapc=cov=bad=0; miss=[]
for n in range(2,N+1):
    pairs=[(a,b) for a in range(n) for b in range(a+1,n)]
    for mask in range(1<<len(pairs)):
        edges=[pairs[i] for i in range(len(pairs)) if mask>>i&1]
        for asg in itertools.product(range(5),repeat=n):
            Y={v for v in range(n) if asg[v]==3}; Z={v for v in range(n) if asg[v]==4}
            if not Y or not Z or len(Z)<2: continue   # singletons already done
            X={v for v in range(n) if asg[v]==1}; W={v for v in range(n) if asg[v]==2}
            S=X|W; H=[(a,b) for a,b in edges if b not in X]
            Z2={z for z in Z if z not in anc(H,W)}
            Hc=[(a,b) for a,b in H if b not in Z2]
            if all(dsep(Hc,y,z,S) for y in Y for z in Z): continue
            fail+=1
            HZ=[(a,b) for a,b in H if b not in Z]
            if not all(dsep(HZ,y,z,S) for y in Y for z in Z): root+=1; continue
            gapc+=1
            found=None
            for y in Y:
                for z in Z:
                    Zp=Z-{z}; SZ=S|Zp
                    if y in ra(H,SZ,z): continue
                    for w1 in W:
                        if not rz(H,SZ,z,w1): continue
                        r=find_chain(H,S,y,z,{w1})
                        if r: found=(y,z,w1,r); break
                    if found: break
                if found: break
            if not found:
                if len(miss)<6: miss.append((n,edges,sorted(X),sorted(W),sorted(Y),sorted(Z)))
                continue
            cov+=1; y,z,w1,(ch,cs)=found; k=len(ch)-1
            do={zz:((1,)*(k+1) if zz==z else (0,)*(k+1)) for zz in Z}
            Jo=joint(n,H,S,ch,cs,w1,{}); Jd=joint(n,H,S,ch,cs,w1,do)
            wp={w:((1,)*(k+1) if w==w1 else (0,)*(k+1)) for w in S}
            yp={y:(0,)*(k+1)}
            lhs=m(Jd,{**yp,**wp})*m(Jo,wp); rhs=m(Jo,{**yp,**wp})*m(Jd,wp)
            if not (lhs>0 and rhs==0):
                bad+=1
                if bad<4: print("BAD",n,edges,X,W,Y,Z,found,lhs,rhs)
print("N",N,"svikter:",fail,"rot:",root,"gap:",gapc,"dekket:",cov,"feil:",bad)
for x in miss: print("  udekket:",x)
