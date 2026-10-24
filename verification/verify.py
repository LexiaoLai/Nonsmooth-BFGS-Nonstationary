#!/usr/bin/env python3
"""Exact rational certificates for the algebraic four-step BFGS example.

Run from any working directory. Only Python's standard library is needed.
All decisive comparisons use Fraction and outward rational intervals.
Manuscript: Lemmas 2.3 and 2.5; Propositions 2.7--2.9; Appendix A,
including Proposition A.1. See docs/manuscript-map.md for the result correspondence.
"""
from pathlib import Path
from fractions import Fraction as F
import json
import intervals as iv
from intervals import IV,format_interval
from polynomial import Algebraic, B, P

if not __debug__:
    raise RuntimeError("Run the verifier without Python's -O option.")

COARSE_LO,COARSE_HI=F('0.9178'),F('0.9179')
STABILITY_NORM_BOUND=F('0.78')
checks=[]
def require(name,condition):
    if not condition: raise ArithmeticError(name)
    checks.append(name)
def poly(b):return ((((777924*b-576632)*b-587665)*b+352256)*b+65536)

def refine_root_interval(lo,hi,places=11):
    """Isolate the root on a decimal grid using exact polynomial signs."""
    grid=10**places
    left,right=F(lo)*grid,F(hi)*grid
    if left.denominator!=1 or right.denominator!=1:
        raise ValueError('Coarse endpoints must lie on the requested decimal grid')
    left,right=int(left),int(right)
    if not poly(F(left,grid))<0<poly(F(right,grid)):
        raise ArithmeticError('The coarse interval does not bracket the root')
    while right-left>1:
        middle=(left+right)//2
        value=poly(F(middle,grid))
        if value<0:left=middle
        elif value>0:right=middle
        else:
            left,right=middle-1,middle+1
            break
    return F(left,grid),F(right,grid)

ROOT_LO,ROOT_HI=refine_root_interval(COARSE_LO,COARSE_HI)

def add(a,b): return [x+y for x,y in zip(a,b)]
def neg(a): return [-x for x in a]
def sub(a,b): return add(a,neg(b))
def scale(a,k): return [k*x for x in a]
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def tr(a): return list(map(list,zip(*a)))
def mv(a,b): return [dot(row,b) for row in a]
def mm(a,b): return [[dot(row,col) for col in tr(b)] for row in a]
def ma(a,b): return [add(x,y) for x,y in zip(a,b)]
def ms(a,k): return [scale(row,k) for row in a]
def outer(a,b): return [[x*y for y in b] for x in a]
def eye(n): return [[F(i==j) for j in range(n)] for i in range(n)]
def unpack(v): return v[:2],[[v[2],v[3]],[v[3],v[4]]]
def pack(x,h): return x+[h[0][0],h[0][1],h[1][1]]
def inverse(a):
    n=len(a); rows=[list(map(F,row))+e for row,e in zip(a,eye(n))]
    det=F(1)
    for k in range(n):
        p=next(i for i in range(k,n) if rows[i][k])
        if p!=k: rows[p],rows[k]=rows[k],rows[p];det=-det
        d=rows[k][k];det*=d;rows[k]=[x/d for x in rows[k]]
        for i in range(n):
            if i!=k:
                m=rows[i][k];rows[i]=[x-m*y for x,y in zip(rows[i],rows[k])]
    out=[row[n:] for row in rows]
    if mm(a,out)!=eye(n) or mm(out,a)!=eye(n):
        raise ArithmeticError('Matrix inverse verification failed')
    return out,det

def data(b):
    """Cycle data (2.4)--(2.8), and Hessians (2.21), (2.28)."""
    rho=F(8,9);r=rho*rho
    p=-9*(882*b*b-463*b-256)/(640*(2*b-1))
    t=-(3087*b*b-2233*b-256)/(320*(2*b-1))
    q=(15876*b*b*b-4316*b*b-6815*b-2304)/(1280*b*(2*b-1))
    J=[[p,t],[q,-p]]
    g=[[1,0],[0,1],[p,q],[t,-p],[1,0]]
    H0=[[1,F(1,2)],[F(1,2),b/4+F(1,8)]]
    H1=[[b+F(3,2),b+F(1,2)],[b+F(1,2),b]]
    H=[H0,H1,ms(mm(mm(tr(J),H0),J),rho),ms(mm(mm(tr(J),H1),J),rho),ms(H0,r)]
    x0=[-9*(8978*b*b-6527*b-2304)/(5440*b),9*(1764*b*b-2671*b+1488)/2720]
    x1=sub(x0,[1,F(1,2)])
    x=[x0,x1,scale(mv(tr(J),x0),rho),scale(mv(tr(J),x1),rho),scale(x0,r)]
    beta=[F(19,10),F(8,5),F(-41,10),F(1,5)]
    K=[ms(outer([-a[1],a[0]],[-a[1],a[0]]),be/dot(a,a)) for a,be in zip(x,beta)]
    K.append(ms(K[0],1/r))
    return g,H,x,K,r

def diff_step(h,g,gp,k,kp,dx,dh,expanded=True):
    """Apply the derivative in Appendix A.2, equations (A.5)--(A.8)."""
    s=neg(mv(h,g));y=sub(gp,g);c=dot(s,y)
    dg=mv(k,dx);ds=neg(add(mv(dh,g),mv(h,dg)))
    dxp=add(dx,ds);dy=sub(mv(kp,dxp),dg)
    dc=dot(ds,y)+dot(s,dy)
    if expanded:
        t=mv(h,y);d=dot(y,t);N=ma(outer(t,s),outer(s,t));V=outer(s,s)
        dt=add(mv(dh,y),mv(h,dy));dd=2*dot(dy,t)+dot(y,mv(dh,y))
        dV=ma(outer(ds,s),outer(s,ds))
        dN=ma(ma(outer(dt,s),outer(t,ds)),ma(outer(ds,t),outer(s,dt)))
        hp=ma(ma(dh,ms(dN,-1/c)),ms(N,dc/(c*c)))
        hp=ma(hp,ms(V,(dc+dd)/(c*c)-2*(c+d)*dc/(c*c*c)))
        hp=ma(hp,ms(dV,(c+d)/(c*c)))
    else:
        a=1/c;da=-dc/(c*c);V=ma(eye(2),ms(outer(s,y),-a))
        dV=ma(ms(outer(s,y),-da),ms(ma(outer(ds,y),outer(s,dy)),-a))
        hp=ma(ma(mm(mm(dV,h),tr(V)),mm(mm(V,dh),tr(V))),mm(mm(V,h),tr(dV)))
        hp=ma(hp,ma(ms(outer(s,s),da),ms(ma(outer(ds,s),outer(s,ds)),a)))
    return pack(dxp,hp)

S=[[464,1077,4501,-1708],[1366,2793,10000,552],[-448,-1058,-4343,1648],[16,293,1787,-2075]]
SI,det=inverse(S)
if det == 0: raise ArithmeticError('The coordinate matrix is singular')

def calculate(b,expanded):
    """Compose four derivatives and form S A S^{-1}: (A.9)--(A.10)."""
    g,H,x,K,r=data(b);prod=eye(5)
    for i in range(4):
        columns=[diff_step(H[i],g[i],g[i+1],K[i],K[i+1],*unpack(v),expanded) for v in eye(5)]
        prod=mm(tr(columns),prod)
    prod=ms(prod,1/r)
    w=pack(x[0],H[0]);keep=[0,1,3,4]
    A=[[prod[i][j]-w[i]*prod[2][j] for j in keep] for i in keep]
    return mm(mm(S,A),SI),prod,w


def root_certificate():
    """Lemma 2.3 and the refined root interval Y in (A.3)."""
    a,c=COARSE_LO,COARSE_HI
    pa,pc=poly(a),poly(c)
    derivative=3111696*a*a*a-1729896*c*c-1175330*c+352256
    require('root.coarse.lower',pa < -2)
    require('root.coarse.upper',pc > 19)
    require('root.monotonicity',derivative>200000)
    require('root.narrow.lower',poly(ROOT_LO)<0)
    require('root.narrow.upper',poly(ROOT_HI)>0)
    return dict(coarse=[a,c],narrow=[ROOT_LO,ROOT_HI],coarse_values=[pa,pc],
                derivative_lower=derivative,narrow_values=[poly(ROOT_LO),poly(ROOT_HI)])

def update(h,s,y):
    c=dot(s,y);v=ma(eye(2),ms(outer(s,y),-1/c))
    return ma(mm(mm(v,h),tr(v)),ms(outer(s,s),1/c))

def same(a,b):
    if isinstance(a,list):return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
    return a==b

def cycle_certificate():
    """Exact identities of Lemma 2.5, plus formulas used in Proposition 2.9."""
    b=B;g,H,x,K,r=data(b);rho=F(8,9)
    p,q=g[2];t=g[3][0];J=[[p,t],[q,-p]]
    require('cycle.involution',same(mm(J,J),eye(2)))
    v=[b+F(3,2),b+F(1,2)]
    require('cycle.short_position',same(x[0],scale(mv(ma(eye(2),ms(tr(J),rho)),v),1/(1-r))))
    require('cycle.H0_determinant',H[0][0][0]*H[0][1][1]-H[0][0][1]*H[0][1][0]==(2*b-1)/8)
    require('cycle.H1_determinant',H[1][0][0]*H[1][1][1]-H[1][0][1]*H[1][1][0]==(2*b-1)/4)
    curv=[F(1,2),81*b/32,F(4,9),9*b/4]
    A0=-(158760*b*b*b+163620*b*b-172579*b-103680)/(27200*b)
    A1=(79380*b*b*b+58957*b*b-70380*b-46080)/(13600*b)
    armijo=[A0,A1,rho*A0,rho*A1]
    wolfe=[F(1,10),341*b/160,F(4,45),341*b/180]
    values=[dot(u,v) for u,v in zip(g,x)]
    for i in range(4):
        s=neg(mv(H[i],g[i]));y=sub(g[i+1],g[i])
        require(f'cycle.update.{i}',same(update(H[i],s,y),H[i+1]))
        require(f'cycle.position.{i}',same(add(x[i],s),x[i+1]))
        require(f'cycle.curvature.{i}',dot(s,y)==curv[i])
        require(f'cycle.armijo_formula.{i}',values[i]+F(3,100)*dot(g[i],s)-values[i+1]==armijo[i])
        require(f'cycle.wolfe_formula.{i}',dot(sub(g[i+1],scale(g[i],F(3,5))),s)==wolfe[i])
    require('cycle.return_position',same(x[4],scale(x[0],r)))
    require('cycle.return_metric',same(H[4],ms(H[0],r)))
    return dict(identities='Exact equality in Q[b]/(P); every inverse verified',r=r)

def interpolation_nodes(g,x,K,make_interval=IV):
    nodes=[];coords=[]
    for i in range(4):
        z=[x[i][0]-x[i][1]/20,x[i][1]];coords.append(z[0])
        a=z[0] if i<2 else -z[0]
        t=z[1]/a;eta=dot(g[i],x[i])/a;d=make_interval(F(1,20)*g[i][0]+g[i][1])
        k=a*dot([F(1,20),1],mv(K[i],[F(1,20),1]))
        nodes.append(dict(t=t,eta=eta,d=d,k=k))
    return nodes,coords

def interpolation_branches(nodes,outer=False,make_interval=IV):
    anchors=[dict(t=make_interval(-1),eta=make_interval(-1),d=make_interval(1),k=make_interval(0)),dict(t=make_interval(6),eta=make_interval(6),d=make_interval(1),k=make_interval(0))]
    branches=[(sign,[anchors[0],nodes[indices[0]],nodes[indices[1]],anchors[1]])
              for sign,indices in [('+',(0,1)),('-',(2,3))]]
    if outer:
        branches=[(sign,[dict(t=branch[0]['t']-1,eta=branch[0]['eta']-1,d=make_interval(1),k=make_interval(0))]
                   +branch+[dict(t=branch[-1]['t']+1,eta=branch[-1]['eta']+1,d=make_interval(1),k=make_interval(0))])
                  for sign,branch in branches]
    return branches

def geometry_certificate(b):
    """Lemma 2.5 position bounds; Propositions 2.7--2.9 and Appendix A.1."""
    g,H,x,K,r=data(b);nodes,coords=interpolation_nodes(g,x,K);norms=[]
    for i in range(5):
        a,c=x[i];n=a*a+c*c
        require(f'geometry.norm.{i}',n.lo>0 and n.hi<8)
        norms.append(n)
    for i in range(4):
        coordinate=coords[i];d=nodes[i]['d'];k=nodes[i]['k']
        lo,hi=[('1.229','1.234'),('.254','.259'),('-1.122','-1.104'),('-.253','-.240')][i]
        require(f'geometry.displayed_coordinate.{i}',F(lo)<coordinate.lo and coordinate.hi<F(hi))
        if i<2:require(f'geometry.sign.{i}',coordinate.lo>0)
        else:require(f'geometry.sign.{i}',coordinate.hi<0)
        require(f'interpolation.d_lower.{i}',d.lo>F(1,50))
        require(f'interpolation.d_upper.{i}',d.hi<=1)
        # Descriptive instance bound only; the bridge allows arbitrary k.
        require(f'interpolation.k.{i}',k.mag()<5)
    gaps=[]
    for sign,branch in interpolation_branches(nodes):
        for j,(left,right) in enumerate(zip(branch,branch[1:])):
            ell=right['t']-left['t'];D=right['eta']-left['eta'];secant=D/ell
            require(f'interpolation.gap.{sign}.{j}',ell.lo>1)
            require(f'interpolation.secant.{sign}.{j}',secant.lo>F(1,2) and secant.hi<2)
            gaps.append(dict(branch=sign,gap=j,length=ell,secant=secant))
    A0=-(158760*b*b*b+163620*b*b-172579*b-103680)/(27200*b)
    A1=(79380*b*b*b+58957*b*b-70380*b-46080)/(13600*b)
    armijo=[A0,A1,F(8,9)*A0,F(8,9)*A1]
    wolfe=[IV(F(1,10)),341*b/160,IV(F(4,45)),341*b/180]
    require('margins.A0',F('.0575')<A0.lo and A0.hi<F('.0611') and A0.lo>F(1,20))
    require('margins.A1',F('.0281')<A1.lo and A1.hi<F('.0312') and A1.lo>F(1,50))
    for i,w in enumerate(wolfe):require(f'margins.W{i}',w.lo>0)
    curv=[dot(neg(mv(H[i],g[i])),sub(g[i+1],g[i])) for i in range(4)]
    for i,c in enumerate(curv):require(f'curvature.{i}',c.lo>0)
    return dict(nodes=nodes,gaps=gaps,norm_squared=norms,z1=coords,armijo=armijo,wolfe=wolfe,curvature=curv)

def bridge_parameters(left,right,n,m=F(1,100)):
    """Rescale one interpolation gap to [0,1] and enclose its coefficients."""
    ell=right['t']-left['t'];delta=right['eta']-left['eta'];mu=ell*m
    p,q=ell*left['d'],ell*right['d']
    P,Q=ell*ell*left['k'],ell*ell*right['k']
    L=P+(n+2)*(p-mu);R=Q-(n+2)*(q-mu)
    # At n=0, cancel mu before interval evaluation. This certifies the exact
    # equality I_0=Delta on identity gaps, hence rejects that index decisively.
    integral=((p+q)/2+(P-Q)/12 if n==0 else
              mu+2*(p+q-2*mu)/(n+4)+(P-Q)/((n+3)*(n+4)))
    return dict(n=n,degree_bound=max(n+4,5),length=ell,delta=delta,mu=mu,
                p=p,q=q,P=P,Q=Q,L=L,R=R,integral=integral,remaining=delta-integral)

def least_bridge(left,right,label,m=F(1,100)):
    """Certify the least admissible index, rejecting every preceding one."""
    require(f'bridge.hypotheses.{label}',(right['t']-left['t']).lo>0
            and left['d'].lo>m and right['d'].lo>m
            and ((right['eta']-left['eta'])-m*(right['t']-left['t'])).lo>0)
    rejected=[]
    for n in range(10000):
        candidate=bridge_parameters(left,right,n,m)
        L,R,remaining=[candidate[key] for key in ('L','R','remaining')]
        if L.lo>=0 and R.hi<=0 and remaining.lo>0:
            require(f'bridge.L.{label}',L.lo>=0)
            require(f'bridge.R.{label}',R.hi<=0)
            require(f'bridge.remaining.{label}',remaining.lo>0)
            require(f'bridge.least.{label}',len(rejected)==n and all(item['fails'] for item in rejected))
            candidate['rejected']=rejected
            return candidate
        failures=[]
        if L.hi<0:failures.append('L<0')
        if R.lo>0:failures.append('R>0')
        if remaining.hi<=0:failures.append('Delta-I<=0')
        if not failures:
            raise ArithmeticError(f'bridge.{label}: interval too wide to decide n={n}')
        rejected.append(dict(n=n,fails=failures))
    raise ArithmeticError(f'bridge.{label}: no certified index below 10000')

def bridge_certificate(b):
    g,H,x,K,r=data(b);nodes,_=interpolation_nodes(g,x,K);gaps=[]
    for sign,branch in interpolation_branches(nodes,outer=True):
        for j,(left,right) in enumerate(zip(branch,branch[1:])):
            result=least_bridge(left,right,f'{sign}.{j}')
            result.update(branch=sign,gap=j)
            gaps.append(result)
    return dict(m=F(1,100),root_interval=[b.lo,b.hi],gaps=gaps)

def stability_certificate(b):
    require('stability.S_inverse_left',mm(S,SI)==eye(4))
    require('stability.S_inverse_right',mm(SI,S)==eye(4))
    require('stability.determinant',det!=0)
    M,derivative,w=calculate(b,True)
    upper=[[F(iv.decimal_up(x.mag(),3)) for x in row] for row in M]
    rows=list(map(sum,upper))
    for i,value in enumerate(rows):
        require(f'stability.row.{i}',value<STABILITY_NORM_BOUND)
    require('stability.norm',max(rows)<=STABILITY_NORM_BOUND)
    # The expanded and factorized differentiation agree exactly modulo P,
    # throughout all roots at which the verified inverses exist.
    ex,prod_ex,_=calculate(B,True)
    fa,prod_fa,_=calculate(B,False)
    require('stability.exact_differentiations',same(ex,fa) and same(prod_ex,prod_fa))
    return dict(matrix=M,magnitude=upper,rows=rows,norm=max(rows),S=S,S_inverse=SI,determinant=det)

def serialize(v):
    if isinstance(v,IV):return v.out()
    if isinstance(v,F):return str(v)
    if isinstance(v,dict):return {k:serialize(x) for k,x in v.items()}
    if isinstance(v,list):return [serialize(x) for x in v]
    return v

def verify():
    checks.clear()
    root=root_certificate();cycle=cycle_certificate()
    # Broad interval is enough for interpolation and line-search margins;
    # the narrow one certifies the least bridge indices and transverse derivative.
    geometry=geometry_certificate(IV(COARSE_LO,COARSE_HI))
    bridges=bridge_certificate(IV(ROOT_LO,ROOT_HI))
    stability=stability_certificate(IV(ROOT_LO,ROOT_HI))
    return dict(config={'bits':iv.BITS,'arithmetic':'Fraction and outward dyadic intervals'},
                root=root,cycle=cycle,geometry=geometry,bridges=bridges,stability=stability,checks=list(checks))

def tex_number(q):
    q=F(q)
    return str(q.numerator) if q.denominator==1 else r'\frac{'+str(q.numerator)+'}{'+str(q.denominator)+'}'

def tex_interval(x,places=4):return format_interval(x,places)

def write_outputs(result,directory=None):
    directory=Path(__file__).parent if directory is None else Path(directory)
    directory.mkdir(exist_ok=True,parents=True)
    (directory/'certificate.json').write_text(json.dumps(serialize(result),indent=2)+'\n')
    lines=['% Generated by verify.py after all exact checks pass.']
    def macro(name,value):lines.append('\\newcommand{\\'+name+'}{'+value+'}')
    macro('BFGSRootInterval',tex_interval(result['root']['narrow'],11))
    macro('BFGSCheckCount',str(len(result['checks'])))
    node_rows=[]
    for i,n in enumerate(result['geometry']['nodes']):
        node_rows.append(str(i)+' & '+' & '.join(tex_interval(n[k],4) for k in ['t','eta','d'])+r' \\')
    macro('BFGSNodeRows','\n'.join(node_rows))
    gap_rows=[]
    for g in result['geometry']['gaps']:
        gap_rows.append(g['branch']+' & '+str(g['gap'])+' & '+tex_interval(g['length'],4)+' & '+tex_interval(g['secant'],4)+r' \\')
    macro('BFGSGapRows','\n'.join(gap_rows))
    bridge_rows=[]
    for g in result['bridges']['gaps']:
        bridge_rows.append(g['branch']+' & '+str(g['gap'])+' & '+str(g['n'])+' & '
                           +' & '.join(tex_interval(g[k],6) for k in ['L','R','remaining'])+r' \\')
    macro('BFGSBridgeRows','\n'.join(bridge_rows))
    macro('BFGSNormRows','\n'.join(str(i)+' & '+tex_interval(n,4)+r' \\' for i,n in enumerate(result['geometry']['norm_squared'])))
    st=result['stability']
    macro('BFGSMagnitudeMatrix',r'\begin{pmatrix}'+(r'\\'+'\n').join(' & '.join(iv.decimal_up(v,3) for v in row) for row in st['magnitude'])+r'\end{pmatrix}')
    macro('BFGSRowBounds','('+r',\,'.join(iv.decimal_up(v,3) for v in st['rows'])+')')
    macro('BFGSTransverseMatrix',r'\begin{pmatrix}'+(r'\\'+'\n').join(' & '.join(tex_interval(v,6) for v in row) for row in st['matrix'])+r'\end{pmatrix}')
    (directory/'certified_bounds.tex').write_text('\n'.join(lines)+'\n')
    report=['All '+str(len(result['checks']))+' exact checks passed.',
            'Lemma 2.3; Appendix A.2, (A.3): root interval Y = '+tex_interval(result['root']['narrow'],11),
            'Explicit realization of Lemmas 2.6 and 2.10: bridge indices (+, then -) = '+str([g['n'] for g in result['bridges']['gaps']]),
            'Proposition A.1, (A.12): row-sum bounds = '+str([iv.decimal_up(v,3) for v in st['rows']]),
            'Proposition A.1: certified maximum row sum = '+iv.decimal_up(st['norm'],3),
            'Proposition A.1: contraction bound = '+iv.decimal_up(STABILITY_NORM_BOUND,2),
            'No binary floating-point comparisons are used.']
    (directory/'bounds.txt').write_text('\n'.join(report)+'\n')
    return report

if __name__=='__main__':
    result=verify()
    print('\n'.join(write_outputs(result)))
