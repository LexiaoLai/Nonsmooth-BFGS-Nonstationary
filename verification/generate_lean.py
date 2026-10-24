#!/usr/bin/env python3
"""Generate kernel-checkable rational interval proofs for this manuscript.

This generator is untrusted: Lean rechecks every arithmetic enclosure.
No generated file uses native_decide, external results, or new axioms.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import argparse
import verify as v

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'BFGS' / 'Counterexample' / 'Certificates'
GRID = 10**30

def down(x): return F(x.numerator*GRID//x.denominator,GRID)
def up(x): return -down(-x)
def qstr(x):
    x=F(x)
    return str(x.numerator) if x.denominator==1 else f'{x.numerator} / {x.denominator}'

class Trace:
    nodes=[]
    cache={}
    def __init__(self,n): self.n=n
    @classmethod
    def make(cls,op,*args):
        key=(op,*args)
        if key in cls.cache:return cls(cls.cache[key])
        if op=='var':lo,hi=v.ROOT_LO,v.ROOT_HI
        elif op=='const':lo=hi=args[0]
        else:
            vals=[cls.nodes[i][2:] for i in args]
            if op=='add':lo,hi=vals[0][0]+vals[1][0],vals[0][1]+vals[1][1]
            elif op=='neg':lo,hi=-vals[0][1],-vals[0][0]
            elif op=='mul':
                p=[a*b for a in vals[0] for b in vals[1]];lo,hi=min(p),max(p)
            elif op=='inv':
                a,b=vals[0]
                if a<=0<=b:raise ArithmeticError(('zero denominator',args,vals))
                lo,hi=1/b,1/a
            else:raise ValueError(op)
            lo,hi=down(lo),up(hi)
        n=len(cls.nodes);cls.nodes.append((op,args,lo,hi));cls.cache[key]=n
        return cls(n)
    @classmethod
    def coerce(cls,x):return x if isinstance(x,cls) else cls.make('const',F(x))
    def const(self):
        op,args,*_=self.nodes[self.n]
        return args[0] if op=='const' else None
    def __add__(self,b):
        b=self.coerce(b);a0,b0=self.const(),b.const()
        if a0 is not None and b0 is not None:return self.coerce(a0+b0)
        if a0==0:return b
        if b0==0:return self
        return self.make('add',self.n,b.n)
    __radd__=__add__
    def __neg__(self):
        if self.const() is not None:return self.coerce(-self.const())
        return self.make('neg',self.n)
    def __sub__(self,b):return self+-self.coerce(b)
    def __rsub__(self,b):return self.coerce(b)+-self
    def __mul__(self,b):
        b=self.coerce(b);a0,b0=self.const(),b.const()
        if a0 is not None and b0 is not None:return self.coerce(a0*b0)
        if a0==0 or b0==0:return self.coerce(0)
        if a0==1:return b
        if b0==1:return self
        return self.make('mul',self.n,b.n)
    __rmul__=__mul__
    def inv(self):
        if self.const() is not None:return self.coerce(1/self.const())
        return self.make('inv',self.n)
    def __truediv__(self,b):return self*self.coerce(b).inv()
    def __rtruediv__(self,b):return self.coerce(b)*self.inv()


def build():
    Trace.nodes=[];Trace.cache={}
    selected=[gap['n'] for gap in v.bridge_certificate(v.IV(v.ROOT_LO,v.ROOT_HI))['gaps']]
    b=Trace.make('var');named={}
    def name(k,x):
        if isinstance(x,list):
            for i,a in enumerate(x):name(f'{k}_{i}',a)
        else:named[k]=Trace.coerce(x).n
        return x
    g,H,x,K,r=v.data(b)
    for k,a in [('gradient',g),('metric',H),('position',x),('hessian',K)]:name(k,a)
    values=[v.dot(a,c) for a,c in zip(g,x)];name('value',values)
    nodes,coords=v.interpolation_nodes(g,x,K,make_interval=Trace.coerce)
    name('coordinate',coords)
    for i,d in enumerate(nodes):
        for k,a in d.items():name(f'node_{i}_{k}',a)
    norms=[v.dot(a,a) for a in x];name('normSquared',norms)
    steps=[v.neg(v.mv(H[i],g[i])) for i in range(4)]
    curvature=[v.dot(steps[i],v.sub(g[i+1],g[i])) for i in range(4)]
    name('curvature',curvature)
    armijo=[values[i]+F(3,100)*v.dot(g[i],steps[i])-values[i+1] for i in range(4)]
    wolfe=[v.dot(v.sub(g[i+1],v.scale(g[i],F(3,5))),steps[i]) for i in range(4)]
    name('armijo',armijo);name('wolfe',wolfe)
    for sign,branch in v.interpolation_branches(nodes,make_interval=Trace.coerce):
        for j,(l,u) in enumerate(zip(branch,branch[1:])):
            name(f'gap_{sign}_{j}',u['t']-l['t'])
            name(f'secant_{sign}_{j}',(u['eta']-l['eta'])/(u['t']-l['t']))
    for (sign,branch),degrees in zip(v.interpolation_branches(nodes,outer=True,make_interval=Trace.coerce),[selected[:5],selected[5:]]):
        for j,(l,u,n) in enumerate(zip(branch,branch[1:],degrees)):
            d=v.bridge_parameters(l,u,n)
            for k in ['L','R','remaining']:name(f'bridge_{sign}_{j}_{k}',d[k])
    prod=v.eye(5)
    for i in range(4):
        columns=[v.diff_step(H[i],g[i],g[i+1],K[i],K[i+1],*v.unpack(a),True) for a in v.eye(5)]
        name(f'jacobian_{i}',v.tr(columns))
        prod=v.mm(v.tr(columns),prod)
        name(f'product_{i}',prod)
    prod=v.ms(prod,1/r)
    w=v.pack(x[0],H[0]);keep=[0,1,3,4]
    A=[[prod[i][j]-w[i]*prod[2][j] for j in keep] for i in keep]
    M=v.mm(v.mm(v.S,A),v.SI)
    name('returnDerivative',prod);name('baseState',w);name('conjugatedTransverse',M)
    return named


def emit(out,chunk_size=90):
    named=build();out.mkdir(parents=True,exist_ok=True)
    previous='BFGS.Counterexample.Certificates.IntervalBase'
    modules=[]
    for start in range(0,len(Trace.nodes),chunk_size):
        ix=start//chunk_size;module=f'BFGS.Counterexample.Certificates.IntervalTrace{ix}'
        lines=[f'import {previous}', '', '/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/',
          'namespace BFGS.Counterexample.Trace','noncomputable section','open BFGS RationalInterval',
          'set_option maxHeartbeats 0','set_option maxRecDepth 100000','set_option linter.unusedVariables false','']
        for n in range(start,min(start+chunk_size,len(Trace.nodes))):
            op,args,lo,hi=Trace.nodes[n]
            ref=lambda j:f'(n{j} b)'
            if op=='var':expr='b'
            elif op=='const':expr=f'(({qstr(args[0])} : ℚ) : ℝ)'
            elif op=='neg':expr=f'-{ref(args[0])}'
            elif op=='inv':expr=f'1 / {ref(args[0])}'
            else:expr=f'{ref(args[0])} '+('+' if op=='add' else '*')+f' {ref(args[1])}'
            lines += [f'def n{n} (b : ℝ) : ℝ := {expr}',
                f'def i{n} : RationalInterval := ⟨({qstr(lo)} : ℚ), ({qstr(hi)} : ℚ)⟩',
                f'theorem b{n} (b : ℝ) (hb : rootInterval.Contains b) : i{n}.Contains (n{n} b) := by']
            if op=='var':lines += [f'  convert hb using 1 <;> norm_num [n{n}, i{n}, rootInterval, RationalInterval.Contains]']
            elif op=='const':lines += [f'  exact RationalInterval.contains_point ({qstr(args[0])} : ℚ)']
            else:
                refs=[f'(b{j} b hb)' for j in args]
                if op=='inv':
                    a=args[0];sgn='positive' if Trace.nodes[a][2]>0 else 'negative'
                    base=f'RationalInterval.contains_inv_of_{sgn} {refs[0]} (by norm_num [i{a}])'
                else:base=f'RationalInterval.contains_{op} '+ ' '.join(refs)
                unfolds=', '.join([f'i{n}']+[f'i{j}' for j in args]+[f'RationalInterval.{op}'])
                lines += [f'  exact RationalInterval.contains_widen ({base})',
                    f'    (by norm_num [{unfolds}]) (by norm_num [{unfolds}])']
            lines+=['']
        (out/f'IntervalTrace{ix}.lean').write_text('\n'.join(lines)+'\n')
        previous=module;modules.append(module)
    metadata={'nodes':len(Trace.nodes),'modules':modules,'named':named,
      'bounds':{k:[str(Trace.nodes[n][2]),str(Trace.nodes[n][3])] for k,n in named.items()},
      'operations':[(op,[str(a) for a in args] if op=='const' else list(args)) for op,args,_,_ in Trace.nodes]}
    (out/'trace_metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
    print(f'Generated {len(Trace.nodes)} arithmetic nodes in {len(modules)} modules.')
    return metadata

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=OUT)
    args=parser.parse_args();emit(args.output)
