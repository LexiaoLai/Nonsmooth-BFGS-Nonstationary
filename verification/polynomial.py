"""Exact arithmetic modulo the cycle quartic, using Fraction only.

An identity here is a polynomial identity modulo P, not a floating-point
residual test. Every division explicitly verifies a multiplicative inverse.
"""
from fractions import Fraction as F

P = tuple(map(F, [65536,352256,-587665,-576632,777924]))

def reduce(coeff):
    a=list(map(F,coeff))
    while len(a)>4:
        c=a[-1]/P[4]; k=len(a)-5
        for j in range(5): a[k+j]-=c*P[j]
        a.pop()
    return tuple(a+[F(0)]*(4-len(a)))

class Algebraic:
    def __init__(self,value=0):
        if isinstance(value,Algebraic): self.c=value.c
        elif isinstance(value,(tuple,list)): self.c=reduce(value)
        elif isinstance(value,float): raise TypeError('Use exact rational inputs')
        else:self.c=(F(value),F(0),F(0),F(0))
    def __add__(self,b):
        b=Algebraic(b);return Algebraic([x+y for x,y in zip(self.c,b.c)])
    __radd__=__add__
    def __neg__(self):return Algebraic([-x for x in self.c])
    def __sub__(self,b):return self+-Algebraic(b)
    def __rsub__(self,b):return Algebraic(b)+-self
    def __mul__(self,b):
        b=Algebraic(b);c=[F(0)]*7
        for i,x in enumerate(self.c):
            for j,y in enumerate(b.c):c[i+j]+=x*y
        return Algebraic(c)
    __rmul__=__mul__
    def inverse(self):
        cols=[(self*Algebraic([0]*j+[1])).c for j in range(4)]
        rows=[[cols[j][i] for j in range(4)]+[F(i==0)] for i in range(4)]
        for k in range(4):
            pivot=next((i for i in range(k,4) if rows[i][k]),None)
            if pivot is None:raise ZeroDivisionError('Noninvertible residue class')
            rows[k],rows[pivot]=rows[pivot],rows[k]
            t=rows[k][k];rows[k]=[v/t for v in rows[k]]
            for i in range(4):
                if i!=k:
                    t=rows[i][k];rows[i]=[x-t*y for x,y in zip(rows[i],rows[k])]
        out=Algebraic([row[-1] for row in rows])
        if self*out!=1:raise ArithmeticError('Inverse check failed')
        return out
    def __truediv__(self,b):return self*Algebraic(b).inverse()
    def __rtruediv__(self,b):return Algebraic(b)*self.inverse()
    def __eq__(self,b):return self.c==Algebraic(b).c
    def __repr__(self):return 'Algebraic('+repr(self.c)+')'

B=Algebraic([0,1])
