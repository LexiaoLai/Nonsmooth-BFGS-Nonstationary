#!/usr/bin/env python3
"""Build and execute verification.ipynb, then export offline verification.html.

Install requirements-notebook.txt in a virtual environment and run this file
with that environment's Python. The fresh kernel uses the same interpreter.
The standalone standard-library checker remains independent of these dependencies.
No saved certificate is read and no manuscript file is modified.
"""
from __future__ import annotations

import html
import json
from pathlib import Path
import re
import sys
import tempfile
import textwrap
import xml.etree.ElementTree as ET

import mistune
import nbformat
from jupyter_client import KernelManager
from jupyter_client.kernelspec import KernelSpecManager
from latex2mathml.converter import convert as mathml
from nbclient import NotebookClient
from pygments import highlight
from pygments.formatters import HtmlFormatter
from pygments.lexers import PythonLexer

HERE = Path(__file__).resolve().parent


def markdown(source):
    return nbformat.v4.new_markdown_cell(textwrap.dedent(source).strip())


def code(source, *, show_source=False):
    return nbformat.v4.new_code_cell(textwrap.dedent(source).strip(),
                                   metadata={"show_source": show_source})


def make_notebook():
    cells=[
        markdown(r"""
        # Verification of the BFGS counterexample

        Run the cells in order. This self-contained notebook defines the data
        once and checks each certificate once. The displayed quantities use
        the manuscript's notation, with superscripts for iterations and
        subscripts for coordinates. Section 4 additionally
        specifies the polynomial realization used in the figures and Lean
        proof; the manuscript uses Manni's result for interpolation existence.
        It needs SymPy and IPython; it reads no project files or saved results.
        Formulas, matrices and tables use native Jupyter LaTeX outputs.
        Identities
        use exact polynomial arithmetic. Inequalities use outward rational
        intervals with 256-bit dyadic endpoints. The interpolation,
        positive-definiteness, local Lipschitz and open-basin arguments remain
        the analytical proofs in the manuscript.
        Section 2 provides an independent symbolic check of the analytically
        proved identities; Sections 1, 3 and 5 certify the finite inequalities.
        The root interval, interpolation tables, matrix $\Gamma$ and its
        row sums are computed from the defining data. Displayed decimal
        bounds are rounded outward; no output table or matrix is supplied
        as input.
        """),
        code(r"""
        from fractions import Fraction as F
        import platform
        import sympy as sp
        from IPython.display import display, Math, Latex

        def require(condition,message):
            if not condition: raise ArithmeticError(message)

        def equation(source):
            display(Math(source))

        def table(headings,rows,math_columns=(),math_headings=(),caption=None):
            def text(value):
                escapes={'\\':r'\backslash ', '{':r'\{', '}':r'\}', '&':r'\&',
                         '%':r'\%', '$':r'\$', '#':r'\#', '_':r'\_'}
                return r'\text{'+''.join(escapes.get(char,char) for char in str(value))+'}'
            def entry(value,column):
                return str(value) if column in math_columns else text(value)
            heading=' & '.join(h if j in math_headings else text(h) for j,h in enumerate(headings))
            body=r'\\'.join(' & '.join(entry(value,j) for j,value in enumerate(row)) for row in rows)
            if caption: print(caption)
            display(Latex(r'\[\begin{array}{'+'l'*len(headings)+'}'
                          +heading+r'\\\hline '+body+r'\end{array}\]'))

        def fraction(q):
            q=sp.Rational(q)
            return F(int(q.p),int(q.q))

        def exact(q):
            if isinstance(q,float): raise TypeError('Use exact rational inputs.')
            return F(q)

        _IV_GRID=2**256
        def downward(q):
            q=exact(q)
            return F((q.numerator*_IV_GRID)//q.denominator,_IV_GRID)
        def upward(q):
            return -downward(-exact(q))

        class IV:
            def __init__(self,a,b=None):
                if isinstance(a,IV):
                    if b is not None: raise TypeError('An interval copy has one argument.')
                    self.lo,self.hi=a.lo,a.hi
                else:
                    a,b=exact(a),exact(a if b is None else b)
                    require(a<=b,'Unordered interval endpoints')
                    self.lo,self.hi=downward(a),upward(b)
            def __add__(self,b):
                b=IV(b)
                return IV(self.lo+b.lo,self.hi+b.hi)
            __radd__=__add__
            def __neg__(self): return IV(-self.hi,-self.lo)
            def __sub__(self,b): return self+-IV(b)
            def __rsub__(self,b): return IV(b)+-self
            def __mul__(self,b):
                b=IV(b)
                products=[x*y for x in (self.lo,self.hi) for y in (b.lo,b.hi)]
                return IV(min(products),max(products))
            __rmul__=__mul__
            def __truediv__(self,b):
                b=IV(b)
                if b.lo<=0<=b.hi: raise ZeroDivisionError('Interval denominator contains zero.')
                return self*IV(1/b.hi,1/b.lo)
            def __rtruediv__(self,b): return IV(b)/self
            def mag(self): return max(abs(self.lo),abs(self.hi))

        def decimal_bound(value,places=6,up=False):
            value=exact(value); scale=10**places; numerator=value.numerator*scale
            integer=-((-numerator)//value.denominator) if up else numerator//value.denominator
            sign='-' if integer<0 else ''; whole,part=divmod(abs(integer),scale)
            return f'{sign}{whole}.{part:0{places}d}' if places else f'{sign}{whole}'
        def enclosure(value,places=6):
            return f'[{decimal_bound(value.lo,places)}, {decimal_bound(value.hi,places,True)}]'
        def checked_enclosure(value,lower,upper):
            require(F(lower)<=value.lo and value.hi<=F(upper),'Published enclosure does not contain the calculation')
            return f'[{lower}, {upper}]'
        def decimal_matrix(matrix,places):
            return r'\begin{pmatrix}'+r'\\'.join(
                ' & '.join(decimal_bound(value,places) for value in row) for row in matrix)+r'\end{pmatrix}'

        def polynomial_interval(poly,interval):
            value=IV(0)
            for coefficient in poly.all_coeffs(): value=value*interval+fraction(coefficient)
            return value
        print('Python',platform.python_version(),'| SymPy',sp.__version__)
        """),
        markdown(r"""
        ## 1. Data and isolated root

        **Manuscript:** Section 2.1, Lemma 2.3, equations (2.3)–(2.9); the refined root
        interval is (A.3) in Appendix A.2.

        The following exact definitions specify the quartic, involution,
        gradients, inverse Hessian matrices and positions. Endpoint signs and
        a derivative lower bound isolate the root in $(0.9178,0.9179)$.
        Exact bisection on a decimal grid then computes a narrower interval
        $Y$, whose endpoint signs enclose the same root. The interpolation tables use the coarse interval;
        the remaining interval evaluations use $Y$.
        In the symbolic formulas, $b$ is a free variable; polynomial remainders
        in Section 2 establish identities at the root. Interval evaluation
        replaces it by an independent variable $\lambda\in Y$, as in the
        appendix; a root identity is not assumed to hold for every $\lambda$.

        The matrices $H^0,H^1,J$ and constants $\rho,r$ displayed below
        determine the cycle by
        $$
        (g^0,g^1,g^2,g^3,g^4)=(e_1,e_2,Je_1,Je_2,e_1),\qquad
        (H^2,H^3,H^4)=(\rho J^TH^0J,\rho J^TH^1J,rH^0).
        $$
        With $v_0=(b+3/2,b+1/2)^T$, the positions are
        $$
        x^0=\frac{(I+\rho J^T)v_0}{1-r},\quad
        x^1=x^0-(1,1/2)^T,\quad
        (x^2,x^3,x^4)=(\rho J^Tx^0,\rho J^Tx^1,rx^0).
        $$
        Finally, $s^i=-H^ig^i$ and $y^i=g^{i+1}-g^i$ for $0\le i<4$,
        and $f^i=(g^i)^Tx^i$ for $0\le i\le4$.
        """),
        code(r"""
        b=sp.Symbol('b'); Q=sp.Rational
        P=sp.Poly(777924*b**4-576632*b**3-587665*b**2+352256*b+65536,b,domain=sp.QQ)
        rho=Q(8,9); r=rho**2; I=sp.eye(2)
        p=-9*(882*b**2-463*b-256)/(640*(2*b-1))
        t=-(3087*b**2-2233*b-256)/(320*(2*b-1))
        q=(15876*b**3-4316*b**2-6815*b-2304)/(1280*b*(2*b-1))
        J=sp.Matrix([[p,t],[q,-p]])
        e1,e2=sp.Matrix([1,0]),sp.Matrix([0,1])
        g=[e1,e2,J*e1,J*e2,e1]
        H0=sp.Matrix([[1,Q(1,2)],[Q(1,2),b/4+Q(1,8)]])
        H1=sp.Matrix([[b+Q(3,2),b+Q(1,2)],[b+Q(1,2),b]])
        def compact(matrix): return matrix.applyfunc(sp.cancel)
        H=[compact(h) for h in [H0,H1,rho*J.T*H0*J,rho*J.T*H1*J,r*H0]]
        v0=sp.Matrix([b+Q(3,2),b+Q(1,2)])
        x0=(I+rho*J.T)*v0/(1-r); x1=x0-sp.Matrix([1,Q(1,2)])
        x=[compact(point) for point in [x0,x1,rho*J.T*x0,rho*J.T*x1,r*x0]]
        s=[compact(-H[i]*g[i]) for i in range(4)]
        y=[compact(g[i+1]-g[i]) for i in range(4)]
        curvature=[sp.cancel((s[i].T*y[i])[0]) for i in range(4)]
        target_curvature=[Q(1,2),81*b/32,Q(4,9),9*b/4]
        m=F(1,100); beta=list(map(F,['1.9','1.6','-4.1','0.2']))
        c1,c2=F(3,100),F(3,5)
        S=sp.Matrix([[464,1077,4501,-1708],[1366,2793,10000,552],
                     [-448,-1058,-4343,1648],[16,293,1787,-2075]])

        def polynomial_at(a): return fraction(P.eval(Q(a.numerator,a.denominator)))
        coarse_lo,coarse_hi=F('0.9178'),F('0.9179')
        coarse_values=[polynomial_at(a) for a in (coarse_lo,coarse_hi)]
        derivative_lower=3111696*coarse_lo**3-1729896*coarse_hi**2-1175330*coarse_hi+352256
        require(coarse_values[0]<-2 and coarse_values[1]>19 and derivative_lower>200000,
                'Coarse root isolation')
        def refine_root_interval(lo,hi,places=11):
            grid=10**places; left,right=lo*grid,hi*grid
            require(left.denominator==right.denominator==1,'Root bracket must lie on the decimal grid')
            require(polynomial_at(lo)<0<polynomial_at(hi),'Root bracket signs')
            left,right=int(left),int(right)
            while right-left>1:
                middle=(left+right)//2; value=polynomial_at(F(middle,grid))
                if value==0: return F(middle-1,grid),F(middle+1,grid)
                if value<0: left=middle
                else: right=middle
            return F(left,grid),F(right,grid)
        root_lo,root_hi=refine_root_interval(coarse_lo,coarse_hi)
        Y=IV(root_lo,root_hi)
        require(coarse_lo<root_lo<root_hi<coarse_hi,'Nested root intervals')
        endpoint_values=[polynomial_at(a) for a in (root_lo,root_hi)]
        derivative=polynomial_interval(P.diff(),Y)
        require(endpoint_values[0]<0<endpoint_values[1],'Root endpoint signs')
        require(Y.lo>F('0.9') and (2*Y-1).lo>F('0.8'),'Parameter denominator bounds')
        equation(r'P(b)='+sp.latex(P.as_expr()))
        equation(r'J=\begin{pmatrix}p&t\\q&-p\end{pmatrix},\qquad'
                 +r'\rho='+sp.latex(rho)+r',\quad r=\rho^2='+sp.latex(r))
        for name,value in [('p',p),('t',t),('q',q)]:
            equation(name+'='+sp.latex(value))
        equation(r'H^0='+sp.latex(H[0])+r',\qquad H^1='+sp.latex(H[1]))
        table(('Quantity','Certified enclosure or lower bound'),[
            (r'[a,c]',f'[{decimal_bound(coarse_lo,4)}, {decimal_bound(coarse_hi,4)}]'),
            ('P(a)',enclosure(IV(coarse_values[0]),6)),
            ('P(c)',enclosure(IV(coarse_values[1]),6)),
            (r'\inf_{\lambda\in[a,c]}P\prime(\lambda)\ge',decimal_bound(derivative_lower,6)),
            ('Y',f'[{decimal_bound(root_lo,11)}, {decimal_bound(root_hi,11)}]'),
            (f'P({decimal_bound(root_lo,11)})',enclosure(IV(endpoint_values[0]),12)),
            (f'P({decimal_bound(root_hi,11)})',enclosure(IV(endpoint_values[1]),12)),
            (r'P\prime(Y)',enclosure(derivative,6))],math_columns=(0,1),
            caption='Lemma 2.3 and equation (A.3): root certificates')
        equation(r'P(a)<-2,\quad P(c)>19,\quad P\prime(\lambda)>200000'
                 +r'\ (\lambda\in[a,c]),\qquad b\in Y')
        """,show_source=True),
        markdown(r"""
        ## 2. Exact cycle identities

        **Manuscript:** Lemma 2.5, equations (2.11) and (2.12), in Section 2.1.

        For a residual $N(b)/D(b)$, a zero numerator remainder modulo $P$
        proves equality at its roots, provided $\gcd(D,P)=1$. The original
        divisors are also checked before cancellation. The factorized update is
        $\mathcal B(H,s,y)=(I-sy^T/c)H(I-ys^T/c)+ss^T/c$, where $c=s^Ty$.
        The tables report only the necessary divisor checks and the fourteen
        identities stated in the exact-cycle lemma.
        """),
        code(r"""
        def rational_parts(expression):
            require(not sp.sympify(expression).has(sp.Float),'Inexact symbolic input')
            numerator,denominator=sp.cancel(expression).as_numer_denom()
            return sp.Poly(numerator,b,domain=sp.QQ),sp.Poly(denominator,b,domain=sp.QQ)
        def check_nonzero(expression):
            numerator,denominator=rational_parts(expression)
            gcds=[part.gcd(P).monic() for part in (numerator,denominator)]
            require(all(gcd.degree()==0 for gcd in gcds),'A divisor vanishes at a root')
            return [str(gcd.as_expr()) for gcd in gcds]
        def check_equality(residual):
            matrix=residual if isinstance(residual,sp.MatrixBase) else sp.Matrix([residual])
            remainders=[]
            for entry in matrix:
                numerator,denominator=rational_parts(entry)
                require(denominator.gcd(P).degree()==0,'Undefined equality')
                remainder=numerator.rem(P)
                require(remainder.is_zero,'Nonzero polynomial remainder')
                remainders.append(remainder.as_expr())
            return sp.Matrix(matrix.rows,matrix.cols,remainders)
        def BFGS(H,s,y):
            c=sp.cancel((s.T*y)[0])
            left,right=compact(I-s*y.T/c),compact(I-y*s.T/c)
            return compact(left*H*right+s*s.T/c)

        divisors={'b':b,'2b-1':2*b-1,'1-r':1-r}
        divisors.update({rf'(s^{{{i}}})^Ty^{{{i}}}':curvature[i] for i in range(4)})
        table(('Original divisor','Numerator gcd with P','Denominator gcd with P'),
              [(name,*check_nonzero(value)) for name,value in divisors.items()],math_columns=(0,1,2))
        desired=[]
        for i in range(4):
            desired.extend([
                (rf'x^{{{i+1}}}=x^{{{i}}}+s^{{{i}}}',x[i+1]-x[i]-s[i]),
                (rf'H^{{{i+1}}}=\mathcal B(H^{{{i}}},s^{{{i}}},y^{{{i}}})',H[i+1]-BFGS(H[i],s[i],y[i])),
                (rf'(s^{{{i}}})^Ty^{{{i}}}={sp.latex(target_curvature[i])}',curvature[i]-target_curvature[i])])
        desired.extend([(r'H^4=rH^0',H[4]-r*H[0]),(r'x^4=rx^0',x[4]-r*x[0])])
        table(('Conclusion','Entrywise numerator remainder modulo P'),
              [(equality,sp.latex(check_equality(residual))) for equality,residual in desired],math_columns=(0,1),
              caption=f'Lemma 2.5, equations (2.11)–(2.12): {len(desired)} exact identities')
        """,show_source=True),
        markdown(r"""
        ## 3. Geometry, interpolation data and line-search margins

        **Manuscript:** Propositions 2.7–2.9
        in Section 2.2; Tables 1–2 in Appendix A.1.
        The data are defined in (2.15), (2.17), (2.19), (2.21)–(2.22),
        and the Hessian coefficients are fixed in (2.28).

        Evaluate the defining rational formulas on $Y$, using the shorter
        position formula (A.2). Division always excludes zero. The positive norm
        bounds justify the Hessians
        $K^i=\beta^i q^i(q^i)^T/\|x^i\|^2$, where
        $q^i=(-x_2^i,x_1^i)^T$, and $K^4=K^0/r$.
        As in the manuscript, use $M=\begin{pmatrix}1&0.05\\0&1\end{pmatrix}$,
        $z^i=M^{-1}x^i$ and $v=Me_2=(0.05,1)^T$. Set
        $t^i=z_2^i/|z_1^i|$, $\eta^i=f^i/|z_1^i|$,
        $d^i=(g^i)^Tv$ and $k^i=|z_1^i|v^TK^iv$.
        The Hessian coefficients used for the stability calculation are
        $(\beta^0,\beta^1,\beta^2,\beta^3)=(1.9,1.6,-4.1,0.2)$.
        The manuscript's Armijo and Wolfe margins are
        $$
        \mathsf A^i=f^i+0.03(g^i)^Ts^i-f^{i+1},\qquad
        \mathsf W^i=(g^{i+1})^Ts^i-0.6(g^i)^Ts^i.
        $$
        Their positivity and $(g^i)^Ts^i<0$ certify the parameter range
        $0<c_1\le0.03<0.6\le c_2<1$.

        To compute Tables 1 and 2, evaluate the formulas directly on
        $[0.9178,0.9179]$, using the shorter formula for $x^0$ in (A.2).
        The code checks that this formula agrees with the original one at
        the root. It then computes $t^i,\eta^i,d^i$, the consecutive gaps
        and their secant slopes. Each displayed lower endpoint is rounded
        down and each upper endpoint up to four decimal places; no table
        entries are supplied as input. These enclosures establish
        $0.02<d^i\le1$, gaps greater than one, and secant slopes in $(0.5,2)$.
        The calculations on $Y$ remain in `nodes` and `gaps` for
        the subsequent realization and stability calculations.
        """),
        code(r"""
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

        short_x0=sp.Matrix([-9*(8978*b**2-6527*b-2304)/(5440*b),
                            9*(1764*b**2-2671*b+1488)/2720])
        check_equality(x[0]-short_x0)

        def interval_cycle_data(lam):
            rho=F(8,9); r=rho*rho
            p=-9*(882*lam*lam-463*lam-256)/(640*(2*lam-1))
            t=-(3087*lam*lam-2233*lam-256)/(320*(2*lam-1))
            q=(15876*lam*lam*lam-4316*lam*lam-6815*lam-2304)/(1280*lam*(2*lam-1))
            J=[[p,t],[q,-p]]
            gradients=[[1,0],[0,1],[p,q],[t,-p],[1,0]]
            H0=[[1,F(1,2)],[F(1,2),lam/4+F(1,8)]]
            H1=[[lam+F(3,2),lam+F(1,2)],[lam+F(1,2),lam]]
            matrices=[H0,H1,ms(mm(mm(tr(J),H0),J),rho),
                      ms(mm(mm(tr(J),H1),J),rho),ms(H0,r)]
            x0=[-9*(8978*lam*lam-6527*lam-2304)/(5440*lam),
                 9*(1764*lam*lam-2671*lam+1488)/2720]
            x1=sub(x0,[1,F(1,2)])
            positions=[x0,x1,scale(mv(tr(J),x0),rho),scale(mv(tr(J),x1),rho),scale(x0,r)]
            hessians=[ms(outer([-point[1],point[0]],[-point[1],point[0]]),coefficient/dot(point,point))
                      for point,coefficient in zip(positions,beta)]
            hessians.append(ms(hessians[0],1/r))
            return gradients,matrices,positions,hessians,r

        gi,Hi,xi,K,ri=interval_cycle_data(Y)
        norms=[dot(point,point) for point in xi]
        require(all(norm.lo>F('0.7') and norm.hi<8 for norm in norms),'Position norm bounds')
        nodes=[];coordinates=[];v=[F(1,20),F(1)]
        for i in range(4):
            z1=xi[i][0]-xi[i][1]/20; coordinates.append(z1)
            require(z1.lo>0 if i<2 else z1.hi<0,'Interpolation branch sign')
            a=z1 if i<2 else -z1
            nodes.append(dict(t=xi[i][1]/a,eta=dot(gi[i],xi[i])/a,
                              d=IV(dot(gi[i],v)),k=a*dot(v,mv(K[i],v))))
        require(all(F('0.02')<node['d'].lo and node['d'].hi<=1 for node in nodes),
                'Published first-derivative bounds')
        def affine_anchor(t): return dict(t=IV(t),eta=IV(t),d=IV(1),k=IV(0))
        interpolation_branches=[(sign,[affine_anchor(-1),nodes[a],nodes[c],affine_anchor(6)])
                                for sign,a,c in [('+',0,1),('-',2,3)]]
        gaps=[]
        for sign,branch in interpolation_branches:
            for j,(left,right) in enumerate(zip(branch,branch[1:])):
                ell=right['t']-left['t']; secant=(right['eta']-left['eta'])/ell
                require(ell.lo>1 and F('0.5')<secant.lo and secant.hi<2,
                        'Published gap and secant bounds')
                gaps.append(dict(branch=sign,gap=j,length=ell,secant=secant))
        steps=[neg(mv(Hi[i],gi[i])) for i in range(4)]
        differences=[sub(gi[i+1],gi[i]) for i in range(4)]
        curvatures=[dot(steps[i],differences[i]) for i in range(4)]
        slopes=[dot(gi[i],steps[i]) for i in range(4)]
        values=[dot(gradient,point) for gradient,point in zip(gi,xi)]
        armijo=[values[i]+c1*slopes[i]-values[i+1] for i in range(4)]
        wolfe=[dot(sub(gi[i+1],scale(gi[i],c2)),steps[i]) for i in range(4)]
        require(all(c.lo>F('0.4') for c in curvatures),'Published curvature lower bound')
        require(all(slope.hi<0 for slope in slopes),'Descent directions')
        require(all(margin.lo>0 for margin in armijo+wolfe),'Strict line-search margins')
        for value,(lower,upper) in zip(armijo[:2],[('0.0575','0.0611'),('0.0281','0.0312')]):
            require(F(lower)<value.lo and value.hi<F(upper),'Published Armijo enclosure')
        coordinate_bounds=[('1.1','1.3'),('0.2','0.3'),('-1.2','-1'),('-0.3','-0.2')]
        for value,(lower,upper) in zip(coordinates,coordinate_bounds):
            require(F(lower)<value.lo and value.hi<F(upper),'Published coordinate bounds')
        def coarse_interpolation_data(lam):
            gradients,_,positions,_,_=interval_cycle_data(lam)
            coarse_nodes=[]
            for i,(point,gradient) in enumerate(zip(positions[:4],gradients[:4])):
                z1=point[0]-point[1]/20
                require(z1.lo>0 if i<2 else z1.hi<0,'Coarse interpolation branch sign')
                a=z1 if i<2 else -z1
                node=dict(t=point[1]/a,eta=dot(gradient,point)/a,
                          d=IV(F(1,20)*gradient[0]+gradient[1]))
                require(F('0.02')<node['d'].lo and node['d'].hi<=1,'Coarse derivative bounds')
                coarse_nodes.append(node)
            coarse_gaps=[]
            for sign,i,j in [('+',0,1),('-',2,3)]:
                branch=[affine_anchor(-1),coarse_nodes[i],coarse_nodes[j],affine_anchor(6)]
                for index,(left,right) in enumerate(zip(branch,branch[1:])):
                    ell=right['t']-left['t']; secant=(right['eta']-left['eta'])/ell
                    require(ell.lo>1 and F('0.5')<secant.lo and secant.hi<2,'Coarse gaps and secants')
                    coarse_gaps.append(dict(branch=sign,gap=index,length=ell,secant=secant))
            return coarse_nodes,coarse_gaps

        coarse_nodes,coarse_gaps=coarse_interpolation_data(IV(coarse_lo,coarse_hi))
        def rounded_bounds(value,places=4):
            return decimal_bound(value.lo,places),decimal_bound(value.hi,places,True)
        node_bounds=[[rounded_bounds(node[key]) for key in ('t','eta','d')] for node in coarse_nodes]
        gap_bounds=[[rounded_bounds(gap[key]) for key in ('length','secant')] for gap in coarse_gaps]
        table(('i',r'\|x^i(\lambda)\|^2'),[(i,enclosure(norm,6)) for i,norm in enumerate(norms)],
              math_columns=(0,1),math_headings=(0,1),
              caption='Lemma 2.5: position bounds, for every λ in Y')
        table(('i',r'z_1^i(\lambda)'),[(i,enclosure(value,6)) for i,value in enumerate(coordinates)],
              math_columns=(0,1),math_headings=(0,1),
              caption='Proposition 2.7: branch signs, for every λ in Y')
        table(('i','t^i',r'\eta^i','d^i'),
              [(i,*(checked_enclosure(node[key],*bounds) for key,bounds in zip(('t','eta','d'),node_bounds[i])))
               for i,node in enumerate(coarse_nodes)],math_columns=(0,1,2,3),math_headings=(0,1,2,3),
              caption='Table 1: computed interpolation enclosures for Proposition 2.8 (rounded outward to four decimals)')
        table((r'h_\sigma','Gap','c-a',r'(B-A)/(c-a)'),
              [(gap['branch'],gap['gap'],*(checked_enclosure(gap[key],*bounds)
                for key,bounds in zip(('length','secant'),gap_bounds[i]))) for i,gap in enumerate(coarse_gaps)],
              math_columns=(0,1,2,3),math_headings=(0,2,3),
              caption='Table 2: computed gap and secant enclosures for Proposition 2.8 (rounded outward to four decimals)')
        table(('i',r'(s^i(\lambda))^Ty^i(\lambda)',r'\mathsf A^i(\lambda)',r'\mathsf W^i(\lambda)'),
              [(i,*(enclosure(data[i]) for data in (curvatures,armijo,wolfe))) for i in range(4)],
              math_columns=(0,1,2,3),math_headings=(0,1,2,3),
              caption='Proposition 2.9, equation (2.19): positive margins for every λ in Y')
        """),
        markdown(r"""
        ## 4. A concrete polynomial realization

        **Manuscript:** an explicit realization of the interpolation
        conditions in Lemma 2.6 and the prescribed
        data in Lemma 2.10, Section 2.2.

        The manuscript proves interpolation existence using Manni's
        parametric construction. The figures and Lean proof use the
        following independent polynomial construction satisfying the same
        conditions. These additional checks identify that concrete
        realization; its formula is not needed for the manuscript proof.

        Adjoin identity data $(t,t,1,0)$ at $t=-1,6$ and outer data
        of the same form at $t=-2,7$. On a gap $[a,c]$ of length $\ell$, use the rescaled endpoint
        data $\mu=\ell m$, $p=\ell d_a$, $q=\ell d_c$,
        $P_0=\ell^2k_a$, $Q_0=\ell^2k_c$ and $\Delta=\eta_c-\eta_a$.
        Choose the least $n\ge0$ for which
        $L_n=P_0+(n+2)(p-\mu)\ge0$,
        $R_n=Q_0-(n+2)(q-\mu)\le0$ and
        $I_n=\mu+2(p+q-2\mu)/(n+4)+(P_0-Q_0)/((n+3)(n+4))<\Delta$.
        Such an integer exists because $p,q,\Delta>\mu$.
        Set
        $$
        \psi(s)=\mu+(1-s)^{n+2}(p-\mu+L_ns)
        +s^{n+2}(q-\mu+R_n(s-1))
        +30(\Delta-I_n)s^2(1-s)^2
        $$
        and $h(a+\ell s)=\eta_a+\int_0^s\psi(u)\,du$ for $0\le s\le1$.
        The added terms in $\psi$ are nonnegative. Its endpoint values are
        $p,q$, its endpoint derivatives are $P_0,Q_0$, and its integral is
        $\Delta$. Thus $h$ matches the prescribed values and first two
        derivatives, with $h'\ge m$. Joining the pieces and extending by
        the identity outside $[-2,7]$ gives the required $C^2$
        semialgebraic functions.

        The following cell certifies the least indices by rational intervals.
        Every smaller index is excluded by an interval proving failure of
        at least one condition. At $n=0$, cancel $\mu$ first to resolve the
        exact zero remaining integral on identity gaps.
        """),
        code(r"""
        branches=[(sign,[affine_anchor(-2),*branch,affine_anchor(7)])
                  for sign,branch in interpolation_branches]
        bridges=[]
        for sign,branch in branches:
            for j,(left,right) in enumerate(zip(branch,branch[1:])):
                ell=right['t']-left['t']; delta=right['eta']-left['eta']; mu=ell*m
                p0,q0=ell*left['d'],ell*right['d']
                P0,Q0=ell*ell*left['k'],ell*ell*right['k']
                require(ell.lo>0 and (delta-mu).lo>0,'Interpolation ordering and secant lower bound')
                rejected=[]
                for n in range(10000):
                    L=P0+(n+2)*(p0-mu); R=Q0-(n+2)*(q0-mu)
                    integral=((p0+q0)/2+(P0-Q0)/12 if n==0 else
                              mu+2*(p0+q0-2*mu)/(n+4)+(P0-Q0)/((n+3)*(n+4)))
                    remaining=delta-integral
                    if L.lo>=0 and R.hi<=0 and remaining.lo>0:
                        bridges.append(dict(branch=sign,gap=j,n=n,L=L,R=R,remaining=remaining,rejected=rejected))
                        break
                    failures=[]
                    if L.hi<0: failures.append('L<0')
                    if R.lo>0: failures.append('R>0')
                    if remaining.hi<=0: failures.append('Delta-I<=0')
                    require(bool(failures),'Root interval too wide to decide a bridge index')
                    rejected.append((n,failures))
                else: raise ArithmeticError('No certified bridge index below 10000')
        table((r'h_\sigma','Gap',r'n_{\min}','L_n','R_n',r'\Delta-I_n','Smaller indices excluded'),
              [(gap['branch'],gap['gap'],gap['n'],*(enclosure(gap[key]) for key in ('L','R','remaining')),
                len(gap['rejected'])) for gap in bridges],
              math_columns=(0,1,2,3,4,5,6),math_headings=(0,2,3,4,5),
              caption='Explicit realization satisfying Lemma 2.6 and Lemma 2.10')
        """),
        markdown(r"""
        ## 5. Contraction toward the fixed ray

        **Manuscript:** Proposition A.1 in
        Appendix A.2, used in Lemma 2.12 in Section 2.3.

        **Step 1: differentiate a BFGS step.** In the state coordinates
        $\omega=(x_1,x_2,H_{11},H_{12},H_{22})$, a variation
        $\delta\omega$ specifies $\delta x$ and the symmetric matrix
        $\delta H$. At the cycle state $\omega^i$, equation (A.5) gives
        $$
        \delta g=K^i\delta x,\qquad
        \delta s=-((\delta H)g^i+H^i\delta g),\qquad
        \delta\widehat x=\delta x+\delta s,\qquad
        \delta y=K^{i+1}\delta\widehat x-\delta g.
        $$
        With $c=s^Ty$, $t=Hy$, $d=y^THy$, $N=ts^T+st^T$ and
        $V=ss^T$, the update is $\widehat H=H-N/c+(c+d)V/c^2$.
        The product and quotient rules give $\delta\widehat H$ in (A.7), implemented below. Evaluating at each
        standard basis vector $\delta\omega$ gives the five columns of
        $D^i=D\mathcal T(\omega^i)$, as in (A.8).

        **Step 2: form the derivative toward the fixed ray.** Equations
        (A.9)–(A.10)
        give $D_{\mathrm{tot}}=D^3D^2D^1D^0=D\mathcal T^4(\omega_*)$ and
        $$
        A_{ij}=\frac{(D_{\mathrm{tot}})_{\kappa_i\kappa_j}
        -(\omega_*)_{\kappa_i}(D_{\mathrm{tot}})_{3\kappa_j}}{r},
        \qquad (\kappa_1,\kappa_2,\kappa_3,\kappa_4)=(1,2,4,5).
        $$
        Here $\omega_*=(x_1^0,x_2^0,H_{11}^0,H_{12}^0,H_{22}^0)$.
        Replacing $b$ by $\lambda\in Y$ defines the rational extension
        $\widehat A(\lambda)$, which satisfies $\widehat A(b)=A$.

        **Step 3: certify the entry bounds and row sums.** Use $S$ from
        (A.4) and evaluate
        $S\widehat A(\lambda)S^{-1}$ by interval arithmetic.
        For each resulting interval $\mathbf M_{ij}$, compute
        $\operatorname{mag}(\mathbf M_{ij})$ as the largest absolute endpoint
        and round it upward to three decimal places. These computed entries
        form $\Gamma$ in (A.11). Summing its rows produces (A.12), which
        is then compared with the theorem's contraction threshold $0.78$.
        """),
        code(r"""
        def diff_step(h,g,gp,k,kp,dx,dh):
            s=neg(mv(h,g));y=sub(gp,g);c=dot(s,y)
            dg=mv(k,dx);ds=neg(add(mv(dh,g),mv(h,dg)))
            dxp=add(dx,ds);dy=sub(mv(kp,dxp),dg)
            dc=dot(ds,y)+dot(s,dy)
            t=mv(h,y);d=dot(y,t);N=ma(outer(t,s),outer(s,t));V=outer(s,s)
            dt=add(mv(dh,y),mv(h,dy));dd=2*dot(dy,t)+dot(y,mv(dh,y))
            dV=ma(outer(ds,s),outer(s,ds))
            dN=ma(ma(outer(dt,s),outer(t,ds)),ma(outer(ds,t),outer(s,dt)))
            hp=ma(ma(dh,ms(dN,-1/c)),ms(N,dc/(c*c)))
            hp=ma(hp,ms(V,(dc+dd)/(c*c)-2*(c+d)*dc/(c*c*c)))
            hp=ma(hp,ms(dV,(c+d)/(c*c)))
            return pack(dxp,hp)

        D_tot=eye(5)
        for i in range(4):
            columns=[diff_step(Hi[i],gi[i],gi[i+1],K[i],K[i+1],*unpack(e)) for e in eye(5)]
            D_tot=mm(tr(columns),D_tot)
        D_F=ms(D_tot,1/ri); base=pack(xi[0],Hi[0]); keep=[0,1,3,4]
        A=[[D_F[i][j]-base[i]*D_F[2][j] for j in keep] for i in keep]
        determinant_S=S.det()
        require(determinant_S!=0,'S must be invertible')
        inverse_S=S.inv()
        require(S*inverse_S==sp.eye(4),'Exact inverse of S')
        S_rational=[[fraction(value) for value in row] for row in S.tolist()]
        inverse_rational=[[fraction(value) for value in row] for row in inverse_S.tolist()]
        transformed=mm(mm(S_rational,A),inverse_rational)
        Gamma=[[F(decimal_bound(value.mag(),3,True)) for value in row] for row in transformed]
        for i in range(4):
            for j in range(4):
                require(transformed[i][j].mag()<=Gamma[i][j],f'Outward Gamma entry ({i+1},{j+1})')
        rows=list(map(sum,Gamma))
        require(max(rows)<F(78,100),'Published transverse norm must be below 0.78')
        equation('S='+sp.latex(S)+r',\qquad \det S='+sp.latex(determinant_S)+r'\ne0')
        equation(r'\Gamma='+decimal_matrix(Gamma,3))
        equation(r'|(S\widehat A(\lambda)S^{-1})_{ij}|\le\Gamma_{ij}'
                 +r'\qquad(1\le i,j\le4,\ \lambda\in Y)')
        table(('i',r'\sum_{j=1}^4\Gamma_{ij}'),
              [(i+1,decimal_bound(value,3)) for i,value in enumerate(rows)],
              math_columns=(0,1),math_headings=(0,1),
              caption='Proposition A.1, equation (A.12): verified row sums')
        equation(r'\|SAS^{-1}\|_\infty\le\max_{1\le i\le4}\sum_{j=1}^4\Gamma_{ij}='
                 +decimal_bound(max(rows),3)+r'<0.78<1')
        print('PASS: every entry of Γ in (A.11) and every row sum in (A.12) has been verified.')
        """),
    ]
    notebook=nbformat.v4.new_notebook(cells=cells,metadata={
        'kernelspec':{'display_name':'Python 3','language':'python','name':'python3'},
        'language_info':{'name':'python','version':platform_version()}})
    for i,cell in enumerate(cells): cell['id']=f'bfgs-verification-{i:02d}'
    return notebook


def platform_version():
    import platform
    return platform.python_version()


def execute(notebook):
    # A private kernelspec avoids relying on any globally registered interpreter.
    with tempfile.TemporaryDirectory(prefix="bfgs-verification-kernel-") as folder:
        kernel_dir = Path(folder) / "bfgs-verification"
        kernel_dir.mkdir()
        execution_dir = Path(folder) / "empty-working-directory"
        execution_dir.mkdir()
        (kernel_dir / "kernel.json").write_text(json.dumps({
            "argv": [sys.executable, "-m", "ipykernel_launcher", "-f", "{connection_file}"],
            "display_name": "BFGS verification (build interpreter)",
            "language": "python",
        }), encoding="utf-8")
        manager = KernelManager(
            kernel_name="bfgs-verification",
            kernel_spec_manager=KernelSpecManager(kernel_dirs=[folder]),
        )
        client = NotebookClient(notebook, km=manager, timeout=300, allow_errors=False,
                                resources={"metadata": {"path": str(execution_dir)}})
        try:
            client.execute(cwd=str(execution_dir))
        finally:
            if manager.has_kernel:
                manager.shutdown_kernel(now=True)
    code_cells = [cell for cell in notebook.cells if cell.cell_type == "code"]
    assert all(cell.execution_count is not None for cell in code_cells)
    assert not any(output.output_type == "error" for cell in code_cells for output in cell.outputs)
    return len(code_cells)


def export_html(notebook):
    renderer = mistune.HTMLRenderer(escape=False)
    render = mistune.create_markdown(renderer=renderer, plugins=["table", "math"])
    renderer.register("inline_math", lambda renderer, text: mathml(text, display="inline"))
    renderer.register("block_math", lambda renderer, text:
                      '<div class="display-math">' + mathml(text, display="block") + '</div>\n')
    formatter = HtmlFormatter(cssclass="highlight")
    def render_latex_output(source):
        source = source.strip()
        for opening, closing in [(r"\[", r"\]"), ("$$", "$$"), ("$", "$")]:
            if source.startswith(opening) and source.endswith(closing):
                source = source[len(opening):-len(closing)].strip()
                break
        return '<div class="display-math">' + mathml(source, display="block") + '</div>'
    sections = []
    headings = []
    for cell in notebook.cells:
        if cell.cell_type == "markdown":
            content = render(cell.source)
            for heading in re.findall(r"^## (.+)$", cell.source, flags=re.MULTILINE):
                anchor = f"section-{len(headings) + 1}"
                # Place a reliable anchor before this markdown cell.
                content = f'<a class="section-anchor" id="{anchor}"></a>' + content
                label = re.sub(r"\$([^$]*)\$", r"\1", heading).replace("10^{-12}", "10⁻¹²")
                headings.append((anchor, label))
            sections.append('<section class="markdown-cell">' + content + '</section>')
        elif cell.cell_type == "code":
            execution = cell.execution_count
            source = highlight(cell.source, PythonLexer(), formatter)
            outputs = []
            for output in cell.outputs:
                if output.output_type == "stream":
                    outputs.append('<pre class="stream">' + html.escape(output.text) + '</pre>')
                elif output.output_type in ("display_data", "execute_result"):
                    data = output.data
                    if "text/latex" in data:
                        outputs.append(render_latex_output(data["text/latex"]))
                    elif "text/html" in data:
                        outputs.append(data["text/html"])
                    elif "text/plain" in data:
                        outputs.append('<pre class="stream">' + html.escape(data["text/plain"]) + '</pre>')
                elif output.output_type == "error":
                    raise RuntimeError("Refusing to export a notebook containing an error.")
            opened = ' open' if cell.metadata.get('show_source', False) else ''
            sections.append(f'<section class="code-cell"><details class="cell-source"{opened}>'
                            f'<summary>Executed code [{execution}]</summary>{source}</details>'
                            f'<div class="cell-output">{"".join(outputs)}</div></section>')
    navigation = "".join(f'<a href="#{anchor}">{html.escape(label)}</a>' for anchor, label in headings)
    css = """
    :root { color-scheme: light; --ink: #20323c; --muted: #52636b; --rule: #dbe4e8;
      --accent: #096f69; --paper: #fff; --wash: #f4f7f8; }
    * { box-sizing: border-box; } body { margin: 0; color: var(--ink); background: var(--wash);
      font: 16px/1.65 system-ui, -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif; }
    .layout { max-width: 1480px; margin: auto; display: grid; grid-template-columns: 255px minmax(0, 1fr); }
    nav { position: sticky; top: 0; height: 100vh; padding: 38px 24px; overflow: auto; }
    nav strong { display: block; color: var(--accent); margin-bottom: 20px; }
    nav a { display: block; color: var(--muted); text-decoration: none; margin-bottom: 18px;
      font-size: 14px; line-height: 1.5; } nav a:hover { color: var(--accent); }
    main { min-width: 0; background: var(--paper); padding: 38px 54px 80px; border-left: 1px solid var(--rule); }
    h1 { font-size: 2.05rem; line-height: 1.2; letter-spacing: -.025em; max-width: 840px; margin: 0 0 26px; }
    h2 { font-size: 1.45rem; line-height: 1.35; margin: 45px 0 18px; padding-top: 20px;
      border-top: 2px solid var(--rule); } p { margin: 0 0 18px; }
    a { color: var(--accent); } .section-anchor { scroll-margin-top: 18px; }
    code, pre { font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
    code { font-size: .88em; background: #eef3f4; padding: 2px 4px; border-radius: 3px; }
    pre { overflow-x: auto; white-space: pre; padding: 15px; margin: 10px 0; background: #f5f8f9;
      border: 1px solid var(--rule); border-radius: 5px; font-size: 12px; line-height: 1.55; }
    pre code { background: none; padding: 0; font-size: inherit; }
    details { margin: 12px 0; border: 1px solid var(--rule); border-radius: 6px; padding: 8px 12px; }
    summary { cursor: pointer; color: var(--accent); font-size: 14px; font-weight: 600; }
    .cell-source { background: #fafcfc; } .cell-source .highlight pre { border: 0; }
    .cell-output { margin: 12px 0 28px; } .table-wrap { overflow-x: auto; margin: 14px 0 20px; }
    table { border-collapse: collapse; width: 100%; font-size: 13px; line-height: 1.5; }
    th, td { padding: 10px 11px; border-bottom: 1px solid var(--rule); text-align: left; vertical-align: top; }
    th { color: var(--accent); background: #eef6f5; font-weight: 650; }
    caption { text-align: left; padding: 0 0 12px; color: var(--muted); font-size: 14px; }
    td { font-variant-numeric: tabular-nums; } tr:nth-child(even) td { background: #fafcfc; }
    math { font-size: 1.05em; } .display-math { overflow-x: auto; padding: 8px 0; }
    @media (max-width: 950px) { .layout { display: block; } nav { position: static; height: auto;
      padding: 18px 24px; } nav a { display: inline-block; margin: 0 18px 8px 0; }
      main { padding: 28px 24px 60px; border-left: 0; } }
    @media print { body, main { background: white; } nav, .cell-source { display: none; }
      .layout { display: block; } main { padding: 0; border: 0; } details:not([open]) { display: none; }
      h2 { break-after: avoid; } table, .cell-output { break-inside: avoid; } }
    """
    return ('<!doctype html><html lang="en"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            '<title>Exact BFGS verification</title><style>' + css + formatter.get_style_defs('.highlight')
            + '</style></head><body><div class="layout"><nav><strong>BFGS · exact verification</strong>'
            + navigation + '<a href="verification.ipynb">Download executed notebook</a>'
            + '</nav><main>' + '\n'.join(sections) + '</main></div></body></html>\n')


def main():
    notebook = make_notebook()
    count = execute(notebook)
    nbformat.validate(notebook)
    rendered = export_html(notebook)
    assert '<math ' in rendered and '<script' not in rendered
    assert '\\(' not in rendered and '$$' not in rendered
    for block in re.findall(r'<math\b.*?</math>', rendered, flags=re.DOTALL):
        expression = ET.fromstring(block)
        assert '\\' not in ''.join(expression.itertext()), "Unresolved mathematical command."
    (HERE / 'verification.ipynb').write_text(nbformat.writes(notebook), encoding='utf-8')
    (HERE / 'verification.html').write_text(rendered, encoding='utf-8')
    print(f"PASS: {count} code cells executed in a fresh kernel in an empty directory; zero error outputs.")
    print("Wrote verification.ipynb and verification.html (offline native MathML).")


if __name__ == '__main__':
    main()
