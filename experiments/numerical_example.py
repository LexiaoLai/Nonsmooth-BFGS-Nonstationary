"""Evaluate the manuscript objective, run BFGS, and regenerate its figure.

The root and all iterates are approximated with 100-digit Decimal arithmetic.
These numerical checks illustrate the construction; ../verification/verify.py
provides the independent exact finite certificates. No gradient, step, or
inverse-Hessian estimate is reset to prescribed cycle data during a run.
"""
from __future__ import annotations

from decimal import Decimal, getcontext, localcontext
from pathlib import Path
import hashlib
import io
import json
import math
import os
import numpy as np

ROOT = Path(__file__).resolve().parent
PRECISION = 100
PLOT_STEPS = 120
C1, C2 = Decimal("0.01"), Decimal("0.9")


class NondifferentiabilityError(ArithmeticError):
    pass


def polynomial(b):
    return (((777924*b-576632)*b-587665)*b+352256)*b+65536


def cycle_data():
    """One coherent high-precision approximation of the algebraic data."""
    D = Decimal
    a, c = D("0.9178"), D("0.9179")
    for _ in range(4*getcontext().prec):
        b = (a+c)/2
        if b == a or b == c:
            break
        if polynomial(b) < 0:
            a = b
        else:
            c = b
    b = (a+c)/2
    rho, r = D(8)/9, D(64)/81
    p = -9*(882*b*b-463*b-256)/(640*(2*b-1))
    t = -(3087*b*b-2233*b-256)/(320*(2*b-1))
    q = (15876*b**3-4316*b*b-6815*b-2304)/(1280*b*(2*b-1))
    J = np.array([[p,t],[q,-p]], dtype=object)
    H0 = np.array([[D(1),D(".5")],[D(".5"),b/4+D(1)/8]], dtype=object)
    H1 = np.array([[b+D("1.5"),b+D(".5")],[b+D(".5"),b]], dtype=object)
    H = [H0,H1,rho*J.T@H0@J,rho*J.T@H1@J,r*H0]
    g = [np.array(v,dtype=object) for v in
            [[D(1),D(0)],[D(0),D(1)],[p,q],[t,-p],[D(1),D(0)]]]
    x0 = np.array([-9*(8978*b*b-6527*b-2304)/(5440*b),
                   9*(1764*b*b-2671*b+1488)/2720],dtype=object)
    x1 = x0-np.array([D(1),D(".5")],dtype=object)
    x = [x0,x1,rho*(J.T@x0),rho*(J.T@x1),r*x0]
    Minv = np.array([[D(1),-D(".05")],[D(0),D(1)]],dtype=object)
    beta = list(map(D,["1.9","1.6","-4.1","0.2"]))
    K, nodes = [], {1:[], -1:[]}
    for i in range(4):
        v = x[i]
        jv = np.array([-v[1],v[0]],dtype=object)
        k = beta[i]*np.outer(jv,jv)/(v@v)
        K.append(k)
        z = Minv@v
        a = abs(z[0])
        eta = g[i]@v/a
        d = g[i][0]/20+g[i][1]
        direction = np.array([D(".05"),D(1)],dtype=object)
        second = a*(direction@k@direction)
        nodes[1 if z[0]>0 else -1].append([z[1]/a,eta,d,second])
    return {"b":b,"root_residual":polynomial(b),"r":r,"x":x,"g":g,"H":H,
            "K":K,"nodes":nodes,"A":Minv,"beta":beta}


class Segment:
    """The monotone polynomial bridge, evaluated from the nearer endpoint."""
    def __init__(self,left,right,cast):
        self.a,self.va,self.da,self.ka = map(cast,left)
        self.c,self.vc,self.dc,self.kc = map(cast,right)
        self.cast = cast
        self.length = self.c-self.a
        if self.length <= 0:
            raise ValueError("Interpolation points must be strictly ordered")
        self.mu = self.length*cast(".01")
        self.p,self.q = self.length*self.da,self.length*self.dc
        self.P,self.Q = self.length**2*self.ka,self.length**2*self.kc
        if min(self.p,self.q,self.vc-self.va) <= self.mu:
            raise ValueError("Endpoint slopes and secant slope must exceed 0.01")
        # These linear inequalities exclude every smaller integer before
        # testing the integral condition; no large-degree search is needed.
        n = max(0,math.ceil(-self.P/(self.p-self.mu))-2,
                  math.ceil(self.Q/(self.q-self.mu))-2)
        while True:
            left,right,integral = self.coefficients(n)
            if left >= 0 and right <= 0 and integral < self.vc-self.va:
                self.n = n
                self.bump = 30*(self.vc-self.va-integral)
                self.selection_margins = [left,-right,self.bump/30]
                break
            n += 1

    def coefficients(self,n):
        left = self.P+(n+2)*(self.p-self.mu)
        right = self.Q-(n+2)*(self.q-self.mu)
        integral = self.mu+2*(self.p+self.q-2*self.mu)/(n+4)
        integral += (self.P-self.Q)/((n+3)*(n+4))
        return left,right,integral

    def _unit(self,s,p,q,P,Q):
        n,mu,bump = self.n,self.mu,self.bump
        left,right = P+(n+2)*(p-mu),Q-(n+2)*(q-mu)
        # Factored powers avoid expanding a polynomial of potentially high
        # degree. expm1/log1p preserve the float integral near s=0.
        if self.cast is float:
            difference3 = -math.expm1((n+3)*math.log1p(-s))
            difference4 = -math.expm1((n+4)*math.log1p(-s))
        else:
            difference3,difference4 = 1-(1-s)**(n+3),1-(1-s)**(n+4)
        value = mu*s+(p-mu+left)*difference3/(n+3)
        value -= left*difference4/(n+4)
        value += (q-mu-right)*s**(n+3)/(n+3)+right*s**(n+4)/(n+4)
        value += bump*(s**3/3-s**4/2+s**5/5)
        first = mu+(1-s)**(n+2)*(p-mu+left*s)
        first += s**(n+2)*(q-mu+right*(s-1))+bump*s*s*(1-s)**2
        second = (1-s)**(n+1)*(P-(n+3)*left*s)
        second += s**(n+1)*(Q+(n+3)*right*(s-1))
        second += 2*bump*s*(1-s)*(1-2*s)
        return value,first,second

    def evaluate(self,t):
        if t == self.a:
            return self.va,self.da,self.ka
        if t == self.c:
            return self.vc,self.dc,self.kc
        s = (t-self.a)/self.length
        if s <= self.cast(".5"):
            value,first,second = self._unit(s,self.p,self.q,self.P,self.Q)
            return self.va+value,first/self.length,second/self.length**2
        value,first,second = self._unit(1-s,self.q,self.p,-self.Q,-self.P)
        return self.vc-value,first/self.length,-second/self.length**2


class Interpolant:
    def __init__(self,nodes,cast):
        self.cast = cast
        anchors = [[-1,-1,1,0],[6,6,1,0]]
        prescribed = sorted([list(map(cast,v)) for v in [anchors[0],*nodes,anchors[1]]])
        left,right = prescribed[0],prescribed[-1]
        # The general lemma adjoins points one unit beyond the given data.
        outer_left = [left[0]-1,left[1]-1,cast(1),cast(0)]
        outer_right = [right[0]+1,right[1]+1,cast(1),cast(0)]
        self.nodes = [outer_left,*prescribed,outer_right]
        self.segments = [Segment(a,c,cast) for a,c in zip(self.nodes,self.nodes[1:])]

    def evaluate(self,t):
        if t <= self.nodes[0][0]:
            return t+self.nodes[0][1]-self.nodes[0][0],self.cast(1),self.cast(0)
        if t >= self.nodes[-1][0]:
            return t+self.nodes[-1][1]-self.nodes[-1][0],self.cast(1),self.cast(0)
        for segment in self.segments:
            if t <= segment.c:
                return segment.evaluate(t)
        raise ArithmeticError("No interpolation interval found")


class Example:
    def __init__(self,data,decimal=True):
        self.cast = Decimal if decimal else float
        self.decimal = decimal
        self.dtype = object if decimal else float
        self.data = data
        self.A = np.array([[self.cast(v) for v in row] for row in data["A"]],dtype=self.dtype)
        self.interpolants = {sign:Interpolant(nodes,self.cast) for sign,nodes in data["nodes"].items()}

    def sqrt(self,v):
        return v.sqrt() if self.decimal else np.sqrt(v)

    def jets(self,x,need_hessian=False):
        x = np.array(x,dtype=self.dtype)
        norm = self.sqrt(x@x)
        if norm == 0 or norm == 10:
            raise NondifferentiabilityError("The objective is nonsmooth at this point")
        z = self.A@x
        zero,one = self.cast(0),self.cast(1)
        if z[0] == 0:
            value = z[1]
            gradient = np.array([zero,one],dtype=self.dtype)
            hessian = np.zeros((2,2),dtype=self.dtype)*zero
        else:
            a,sign = abs(z[0]), 1 if z[0]>0 else -1
            t = z[1]/a
            val,first,second = self.interpolants[sign].evaluate(t)
            value = a*val
            gradient = np.array([sign*(val-t*first),first],dtype=self.dtype)
            if need_hessian:
                q = np.array([-z[1],z[0]],dtype=self.dtype)
                hessian = second*np.outer(q,q)/a**3
        gradient = self.A.T@gradient
        if need_hessian:
            hessian = self.A.T@hessian@self.A
        if norm > 10:
            value += norm*norm-100
            gradient += 2*x
            if need_hessian:
                identity = np.array([[one,zero],[zero,one]],dtype=self.dtype)
                hessian += 2*identity
        return (value,gradient,hessian) if need_hessian else (value,gradient)

    def value(self,x):
        # Separate value path makes the dense landscape evaluation economical.
        z = self.A@np.array(x,dtype=self.dtype)
        if z[0] == 0:
            val = z[1]
        else:
            a = abs(z[0])
            val = a*self.interpolants[1 if z[0]>0 else -1].evaluate(z[1]/a)[0]
        norm = self.sqrt(sum(v*v for v in x))
        return val+max(self.cast(0),norm*norm-100)

    def run(self,steps=120,perturbation=None):
        D = self.cast
        x = np.array([D(v) for v in self.data["x"][0]],dtype=self.dtype)
        H = np.array([[D(v) for v in row] for row in self.data["H"][0]],dtype=self.dtype)
        if perturbation is not None:
            v = np.array([D(str(a)) for a in perturbation],dtype=self.dtype)
            x += v[:2]
            H += np.array([[v[2],v[3]],[v[3],v[4]]],dtype=self.dtype)
        rows, all_first_trials_accepted = [],True
        cycle_error,metric_error = D(0),D(0)
        initial_exact = perturbation is None
        for k in range(steps+1):
            f,g = self.jets(x)
            rows.append({"k":k,"x":[float(v) for v in x],"f":float(f),
                         "norm":float(self.sqrt(x@x))})
            if initial_exact:
                target = D(self.data["r"])**(k//4)*np.array(self.data["x"][k%4],dtype=self.dtype)
                cycle_error = max(cycle_error,max(abs(v) for v in x-target))
                target_metric = D(self.data["r"])**(k//4)*np.array(self.data["H"][k%4],dtype=self.dtype)
                metric_error = max(metric_error,max(abs(v) for v in (H-target_metric).flat))
            if k==steps:
                break
            p = -H@g
            slope = g@p
            assert slope < 0
            lower,upper,alpha = D(0),None,D(1)
            for trials in range(100):
                trial = x+alpha*p
                fn = self.value(trial)
                armijo = fn < f+D(C1)*alpha*slope
                wolfe = False
                if armijo:
                    try:
                        _,gn = self.jets(trial)
                        wolfe = gn@p > D(C2)*slope
                    except NondifferentiabilityError:
                        pass
                if armijo and wolfe:
                    break
                if not armijo:
                    upper = alpha
                else:
                    lower = alpha
                alpha = (lower+upper)/2 if upper is not None else 2*lower
            else:
                raise ArithmeticError("Line search did not terminate")
            s = alpha*p
            y = gn-g
            curvature = s@y
            assert curvature > 0
            hy = H@y
            H = H-(np.outer(hy,s)+np.outer(s,hy))/curvature
            H += (1+(y@hy)/curvature)*np.outer(s,s)/curvature
            assert H[0,0]>0 and H[0,0]*H[1,1]-H[0,1]*H[1,0]>0
            rows[-1].update(alpha=float(alpha),trials=trials+1,
                            armijo_margin=float(f+D(C1)*alpha*slope-fn),
                            wolfe_margin=float(gn@p-D(C2)*slope))
            all_first_trials_accepted = all_first_trials_accepted and alpha==1
            x = trial
        return {"rows":rows,"all_first_trials_accepted":bool(all_first_trials_accepted),
                "max_absolute_cycle_position_error":str(cycle_error) if initial_exact else None,
                "max_absolute_cycle_metric_error":str(metric_error) if initial_exact else None}


def check_jets(example,data):
    errors = {"values":Decimal(0),"gradients":Decimal(0),"hessians":Decimal(0)}
    for i in range(4):
        value,gradient,hessian = example.jets(data["x"][i],True)
        errors["values"] = max(errors["values"],abs(value-data["g"][i]@data["x"][i]))
        errors["gradients"] = max(errors["gradients"],max(abs(v) for v in gradient-data["g"][i]))
        errors["hessians"] = max(errors["hessians"],max(abs(v) for v in (hessian-data["K"][i]).flat))
    assert max(errors.values()) < Decimal("1e-85")
    for interpolant in example.interpolants.values():
        for j,segment in enumerate(interpolant.segments):
            for k in range(21):
                t = segment.a+segment.length*Decimal(k)/20
                assert segment.evaluate(t)[1] >= Decimal(".01")
            # Adjacent polynomials interpolate the same jets exactly.
            assert segment.evaluate(segment.a) == tuple(interpolant.nodes[j][1:])
            assert segment.evaluate(segment.c) == tuple(interpolant.nodes[j+1][1:])
    return {k:str(v) for k,v in errors.items()}


def check_derivatives_and_extension(example,data):
    """Numerical consistency tests, separate from the exact certificate."""
    D = Decimal
    step = D("1e-30")
    gradient_error,hessian_error = D(0),D(0)
    points = [*data["x"][:4],np.array([D(1),D(1)],dtype=object),
              np.array([D(-1),D(-1)],dtype=object),np.array([D(11),D(2)],dtype=object)]
    for x in points:
        _,g,h = example.jets(x,True)
        for j in range(2):
            e = np.array([D(j==0),D(j==1)],dtype=object)
            fp,gp = example.jets(x+step*e)
            fm,gm = example.jets(x-step*e)
            gradient_error=max(gradient_error,abs((fp-fm)/(2*step)-g[j]))
            hessian_error=max(hessian_error,max(abs(v) for v in (gp-gm)/(2*step)-h[:,j]))
    assert gradient_error<D("1e-40") and hessian_error<D("1e-20")
    for x in ([D(0),D(0)],[D(10),D(0)]):
        example.value(x)
        try:
            example.jets(x)
        except NondifferentiabilityError:
            pass
        else:
            raise AssertionError("Returned a gradient at a nonsmooth point")
    return {"difference_step":str(step),"gradient_error":str(gradient_error),
            "hessian_error":str(hessian_error),"nonsmooth_gradient_requests_rejected":True}


def render(example,run,output):
    os.environ["PATH"] = "/Library/TeX/texbin:"+os.environ.get("PATH","")
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.ticker import FixedLocator, MaxNLocator
    plt.rcParams.update({"text.usetex":True,"font.family":"serif",
        "font.serif":["Computer Modern Roman"],"font.size":9,
        "axes.labelsize":9.5,"xtick.labelsize":8,"ytick.labelsize":8})
    fig = plt.figure(figsize=(6,3.4))
    left_xlim,left_ylim = (-1.6,1.6),(-2,2)
    left = fig.add_axes([.045,.19,.49,.73],projection="3d",computed_zorder=False)
    X,Y = np.meshgrid(np.linspace(*left_xlim,45),np.linspace(*left_ylim,49))
    Z = np.array([[example.value([x,y]) for x,y in zip(rx,ry)] for rx,ry in zip(X,Y)])
    left.plot_surface(X,Y,Z,cmap="viridis",edgecolor=(.12,.16,.19,.75),
                      linewidth=.13,rstride=1,cstride=1,antialiased=True)
    left.scatter([0],[0],[0],s=37,c="#b83636",marker="*",depthshade=False,zorder=8)
    left.set(xlabel="$x_1$",ylabel="$x_2$",zlabel="$f(x)$",xlim=left_xlim,ylim=left_ylim)
    left.view_init(elev=27,azim=-135)
    left.set_proj_type("ortho")
    left.set_box_aspect((1,1,.85))
    left.xaxis.set_major_locator(FixedLocator([-1,0,1]))
    left.yaxis.set_major_locator(FixedLocator([-2,-1,0,1,2]))
    left.zaxis.set_major_locator(MaxNLocator(4))
    left.tick_params(pad=0)
    left.xaxis.labelpad=left.yaxis.labelpad=-4
    left.zaxis.labelpad=-3
    for axis in (left.xaxis,left.yaxis,left.zaxis):
        axis.set_pane_color((1,1,1,1))
        axis.pane.set_edgecolor((.88,.88,.88,1))
        axis.line.set_color("#a2a2a2")
        axis.line.set_linewidth(.5)
        axis._axinfo["grid"].update(color=(.83,.83,.83,.65),linewidth=.4)
    right = fig.add_axes([.59,.23,.38,.67])
    xlim,ylim = (-1.6,1.6),(-.4,2)
    X,Y = np.meshgrid(np.linspace(*xlim,301),np.linspace(*ylim,401))
    Z = np.array([[example.value([x,y]) for x,y in zip(rx,ry)] for rx,ry in zip(X,Y)])
    right.contour(X,Y,Z,levels=[-1,0,.25,.5,.75,1,1.5,2,2.5,3,4],
                  colors="#b8b8b8",linewidths=.45)
    points = np.array([row["x"] for row in run["rows"][:PLOT_STEPS+1]])
    right.plot(*points.T,color="#245e91",lw=.95,marker="o",ms=1.6,
               label="BFGS iterates",zorder=4)
    right.scatter([0],[0],color="#b83636",marker="*",s=45,zorder=7,label="Nonstationary limit")
    right.annotate("$x^0$",points[0],xytext=(3,3),textcoords="offset points",fontsize=8.5)
    right.set(xlim=xlim,ylim=ylim,xlabel="$x_1$",ylabel="$x_2$")
    right.set_aspect("auto")
    right.set_box_aspect(1)
    right.set_xticks([-1,0,1])
    right.set_yticks([0,.5,1,1.5,2])
    right.spines[["top","right"]].set_visible(False)
    handles,labels=right.get_legend_handles_labels()
    fig.legend(handles,labels,loc="lower center",bbox_to_anchor=(.5,.015),frameon=False,
               fontsize=7.8,ncol=2,handlelength=1.8,columnspacing=2)
    for suffix in ("pdf","png"):
        buffer = io.BytesIO()
        fig.savefig(buffer,format=suffix,dpi=260)
        temporary = output/(".main_two_panel."+suffix)
        temporary.write_bytes(buffer.getvalue())
        temporary.replace(output/("main_two_panel."+suffix))
    plt.close(fig)
    return {"surface_x_limits":left_xlim,"surface_y_limits":left_ylim,
            "right_x_limits":xlim,"right_y_limits":ylim,"surface_mesh":[49,45],
            "text_rendering":"LaTeX Computer Modern","equal_displayed_axis_lengths":True}


def main():
    with localcontext() as context:
        context.prec = PRECISION
        data = cycle_data()
        precise = Example(data)
        errors = check_jets(precise,data)
        derivatives = check_derivatives_and_extension(precise,data)
        reference = precise.run(PLOT_STEPS)
        assert reference["all_first_trials_accepted"]
        assert Decimal(reference["max_absolute_cycle_position_error"]) < Decimal("1e-70")
        assert Decimal(reference["max_absolute_cycle_metric_error"]) < Decimal("1e-70")
        nearby = []
        for seed in range(6):
            perturbation = np.random.default_rng(seed).normal(size=5)
            perturbation *= 1e-12/np.linalg.norm(perturbation)
            sample = precise.run(PLOT_STEPS,perturbation)
            assert sample["all_first_trials_accepted"]
            nearby.append({"seed":seed,"initial_perturbation_norm":1e-12,
                           "all_first_trials_accepted":True,"final_norm":sample["rows"][-1]["norm"]})
        example = Example(data,decimal=False)
        output = ROOT/"figures"
        output.mkdir(exist_ok=True)
        figure_data = render(example,reference,output)
        result = {"root":str(data["b"]),"root_residual":str(data["root_residual"]),
                  "precision_digits":PRECISION,"r":"64/81","beta":list(map(str,data["beta"])),
                  "x0":list(map(str,data["x"][0])),
                  "initial_metric":[list(map(str,row)) for row in data["H"][0]],
                  "initial_scale":1,
                  "interpolation":{"monotonicity":"0.01",
                    "least_bridge_indices":{str(sign):[seg.n for seg in h.segments]
                                             for sign,h in precise.interpolants.items()}},
                  "parameters":{"c1":str(C1),"c2":str(C2)},"jet_errors":errors,
                  "derivative_checks":derivatives,
                  "reference":reference,"nearby_runs":nearby,"figure":figure_data,
                  "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  "interpretation":"Numerical illustrations using the actual objective and line search; no resets. The exact finite proof certificates are separate in ../verification/verify.py."}
        (output/"simulation_results.json").write_text(json.dumps(result,indent=2)+"\n")
        print("Root:",data["b"])
        print("Jet errors:",errors)
        print("Actual BFGS steps:",PLOT_STEPS,"; every first line-search trial accepted")
        print("Maximum absolute cycle position error:",reference["max_absolute_cycle_position_error"])
        print("Nearby runs passed:",len(nearby))
        print("Figure:",output/"main_two_panel.pdf")


if __name__ == "__main__":
    main()
