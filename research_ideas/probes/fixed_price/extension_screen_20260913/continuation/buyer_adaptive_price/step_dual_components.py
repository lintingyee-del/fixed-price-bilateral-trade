"""New components for the one-jump certificate dual and its global energy.

The exact part checks new algebra and a rational single-cut dual example.
The numerical part evaluates the deliberately relaxed energy upper bound
once at the saved continuous reference. It is discovery, not a credential.
Previously recorded equalizer identities are inputs and are not rerun.
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json
import sys
import sympy as sp
import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.optimize import brentq

HERE = Path(__file__).resolve().parent


def exact_components():
    checks = {}

    def zero(name, expression):
        residual = sp.simplify(expression)
        assert residual == 0, (name, residual)
        checks[name] = str(residual)

    r, l1, l2, level, height = sp.symbols("r L1 L2 level height")
    right1, right2 = r-l1, r-l2
    zero("single_cut_height_coefficient",
         right2-right1-(l1-l2))
    zero("single_cut_compensation_integral",
         level*(r-r)+height*(right2-right1)-height*(l1-l2))
    s = sp.symbols("s", real=True)
    C, H, A, F, z, I = (sp.Function(name) for name in ("C", "H", "A", "F", "z", "I"))
    zero("price_gain_clock_derivative",
         sp.diff(A(s)/C(s), s).subs({
             sp.diff(A(s), s):F(s), sp.diff(C(s), s):-H(s)})
         -(C(s)*F(s)+H(s)*A(s))/C(s)**2)
    zero("cdf_reconstruction_from_gain",
         sp.diff(C(s)*I(s), s).subs({
             sp.diff(C(s), s):-H(s), sp.diff(I(s), s):z(s)/C(s)**2})
         -(z(s)/C(s)-H(s)*I(s)))
    d, tail_h, tail_h2 = sp.symbols("d tail_H tail_H2")
    zero("positive_energy_weight_numerator",
         (1+tail_h)*H(s)+d-tail_h2
         -(H(s)+d+H(s)*tail_h-tail_h2))
    cut_gap, slack1, slack2, B1, B2, mass = sp.symbols(
        "cut_gap slack1 slack2 B1 B2 mass")
    eq1 = B1+slack1-level-height*(1-l1)
    eq2 = B2+slack2+level+height*(1-l2)
    zero("equalizer_compensation_difference",
         (eq1+eq2)/2-((B1+B2+slack1+slack2)/2+height*(l1-l2)/2))
    price_gap, mu_slack1, mu_slack2 = sp.symbols("price_gap mu_slack1 mu_slack2")
    lam_integral = mu_slack1+mu_slack2+height*cut_gap
    zero("full_primal_dual_gap_decomposition",
         price_gap+lam_integral
         -(price_gap+mu_slack1+mu_slack2+height*cut_gap))

    # Both buyer bodies equal 3. The seller measures have common mass 1/6.
    nodes = list(map(Q, [0, 1, 2, 3]))
    mu = [[Q(1,30),Q(1,15),Q(0),Q(1,15)],
          [Q(1,15),Q(0),Q(1,10),Q(0)]]
    common = Q(1,6)
    assert all(sum(row)==common for row in mu)
    cut = Q(2)
    cut_gap_value = sum(mu[0][j]-mu[1][j] for j,v in enumerate(nodes) if v<cut)
    wrong_inclusive_gap = sum(mu[0][j]-mu[1][j] for j,v in enumerate(nodes) if v<=cut)
    assert cut_gap_value==Q(1,30)>0
    assert wrong_inclusive_gap==Q(-1,15)<0
    cdf_gaps = [sum(mu[0][:j+1])-sum(mu[1][:j+1]) for j in range(4)]
    assert min(cdf_gaps)<0

    def gain(row, price):
        return sum(w*((4-v) if price<=3 else 1)
                   for v,w in zip(nodes,row) if v<price)

    price_tests = [Q(0),Q(1,2),Q(1),Q(3,2),Q(2),Q(5,2),Q(3),Q(4)]
    tested = [(p, sum(gain(row,p) for row in mu)) for p in price_tests]
    assert all(v<=1 for _,v in tested) and 2*common<=1
    dd = Q(1,3)
    direct = sum(w*(4-v-dd*v) for row in mu for v,w in zip(nodes,row))
    W = sp.Rational(4,3)/(4-s)**2
    pieces = [(0,1,sp.Rational(2,5)),(1,2,sp.Rational(3,5)),(2,3,sp.Rational(4,5))]
    energy = sum(value*sp.integrate(W,(s,lo,hi)) for lo,hi,value in pieces)
    assert energy==sp.Rational(direct.numerator,direct.denominator)==sp.Rational(32,45)
    return dict(identities=checks,rational_example=dict(
        buyer_bodies="Z1=Z2=3", d=str(dd), seller_nodes=[str(v) for v in nodes],
        seller_multiplier_masses=[[str(v) for v in row] for row in mu],
        common_mass=str(common), cut=str(cut),
        correct_cut_left_gap=str(cut_gap_value),
        wrong_inclusive_cut_gap=str(wrong_inclusive_gap),
        all_cdf_gaps=[str(v) for v in cdf_gaps],
        price_kernel_tests=[[str(p),str(v)] for p,v in tested],
        all_price_branches=[dict(interval="(0,1]",gain="2/5"),
                            dict(interval="(1,2]",gain="3/5"),
                            dict(interval="(2,3]",gain="4/5"),
                            dict(interval="(3,infinity)",gain="1/3")],
        tail_column_gain=str(2*common), direct_objective=str(direct),
        energy_objective=str(energy),
        interpretation="This is feasible for the single left-CDF constraint at cut 2 and for every price, but violates full stochastic seller order. It shows the distinction between dual feasible sets; it is not an outer counterexample.",
    ))


def reference_relaxed_bound():
    sys.path.insert(0,str(HERE.parent/"unified_principle"))
    from continuous_switching import Reference
    ref=Reference()
    d=(1-ref.beta)/ref.beta
    solutions={}
    initial=np.zeros(2)
    for j in reversed(range(4)):
        lo,hi=ref.bounds[j:j+2]
        sol=solve_ivp(lambda s,y:-ref.state(s,j)["H"]**2,
                      (hi,lo),initial,method="DOP853",
                      atol=2e-13,rtol=2e-12,dense_output=True,
                      max_step=(hi-lo)/18)
        assert sol.success,sol.message
        solutions[j]=sol.sol
        initial=sol.y[:,-1]

    def weight(s,j):
        st=ref.state(float(s),j)
        C,H=st["L"],st["H"]
        return (C*H+d-solutions[j](s))/C**2

    totals=np.zeros(2)
    total_max=0.
    crossings=[]
    blocks=[]
    for j,(lo,hi) in enumerate(zip(ref.bounds,ref.bounds[1:])):
        grid=np.linspace(lo,hi,65)
        diff=lambda s:float(weight(s,j)[0]-weight(s,j)[1])
        roots=[]
        for left,right in zip(grid[:-1],grid[1:]):
            if diff(left)*diff(right)<0:
                roots.append(float(brentq(diff,left,right,xtol=1e-14)))
        roots=sorted(set(roots))
        vals=[quad(lambda s:float(weight(s,j)[i]),lo,hi,
                   epsabs=3e-12,epsrel=3e-12)[0] for i in range(2)]
        maximum=quad(lambda s:float(max(weight(s,j))),lo,hi,points=roots or None,
                     epsabs=3e-12,epsrel=3e-12)[0]
        totals+=vals
        total_max+=maximum
        crossings.extend(roots)
        blocks.append(dict(segment=j,interval=[lo,hi],integral_weights=vals,
                           integral_max=maximum,crossings=roots))
    boundary=1-d*ref.b
    relaxed=max(0.,boundary)+total_max
    reference=1/ref.beta
    return dict(actual_layer="floating discovery",
                source=str(ref.source),source_sha256=ref.source_sha256,
                reference_beta=ref.beta,d=d,b=ref.b,
                common_boundary=boundary,
                per_unit_equalizer_B=(boundary+totals).tolist(),
                integral_max_weights=total_max,
                relaxed_upper_mass=relaxed,
                relaxed_upper_budget=ref.beta*relaxed,
                reference_mass=reference,
                excess_mass=relaxed-reference,
                excess_budget=ref.beta*relaxed-1,
                crossings=crossings,blocks=blocks,
                interpretation="This drops all CDF consistency, the common terminal linkage and the cut constraint. It is only a coarse upper bound. The numerical value is not an interval enclosure or a universal credential.")


def main():
    exact=exact_components()
    discovery=reference_relaxed_bound()
    out=dict(scope=__doc__,exact=exact,reference_discovery=discovery,
             source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             reused_without_rerun=["fp_ext_k2_prefix_obstacle_components_20260914: recorded equalizer identities"],
             not_certified=["Strong duality for the continuum seller problem",
                            "A universal one-step certificate at beta_star",
                            "An interchange of cut minimization and seller maximization",
                            "A sharp calibration of the dropped-CDF energy upper bound"])
    dest=HERE/"step_dual_components.json"
    dest.write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(dict(symbolic_identities=len(exact["identities"]),
                          example_objective=exact["rational_example"]["direct_objective"],
                          correct_cut_gap=exact["rational_example"]["correct_cut_left_gap"],
                          relaxed_reference_bound=discovery["relaxed_upper_mass"],
                          relaxed_reference_budget=discovery["relaxed_upper_budget"],
                          excess_mass=discovery["excess_mass"],
                          receipt=str(dest)),indent=2))


if __name__=="__main__":
    main()
