"""Local replay after the proof-register revision; no global proof verdict."""
import hashlib
import json
from pathlib import Path
import traceback

import sympy as s
import first_layer as base

HERE = Path(__file__).resolve().parent
base.OUT = HERE / 'checks/first_layer_register_20260913.json'
base.PREFIX = 'fpm3_20260913_'


def displayed_steps():
    C, y, r, Z = s.symbols('C y r Z', real=True)
    D = 1-y+C*y*y
    Dr = 1-r+C*r*r
    py = -1/(y*D)
    pc = y*y/(2*D)+Z/2
    yp = (y**3+y*D*Z)/2
    U = (y*y/D+(2*C*y-1)*Z)/2
    a, eps = s.symbols('a eps', real=True)
    ell = s.Function('ell')(a)
    v = s.Function('v')(a)
    Q = s.exp(-2*ell) + s.diff(a*s.diff(ell, a), a)
    varied = -s.exp(-2*(ell+eps*v))-a*s.diff(ell+eps*v, a)**2
    first = s.diff(varied, eps).subs(eps, 0)
    expressions = {
        'implicit_endpoint_derivative': -pc/py-yp,
        'primitive_r_over_D': s.diff(r/Dr, r)-(1-C*r*r)/Dr**2,
        'primitive_r_squared_over_D': s.diff(r*r/Dr, r)-(2*r-r*r)/Dr**2,
        'U_from_two_primitives': 2*(y*(y/D+C*Z)-(y*y/D+Z)/2)-2*U,
        'total_D_derivative': y*y+(2*C*y-1)*yp-y*D*(y+U),
        'first_variation_multiplier_2Q': first-2*Q*v-s.diff(-2*a*s.diff(ell, a)*v, a),
    }
    residuals = {k: str(s.simplify(value)) for k, value in expressions.items()}
    return {'scope': 'Displayed endpoint algebra and the local first-variation normalization only.',
            'residuals': residuals, 'all_zero': all(value == '0' for value in residuals.values())}


if __name__ == '__main__':
    # base.main checks the ledger before each actual run and records every run.
    base.main()
    out = HERE / 'checks/register_displayed_steps_20260913.json'
    key = 'fpm3_20260913_displayed_steps'
    if not base.ledger.already_recorded(key):
        try:
            result = displayed_steps()
        except Exception as exc:
            result = {'all_zero': False, 'error': repr(exc), 'traceback': traceback.format_exc()}
        result['tex_sha256'] = hashlib.sha256((HERE / 'paper.tex').read_bytes()).hexdigest()
        result['script_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        out.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
        base.ledger.record(key,
            'The six listed local endpoint and first-variation identities have zero residual; the obstacle multiplier for the displayed energy is 2Q.',
            ['sympy'] if result['all_zero'] else [], str(out.relative_to(base.ROOT)),
            paper=base.PAPER, note='Local algebra only; does not certify endpoint coverage, an a.e. argument, or global optimality.')
    else:
        result = json.loads(out.read_text(encoding='utf-8'))
    print(json.dumps({'displayed_steps': result}, indent=2))
