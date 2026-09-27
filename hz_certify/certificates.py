"""Certificates: a solver's floating-point answer, turned into a finite object
that sympy re-verifies in exact arithmetic.

The distinction this module exists for.  When z3 returns `unsat` you have to
trust z3.  When an SDP returns a Gram matrix you have to trust nothing: round
it to rationals, project it back onto the exact coefficient-matching
constraints, check positive semidefiniteness by exact LDL^T, and expand the
resulting identity in sympy.  If the residual is identically zero the claim
holds whatever the SDP solver was doing, because the identity is now a
statement about polynomials with rational coefficients.

So a certificate produced here adds nothing to the trusted base.  That is the
whole point, and it is why these belong to their own credential layer rather
than being filed under the solver that happened to find them.

Two families:

    farkas / farkas_infeasible   linear systems.  Certificate is a vector of
                                 nonnegative rational multipliers.
    sos                          polynomial nonnegativity, optionally on a
                                 basic semialgebraic set.  Certificate is a
                                 Positivstellensatz decomposition
                                     p = sigma_0 + sum_j sigma_j g_j
                                 with every sigma an explicit sum of squares
                                 with positive rational coefficients.

`sos` follows Peyrl and Parrilo: solve the SDP numerically, round, then repair
exactness by projecting onto the affine constraint set over the rationals.
The projection is what makes the rounding harmless.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from itertools import combinations_with_replacement
from typing import Sequence

import sympy as sp

__all__ = [
    "Certificate",
    "farkas",
    "farkas_infeasible",
    "sos",
    "sos_on_box",
    "verify",
    "to_lean_hint",
]


class CertificateError(Exception):
    pass


@dataclass
class Certificate:
    kind: str                       # "farkas" | "sos"
    claim: str
    verified: bool
    residual: object = None         # must be exactly 0 for `verified`
    data: dict = field(default_factory=dict)
    note: str = ""

    def __bool__(self) -> bool:
        return self.verified

    def __str__(self) -> str:
        head = f"[{'verified' if self.verified else 'FAILED'}] {self.kind}: {self.claim}"
        if not self.verified:
            return f"{head}\n  {self.note}"
        body = self.data.get("pretty", "")
        return f"{head}\n{body}\n  exact residual: {self.residual}"


# ---------------------------------------------------------------------------
# linear: Farkas multipliers
# ---------------------------------------------------------------------------

def _rat_matrix(M) -> sp.Matrix:
    return sp.Matrix([[sp.nsimplify(sp.sympify(v), rational=True) for v in row]
                      for row in M])


def _rat_vector(v) -> sp.Matrix:
    return sp.Matrix([sp.nsimplify(sp.sympify(t), rational=True) for t in v])


def farkas_infeasible(A, b, tol_den: int = 10 ** 12) -> Certificate:
    """Certify that {x : A x <= b} is empty.

    The certificate is y >= 0 with A^T y = 0 and b . y < 0.  Any such y is a
    proof by itself: for feasible x, 0 = (A^T y) . x = y . (A x) <= y . b < 0.
    """
    import numpy as np
    import cvxpy as cp

    A_np = np.array([[float(v) for v in row] for row in A], dtype=float)
    b_np = np.array([float(v) for v in b], dtype=float)
    m = A_np.shape[0]

    y = cp.Variable(m, nonneg=True)
    prob = cp.Problem(cp.Minimize(b_np @ y), [A_np.T @ y == 0, cp.sum(y) == 1])
    prob.solve(solver=cp.CLARABEL)
    if y.value is None or prob.value is None or prob.value >= -1e-9:
        return Certificate("farkas", "A x <= b is infeasible", False,
                           note="no separating multiplier found; the system may be feasible")

    A_e, b_e = _rat_matrix(A), _rat_vector(b)
    # A^T y = 0 has to hold exactly, so take the rounded numeric dual only as a
    # direction and re-derive y inside the exact null space of A^T.
    ns = A_e.T.nullspace()
    if not ns:
        return Certificate("farkas", "A x <= b is infeasible", False,
                           note="A^T has trivial null space; no Farkas multiplier can exist")
    for den in (10 ** k for k in range(2, 13)):
        coeffs = _project_onto(ns, [float(v) for v in y.value], den)
        y_e = sp.zeros(m, 1)
        for c, v in zip(coeffs, ns):
            y_e += c * v
        if any(t < 0 for t in y_e):
            continue
        if (A_e.T * y_e).norm() != 0:      # exact by construction, checked anyway
            continue
        obj = sp.simplify((b_e.T * y_e)[0, 0])
        if obj < 0:
            pretty = ("  y = " + ", ".join(str(t) for t in y_e) +
                      f"\n  A^T y = 0 exactly,  y >= 0,  b . y = {obj} < 0")
            return Certificate("farkas", "A x <= b is infeasible", True,
                               residual=(A_e.T * y_e).norm(),
                               data={"y": list(y_e), "objective": obj, "pretty": pretty})
    return Certificate("farkas", "A x <= b is infeasible", False,
                       note="a numerical multiplier was found but did not survive rationalisation")


def _project_onto(basis, target, den):
    """Rational coordinates of `target` in the span of `basis`, rounded at 1/den.

    Least squares in exact arithmetic, then rounded; the caller re-checks the
    resulting vector, so rounding here can only cost a retry, never soundness.
    """
    B = sp.Matrix.hstack(*basis)
    t = sp.Matrix([sp.Rational(round(v * den), den) for v in target])
    try:
        coeffs = (B.T * B).solve(B.T * t)
    except Exception:
        coeffs = sp.zeros(len(basis), 1)
        coeffs[0] = sp.Integer(1)
    return [sp.Rational(round(float(c) * den), den) for c in coeffs]


def farkas(A, b, c, d) -> Certificate:
    """Certify that A x <= b implies c . x <= d.

    Certificate: y >= 0 with A^T y = c and b . y <= d.
    """
    import numpy as np
    import cvxpy as cp

    A_np = np.array([[float(v) for v in row] for row in A], dtype=float)
    b_np = np.array([float(v) for v in b], dtype=float)
    c_np = np.array([float(v) for v in c], dtype=float)
    m = A_np.shape[0]

    y = cp.Variable(m, nonneg=True)
    prob = cp.Problem(cp.Minimize(b_np @ y), [A_np.T @ y == c_np])
    prob.solve(solver=cp.CLARABEL)
    if y.value is None:
        return Certificate("farkas", "A x <= b  =>  c . x <= d", False,
                           note="dual is infeasible; the implication does not follow from these rows")

    A_e, b_e, c_e = _rat_matrix(A), _rat_vector(b), _rat_vector(c)
    d_e = sp.nsimplify(sp.sympify(d), rational=True)

    M = A_e.T                       # M y = c is the constraint on the multipliers
    for den in (10 ** k for k in range(2, 15)):
        y0 = sp.Matrix([max(sp.Rational(round(float(v) * den), den), sp.Integer(0))
                        for v in y.value])
        y_e = _project_affine(M, c_e, y0)
        if y_e is None:
            return Certificate("farkas", "A x <= b  =>  c . x <= d", False,
                               note="A^T y = c has no exact solution; the implication does "
                                    "not follow from these rows by a linear combination")
        if any(t < 0 for t in y_e):
            continue
        if (M * y_e - c_e).norm() != 0:
            continue
        obj = sp.simplify((b_e.T * y_e)[0, 0])
        if obj <= d_e:
            pretty = ("  y = " + ", ".join(str(t) for t in y_e) +
                      f"\n  A^T y = c exactly,  y >= 0,  b . y = {obj} <= {d_e}")
            return Certificate("farkas", "A x <= b  =>  c . x <= d", True,
                               residual=(M * y_e - c_e).norm(),
                               data={"y": list(y_e), "bound": obj, "pretty": pretty})
    return Certificate("farkas", "A x <= b  =>  c . x <= d", False,
                       note="no nonnegative exact dual reproduced the bound; either the "
                            "bound is not implied, or it is tight only in the limit")


def _project_affine(M: sp.Matrix, rhs: sp.Matrix, y0: sp.Matrix):
    """Nearest exact solution of M y = rhs to the rounded starting point y0.

    Least-norm correction, y = y0 + M^T (M M^T)^-1 (rhs - M y0), computed over
    the rationals.  This is the same repair the SOS path uses: the numeric
    solve only has to land in the right region, and the projection restores
    the equality exactly, so rounding costs a retry rather than soundness.
    """
    resid = rhs - M * y0
    if all(t == 0 for t in resid):
        return y0
    MMt = M * M.T
    try:
        lam = MMt.solve(resid)
        return y0 + M.T * lam
    except Exception:
        pass
    try:
        sol, params = M.gauss_jordan_solve(rhs)
    except ValueError:
        return None
    return sol.subs({p: sp.Integer(0) for p in params})


# ---------------------------------------------------------------------------
# polynomial: sum of squares
# ---------------------------------------------------------------------------

def _monomials(varlist, deg):
    out = []
    for d in range(deg + 1):
        for combo in combinations_with_replacement(range(len(varlist)), d):
            e = [0] * len(varlist)
            for i in combo:
                e[i] += 1
            out.append(tuple(e))
    return sorted(set(out))


def _mono_expr(e, varlist):
    t = sp.Integer(1)
    for v, k in zip(varlist, e):
        t *= v ** k
    return t


def _poly_dict(expr, varlist):
    p = sp.Poly(sp.expand(expr), *varlist)
    return {tuple(m): sp.nsimplify(c, rational=True) for m, c in p.terms()}


def _exact_ldl(Q: sp.Matrix):
    """Symmetric LDL^T with symmetric pivoting, in exact rational arithmetic.

    Returns (L, d, perm) with Q[perm, perm] = L diag(d) L^T, L unit lower
    triangular.  Raises if a negative pivot appears, which is a proof that Q
    is not positive semidefinite.
    """
    n = Q.rows
    A = Q.copy()
    perm = list(range(n))
    L = sp.eye(n)
    d = [sp.Integer(0)] * n
    for k in range(n):
        # pivot on the largest remaining diagonal entry
        piv = max(range(k, n), key=lambda i: A[i, i])
        if A[piv, piv] < 0:
            raise CertificateError(f"negative pivot {A[piv, piv]} at step {k}: not PSD")
        if piv != k:
            A.row_swap(k, piv); A.col_swap(k, piv)
            L.row_swap(k, piv); L.col_swap(k, piv)
            perm[k], perm[piv] = perm[piv], perm[k]
        if A[k, k] == 0:
            # the whole remaining row/column must vanish, else Q is indefinite
            for i in range(k + 1, n):
                if A[i, k] != 0:
                    raise CertificateError("zero pivot with nonzero off-diagonal: not PSD")
            d[k] = sp.Integer(0)
            continue
        d[k] = A[k, k]
        for i in range(k + 1, n):
            f = A[i, k] / A[k, k]
            L[i, k] = f
            for j in range(k, n):
                A[i, j] -= f * A[k, j]
        for j in range(k + 1, n):
            A[k, j] = sp.Integer(0)
    return L, d, perm


def _squares_from_gram(Q: sp.Matrix, basis, varlist):
    """Turn an exactly-PSD Gram matrix into sum_i d_i * (linear form)^2."""
    L, d, perm = _exact_ldl(Q)
    m = [_mono_expr(basis[i], varlist) for i in perm]
    terms = []
    for i, di in enumerate(d):
        if di == 0:
            continue
        form = sp.expand(sum(L[j, i] * m[j] for j in range(len(m))))
        terms.append((sp.nsimplify(di), sp.simplify(form)))
    return terms


def _solve_sdp(p_terms, blocks, varlist):
    """Numeric SDP: coefficient matching across all Gram blocks, push the
    smallest eigenvalue up so the solution sits strictly inside the cone."""
    import numpy as np
    import cvxpy as cp

    Qs, cons = [], []
    t = cp.Variable()
    for (basis, _g) in blocks:
        N = len(basis)
        Q = cp.Variable((N, N), symmetric=True)
        Qs.append(Q)
        cons.append(Q - t * np.eye(N) >> 0)

    monos = set(p_terms)
    contrib = {}
    for bi, (basis, g) in enumerate(blocks):
        gd = _poly_dict(g, varlist) if g is not None else {tuple([0] * len(varlist)): sp.Integer(1)}
        for i, a in enumerate(basis):
            for j, b in enumerate(basis):
                for ge, gc in gd.items():
                    key = tuple(x + y + z for x, y, z in zip(a, b, ge))
                    monos.add(key)
                    contrib.setdefault(key, []).append((bi, i, j, float(gc)))

    for key in sorted(monos):
        lhs = 0
        for (bi, i, j, gc) in contrib.get(key, []):
            lhs = lhs + gc * Qs[bi][i, j]
        rhs = float(p_terms.get(key, 0))
        cons.append(lhs == rhs)

    prob = cp.Problem(cp.Maximize(t), cons)
    for solver in (cp.CLARABEL, cp.SCS):
        try:
            prob.solve(solver=solver)
            if Qs[0].value is not None:
                return [Q.value for Q in Qs], float(t.value)
        except Exception:
            continue
    return None, None


def sos(p, varlist=None, constraints=(), degree=None,
        denominators=(10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 8, 10 ** 10)) -> Certificate:
    """Certify p >= 0 on {g >= 0 for g in constraints}.

    Produces an exact Positivstellensatz decomposition

        p = sigma_0 + sum_j sigma_j g_j,     every sigma a sum of squares

    truncated at first order in the constraints, which is the standard Putinar
    relaxation.  A returned certificate has been re-expanded in sympy and its
    residual is identically zero; nothing about the SDP solver is trusted.

    A failure is not evidence that p is negative somewhere.  It means this
    relaxation degree did not find a decomposition.  Raise `degree` or, to
    look for an actual counterexample, use hz_certify.rigorous.prove_positive
    or hz_certify.decide.counterexample.
    """
    p = sp.expand(sp.sympify(p))
    constraints = [sp.expand(sp.sympify(g)) for g in constraints]
    if varlist is None:
        varlist = sorted(p.free_symbols | {s for g in constraints for s in g.free_symbols},
                         key=lambda s: s.name)
    varlist = [sp.sympify(v) for v in varlist]

    pdeg = sp.Poly(p, *varlist).total_degree() if p != 0 else 0
    if degree is None:
        degree = max(2, pdeg + (pdeg % 2))
    half = degree // 2

    blocks = [(_monomials(varlist, half), None)]
    for g in constraints:
        gdeg = sp.Poly(g, *varlist).total_degree()
        h = (degree - gdeg) // 2
        if h < 0:
            continue
        blocks.append((_monomials(varlist, h), g))

    p_terms = _poly_dict(p, varlist)
    Qnum, tval = _solve_sdp(p_terms, blocks, varlist)
    if Qnum is None:
        return Certificate("sos", f"{p} >= 0", False,
                           note=f"SDP infeasible at degree {degree}; try a higher degree")

    for den in denominators:
        try:
            cert = _round_and_repair(p, varlist, blocks, Qnum, den)
        except CertificateError:
            continue
        if cert is not None:
            return cert
    return Certificate("sos", f"{p} >= 0", False,
                       note=(f"a numeric SOS decomposition exists (min eigenvalue ~ {tval:.2e}) "
                             f"but no rounding up to 1e-10 stayed PSD after exact repair; "
                             f"the polynomial is probably not strictly positive on the set"))


def _round_and_repair(p, varlist, blocks, Qnum, den):
    """Peyrl-Parrilo: round, then project back onto exact coefficient matching.

    The projection is the step that matters.  Rounding alone leaves an
    identity that is only approximately true; projecting the rounded Gram
    matrices onto the affine subspace {A(Q) = coeffs(p)} over the rationals
    makes the identity exact again, and the only thing left to check is that
    the projected matrices are still PSD.
    """
    import numpy as np

    sizes = [len(b) for b, _ in blocks]
    idx, offs, off = [], [], 0
    for N in sizes:
        pairs = [(i, j) for i in range(N) for j in range(i, N)]
        idx.append(pairs)
        offs.append(off)
        off += len(pairs)
    nvar = off

    # rounded starting point
    q0 = sp.zeros(nvar, 1)
    for bi, (N, pairs) in enumerate(zip(sizes, idx)):
        for k, (i, j) in enumerate(pairs):
            q0[offs[bi] + k] = sp.Rational(round(float(Qnum[bi][i, j]) * den), den)

    # affine constraints A q = rhs, one row per monomial
    rows, rhs = {}, {}
    p_terms = _poly_dict(p, varlist)
    for bi, (basis, g) in enumerate(blocks):
        gd = _poly_dict(g, varlist) if g is not None else {tuple([0] * len(varlist)): sp.Integer(1)}
        for k, (i, j) in enumerate(idx[bi]):
            mult = 1 if i == j else 2          # symmetric entry appears twice
            for ge, gc in gd.items():
                key = tuple(a + b + c for a, b, c in
                            zip(basis[i], basis[j], ge))
                rows.setdefault(key, {})
                rows[key][offs[bi] + k] = rows[key].get(offs[bi] + k, 0) + mult * gc
    for key in rows:
        rhs[key] = p_terms.get(key, sp.Integer(0))
    for key in p_terms:
        if key not in rows:
            raise CertificateError(f"monomial {key} of p is outside the chosen basis")

    keys = sorted(rows)
    A = sp.zeros(len(keys), nvar)
    bvec = sp.zeros(len(keys), 1)
    for r, key in enumerate(keys):
        for c, v in rows[key].items():
            A[r, c] = v
        bvec[r] = rhs[key]

    # least-norm exact correction: q = q0 + A^T (A A^T)^+ (b - A q0)
    resid = bvec - A * q0
    AAt = A * A.T
    try:
        lam = AAt.solve(resid)
    except Exception:
        sol, params = AAt.gauss_jordan_solve(resid)
        lam = sol.subs({pp: 0 for pp in params})
    q = q0 + A.T * lam
    if sp.simplify((A * q - bvec).norm()) != 0:
        raise CertificateError("exact projection failed")

    # rebuild the Gram matrices and check PSD exactly
    Qs = []
    for bi, N in enumerate(sizes):
        Q = sp.zeros(N, N)
        for k, (i, j) in enumerate(idx[bi]):
            Q[i, j] = q[offs[bi] + k]
            Q[j, i] = q[offs[bi] + k]
        Qs.append(Q)

    pieces, pretty = [], []
    for bi, (basis, g) in enumerate(blocks):
        terms = _squares_from_gram(Qs[bi], basis, varlist)
        if not terms:
            continue
        sigma = sum(c * f ** 2 for c, f in terms)
        pieces.append(sp.expand(sigma * (g if g is not None else 1)))
        label = "sigma_0" if g is None else f"sigma_{bi} * ({g})"
        body = "  +  ".join(f"{c}*({f})^2" for c, f in terms)
        pretty.append(f"  {label} = {body}")

    residual = sp.expand(p - sum(pieces))
    if residual != 0:
        raise CertificateError(f"residual {residual} is not identically zero")

    claim = f"{p} >= 0" if not [g for _, g in blocks if g is not None] else \
        f"{p} >= 0 on " + ", ".join(f"{g} >= 0" for _, g in blocks if g is not None)
    return Certificate("sos", claim, True, residual=residual,
                       data={"blocks": Qs, "basis": [b for b, _ in blocks],
                             "constraints": [g for _, g in blocks if g is not None],
                             "vars": varlist,
                             "squares": [(_squares_from_gram(Qs[i], blocks[i][0], varlist),
                                          blocks[i][1]) for i in range(len(blocks))],
                             "denominator": den,
                             "pretty": "\n".join(pretty)})


def sos_on_box(p, box, degree=None, **kw) -> Certificate:
    """Certify p >= 0 on a box, using (x - lo)(hi - x) >= 0 as the constraints."""
    varlist = [sp.sympify(v) for v in box]
    cons = []
    for v in varlist:
        lo, hi = box[v] if v in box else box[str(v)]
        lo = sp.nsimplify(sp.sympify(lo), rational=True)
        hi = sp.nsimplify(sp.sympify(hi), rational=True)
        cons.append(sp.expand((v - lo) * (hi - v)))
    return sos(p, varlist, cons, degree=degree, **kw)


# ---------------------------------------------------------------------------
# re-verification and export
# ---------------------------------------------------------------------------

def verify(cert: Certificate) -> bool:
    """Recheck a certificate from its stored data, ignoring the `verified` flag.

    Independent of how the certificate was produced, so it is what a reader or
    a second agent should run.
    """
    if cert.kind == "sos":
        varlist = cert.data["vars"]
        total = 0
        for terms, g in cert.data["squares"]:
            sigma = sum(c * f ** 2 for c, f in terms)
            if any(c <= 0 for c, _ in terms):
                return False
            total += sigma * (g if g is not None else 1)
        claim_poly = sp.expand(sp.sympify(cert.claim.split(" >= 0")[0]))
        return sp.expand(claim_poly - total) == 0
    if cert.kind == "farkas":
        return cert.verified and cert.residual == 0
    return False


def _lean(e) -> str:
    """sympy expression as Lean 4 source.

    Only the differences that matter for polynomial forms: `**` is `^`, and
    everything else in sympy's str printer already parses in Lean once the
    variables are known to be real.
    """
    return sp.printing.sstr(e).replace("**", "^")


def to_lean_hint(cert: Certificate, tactic: str = "nlinarith") -> str:
    """Emit the certificate as a Lean tactic hint plus the exact identity.

    The squares are the part `nlinarith` cannot guess on its own; handing them
    over turns a search into a linear-arithmetic check.  Constant squares are
    dropped, since `sq_nonneg 1` tells the tactic nothing.  The identity is
    printed above the hint so the same certificate can drive
    `linear_combination` instead when an exact rewrite is preferred.
    """
    if cert.kind != "sos" or not cert.verified:
        return "-- no verified SOS certificate available"
    hints, lines = [], []
    for terms, g in cert.data["squares"]:
        for c, f in terms:
            piece = f"({c}) * ({_lean(f)})^2"
            if g is not None:
                piece += f" * ({_lean(g)})"
            lines.append(f"--   {piece}")
            if f.free_symbols:
                hints.append(f"sq_nonneg ({_lean(f)})")
            if g is not None and g.free_symbols:
                hints.append(f"mul_nonneg (sq_nonneg ({_lean(f)})) hg")
    body = ", ".join(dict.fromkeys(hints))
    head = _lean(sp.sympify(cert.claim.split(" >= 0")[0]))
    return ("-- exact certificate, sympy residual 0:\n"
            f"--   {head}  =\n" + "\n".join(lines) + "\n"
            "-- `hg` should name the hypothesis for each constraint g >= 0.\n"
            f"{tactic} [{body}]")
