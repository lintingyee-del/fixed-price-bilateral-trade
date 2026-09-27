"""Named first-layer components for finite-buyer seller-prefix separation.

This checks algebra and one rational example. It does not machine-prove the
continuous-domain reduction or a universal approximation guarantee. Existing
prefix certificates and finite-tail seller identities are reused, not rerun.
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json
import sympy as sp

HERE = Path(__file__).resolve().parent


def identities():
    beta, value, tail, excess, gain = sp.symbols("beta value tail excess gain")
    prob, moment, atom, post, seller = sp.symbols("prob moment atom post seller")
    kappa = 1 - beta
    residuals = {}

    def zero(name, expression):
        residual = sp.factor(sp.together(expression))
        assert residual == 0, (name, residual)
        residuals[name] = str(residual)

    zero("normalized_single_seller_welfare",
         value + gain - beta * (value + tail + excess)
         - (kappa * value - beta * (tail + excess) + gain))
    zero("projected_new_trade_nonnegative_decomposition",
         1 + moment - prob * seller
         - (1 + (moment - prob * post) + prob * (post - seller)))
    zero("seller_price_atom_jump",
         atom * (1 + moment - prob * post)
         - atom * (1 + (moment - prob * post)))
    intercept, survival, priced_intercept, priced_survival = sp.symbols(
        "intercept survival priced_intercept priced_survival")
    affine = kappa * seller - beta * (1 + intercept - survival * seller)
    affine += priced_intercept - priced_survival * seller
    zero("interior_seller_potential_slope",
         sp.diff(affine, seller) - (kappa + beta * survival - priced_survival))

    n = 4
    ell1 = sp.symbols("ell1_0:4")
    ell2 = sp.symbols("ell2_0:4")
    transfer = sp.symbols("K_0:4")
    mass1 = list(sp.symbols("sigma1_0:3"))
    mass2 = list(sp.symbols("sigma2_0:3"))
    mass1 += [1 - sum(mass1)]
    mass2 += [1 - sum(mass2)]
    lhs = sum(ell1[j] * mass1[j] + ell2[j] * mass2[j] for j in range(n))
    rhs = sum((ell1[j] + transfer[j]) * mass1[j]
              + (ell2[j] - transfer[j]) * mass2[j] for j in range(n))
    rhs += sum((transfer[j + 1] - transfer[j])
               * (sum(mass1[:j + 1]) - sum(mass2[:j + 1]))
               for j in range(n - 1))
    zero("four_node_cdf_transfer_abel_decomposition", lhs - rhs)
    x, y, kx, ky = sp.symbols("ell1x ell2y Kx Ky")
    zero("ordered_pair_transfer_decomposition",
         x + y - ((x + kx) + (y - ky) + (ky - kx)))
    delta, survival, mass, future, cprev = sp.symbols(
        "delta survival mass future cprev")
    gamma = kappa + beta * survival - future
    ccurr = cprev - delta * survival
    zero("node_increment_combines_affine_piece_and_downward_jump",
         delta * (gamma - mass * survival) - mass * ccurr
         - (delta * gamma - mass * cprev))
    total_mass = sp.symbols("total_mass")
    zero("nonnegative_interval_slope_decomposition",
         kappa + beta * survival - future
         - (kappa * (1 - survival) + (1 - total_mass) * survival
            + total_mass * survival - future))
    c1, c2, gamma1, gamma2 = sp.symbols("c1 c2 gamma1 gamma2")
    double_mass = delta * (gamma1 + gamma2) / (c1 + c2)
    transfer_increment = delta * (c1 * gamma2 - c2 * gamma1) / (c1 + c2)
    zero("double_contact_first_increment",
         delta * gamma1 - double_mass * c1 + transfer_increment)
    zero("double_contact_second_increment",
         delta * gamma2 - double_mass * c2 - transfer_increment)
    zero("frozen_single_contact_increment", delta * gamma1 - (delta * gamma1 / c1) * c1)
    return residuals


def rational_example():
    buyers = [[(Q(1), Q(1, 3)), (Q(3), Q(2, 3))],
              [(Q(1, 2), Q(1, 2)), (Q(2), Q(1, 2))]]
    nodes = sorted({Q(0), *(z for law in buyers for z, _ in law)})
    prices = list(zip(nodes[1:], [Q(1, 10), Q(1, 5), Q(1, 4), Q(1, 5)]))
    tail_mass = Q(1, 4)
    beta = Q(3, 4)
    assert sum(p for _, p in prices) + tail_mass == 1
    assert all(sum(p for z, p in buyers[0] if z <= s)
               <= sum(p for z, p in buyers[1] if z <= s) for s in nodes)

    def loss(law, seller):
        return sum(prob * max(z - seller, 0) for z, prob in law)

    def kernel(law, seller, price):
        return ((1 + sum(prob * (z - seller) for z, prob in law if z >= price))
                if seller < price else Q(0))

    def ell(law, seller):
        return ((1 - beta) * seller - beta * (1 + loss(law, seller))
                + tail_mass + sum(prob * kernel(law, seller, price)
                                  for price, prob in prices))

    projection = []
    affine_rows = []
    jump_rows = []
    for q, law in enumerate(buyers):
        for left, right in zip(nodes[:-1], nodes[1:]):
            old_price = (left + right) / 2
            seller_events = sorted({Q(0), left, old_price, right, nodes[-1] + 1})
            seller_tests = sorted(set(seller_events)
                                  | {(x + y) / 2 for x, y in zip(seller_events[:-1], seller_events[1:])})
            for seller in seller_tests:
                gap = kernel(law, seller, right) - kernel(law, seller, old_price)
                assert gap >= 0
                projection.append(dict(unit=q + 1, old=str(old_price), new=str(right),
                                       seller=str(seller), gap=str(gap)))
            s1 = (2 * left + right) / 3
            s2 = (left + 2 * right) / 3
            midpoint = (left + right) / 2
            assert ell(law, midpoint) == (ell(law, s1) + ell(law, s2)) / 2
            assert ell(law, left) == 2 * ell(law, s1) - ell(law, s2)
            affine_rows.append(dict(unit=q + 1, interval=[str(left), str(right)],
                                    slope=str((ell(law, s2) - ell(law, s1)) / (s2 - s1))))
            left_trace = 2 * ell(law, s2) - ell(law, s1)
            price_mass = dict(prices)[right]
            jump = price_mass * (1 + loss(law, right))
            assert left_trace - ell(law, right) == jump
            jump_rows.append(dict(unit=q + 1, node=str(right),
                                  left_trace=str(left_trace), right_value=str(ell(law, right)),
                                  jump=str(jump)))

    values = [[ell(law, node) for node in nodes] for law in buyers]
    prefix = [-min(values[0][:j + 1]) for j in range(len(nodes))]
    pairs = [(values[0][i] + values[1][j], i, j)
             for j in range(len(nodes)) for i in range(j + 1)]
    assert min(row[0] for row in pairs) == min(values[1][j] - prefix[j]
                                             for j in range(len(nodes)))
    return dict(
        buyers=[[[str(z), str(p)] for z, p in law] for law in buyers],
        posted_price_masses=[[str(z), str(p)] for z, p in prices],
        tail_mass=str(tail_mass), beta=str(beta),
        projection_comparisons=projection,
        affine_interval_replays=affine_rows, atom_jump_replays=jump_rows,
        node_potentials=[[str(x) for x in row] for row in values],
        canonical_prefix=[str(x) for x in prefix],
        minimum_pair_slack=str(min(row[0] for row in pairs)),
        scope="One rational example of the new tail-normalized kernels only. Its arbitrary chosen price policy is not asserted optimal or feasible at beta.",
    )


def main():
    residuals = identities()
    example = rational_example()
    out = dict(
        scope=__doc__, actual_layer="exact",
        symbolic_identities=residuals, rational_example=example,
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        reused_without_rerun=[
            "fp_ext_k2_prefix_initial_freeze_exact_20260913",
            "fp_ext_k2_prefix_multistage_exact_20260913",
            "fp_ext_k2_continuous_switching_components_20260914: tail_seller_constant_piece and tail_seller_outside_piece",
        ],
        not_certified=[
            "Continuous-domain finite-event reduction as a complete argument",
            "Any universal lower bound over buyer pairs",
            "Optimal-policy switching pattern or number of switches",
        ],
    )
    path = HERE / "prefix_components.json"
    path.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(dict(
        identities=len(residuals),
        projection_comparisons=len(example["projection_comparisons"]),
        affine_intervals=len(example["affine_interval_replays"]),
        price_atom_jumps=len(example["atom_jump_replays"]),
        example_minimum_slack=example["minimum_pair_slack"],
        output=str(path),
    ), indent=2))


if __name__ == "__main__":
    main()
