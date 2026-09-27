"""hz_certify - the pre-Lean verification layer, as four roles rather than four tools.

    falsifier    decide.counterexample, rigorous.prove_* refutations
                 Output: a witness.  Trusts nothing, because the witness is
                 replayed in exact arithmetic outside the solver.

    certifier    certificates.sos, certificates.farkas
                 Output: a finite object making the claim an identity.  Trusts
                 nothing, because sympy expands the identity to zero.

    decider      decide.prove_forall
                 Output: a verdict.  Trusts the solvers, so it runs two.

    bounder      rigorous.prove_positive, rigorous.integral, rigorous.range_enclosure
                 Output: a proved enclosure.  Trusts Arb.

The ordering is not stylistic.  A falsification or a certificate adds nothing
to the trusted base and can be rechecked by anyone; a solver verdict cannot.
Reach for the earlier roles first and the results get cheaper to defend, not
just cheaper to obtain.

Recording is part of the workflow, not an afterthought:

    from hz_certify import rigorous, certificates, decide, ledger

    ledger.already_recorded("my_claim")          # always first
    cert = certificates.sos(p, [x])              # then the cheap layer
    ledger.record_certificate(cert, "my_claim")  # then the entry

`ledger.record_*` picks the credential layer from the kind of result, so
`exact`, `arb`, `z3` and `cvc5` stay consistent across sessions and agents.
"""

from . import certificates, decide, ledger, rigorous

__all__ = ["rigorous", "certificates", "decide", "ledger"]
__version__ = "0.1.0"
