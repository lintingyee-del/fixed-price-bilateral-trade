# Fixed-Price Bilateral Trade: Proof Artifact

Lean proofs and machine-checkable certificates accompanying *The Exact Welfare Guarantee of Fixed-Price Bilateral Trade*.

Start with the [formalization supplement (PDF)](research_ideas/probes/fixed_price/manuscript/formalization_supplement.pdf) for the correspondence between the paper and the formal statements. The [TeX/Lean source comparison](research_ideas/probes/fixed_price/manuscript/checks/statement_correspondence.md) displays the extracted statements next to the Lean declarations. Its [JSON companion](research_ideas/probes/fixed_price/manuscript/checks/statement_correspondence.json) also expands named statement definitions and certificate structures.

## Contents

- [Lean project](research_ideas/probes/fixed_price/lean): 130 source files, with 1,701 theorem or lemma declarations. Lean 4.30.0; Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- [Standalone certificates](research_ideas/probes/fixed_price/manuscript/supplement): exact finite instances, rational certificates, and interval covers, with a replay program.
- [Additional symbolic and solver checks](research_ideas/probes/fixed_price/manuscript/first_layer_repair_20260921.py), their original construction programs and inputs, and the shared [Python helpers](hz_certify).
- [Statement/dependency manifest](research_ideas/probes/fixed_price/manuscript/factgraph.toml), [checker](proof_factgraph/factgraph.py), and [project-specific machine ledger excerpt](proof_factgraph/ledger.toml).
- [Packaging notes](PACKAGING.md): complete selection, dependencies, and the single portability adaptation.

Original relative paths are retained so the checking programs work from a standalone checkout. The full paper sources, proof-audit conversations, unrelated research, and build caches are not part of this artifact. Extracted paper statements and the formalization supplement are included; `paper.aux` supplies the supplement's cross-references.

## Scope

The central single-unit results are proved in Lean: the optimal welfare guarantee and strictness, approaching bounded instances, the affine and conditional frontiers, endpoint asymptotics, and the calibration bound with attainment and almost-everywhere uniqueness. The two finite separation instances of Theorem D are evaluated in the Lean kernel.

Theorem E and the two-unit curve-family optimization use explicit hypotheses for scalar identities, signs, and interval enclosures certified outside Lean. The manifest tracks 29 paper statements, of which 25 have Lean counterparts, including 9 conditional on such facts. A counterpart may cover only selected clauses.

In particular, the exported frontier theorems do not assert bounded support of their refuting/approaching witnesses. The combined calibration identity (G), including its `C = 0` endpoint identity, is not exported; its optimization consequences are proved. Other documented differences include reference-family parametrization, exact attainment of the hard-pair price bound, and the full-support clause of smoothing. The general two-unit exact-ratio conjecture remains open. Decimal enclosures and interval covers are checked outside Lean.

Lean checks the formal implications. Matching them to the paper remains a semantic task: the comparison script locates source statements and declarations, but does **not** certify equivalence of their meanings. The supplement documents the scope differences and external premises.

## Reproduce

Install Python 3.11 or later and the dependencies, preferably in a virtual environment:

```sh
python -m pip install -r requirements.txt
python research_ideas/probes/fixed_price/manuscript/supplement/verify.py
python research_ideas/probes/fixed_price/manuscript/first_layer_repair_20260921.py --run
python research_ideas/probes/fixed_price/manuscript/checks/first_layer_20260921/max_convexity_exact.py
python research_ideas/probes/fixed_price/manuscript/checks/first_layer_repair_20260921/physical_conditions.py
```

The first command after installation re-evaluates all 37 certificate checks, including the stored interval partitions. `--fast` skips the two interval-cover replays. The remaining commands replay local algebra/solver implications and physical margins; they do not establish the analytic premises listed in their receipts. Historical scripts with manuscript-location metadata require the authors' full TeX; the supported replay commands above do not.

With Lean installed through `elan`, build the formal project:

```sh
cd research_ideas/probes/fixed_price/lean
lake exe cache get
lake build FixedPrice
```

Mathlib is the only direct library dependency. The recorded Lean checks use only the standard foundational axioms `propext`, `Classical.choice`, and `Quot.sound`; the project contains no `sorry`, custom axioms, or `native_decide` proofs. Building alone is distinct from checking axiom dependencies; the supplement explains how to inspect both.

From the repository root, inspect the manifest and regenerate the source comparison:

```sh
python proof_factgraph/factgraph.py research_ideas/probes/fixed_price/manuscript/factgraph.toml check
python research_ideas/probes/fixed_price/manuscript/statement_correspondence.py
```

In this checkout, comparison uses the included TeX excerpts. Supply `--tex-dir /path/to/manuscript` to compare an updated complete manuscript. A successful manifest check confirms stored statements, premises and graph consistency, not agreement with the current manuscript or semantic equivalence with Lean.

## Reproduction record

The standalone checkout was replayed on 2026-09-27. Results and tested Python package versions are recorded in [reproduction/README.md](reproduction/README.md). The Lean sources and pinned configuration are unchanged from the recorded 2026-09-26 build and axiom checks; those checks are reused, not presented as a fresh clean-machine build.
