# Standalone replay, 2026-09-27

The published copy was exercised from its own directory on Windows with Python 3.11.5. Imports resolved to this checkout, including the repository-relative ledger. This run checks that the packaged programs and data can replay without the unpublished manuscript or other research projects. It is a replay of existing mathematical evidence, not an independent proof of the paper.

| Command | Observed result | Output |
| --- | --- | --- |
| `manuscript/supplement/verify.py` | 37 checks, 0 failed; both interval covers replayed | [log](supplement_verify_20260927.log) |
| `manuscript/first_layer_repair_20260921.py --run` | 27 groups, no nonpassing group | [log](first_layer_replay_20260927.log) |
| `manuscript/checks/first_layer_20260921/max_convexity_exact.py` | 27 branches, all passed | [log](max_convexity_20260927.log) |
| `manuscript/checks/first_layer_repair_20260921/physical_conditions.py` | Arb margins proved; all local symbolic residuals zero | [log](physical_conditions_20260927.log) |
| Manifest consistency check | 103 nodes, no dangling references or cycles | Standard checker |
| Source-correspondence script | 32 rows, 1,701 theorem/lemma declarations, no source-navigation errors | [report](../research_ideas/probes/fixed_price/manuscript/checks/statement_correspondence.md) |

Paths in the command column start at `research_ideas/probes/fixed_price/`. Full commands are in the root README. The programs retain their historical receipt names and date constants; their stdout logs above are the record of this later replay. The checked-in historical JSON receipts are preserved. Running the programs again may overwrite those local receipt files, without changing the ledger.

Tested package versions:

```text
sympy==1.14.0
python-flint==0.9.0
z3-solver==5.0.0.0
cvc5==1.3.4
numpy==2.4.6
scipy==1.17.1
mpmath==1.3.0
cvxpy==1.9.2
threadpoolctl==3.6.0
```

The 130 Lean files and project configuration were copied unchanged. We reuse the existing build and axiom-check credentials; no new Lean build is claimed here. Import/parse checks covered the packaged Python sources, JSON/TOML, and local Lean import paths. The original standalone certificate directory was preserved byte for byte.

## Statement correspondence review

Source comparison checks the table's labels and Lean names, and exposes named statement abbreviations and certificate structures. It cannot decide semantic equivalence. The focused reading of the principal theorem types and short definitions found these additional scope boundaries, now disclosed in the supplement:

- Theorem B's bounded refuting and approaching witnesses do not appear in the exported theorem types. The exact conditional ratio and infimum do.
- Theorem C's bound, attainment, and almost-everywhere uniqueness are proved. The printed combined identity (G) is not one exported theorem; its `C = 0` endpoint integral identity is also not formalized.
- The general two-unit infimum `r2star` is defined in Lean. The comparison from Theorem D's explicit instances to that infimum is not exported.

Four table references were corrected to include the file containing their exported declarations. This review did not reprove the mathematics or individually audit all 62 external family-certificate fields. The supplement's other partial and conditional coverage disclosures remain applicable.
