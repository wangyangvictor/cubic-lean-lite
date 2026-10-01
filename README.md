# Cubic forms: Lean formalization

A Lean 4 development of geometry and analytic estimates for rational cubic
forms, with a conditional deduction that every homogeneous cubic over the
rationals in at least ten variables has a nonzero rational zero.

**The main theorem remains conditional on seven explicit propositions.**
This repository does not claim an unconditional proof of that theorem.

## Main statement and remaining inputs

The exact target is `CubicTenVariables.MainTheorem`; its definition is in
[Targets.lean](formalization/CubicTenVariables/CubicTenVariables/Targets.lean).
The proved implication is
[`CubicTenVariables.Theorem11ReducedLiterature.main`](formalization/CubicTenVariables/CubicTenVariables/Theorem11ReducedLiterature.lean).
Its seven proposition arguments are:

1. `CubicTenVariables.Literature.ProjectiveMicrolocalCertificate`.
2. `TranslatedDepthSeven.StandardAG.ProjectiveDegreeSpanInequality ℚ`.
3. `CubicTenVariables.Literature.AffinePlaneCurveWeil`.
4. `CubicTenVariables.Literature.ProperHyperplaneWeightDichotomy`.
5. `TranslatedDepthSeven.Published.Salberger2023Theorem04`.
6. `CubicTenVariables.Literature.HooleyKatzPointCount`.
7. `CubicTenVariables.Literature.BrowningCubicPointCount`.

Their exact definitions and source references are in the Lean files. Inputs 1
and 4 are composite cohomological interfaces, not verbatim textbook theorems.
An axiom audit does not prove these hypotheses: an implication can use only
Lean's standard axioms while still requiring mathematical premises.

## Reproduce the checks

Install Git and [Lean through elan](https://lean-lang.org/install/).
Clone this repository, then run from its root:

```sh
cd formalization/CubicTenVariables
lake exe cache get
cd ../..
./scripts/check.sh
```

The cache command downloads external dependency build artifacts. The check
script builds all three public roots and checks `PublicationAudit.lean`, which
recursively rejects project axioms, `sorryAx` and nonstandard proof axioms in
the imported project theorems. It allows only `propext`, `Classical.choice` and
`Quot.sound`. It also checks the exact seven-input main theorem type and target
equivalences. A successful check verifies those formal statements, not the
informal correctness of their definitions or the unproved input propositions.

Keep the three directories below together: their Lake dependencies are relative.
Open `formalization/CubicTenVariables` in VS Code with the Lean extension.

| Package | Purpose |
| --- | --- |
| `CubicTenVariables` | Ten-variable reductions, estimates, and conditional main theorem |
| `HessianTheorem11` | Hessian geometry, including earlier dimensional cases |
| `TranslatedDepthSeven` | Geometry, counting, and supporting arguments |

Lean is pinned to **4.26.0**. The committed Lake manifests pin Mathlib to
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` and PrimeNumberTheoremAnd to
`db0b69d008f3991b6f03bc5f59504f02eb6c724b`, together with their dependencies.
Preserve the toolchain and manifests when reproducing this snapshot; do not
run `lake update` as part of reproduction. The external PNT development contains
unrelated admissions; the audit rejects any such dependency in the imported
theorems of these three project namespaces.

GitHub Actions runs the same build and audit on pushes and pull requests.
The main theorem has not received a complete independent Comparator/Nanoda
recheck, and no such certification is claimed here.

## Snapshot scope and provenance

This source-only snapshot contains the transitive local imports of all three
public package roots: 1,751 original Lean modules, plus a publication audit.
Unimported exploratory files, manuscripts, drafts, reports, progress ledgers,
logs, downloaded libraries, compiler caches and model files are excluded.
Original Lean proof files are unchanged from the local research snapshot.
Some retained Lean comments describe earlier intermediate steps; the exact
declaration types and the seven-input theorem above determine the current scope.

The exported package was checked on macOS on 29 September 2026: all three
public roots built successfully (9,517 Lake jobs), and the fresh publication
audit passed for 7,392 cubic, 4,498 Hessian and 5,724 translated/counting
theorems. Existing compiled caches were reused for unchanged proof files and
pinned external dependencies. All twelve external Git dependencies matched
their manifest commits and had no tracked changes. A completely cache-free
build and a GitHub-hosted Linux run have not been completed for this export;
the included workflow performs the latter after publication.


Development used AI assistance in an interactive mathematical research workflow.
Reused proof fragments retain their source attributions and notices. Original
project code is licensed under Apache-2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE).
See [CITATION.cff](CITATION.cff) for citation metadata.
