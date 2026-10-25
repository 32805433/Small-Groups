# Verification

## Scope

The publication contains 600 proof-library modules, the axiom audit module, and one
independent statement challenge (602 Lean files in total).
The canonical UniversalGroup modules are under `SmallPresentation/UniversalGroup/`, and
[AxiomAudit.lean](AxiomAudit.lean) checks the four public theorems and intermediate
results at 277 named checkpoints. The audit fails on a missing declaration or any
axiom outside `propext`, `Classical.choice`, and `Quot.sound`.

The protected statement file has SHA256:

```text
3548d6acc1c1a7e1f61b8420fb438087b81aa83a813acdf6138845d1e95afb3a
```

Its four placeholders are intentional comparison inputs. The proved library does
not import the challenge. Original upstream linter settings are preserved; no new
warning suppression was introduced for publication.

## Reproduce the checks

With the pinned Lean toolchain installed through elan:

```sh
lake exe cache get
lake --wfail build
lake env lean AxiomAudit.lean
```

Lake builds the local proof library with warnings treated as failures. Running the
audit separately freshly elaborates its checkpoint commands, even when the build
reuses a compiled audit module. Normal Lake dependency-cache reuse is permitted;
these commands do not rebuild Mathlib from source.

[GitHub Actions](.github/workflows/lean.yml) is configured to run the build and axiom audit, followed
by a separate elaboration of the independent statement challenge. The workflow uses
these direct Lake commands. It does not perform the former Python source-inventory,
source-token, receipt, or saved-type comparison checks. References in preserved Lean
comments to source-ledger checks or artifact hashes describe that earlier tooling.

## Recorded publication validation

On 25 October 2026, the current relocated source layout passed:

- `lake exe cache get`, using the pinned dependencies and Mathlib cache;
- `LEAN_NUM_THREADS=2 lake --wfail build`, completing 2,552 jobs with zero warnings
  or errors and compiling all 600 proof-library modules plus the audit module;
- `LEAN_NUM_THREADS=2 lake env lean AxiomAudit.lean`, freshly executing all
  277 checkpoints with no warnings or errors;
- `LEAN_NUM_THREADS=2 lake build SmallPresentationStatements`, elaborating the
  independent challenge with exactly four expected `sorry` warnings and no errors.

All four public theorems reported exactly `propext`, `Classical.choice`, and
`Quot.sound`. Publication-file hashes were unchanged by the build and audit.
Build artifacts were kept under `.lake`, with logs outside the publication tree.

The earlier development verification run
`2a559e2e-daab-4372-a25b-1599c80b2357` is historical evidence; the local checks
above validate the current module layout separately.

The workflow's presence is not evidence that hosted CI has run. No external
Comparator or additional kernel-replay result is claimed unless separately recorded.

## Statement challenge and Comparator

The standard proof build does not compile the challenge. To check that it elaborates:

```sh
lake build SmallPresentationStatements
```

Its exactly four expected placeholder warnings are not proof-library warnings.

The pinned Lean 4.35.0 toolchain includes the native `lake comparator` command.
[comparator.json](comparator.json) compares the protected
`SmallPresentationStatements` module with the proved `SmallPresentation` module
for all four fully qualified targets. The environments remain separate; the
solution does not import the challenge. Only `propext`, `Quot.sound`, and
`Classical.choice` are permitted in the solution.

A local Comparator run is optional preparation for Palomar submission. Palomar
performs its own Comparator verification on the exact submitted public commit;
a successful local run is not a prerequisite for submission. See
[Palomar's submission instructions](https://palomar-registry.org/how-to-submit).

To run the optional local check after installing the pinned toolchain and Mathlib
cache, run from the repository root:

```sh
lake comparator --config comparator.json
```

Comparator checks statements and referenced definitions, audits the solution's
axioms, and replays exported proofs. A successful ordinary build, source-contract
check, or saved-type comparison is not a Comparator verdict. No completed external
Comparator run is recorded for this publication.

The sandboxed command requires Linux and a compatible `bubblewrap` (`bwrap`), with
`git` and `env` available. The selected toolchain supplies its exporter and kernel
checker. The host must allow the namespaces required by bubblewrap; sandbox creation
failure is an environment failure, not a theorem result. Sandboxing is not disabled
by this project.

## Maintenance

Use the pinned Lean and Mathlib versions. Keep mathematical interfaces general
where the proof supports generality; avoid changing a definition or introducing a
hypothesis merely to make a target easier to prove.

The protected `SmallPresentationStatements.lean` must remain unchanged. The proved
library is maintained under `SmallPresentation/`, with its four public endpoints in
`SmallPresentation.lean`. General upstream machinery is shared through
`SmallPresentation/UniversalGroup/`; the adapted Adian–Rabin modules are under
`SmallPresentation/AdianRabin/`.
Preserve third-party notices and record further upstream changes in the relevant
provenance manifest and complete patch.

Before submitting a change, run the build and audit commands in
[Reproduce the checks](#reproduce-the-checks), and elaborate the statement challenge
separately. Review changes to public statements explicitly and rerun compilation
and the axiom audit after proof changes.

Keep generated artifacts, private logs, downloaded literature, and local experiments
outside the publication tree. Do not add global lint suppressions to conceal a
failed cleanup. Recheck source and elaboration uses before removing a declaration
that is absent from one proof's compiled dependency graph.
