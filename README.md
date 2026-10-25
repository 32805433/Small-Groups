# SmallGroups

Lean 4 proofs of groups with small finite presentations and universality or undecidability properties.

The four results are proved in [SmallPresentation.lean](SmallPresentation.lean),
under the namespace `SmallPresentationStatements`:

| Presentation | Proved properties |
| --- | --- |
| Two generators, three relators | Universal: contains every finitely presented group. Its abelianization is infinite cyclic, and one displayed generator normally generates it. |
| Effective two-generator, four-relator family | Triviality is undecidable; every nontrivial member is universal. |
| Two generators, four relators | Torsion-free with undecidable word problem and infinite cyclic abelianization; one displayed generator normally generates it. |
| Effective two-generator, five-relator family | Every member is torsion-free, and triviality is undecidable. |

Counts are displayed generator/relator slots, with redundant rows allowed; no minimality
claim is made. The universal group and the torsion-free group are separate witnesses.
“Undecidable” means `¬ ComputablePred`, and effectiveness means the relator table is
jointly computable in the family and relator indices.

## Build and verify

Install [Lean through elan](https://lean-lang.org/install/), then run from this directory:

```sh
lake exe cache get
lake --wfail build
lake env lean AxiomAudit.lean
```

The project pins **Lean 4.35.0** and **Mathlib 4.35.0**. The build covers the local
proof library with warnings treated as failures. The separate command freshly runs
the 277-checkpoint axiom audit, permitting only `propext`, `Classical.choice`,
and `Quot.sound`. GitHub Actions is configured to run these checks and separately elaborate the
independent statement challenge.

The current source layout passed a local build with zero warnings or errors and a
fresh audit of all 277 checkpoints on 25 October 2026. All four public theorems
use only the three permitted axioms. See
[recorded validation](VERIFICATION.md#recorded-publication-validation) for its scope.

Import `SmallPresentation` to use the results. For example:

```lean
import SmallPresentation

#check SmallPresentationStatements.exists_two_three_universal_with_abelianization_Z
#check SmallPresentationStatements.exists_two_four_universal_adian_rabin_family
#check SmallPresentationStatements.exists_torsion_free_two_four_with_abelianization
#check SmallPresentationStatements.exists_torsion_free_two_five_adian_rabin_family
```

## Reading the development

- [FORMALIZATION.md](FORMALIZATION.md): proof architecture, mathematical sources, upstream provenance, and licenses.
- [VERIFICATION.md](VERIFICATION.md): trust checks, Comparator instructions, recorded validation, and maintenance requirements.
- [formalization.yaml](formalization.yaml): theorem mapping, source provenance, and review status.

`SmallPresentation/` contains the group-theoretic constructions, general metric
small-cancellation proofs, and algebraic Hopf/Schur machinery. The shared
universal-group foundations and construction are in `SmallPresentation/UniversalGroup/`,
with their root module at `SmallPresentation/UniversalGroup.lean`. The 31 distinct
Adian–Rabin-derived extensions are in `SmallPresentation/AdianRabin/`.

The general results include metric factor injection and torsion preservation,
weighted identity balance, canonical relation-module sequences, quotient five-term
exactness, and degree-two Künneth for arbitrary pairs of groups. The homological
model is algebraic Hopf/Schur; a comparison with Mathlib's separate chain-complex
homology is not claimed.

## Independent statements

[SmallPresentationStatements.lean](SmallPresentationStatements.lean) is the unchanged
statement challenge. Its four intentional `sorry` placeholders and historical draft
comments are retained for comparison. The proved library does not import it.
Its placeholders are excluded from the proof build. The theorem axiom audit rejects
any checkpoint that depends on an admitted proof.
[VERIFICATION.md](VERIFICATION.md#statement-challenge-and-comparator) documents the optional independent
Comparator check. No local Comparator run is recorded. Palomar runs its own
Comparator verification on the submitted commit; a local run is optional preparation.

## Authorship and license

The author and maintainer is Qiuyu Ren. The new proof development and working
manuscript were produced with GPT-6 Astra under human direction; OpenAI models
also assisted with publication documentation and checks. The upstream projects' own authorship
and software attributions are preserved in the
[software provenance and licenses](FORMALIZATION.md#software-provenance-and-licenses).
Compilation, axiom checks, and exact-type checks do not constitute an independent
mathematical review of the informal statements.

Original SmallGroups code and documentation use the [MIT license](LICENSE).
Reused source retains the notices in [LICENSES/](LICENSES/). Lean, Mathlib, and their
dependencies retain their respective licenses.
