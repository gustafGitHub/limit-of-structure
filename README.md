# Where Structure Ends — Lean formalization

Companion Lean 4 formalization to the working paper

> **G. Ullman, "Where Structure Ends: A quotient dilemma for structural theories of consciousness, with a Lean-checked descent core" (2026).**
> Article version DOI: [10.5281/zenodo.20666955](https://doi.org/10.5281/zenodo.20666955) · Concept DOI: [10.5281/zenodo.17159948](https://doi.org/10.5281/zenodo.17159948)
> Principal OE paper concept DOI: [10.5281/zenodo.17077437](https://doi.org/10.5281/zenodo.17077437)

The single file [`WhereStructureEnds.lean`](WhereStructureEnds.lean) machine-checks a deliberately small, domain-neutral core — **the Quotient Test as a unique-factorization theorem**, the fiber-blindness of descended quantities, and the no-go for fiber-sensitive quantities — together with a conditional, clearly demarcated metaphysical layer.

## What is verified — and what is not

**Verified (domain-neutral descent core).**
- **Quotient Test.** A quantity is invariant under the admissible transformations iff it descends through the projection `π : Obs → Str`, and the descended map is *unique* — `quotientTest`, `quotientTest_unique`.
- **Fiber-blindness.** A descended quantity cannot distinguish two perspectives once `π` has identified them — `fiber_blind`.
- **No structural representative.** A fiber-sensitive quantity has no `Q' : Str → X` with `Q = Q' ∘ π` — `no_factor_of_separates`; equivalently `Descends Q ↔ ¬ SeparatesAFiber Q`.

**Conditional metaphysical layer (premises, not theorems).**
Given the *premise* that phenomenal character varies inside a quotient fiber (`CharacterIsFiberLocal`), Lean checks that no structural map on `Str` represents it (`character_not_structural`); the Prop-valued local-zombie case (`phenomenal_not_structural`) is its `C = Prop` specialization. These premises live in `namespace OE.Metaphysics` as explicit hypotheses — **never as global `axiom`s**.

**Not claimed.** The formalization does **not** prove primitivism or the Ontological Closure Principle, does **not** prove that phenomenal character actually varies in a fiber, and does **not** formalize IIT, Global Workspace Theory, or any AI architecture. Lean certifies only that the descent step introduces no hidden consciousness premise.

## Build

Pinned to Lean 4.30.0 / Mathlib `v4.30.0` via [`lean-toolchain`](lean-toolchain) and [`lake-manifest.json`](lake-manifest.json).

```bash
git clone https://github.com/gustafGitHub/limit-of-structure.git
cd limit-of-structure
lake exe cache get   # fetch prebuilt Mathlib oleans — do NOT rebuild Mathlib from source
lake build           # builds WhereStructureEnds.lean
```

| Tool | Version |
|---|---|
| Lean | 4.30.0 (commit `d024af0`) |
| Lake | 5.0.0 |
| Mathlib | `v4.30.0`, commit `c5ea00351c28e24afc9f0f84379aa41082b1188f` |

The file sets `set_option autoImplicit false` and contains **no `sorry`, `admit`, `axiom`, or `unsafe`**.

## Axiom audit

The end of the file carries a commented `#print axioms` block. Verified profile:

- **Core descent / no-go** — `[Quot.sound]`; several (`fiber_blind`, `no_factor_of_separates`, `no_objective_fiber_sensitive_quantity`, `exists_nonstructural_of_forgetful`, `no_factor_through_collapsed_signature`, `time_degenerates`) are **fully axiom-free**.
- **Classical corollaries / group realization** — `[propext, Classical.choice, Quot.sound]` (classicality enters only via `by_cases` / `by_contra`).
- **Metaphysical conditionals** — **axiom-free**: the fiber-locality premises are *definitionally* fiber separations, and each no-go is a specialization of the axiom-free core.

The axiom profile is part of the record: the descent step is constructive apart from the expected quotient principles, and classicality is confined to witness-extraction corollaries.

## Paper ↔ Lean concordance

| Paper claim | Lean name |
|---|---|
| Quotient `S = O/∼` and projection `π` | `Str`, `proj` |
| Invariance = constancy on fibers | `invariant_iff_constantOnFibers` |
| Invariant ⟺ descends | `quotientTest` |
| Unique descended representative | `quotientTest_unique` |
| Descended ⟹ fiber-blind | `fiber_blind` |
| Fiber-sensitive ⟹ no structural representative | `no_factor_of_separates` |
| Strong dichotomy; descent ⟺ no fiber-separation | `quotient_dichotomy_strong`, `descends_iff_not_separatesAFiber` |
| Group-action specialization | `quotientTest_group` |
| Collapse endpoint and time-degeneration | `Collapses`, `no_factor_through_collapsed_signature`, `time_degenerates` |
| Non-structural facts under forgetfulness | `exists_nonstructural_of_forgetful` |
| Character-valued no-go (primary) | `CharacterIsFiberLocal`, `character_not_structural` |
| Prop-valued special case | `PhenomenalIsFiberLocal`, `phenomenal_not_structural` |

The article's §8 gives the full table; each result's docstring cites its paper section.

## Scope

The formalization works at the **quotient/setoid level**: admissible transformations are an equivalence relation and descent is the universal property of the quotient. The genuine group-action case is recovered as the orbit relation `orbitRel G Obs`. The paper's broader categorical / groupoidal language and its order-theoretic `S_min` are deliberately **out of scope**; `Collapses` is a toy *endpoint* condition (globally constant invariant signature), not full `S_min`.

## Repository contents

| Path | Role |
|---|---|
| `WhereStructureEnds.lean` | the formalization (the whole artifact) |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | pinned build configuration and dependency lock |
| `LICENSE` | Apache License 2.0 |

## License

[Apache License 2.0](LICENSE).

## Citation

Please cite the companion article (version DOI [10.5281/zenodo.20666955](https://doi.org/10.5281/zenodo.20666955)) together with this repository's own Zenodo deposit (DOI minted on archival release).
