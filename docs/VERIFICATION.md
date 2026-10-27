# Verification log

## Comparator (as Palomar runs it)

Run on 2026-10-27 on the Lean sources of this repository as published, toolchain `leanprover/lean4:v4.35.0-rc2`, from a clean
build with the Mathlib cache fetched by `lake exe cache get`, with `scripts/verify-comparator.sh`.
Wall time about 18 minutes on a 4-core cloud container (the project already built).

`lake comparator` exported the 13 compared theorems and the permitted axioms from
`Solution`, checked that every constant used by the statements in `Challenge.lean` agrees with the
solution environment, and replayed the solution through three kernels:

```
Running con-ron kernel on solution
con-ron: 1 inductive blocks modelled in-process: Lean.Syntax (30 generated records, checked by the fold as declarations and not counted as records of the file)
con-ron: accepted 56196 declarations (--verified)
con-ron kernel accepts the solution
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

## Axioms

`#print axioms` for every compared theorem gives `[propext, Classical.choice, Quot.sound]`:

* `ArtGallery.etrinv_erComplete`
* `ArtGallery.agp_inER`
* `ArtGallery.agp_inER_guard_variables`
* `ArtGallery.agp_erComplete`
* `ArtGallery.agpInt_erComplete`
* `ArtGallery.etrinv_guard_correspondence`
* `ArtGallery.etr_guard_correspondence`
* `ArtGallery.algebraic_guard_coordinate`
* `ArtGallery.irrational_guards_needed`
* `ArtGallery.agpPointBoundary_inER_guard_variables`
* `ArtGallery.agpPointBoundary_erComplete`
* `ArtGallery.agpBoundaryPoint_inER_guard_variables`
* `ArtGallery.agpBoundaryPoint_erComplete`

## Other checks

* `lake build` (all default targets, from a clean `.lake` apart from the Mathlib cache): succeeds
  (2913 jobs, about 28 minutes on 4 cores).
* No `sorry`, `admit` or `native_decide` in the library (`ArtGallery/`, `Complexity/`, `PT/`,
  `Solution.lean`); `Challenge.lean` contains `sorry` only as the bodies of the statements.
  Kernel computations use `decide +kernel` only.
* Every Lean source file begins with a `module` header and has at most 10,000 physical lines;
  `Challenge.lean` has 654 lines. No `.lean` file is a symbolic link.
