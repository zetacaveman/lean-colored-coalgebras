# Hopfbialg TODO

## Done now

- Added `ConvolutionAPI.lean` for practical convolution rewrites:
  - application formulas,
  - pushforward along algebra maps,
  - precomposition along coalgebra morphisms,
  - antipode/id convenience identities.
- Added `SweedlerAPI.lean` + `SweedlerNotation.md` as a tracked proof-engineering layer.

## Decide later (repo boundary question)

These are likely needed for Hopf-brace / Yang-Baxter formalization, but it is not yet decided
whether they belong in this repository or in a separate Hopf-brace-focused repository.

1. `Opposite.lean`:
   bialgebra/Hopf algebra instances on `Aᵐᵒᵖ` with simp API.
2. `ModuleBialgebra.lean`:
   action compatibility package for bialgebra-on-bialgebra actions.
3. `RotaBaxterHopf.lean`:
   Rota-Baxter operators with coalgebra compatibility assumptions.
4. `YangBaxterCore.lean`:
   braid-equation API for linear maps on tensor products.
5. `Cocycle.lean`:
   bijective 1-cocycle / relative Rota-Baxter bridge.
