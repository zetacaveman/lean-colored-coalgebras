## Design Notes

### 2026-03-10: First auxiliary structure
- Started with weighted Rota-Baxter operators as an easy, high-reuse construction.
- Reused mathlib primitives (`Algebra`, `LinearMap`) instead of introducing new algebraic bases.
- Chose a `structure` (`RotaBaxterOperator`) rather than a typeclass so multiple operators can coexist on the same algebra without instance search conflicts.
- For terminology and baseline identity conventions, we follow Li Guo's introduction:
  *What is a Rota-Baxter algebra?* (Notices AMS, 2009).

### 2026-03-10: Algebraic prerequisite audit
- Confirmed Mathlib already provides core prerequisites:
  `Coalgebra`, convolution algebra on linear maps (`WithConv (C →ₗ[R] A)`),
  `Bialgebra`, `HopfAlgebra`, and group-like elements (`IsGroupLikeElem`, `GroupLike`).
- Added `Hopfbialg/MathlibAudit.lean` to centralize these reused APIs.
- Current expected gaps for this project are colored coalgebras and explicit algebraic comodule
  infrastructure, which we will introduce only as paper-specific structures.

### 2026-03-10: Start colored comonoid layer from coaugmentation
- Created `LeanColoredCoalgebras/ColoredComonoid/` as the new folder for this development line.
- Did not find a dedicated ring-theoretic `CoaugmentedCoalgebra` structure in current Mathlib.
- Introduced a small project structure:
  `CoaugmentedCoalgebra` = coalgebra + chosen group-like element.
- Added the induced linear map `η : R →ₗ[R] C` and bundled coalgebra morphism `η : R →ₗc[R] C`.

### 2026-03-10: Colored coalgebra core (paper-aligned data)
- Added `ColoredCoalgebra` in `ColoredComonoid/Colored.lean` using the paper's core triple
  `(C, G, δ : C → C[G])` with `C[G]` modeled as `G →₀ R`.
- Encoded the retraction data as coalgebra maps
  `incl : C[G] →ₗc[R] C`, `δ : C →ₗc[R] C[G]`, and `δ.comp incl = id`.
- Added basic API: canonical color element `colorElem`, idempotent color projector, and proof that
  each `colorElem g` is set-like.
- Deferred the conilpotence condition (`\bar{Δ}^N(x)=0` on `ker δ`) to a follow-up file where
  reduced-comultiplication iterates are introduced explicitly.

### 2026-03-10: Reduced comultiplication layer (in progress)
- Added paper-style decomposition maps in `ColoredComonoid/Colored.lean`:
  `ωl = (δ₀ ⊗ id) ∘ Δ`, `ωr = (id ⊗ δ₀) ∘ Δ`.
- Added reduced comultiplication over additive assumptions:
  `barComul = Δ - ωr - ωl`, with explicit formula lemma.
- Proved one key associator-adjusted compatibility identity:
  `assoc ∘ (ωr ⊗ id) ∘ Δ = (id ⊗ ωl) ∘ Δ`.
- Remaining work: finish the full family of compatibility identities and then
  prove coassociativity of `barComul` followed by iterated conilpotence.

### 2026-03-10: Iterates + explicit compatibility package
- Added `OmegaCompatibility` as an explicit structure packaging the remaining
  `ω`-cancellation identities needed in the reduced-coassociativity expansion.
- Added theorem
  `barComul_coassoc_of_omegaCompatibility`, proving full reduced coassociativity
  from that compatibility package.
- Added a left-bracketed iterate container `BarComulIterate` and recursive
  constructor `barComulIterate` (`n = 0` is `barComul`).
- Added `IsConilpotentOnKer` formalizing conilpotence on `ker δ` via iterated
  reduced comultiplication.
- Added `SimplyColoredCoalgebra` extending `ColoredCoalgebra` with fields for:
  `omegaCompatibility` and `conilpotent_onKer`.
- Design choice: keep compatibility assumptions explicit in a structure rather
  than silently strengthening base axioms, so assumptions remain audit-friendly.

### 2026-03-10: Endoprofunctor scaffold
- Added `DraftProfunctor/Basic.lean` with a project-local
  endoprofunctor scaffold and `Bimodule C := Profunctor C C`.
- Added coend-style horizontal composition data:
  `CompData`, generating relation `CompRel`, and quotient object `CompObj`.
- Added identity bimodule `HomBimod`.
- Mathlib note: we reuse its general ends/coends infrastructure
  (`CategoryTheory.Limits.Shapes.End`) but keep this explicit quotient model for
  concrete profunctor-composition calculations in this project.

### 2026-03-10: Align profunctors with Mathlib encoding
- Audited Mathlib: `coend` is present, but there is no dedicated category-theoretic
  `Profunctor` structure.
- Rewrote project `Profunctor` to the canonical Mathlib-style encoding
  `Dᵒᵖ ⥤ C ⥤ Type`.
- Kept helper API (`Profunctor.Obj`, `Profunctor.map`) so formulas remain close to
  paper notation while using standard Mathlib foundations.
- Updated `HomBimod` to be defined directly as a bifunctor.

### 2026-03-12: Split profunctor draft from colored/Hopf development
- Moved the profunctor/endoprofunctor scaffold to a separate top-level library:
  `DraftProfunctor`.
- Removed the profunctor import from `LeanColoredCoalgebras/Basic.lean`, so the
  colored coalgebra/Hopf pipeline no longer depends on draft profunctor work.

### 2026-03-12: Hopfbialg split + abstract filtered inversion layer
- Split prerequisite-heavy development into a separate Lean library/module prefix:
  `Hopfbialg.*`.
- Added top-level prerequisite modules:
  `Hopfbialg/MathlibAudit.lean` and
  `Hopfbialg/ConvolutionInverse.lean`.
- Added an abstract multiplicative filtration structure on rings:
  `NatRingFiltration`, with lemmas
  `pow_mem_succ_of_mem_one` and `isNilpotent_of_mem_one`.
- Added filtered invertibility criterion:
  `isUnit_of_filtered_convolution_errors`, reducing convolution invertibility to
  nilpotence of the two convolution error terms via filtration-level assumptions.
- Added `FilteredConvolutionData`, which packages filtration hypotheses at the
  level of submodules and induces nilpotence of convolution errors through
  vanishing-on-filtration-level assumptions.
- Added `CoalgebraFiltrationData`, a coalgebra-side filtration package whose
  `comul_vanish` axiom automatically yields the `mul_vanish` hypothesis needed
  by `FilteredConvolutionData`.
- Added conversion theorem layer from coalgebra filtration data to filtered
  convolution invertibility (`isUnit_mapF_of_errors`) and a convenience
  connected-form entry point
  `takeuchi_connected_form_of_coalgebra_filtration`.
- Added `takeuchi_connected_form` (connected/conilpotent practice form):
  if `(1 - id)` lies in filtration level `1` and top-stage/multiplicative
  filtration hypotheses hold, then `id` is convolution invertible.
- Rationale: this matches the planned Takeuchi-style workflow where coradical/
  QT-sequence machinery is deferred and consumed through an abstract filtration
  interface first.

### 2026-03-12: Convolution helper layer + Sweedler tracking notes
- Added `Hopfbialg/ConvolutionAPI.lean` as a convenience lemma layer for:
  convolution application formulas, algebra-map pushforward, coalgebra-map
  precomposition, and antipode/id identities.
- Added `Hopfbialg/SweedlerAPI.lean` to keep `Coalgebra.Repr`-based
  finite-sum forms close to the convolution/antipode map-level identities.
- Added `Hopfbialg/SweedlerNotation.md` as a design/debug document tracking
  normalization conventions and failure modes.
- Added `Hopfbialg/TODO.md` to track unresolved repository-boundary decisions
  for larger Hopf-brace/Yang-Baxter prerequisite modules.
