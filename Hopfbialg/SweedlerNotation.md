# Sweedler Notation in This Project

This note explains:

1. what Sweedler notation means mathematically,
2. how Mathlib represents the same content,
3. how the local `Hopfbialg` API exposes it in a proof-friendly way.

## 1) What Sweedler notation is

Let `C` be a coalgebra with comultiplication `Δ : C → C ⊗ C`.

Classical form:

- `Δ(x) = Σ_i x_i' ⊗ x_i''`

Sweedler shorthand:

- `Δ(x) = Σ x_(1) ⊗ x_(2)`

The sum is usually suppressed in writing:

- `Δ(x) = x_(1) ⊗ x_(2)` (implicitly summed).

For iterated comultiplication, one writes:

- `(Δ ⊗ id)Δ(x) = Σ x_(1) ⊗ x_(2) ⊗ x_(3)`,
- `(id ⊗ Δ)Δ(x) = Σ x_(1) ⊗ x_(2) ⊗ x_(3)`.

Coassociativity is exactly the statement that these are equal.

## 2) Typical Sweedler formulas used in Hopf algebra

Convolution of `f g : C → A`:

- `(f * g)(x) = Σ f(x_(1)) g(x_(2))`.

Convolution unit:

- `1(x) = η(ε(x))`, where `ε` is counit and `η` is algebra unit.

Antipode identities (in Sweedler form):

- `Σ S(x_(1)) x_(2) = η(ε(x))`,
- `Σ x_(1) S(x_(2)) = η(ε(x))`.

## 3) How Mathlib encodes this (no raw index symbols)

Mathlib keeps everything rigorous at the map/tensor level:

- `Coalgebra.comul (R := R) x : C ⊗[R] C`
- convolution is defined via tensor map + multiplication.

When a finite-sum presentation is needed, Mathlib uses `Coalgebra.Repr R x`:

- `repr.index` (finite index set),
- `repr.left : index → C`,
- `repr.right : index → C`,
- with `comul x = Σ i∈index, left i ⊗ right i`.

So `x_(1), x_(2)` is represented by `repr.left i, repr.right i` under a finite sum.

## 4) Repeated-comultiplication problem (why proofs get hard)

The core facts are already true in Mathlib at map/tensor level (coassociativity, counit identities,
bialgebra multiplicativity of `comul`, Hopf antipode axioms). The problem is proof engineering when
these are used repeatedly.

Main failure modes:

1. `Coalgebra.Repr` is not canonical.
   Two valid decompositions of `comul x` can produce different index types and different `left/right`
   functions, so terms are propositionally equal but not definitionally identical.
2. Iterated comultiplication creates nested sums and nested indices.
   For `Δ²`, `Δ³`, etc., the index bookkeeping grows quickly and obscures algebraic content.
3. Coassociativity transport overhead.
   Coassociativity is a clean tensor-level equality, but translating both sides to `Repr` sums often
   requires explicit transport/reindex lemmas.
4. `simp` fragility.
   Large tensor reassociation plus index transport can make `simp` either ineffective or too aggressive.
5. Term-size blowup.
   Antipode/convolution arguments become long double/triple-sum expressions if expanded too early.

This is primarily a maintainability issue, not a mathematical correctness issue.

## 5) Fix strategy used in this repo

To control the above, we follow a layered workflow:

1. Prove and rewrite map/tensor-level identities first.
2. Expose apply-level bridge lemmas (`..._apply`) for elementwise use.
3. Delay `Coalgebra.Repr`/finite-sum conversion until the last possible step.
4. Keep reusable tensor reassociation and transport rewrites in API lemmas, not inside theorem bodies.
5. Keep rewrite control explicit; avoid broad ad-hoc simp over big tensor expressions.

Planned strengthening:

- add normalized iterated-comultiplication helpers (`Δ²`, `Δ³`) as stable API;
- possibly add a dedicated simp set (for example `hopf_simp`) to avoid global simp side effects.

## 6) Local API layers and roles

Current API anchors:

- `Hopfbialg/ConvolutionAPI.lean`
- `Hopfbialg/SweedlerAPI.lean`

### 6a) ConvolutionAPI (tensor/map-level and apply-level bridge)

Implemented lemmas:

- `convMul_apply`
- `convOne_apply`
- `algHom_comp_convMul`
- `map_convMul`
- `convMul_comp_coalgHom`
- `comap_convMul`
- `antipode_conv_id_end`
- `id_conv_antipode_end`

Use this file when you want robust rewrites without manually expanding tensor plumbing.

### 6b) SweedlerAPI (finite-sum / `Repr` view)

Implemented lemmas:

- `convMul_apply_repr`
- `sum_antipode_mul_eq_algebraMap_counit`
- `sum_mul_antipode_eq_algebraMap_counit`

Use this file when a proof is naturally written with Sweedler sums.

## 7) Recommended proof workflow

1. Start from map-level identity when possible.
2. Move to element form with `_apply` lemmas (`convMul_apply`, etc.).
3. Only then switch to finite sums using `Coalgebra.Repr`.
4. Avoid ad-hoc large `simp` over tensor reassociation unless necessary.
5. If needed repeatedly, package a helper lemma in API rather than repeating local rewrites.

This keeps proofs shorter, less brittle, and easier to debug.

## 8) Minimal usage pattern

For a convolution statement:

1. rewrite `(f * g) x` by `convMul_apply`,
2. if you need explicit sums, choose `repr : Coalgebra.Repr R x`,
3. rewrite by `convMul_apply_repr repr f g`.

For antipode cancellation in sum form:

1. pick `repr : Coalgebra.Repr R x`,
2. use `sum_antipode_mul_eq_algebraMap_counit` or `sum_mul_antipode_eq_algebraMap_counit`.

## 9) Conventions

1. Prefer map-level equalities as primary theorem statements.
2. Export an `_apply` lemma for each map-level theorem.
3. Export a `Coalgebra.Repr` sum lemma only after map/apply forms exist.
4. Keep tensor reassociation/transport rewrites in dedicated helper lemmas.

## 10) Debug checklist

1. If `simp` loops, move a rewrite out of `[simp]` and apply it explicitly.
2. If tensor goals explode, return to map-level and re-derive apply-level.
3. If indexed Sweedler goals are fragile, switch to `Coalgebra.Repr` sum lemmas.
4. Document new lemmas as map-level, apply-level, or repr-level.

## 11) Open design questions

- Should we add a custom simp attribute (for example `@[hopf_simp]`) for controlled normalization?
- Should we add iterated-comultiplication helpers (`Δ²`, `Δ³`) now or later?

## 12) Heuristic status

- `lake build Hopfbialg LeanColoredCoalgebras DraftProfunctor` passes.
- A small smoke test of the API (`/tmp/hopf_api_smoke.lean`) compiles.
