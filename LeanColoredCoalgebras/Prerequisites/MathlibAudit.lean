import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.Bialgebra.GroupLike
import Mathlib.RingTheory.HopfAlgebra.Basic

namespace LeanColoredCoalgebras

universe u

/-!
# Mathlib Prerequisite Audit

This file records and reuses prerequisite algebraic structures already available in Mathlib.

Available in Mathlib:
* `Coalgebra R C`
* `Bialgebra R A`
* `HopfAlgebra R A`
* Convolution product via `WithConv (C →ₗ[R] A)` (`Mathlib.RingTheory.Coalgebra.Convolution`)
* Group-like elements `GroupLike R A` and `IsGroupLikeElem R a`

Likely project-specific extensions:
* Colored coalgebras
* Algebraic comodules over coalgebras (as needed by the papers)
* Semigrouplike notions specific to the paper conventions
* Coaugmented coalgebra wrappers (using a chosen group-like element)
-/

/-- The convolution algebra on linear maps from a coalgebra `C` to an algebra `A`. -/
abbrev ConvolutionHom (R C A : Type u) [CommSemiring R] [AddCommMonoid C] [Module R C]
    [Coalgebra R C] [Semiring A] [Algebra R A] :=
  WithConv (C →ₗ[R] A)

/-- Group-like elements in a bialgebra, reusing Mathlib's `GroupLike`. -/
abbrev GroupLikeElements (R A : Type u) [CommSemiring R] [Semiring A] [Bialgebra R A] :=
  GroupLike (R := R) (A := A)

end LeanColoredCoalgebras
