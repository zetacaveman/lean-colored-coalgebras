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

/-- The convolution algebra on linear endomorphisms of a Hopf algebra. -/
abbrev EndConvolution (R A : Type u) [CommSemiring R] [Semiring A] [HopfAlgebra R A] :=
  WithConv (A →ₗ[R] A)

lemma antipode_conv_id (R A : Type u) [CommSemiring R] [Semiring A] [HopfAlgebra R A] :
    (WithConv.toConv (HopfAlgebra.antipode R : A →ₗ[R] A)) *
      (WithConv.toConv (LinearMap.id : A →ₗ[R] A)) = (1 : EndConvolution R A) := by
  ext a
  simpa [LinearMap.convOne_def, LinearMap.convMul_def, LinearMap.rTensor, LinearMap.lTensor] using
    (HopfAlgebra.mul_antipode_rTensor_comul_apply (R := R) (A := A) a)

lemma id_conv_antipode (R A : Type u) [CommSemiring R] [Semiring A] [HopfAlgebra R A] :
    (WithConv.toConv (LinearMap.id : A →ₗ[R] A)) *
      (WithConv.toConv (HopfAlgebra.antipode R : A →ₗ[R] A)) = (1 : EndConvolution R A) := by
  ext a
  simpa [LinearMap.convOne_def, LinearMap.convMul_def, LinearMap.rTensor, LinearMap.lTensor] using
    (HopfAlgebra.mul_antipode_lTensor_comul_apply (R := R) (A := A) a)

end LeanColoredCoalgebras
