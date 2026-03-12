import Hopfbialg.ConvolutionAPI

namespace LeanColoredCoalgebras

universe u

section ReprConvolution

variable {R C A : Type u}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [Semiring A] [Algebra R A]

lemma convMul_apply_repr {a : C} (repr : Coalgebra.Repr R a)
    (f g : ConvolutionHom R C A) :
    (f * g) a = ∑ i ∈ repr.index, f (repr.left i) * g (repr.right i) := by
  simpa using (Coalgebra.Repr.convMul_apply (R := R) (a := a) repr f g)

end ReprConvolution

section ReprAntipode

variable {R A : Type u}
variable [CommSemiring R] [Semiring A] [HopfAlgebra R A]

lemma sum_antipode_mul_eq_algebraMap_counit {a : A} (repr : Coalgebra.Repr R a) :
    ∑ i ∈ repr.index, HopfAlgebra.antipode R (repr.left i) * repr.right i =
      algebraMap R A (Coalgebra.counit a) := by
  simpa using (HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit (R := R) (a := a) repr)

lemma sum_mul_antipode_eq_algebraMap_counit {a : A} (repr : Coalgebra.Repr R a) :
    ∑ i ∈ repr.index, repr.left i * HopfAlgebra.antipode R (repr.right i) =
      algebraMap R A (Coalgebra.counit a) := by
  simpa using (HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit (R := R) (a := a) repr)

end ReprAntipode

end LeanColoredCoalgebras
