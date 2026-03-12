import Hopfbialg.MathlibAudit

namespace LeanColoredCoalgebras

universe u

section BasicConvolution

variable {R C A : Type u}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [Semiring A] [Algebra R A]

@[simp] lemma convMul_apply
    (f g : ConvolutionHom R C A) (c : C) :
    (f * g) c = LinearMap.mul' R A (.map f.ofConv g.ofConv (Coalgebra.comul (R := R) c)) := by
  simp [LinearMap.convMul_apply]

@[simp] lemma convOne_apply (c : C) :
    (1 : ConvolutionHom R C A) c = algebraMap R A (Coalgebra.counit (R := R) c) := by
  simp [LinearMap.convOne_apply]

end BasicConvolution

section Functoriality

variable {R C D A B : Type u}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable [Semiring A] [Algebra R A]
variable [Semiring B] [Algebra R B]

lemma algHom_comp_convMul
    (h : A →ₐ[R] B) (f g : ConvolutionHom R C A) :
    h.toLinearMap.comp (f * g).ofConv =
      (WithConv.toConv (h.toLinearMap.comp f.ofConv) *
        WithConv.toConv (h.toLinearMap.comp g.ofConv) : ConvolutionHom R C B).ofConv := by
  simpa using (LinearMap.algHom_comp_convMul_distrib (R := R) (A := A) (B := B) (C := C) h f g)

lemma map_convMul
    (h : A →ₐ[R] B) (f g : ConvolutionHom R C A) :
    (WithConv.toConv (h.toLinearMap.comp (f * g).ofConv) : ConvolutionHom R C B) =
      (WithConv.toConv (h.toLinearMap.comp f.ofConv) *
        WithConv.toConv (h.toLinearMap.comp g.ofConv) : ConvolutionHom R C B) := by
  ext c
  simpa using
    (LinearMap.congr_fun
      (algHom_comp_convMul (R := R) (C := C) (A := A) (B := B) h f g) c)

lemma convMul_comp_coalgHom
    (f g : ConvolutionHom R C A) (k : D →ₗc[R] C) :
    (f * g).ofConv.comp k.toLinearMap =
      (WithConv.toConv (f.ofConv.comp k.toLinearMap) *
        WithConv.toConv (g.ofConv.comp k.toLinearMap) : ConvolutionHom R D A).ofConv := by
  simpa using
    (LinearMap.convMul_comp_coalgHom_distrib (R := R) (A := A) (B := D) (C := C) f g k)

lemma comap_convMul
    (f g : ConvolutionHom R C A) (k : D →ₗc[R] C) :
    (WithConv.toConv ((f * g).ofConv.comp k.toLinearMap) : ConvolutionHom R D A) =
      (WithConv.toConv (f.ofConv.comp k.toLinearMap) *
        WithConv.toConv (g.ofConv.comp k.toLinearMap) : ConvolutionHom R D A) := by
  ext d
  simpa using
    (LinearMap.congr_fun
      (convMul_comp_coalgHom (R := R) (C := C) (D := D) (A := A) f g k) d)

end Functoriality

section HopfConvenience

variable {R A : Type u}
variable [CommSemiring R] [Semiring A] [HopfAlgebra R A]

@[simp] lemma antipode_conv_id_end :
    (WithConv.toConv (HopfAlgebra.antipode R : A →ₗ[R] A) : EndConvolution R A) *
      (WithConv.toConv (LinearMap.id : A →ₗ[R] A) : EndConvolution R A) = 1 := by
  simpa using antipode_conv_id (R := R) (A := A)

@[simp] lemma id_conv_antipode_end :
    (WithConv.toConv (LinearMap.id : A →ₗ[R] A) : EndConvolution R A) *
      (WithConv.toConv (HopfAlgebra.antipode R : A →ₗ[R] A) : EndConvolution R A) = 1 := by
  simpa using id_conv_antipode (R := R) (A := A)

end HopfConvenience

end LeanColoredCoalgebras
