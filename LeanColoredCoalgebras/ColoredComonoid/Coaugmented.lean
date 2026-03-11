import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.RingTheory.Coalgebra.GroupLike

namespace LeanColoredCoalgebras
namespace ColoredComonoid

universe u

section

variable (R C : Type u)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/--
A coaugmented coalgebra, presented as a coalgebra with a chosen group-like element.

Equivalently, this is the same data as a coalgebra morphism `R →ₗc[R] C`.
-/
structure CoaugmentedCoalgebra where
  coaug : C
  isGroupLike_coaug : IsGroupLikeElem R coaug

namespace CoaugmentedCoalgebra

variable {R C}

@[simp] lemma counit_coaug (K : CoaugmentedCoalgebra (R := R) (C := C)) :
    Coalgebra.counit (R := R) K.coaug = 1 :=
  K.isGroupLike_coaug.counit_eq_one

@[simp] lemma comul_coaug (K : CoaugmentedCoalgebra (R := R) (C := C)) :
    Coalgebra.comul (R := R) K.coaug = K.coaug ⊗ₜ[R] K.coaug :=
  K.isGroupLike_coaug.comul_eq_tmul_self

/-- The coaugmentation map `η : R → C`, given by `η(r) = r • g`. -/
def coaugLinearMap (K : CoaugmentedCoalgebra (R := R) (C := C)) : R →ₗ[R] C where
  toFun r := r • K.coaug
  map_add' r s := by simp [add_smul]
  map_smul' r s := by simp [smul_smul]

@[simp] lemma coaugLinearMap_apply (K : CoaugmentedCoalgebra (R := R) (C := C)) (r : R) :
    K.coaugLinearMap r = r • K.coaug := rfl

@[simp] lemma counit_coaugLinearMap (K : CoaugmentedCoalgebra (R := R) (C := C)) (r : R) :
    Coalgebra.counit (R := R) (K.coaugLinearMap r) = r := by
  simp [coaugLinearMap, counit_coaug]

@[simp] lemma comul_coaugLinearMap (K : CoaugmentedCoalgebra (R := R) (C := C)) (r : R) :
    Coalgebra.comul (R := R) (K.coaugLinearMap r) = r • (K.coaug ⊗ₜ[R] K.coaug) := by
  simp [coaugLinearMap, comul_coaug]

/-- The coaugmentation as a coalgebra morphism `R →ₗc[R] C`. -/
def coaugCoalgHom (K : CoaugmentedCoalgebra (R := R) (C := C)) : R →ₗc[R] C where
  toLinearMap := K.coaugLinearMap
  counit_comp := by
    apply LinearMap.ext
    intro x
    simp [coaugLinearMap, counit_coaug]
  map_comp_comul := by
    apply LinearMap.ext
    intro x
    calc
      TensorProduct.map (K.coaugLinearMap) (K.coaugLinearMap)
          (Coalgebra.comul (R := R) x)
          = K.coaug ⊗ₜ[R] (x • K.coaug) := by
              simp [coaugLinearMap]
      _ = x • (K.coaug ⊗ₜ[R] K.coaug) := by
            exact TensorProduct.tmul_smul (R := R) (r := x) (x := K.coaug) (y := K.coaug)
      _ = Coalgebra.comul (R := R) (K.coaugLinearMap x) := by
            simp [coaugLinearMap, comul_coaug]

end CoaugmentedCoalgebra
end

end ColoredComonoid
end LeanColoredCoalgebras
