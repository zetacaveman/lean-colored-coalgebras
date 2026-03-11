import Mathlib

namespace LeanColoredCoalgebras

section RotaBaxter

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/--
A weighted Rota-Baxter operator of weight `w` on an `R`-algebra `A`.

This is kept as a structure (rather than a typeclass) so that multiple
operators on the same algebra can coexist without instance conflicts.
The defining identity follows the standard presentation in:
Li Guo, *What is a Rota-Baxter algebra?* (Notices AMS, 2009).
-/
structure RotaBaxterOperator (w : R) where
  toLinearMap : A →ₗ[R] A
  map_mul_map_eq (x y : A) :
    toLinearMap x * toLinearMap y =
      toLinearMap (toLinearMap x * y + x * toLinearMap y + w • (x * y))

namespace RotaBaxterOperator

variable {w : R}

instance : CoeFun (RotaBaxterOperator (R := R) (A := A) w) (fun _ => A → A) :=
  ⟨fun P => P.toLinearMap⟩

@[simp] lemma toLinearMap_apply (P : RotaBaxterOperator (R := R) (A := A) w) (x : A) :
    P.toLinearMap x = P x := rfl

@[simp] lemma map_zero (P : RotaBaxterOperator (R := R) (A := A) w) : P (0 : A) = 0 :=
  P.toLinearMap.map_zero

@[simp] lemma map_add (P : RotaBaxterOperator (R := R) (A := A) w) (x y : A) :
    P (x + y) = P x + P y :=
  P.toLinearMap.map_add x y

lemma map_mul_map (P : RotaBaxterOperator (R := R) (A := A) w) (x y : A) :
    P x * P y = P (P x * y + x * P y + w • (x * y)) :=
  P.map_mul_map_eq x y

lemma map_mul_map_weight_zero (P : RotaBaxterOperator (R := R) (A := A) (0 : R)) (x y : A) :
    P x * P y = P (P x * y + x * P y) := by
  simpa using P.map_mul_map x y

end RotaBaxterOperator
end RotaBaxter
end LeanColoredCoalgebras
