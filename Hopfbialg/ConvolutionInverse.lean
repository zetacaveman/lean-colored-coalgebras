import Hopfbialg.MathlibAudit
import Mathlib.RingTheory.Nilpotent.Basic

namespace LeanColoredCoalgebras

universe u

/-- In the convolution algebra of endomorphisms of a Hopf algebra, `id` is a unit.
Its inverse is the antipode. -/
theorem id_isUnit_endConvolution (R A : Type u)
    [CommSemiring R] [Semiring A] [HopfAlgebra R A] :
    IsUnit (WithConv.toConv (LinearMap.id : A →ₗ[R] A) : EndConvolution R A) := by
  refine ⟨⟨WithConv.toConv (LinearMap.id : A →ₗ[R] A),
    WithConv.toConv (HopfAlgebra.antipode R : A →ₗ[R] A), ?_, ?_⟩, rfl⟩
  · simpa using id_conv_antipode (R := R) (A := A)
  · simpa using antipode_conv_id (R := R) (A := A)

/-- Inverse elements are unique in the convolution monoid. -/
theorem convolution_inverse_unique {R A : Type u}
    [CommSemiring R] [Semiring A] [HopfAlgebra R A]
    {f g h : EndConvolution R A} (hg : g * f = 1) (hh : f * h = 1) :
    g = h :=
  left_inv_eq_right_inv hg hh

/-- If `1 - f` is nilpotent in the convolution ring, then `f` has a two-sided
convolution inverse. This is the algebraic core behind finite geometric-series inverses. -/
theorem exists_inverse_of_nilpotent_one_sub {R A : Type u}
    [CommSemiring R] [Ring A] [HopfAlgebra R A]
    (f : EndConvolution R A)
    (h : IsNilpotent ((1 : EndConvolution R A) - f)) :
    ∃ g : EndConvolution R A, g * f = 1 ∧ f * g = 1 := by
  have hfUnit : IsUnit f := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (IsNilpotent.isUnit_one_sub (r := (1 : EndConvolution R A) - f) h)
  rcases hfUnit with ⟨u, hu⟩
  refine ⟨(↑u⁻¹ : EndConvolution R A), ?_, ?_⟩
  · calc
      (↑u⁻¹ : EndConvolution R A) * f = (↑u⁻¹ : EndConvolution R A) * ↑u := by simp [hu]
      _ = 1 := u.inv_mul
  · calc
      f * (↑u⁻¹ : EndConvolution R A) = (↑u : EndConvolution R A) * ↑u⁻¹ := by simp [hu]
      _ = 1 := u.mul_inv

/-- Abstract filtered-step criterion: if both convolution error terms are nilpotent,
then the target map is convolution invertible. -/
theorem isUnit_of_nilpotent_convolution_errors
    {R C A : Type u}
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [Ring A] [Algebra R A]
    (f g : ConvolutionHom R C A)
    (hgf : IsNilpotent ((1 : ConvolutionHom R C A) - g * f))
    (hfg : IsNilpotent ((1 : ConvolutionHom R C A) - f * g)) :
    IsUnit f := by
  have hgfUnit : IsUnit (g * f) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (IsNilpotent.isUnit_one_sub (r := (1 : ConvolutionHom R C A) - g * f) hgf)
  have hfgUnit : IsUnit (f * g) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (IsNilpotent.isUnit_one_sub (r := (1 : ConvolutionHom R C A) - f * g) hfg)
  rcases hgfUnit with ⟨u, hu⟩
  rcases hfgUnit with ⟨v, hv⟩
  let l : ConvolutionHom R C A := (↑u⁻¹ : ConvolutionHom R C A) * g
  let r : ConvolutionHom R C A := g * (↑v⁻¹ : ConvolutionHom R C A)
  have hl : l * f = 1 := by
    calc
      l * f = ((↑u⁻¹ : ConvolutionHom R C A) * g) * f := rfl
      _ = (↑u⁻¹ : ConvolutionHom R C A) * (g * f) := by simp [mul_assoc]
      _ = (↑u⁻¹ : ConvolutionHom R C A) * ↑u := by simp [hu]
      _ = 1 := u.inv_mul
  have hr : f * r = 1 := by
    calc
      f * r = f * (g * (↑v⁻¹ : ConvolutionHom R C A)) := rfl
      _ = (f * g) * (↑v⁻¹ : ConvolutionHom R C A) := by simp [mul_assoc]
      _ = (↑v : ConvolutionHom R C A) * (↑v⁻¹ : ConvolutionHom R C A) := by simp [hv]
      _ = 1 := v.mul_inv
  have hlr : l = r := left_inv_eq_right_inv hl hr
  refine ⟨⟨f, r, hr, ?_⟩, rfl⟩
  calc
    r * f = l * f := by simp [hlr]
    _ = 1 := hl

/-- A multiplicative `ℕ`-indexed filtration on a ring. -/
structure NatRingFiltration (M : Type u) [Ring M] where
  Q : ℕ → AddSubgroup M
  mul_mem : ∀ {i j : ℕ} {x y : M}, x ∈ Q i → y ∈ Q j → x * y ∈ Q (i + j)

namespace NatRingFiltration

variable {M : Type u} [Ring M] (F : NatRingFiltration M)

lemma pow_mem_succ_of_mem_one {x : M} (hx : x ∈ F.Q 1) :
    ∀ n : ℕ, x ^ (n + 1) ∈ F.Q (n + 1)
  | 0 => by simpa using hx
  | n + 1 => by
      simpa [pow_succ, Nat.add_assoc] using F.mul_mem (pow_mem_succ_of_mem_one hx n) hx

lemma isNilpotent_of_mem_one {x : M} (hx : x ∈ F.Q 1) {N : ℕ} (hN : F.Q (N + 1) = ⊥) :
    IsNilpotent x := by
  refine ⟨N + 1, ?_⟩
  have hxpow : x ^ (N + 1) ∈ F.Q (N + 1) := F.pow_mem_succ_of_mem_one hx N
  have hxbot : x ^ (N + 1) ∈ (⊥ : AddSubgroup M) := by simpa [hN] using hxpow
  exact AddSubgroup.mem_bot.mp hxbot

end NatRingFiltration

/-- Abstract filtered criterion (ring-theoretic form):
if both convolution error terms lie in filtration level `1`, and level `N+1` is zero,
then `f` is convolution invertible. -/
theorem isUnit_of_filtered_convolution_errors
    {R C A : Type u}
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [Ring A] [Algebra R A]
    (f g : ConvolutionHom R C A)
    (F : NatRingFiltration (ConvolutionHom R C A))
    (N : ℕ)
    (hN : F.Q (N + 1) = ⊥)
    (hgf_mem : ((1 : ConvolutionHom R C A) - g * f) ∈ F.Q 1)
    (hfg_mem : ((1 : ConvolutionHom R C A) - f * g) ∈ F.Q 1) :
    IsUnit f := by
  have hgf_nil : IsNilpotent ((1 : ConvolutionHom R C A) - g * f) :=
    F.isNilpotent_of_mem_one hgf_mem hN
  have hfg_nil : IsNilpotent ((1 : ConvolutionHom R C A) - f * g) :=
    F.isNilpotent_of_mem_one hfg_mem hN
  exact isUnit_of_nilpotent_convolution_errors (R := R) (C := C) (A := A) f g hgf_nil hfg_nil

section FilteredConvolution

variable {R C A : Type u}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [Ring A] [Algebra R A]

/-- Linear maps that vanish on a chosen submodule. -/
def vanishOn (V : Submodule R C) : AddSubgroup (ConvolutionHom R C A) where
  carrier := {f | ∀ x ∈ V, f x = 0}
  add_mem' hf hg x hx := by simp [hf x hx, hg x hx]
  zero_mem' x hx := by simp
  neg_mem' hf x hx := by simp [hf x hx]

@[simp] lemma mem_vanishOn_iff (V : Submodule R C) (f : ConvolutionHom R C A) :
    f ∈ vanishOn (R := R) (C := C) (A := A) V ↔ ∀ x ∈ V, f x = 0 :=
  Iff.rfl

lemma vanishOn_top_eq_bot :
    vanishOn (R := R) (C := C) (A := A) (⊤ : Submodule R C) = ⊥ := by
  ext f
  constructor
  · intro hf
    have hzero : ∀ x : C, f x = 0 := fun x => hf x (by simp)
    exact AddSubgroup.mem_bot.mpr <| by
      ext x
      exact hzero x
  · intro hf
    rcases AddSubgroup.mem_bot.mp hf with rfl
    simp [vanishOn]

/-- Abstract filtration package for convolution invertibility arguments.

`filtration` should be thought of as a coalgebra filtration (`QT` / coradical-style),
while `mul_vanish` packages the induced multiplicative behavior on vanishing maps. -/
structure FilteredConvolutionData (R C A : Type u)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [Ring A] [Algebra R A] where
  filtration : ℕ → Submodule R C
  mul_vanish :
    ∀ {i j : ℕ} {φ ψ : ConvolutionHom R C A},
      φ ∈ vanishOn (R := R) (C := C) (A := A) (filtration i) →
      ψ ∈ vanishOn (R := R) (C := C) (A := A) (filtration j) →
      φ * ψ ∈ vanishOn (R := R) (C := C) (A := A) (filtration (i + j))
  top_stage : ∃ N : ℕ, filtration (N + 1) = ⊤
  mapF : ConvolutionHom R C A
  mapG : ConvolutionHom R C A
  left_error_on_one :
    ((1 : ConvolutionHom R C A) - mapG * mapF) ∈
      vanishOn (R := R) (C := C) (A := A) (filtration 1)
  right_error_on_one :
    ((1 : ConvolutionHom R C A) - mapF * mapG) ∈
      vanishOn (R := R) (C := C) (A := A) (filtration 1)

namespace FilteredConvolutionData

variable (D : FilteredConvolutionData R C A)

/-- The ring filtration on convolution maps induced by `D`. -/
def toNatRingFiltration : NatRingFiltration (ConvolutionHom R C A) where
  Q := fun n => vanishOn (R := R) (C := C) (A := A) (D.filtration n)
  mul_mem := by
    intro i j x y hx hy
    exact D.mul_vanish hx hy

lemma top_stage_q_eq_bot :
    ∃ N : ℕ, D.toNatRingFiltration.Q (N + 1) = (⊥ : AddSubgroup (ConvolutionHom R C A)) := by
  rcases D.top_stage with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  simpa [toNatRingFiltration, hN] using (vanishOn_top_eq_bot (R := R) (C := C) (A := A))

lemma left_error_nilpotent :
    IsNilpotent ((1 : ConvolutionHom R C A) - D.mapG * D.mapF) := by
  rcases D.top_stage_q_eq_bot with ⟨N, hN⟩
  exact NatRingFiltration.isNilpotent_of_mem_one
    (F := D.toNatRingFiltration) D.left_error_on_one hN

lemma right_error_nilpotent :
    IsNilpotent ((1 : ConvolutionHom R C A) - D.mapF * D.mapG) := by
  rcases D.top_stage_q_eq_bot with ⟨N, hN⟩
  exact NatRingFiltration.isNilpotent_of_mem_one
    (F := D.toNatRingFiltration) D.right_error_on_one hN

/-- Main abstract consequence: `D.mapF` is convolution invertible. -/
theorem isUnit_mapF : IsUnit D.mapF := by
  exact isUnit_of_nilpotent_convolution_errors
    (R := R) (C := C) (A := A) D.mapF D.mapG D.left_error_nilpotent D.right_error_nilpotent

end FilteredConvolutionData

/-! ### Coalgebra-side filtration package -/

/-- Coalgebra filtration data that can automatically generate the
`mul_vanish` hypothesis needed for convolution-filtered inversion.

The key axiom `comul_vanish` says: if `x` lies in filtration level `i + j`,
then every pair of linear maps vanishing on levels `i` and `j` kills `Δ x`
after applying the standard convolution-evaluation map. -/
structure CoalgebraFiltrationData (R C A : Type u)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [Ring A] [Algebra R A] where
  filtration : ℕ → Submodule R C
  comul_vanish :
    ∀ {i j : ℕ} {φ ψ : ConvolutionHom R C A} {x : C},
      x ∈ filtration (i + j) →
      φ ∈ vanishOn (R := R) (C := C) (A := A) (filtration i) →
      ψ ∈ vanishOn (R := R) (C := C) (A := A) (filtration j) →
      LinearMap.mul' R A (.map φ.ofConv ψ.ofConv (Coalgebra.comul (R := R) x)) = 0
  top_stage : ∃ N : ℕ, filtration (N + 1) = ⊤

namespace CoalgebraFiltrationData

variable (D : CoalgebraFiltrationData R C A)

/-- Coalgebra-side vanishing implies the multiplicative vanishing law on convolution maps. -/
lemma mul_vanish :
    ∀ {i j : ℕ} {φ ψ : ConvolutionHom R C A},
      φ ∈ vanishOn (R := R) (C := C) (A := A) (D.filtration i) →
      ψ ∈ vanishOn (R := R) (C := C) (A := A) (D.filtration j) →
      φ * ψ ∈ vanishOn (R := R) (C := C) (A := A) (D.filtration (i + j)) := by
  intro i j φ ψ hφ hψ x hx
  have h := D.comul_vanish (i := i) (j := j) (x := x) hx hφ hψ
  simpa [LinearMap.convMul_apply] using h

/-- Convert coalgebra-side filtration data into `FilteredConvolutionData`. -/
def toFilteredConvolutionData
    (mapF mapG : ConvolutionHom R C A)
    (left_error_on_one :
      ((1 : ConvolutionHom R C A) - mapG * mapF) ∈
        vanishOn (R := R) (C := C) (A := A) (D.filtration 1))
    (right_error_on_one :
      ((1 : ConvolutionHom R C A) - mapF * mapG) ∈
        vanishOn (R := R) (C := C) (A := A) (D.filtration 1)) :
    FilteredConvolutionData (R := R) (C := C) (A := A) where
  filtration := D.filtration
  mul_vanish := D.mul_vanish
  top_stage := D.top_stage
  mapF := mapF
  mapG := mapG
  left_error_on_one := left_error_on_one
  right_error_on_one := right_error_on_one

/-- Coalgebra-side filtration criterion for convolution invertibility. -/
theorem isUnit_mapF_of_errors
    (mapF mapG : ConvolutionHom R C A)
    (left_error_on_one :
      ((1 : ConvolutionHom R C A) - mapG * mapF) ∈
        vanishOn (R := R) (C := C) (A := A) (D.filtration 1))
    (right_error_on_one :
      ((1 : ConvolutionHom R C A) - mapF * mapG) ∈
        vanishOn (R := R) (C := C) (A := A) (D.filtration 1)) :
    IsUnit mapF := by
  let Df : FilteredConvolutionData (R := R) (C := C) (A := A) :=
    D.toFilteredConvolutionData mapF mapG left_error_on_one right_error_on_one
  simpa [Df] using Df.isUnit_mapF

end CoalgebraFiltrationData

section ConnectedTakeuchi

variable {R C : Type u}
variable [CommSemiring R] [Ring C] [Bialgebra R C]

/-- Connected/conilpotent-style Takeuchi criterion in the common form used in Hopf algebra practice:
if `1 - id` lies in filtration level `1`, and filtration compatibility/top-stage hypotheses hold,
then `id` is convolution invertible. -/
theorem takeuchi_connected_form
    (filtration : ℕ → Submodule R C)
    (mul_vanish :
      ∀ {i j : ℕ} {f g : ConvolutionHom R C C},
        f ∈ vanishOn (R := R) (C := C) (A := C) (filtration i) →
        g ∈ vanishOn (R := R) (C := C) (A := C) (filtration j) →
        f * g ∈ vanishOn (R := R) (C := C) (A := C) (filtration (i + j)))
    (top_stage : ∃ N : ℕ, filtration (N + 1) = ⊤)
    (h_id_on_one :
      ((1 : ConvolutionHom R C C) -
        (WithConv.toConv (LinearMap.id : C →ₗ[R] C) : ConvolutionHom R C C)) ∈
          vanishOn (R := R) (C := C) (A := C) (filtration 1)) :
    IsUnit ((WithConv.toConv (LinearMap.id : C →ₗ[R] C)) : ConvolutionHom R C C) := by
  let D : FilteredConvolutionData (R := R) (C := C) (A := C) := {
    filtration := filtration
    mul_vanish := mul_vanish
    top_stage := top_stage
    mapF := (WithConv.toConv (LinearMap.id : C →ₗ[R] C) : ConvolutionHom R C C)
    mapG := 1
    left_error_on_one := by simpa [one_mul] using h_id_on_one
    right_error_on_one := by simpa [mul_one] using h_id_on_one
  }
  simpa using D.isUnit_mapF

/-- Same connected/conilpotent Takeuchi criterion, but with `mul_vanish`
derived automatically from coalgebra-side filtration data. -/
theorem takeuchi_connected_form_of_coalgebra_filtration
    (D : CoalgebraFiltrationData (R := R) (C := C) (A := C))
    (h_id_on_one :
      ((1 : ConvolutionHom R C C) -
        (WithConv.toConv (LinearMap.id : C →ₗ[R] C) : ConvolutionHom R C C)) ∈
          vanishOn (R := R) (C := C) (A := C) (D.filtration 1)) :
    IsUnit ((WithConv.toConv (LinearMap.id : C →ₗ[R] C)) : ConvolutionHom R C C) := by
  exact takeuchi_connected_form (R := R) (C := C)
    (filtration := D.filtration)
    (mul_vanish := D.mul_vanish)
    (top_stage := D.top_stage)
    h_id_on_one

end ConnectedTakeuchi

end FilteredConvolution

end LeanColoredCoalgebras
