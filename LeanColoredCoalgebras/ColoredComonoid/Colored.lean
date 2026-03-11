import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# Colored Coalgebra Layer

This file formalizes the first algebraic layer of simply colored coalgebras from:

* Y. Mo, "The structure of simply colored coalgebras", arXiv:2301.08462
  (`https://arxiv.org/abs/2301.08462`).

Paper alignment:

* Subsection "Simply colored coalgebras": definition of a triple `(C, G, δ : C → C[G])`.
* Subsubsection "Reduced comultiplication" (in "Simply colored comonoid"):
  definitions of `ω_l`, `ω_r`, and `\bar Δ = Δ - ω_r - ω_l`.
* Theorem labeled `\label{1}` in the source: coassociativity of reduced comultiplication.

This file currently sets up the data and first compatibility lemmas needed for that theorem.
-/

namespace LeanColoredCoalgebras
namespace ColoredComonoid

universe u v

open scoped TensorProduct

section

variable (R : Type u) (G : Type v) [CommSemiring R]

/--
The set-like coalgebra `C[G]` from the paper, implemented as finitely supported functions.

Paper reference: the item defining the set-like coalgebra over a set `G`
in the subsection "Simply colored coalgebras".
-/
abbrev SetLikeCoalgebra := G →₀ R

end

section

variable (R : Type u) (C : Type v) (G : Type v)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/--
Core data of a colored coalgebra in the sense of the paper:
a coalgebra `C`, a color set `G`, and a retraction `δ : C → C[G]`.

Here `C[G]` is formalized as `G →₀ R` with its Mathlib coalgebra structure.

Paper reference:
the definition beginning "Let `C` be a coalgebra, `G` be a set of set-like
elements in `C`, and `δ : C → C[G]` be a retraction ...".
-/
structure ColoredCoalgebra where
  /-- Inclusion of the set-like coalgebra into `C`. -/
  incl : SetLikeCoalgebra R G →ₗc[R] C
  /-- Retraction onto the set-like coalgebra. -/
  δ : C →ₗc[R] SetLikeCoalgebra R G
  /-- The retraction law `δ ∘ incl = id`. -/
  δ_comp_incl : δ.comp incl = CoalgHom.id R (SetLikeCoalgebra R G)

namespace ColoredCoalgebra

variable {R C G}

/-- The canonical element in `C` associated to a color `g : G`. -/
noncomputable def colorElem (S : ColoredCoalgebra (R := R) (C := C) (G := G)) (g : G) : C :=
  S.incl (Finsupp.single g 1)

/-! `δ ∘ incl = id` at the level of elements. -/
@[simp] lemma δ_incl_apply (S : ColoredCoalgebra (R := R) (C := C) (G := G))
    (x : SetLikeCoalgebra R G) : S.δ (S.incl x) = x := by
  simpa using CoalgHom.congr_fun S.δ_comp_incl x

/-- The idempotent coalgebra endomorphism `δ₀ = incl ∘ δ` on `C`. -/
def colorProjectorCoalgHom (S : ColoredCoalgebra (R := R) (C := C) (G := G)) : C →ₗc[R] C :=
  S.incl.comp S.δ

/-- The projection to colors viewed as an endomorphism of `C`. -/
def colorProjector (S : ColoredCoalgebra (R := R) (C := C) (G := G)) : C →ₗ[R] C :=
  S.colorProjectorCoalgHom.toLinearMap

@[simp] lemma colorProjector_apply (S : ColoredCoalgebra (R := R) (C := C) (G := G)) (x : C) :
    S.colorProjector x = S.incl (S.δ x) := rfl

/--
`δ₀` is idempotent.

Paper reference: equation `δ ∘ δ = δ` in the "Reduced comultiplication" discussion.
-/
lemma colorProjector_idempotent (S : ColoredCoalgebra (R := R) (C := C) (G := G)) :
    S.colorProjector.comp S.colorProjector = S.colorProjector := by
  ext x
  simp [colorProjector, colorProjectorCoalgHom]

/--
`δ₀` preserves counit.

Paper reference: equation `ε ∘ δ = ε` in the "Reduced comultiplication" discussion.
-/
@[simp] lemma counit_comp_colorProjector (S : ColoredCoalgebra (R := R) (C := C) (G := G)) :
    Coalgebra.counit ∘ₗ S.colorProjector = Coalgebra.counit := by
  change Coalgebra.counit ∘ₗ S.colorProjectorCoalgHom.toLinearMap = Coalgebra.counit
  exact S.colorProjectorCoalgHom.counit_comp

/--
`δ₀` is compatible with comultiplication.

Paper reference: equation `Δ ∘ δ = (δ ⊗ δ) ∘ Δ` in the "Reduced comultiplication" discussion.
-/
@[simp] lemma map_colorProjector_comp_comul
    (S : ColoredCoalgebra (R := R) (C := C) (G := G)) :
    TensorProduct.map S.colorProjector S.colorProjector ∘ₗ Coalgebra.comul =
      Coalgebra.comul ∘ₗ S.colorProjector := by
  change
      TensorProduct.map S.colorProjectorCoalgHom.toLinearMap S.colorProjectorCoalgHom.toLinearMap
        ∘ₗ Coalgebra.comul
        = Coalgebra.comul ∘ₗ S.colorProjectorCoalgHom.toLinearMap
  exact S.colorProjectorCoalgHom.map_comp_comul

/-- `ω_l = (δ₀ ⊗ id) ∘ Δ` in the paper notation. -/
def omegaL (S : ColoredCoalgebra (R := R) (C := C) (G := G)) :
    C →ₗ[R] TensorProduct R C C :=
  TensorProduct.map S.colorProjector (LinearMap.id : C →ₗ[R] C) ∘ₗ Coalgebra.comul

/-- `ω_r = (id ⊗ δ₀) ∘ Δ` in the paper notation. -/
def omegaR (S : ColoredCoalgebra (R := R) (C := C) (G := G)) :
    C →ₗ[R] TensorProduct R C C :=
  TensorProduct.map (LinearMap.id : C →ₗ[R] C) S.colorProjector ∘ₗ Coalgebra.comul

@[simp] lemma omegaL_apply (S : ColoredCoalgebra (R := R) (C := C) (G := G)) (x : C) :
    S.omegaL x =
      TensorProduct.map S.colorProjector (LinearMap.id : C →ₗ[R] C) (Coalgebra.comul x) :=
  rfl

@[simp] lemma omegaR_apply (S : ColoredCoalgebra (R := R) (C := C) (G := G)) (x : C) :
    S.omegaR x =
      TensorProduct.map (LinearMap.id : C →ₗ[R] C) S.colorProjector (Coalgebra.comul x) :=
  rfl

/--
Associator form of one bicomodule-compatibility identity used in reduced-coassociativity expansions.

This is the strictness-adjusted Lean version of one of the equations computed in the
"Reduced comultiplication" subsection before Theorem `\label{1}`.
-/
lemma assoc_comp_omegaR_rTensor_comp_comul
    (S : ColoredCoalgebra (R := R) (C := C) (G := G)) :
    TensorProduct.assoc R C C C ∘ₗ S.omegaR.rTensor C ∘ₗ Coalgebra.comul (R := R) (A := C) =
      S.omegaL.lTensor C ∘ₗ Coalgebra.comul (R := R) (A := C) := by
  calc
    TensorProduct.assoc R C C C ∘ₗ S.omegaR.rTensor C ∘ₗ Coalgebra.comul (R := R) (A := C)
      = TensorProduct.assoc R C C C ∘ₗ
          (TensorProduct.map
            (TensorProduct.map (LinearMap.id : C →ₗ[R] C) S.colorProjector)
            (LinearMap.id : C →ₗ[R] C) ∘ₗ
            (Coalgebra.comul (R := R) (A := C)).rTensor C) ∘ₗ
            Coalgebra.comul (R := R) (A := C) := by
              rw [omegaR, LinearMap.rTensor, ← LinearMap.map_comp_rTensor]
    _ = TensorProduct.map (LinearMap.id : C →ₗ[R] C)
          (TensorProduct.map S.colorProjector (LinearMap.id : C →ₗ[R] C)) ∘ₗ
          TensorProduct.assoc R C C C ∘ₗ
          (Coalgebra.comul (R := R) (A := C)).rTensor C ∘ₗ
          Coalgebra.comul (R := R) (A := C) := by
            rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
              (TensorProduct.map_map_comp_assoc_eq
                (LinearMap.id : C →ₗ[R] C) S.colorProjector (LinearMap.id : C →ₗ[R] C)).symm]
            simp [LinearMap.comp_assoc]
    _ = TensorProduct.map (LinearMap.id : C →ₗ[R] C)
          (TensorProduct.map S.colorProjector (LinearMap.id : C →ₗ[R] C)) ∘ₗ
          (Coalgebra.comul (R := R) (A := C)).lTensor C ∘ₗ
          Coalgebra.comul (R := R) (A := C) := by
            rw [Coalgebra.coassoc (R := R) (A := C)]
    _ = TensorProduct.map (LinearMap.id : C →ₗ[R] C)
          ((TensorProduct.map S.colorProjector (LinearMap.id : C →ₗ[R] C)).comp
            (Coalgebra.comul (R := R) (A := C))) ∘ₗ
          Coalgebra.comul (R := R) (A := C) := by
            rw [← LinearMap.comp_assoc, LinearMap.map_comp_lTensor]
    _ = S.omegaL.lTensor C ∘ₗ Coalgebra.comul (R := R) (A := C) := by
            simp [omegaL, LinearMap.lTensor]

/-- The inclusion `incl : C[G] → C` is injective because `δ` is a left inverse. -/
lemma incl_injective (S : ColoredCoalgebra (R := R) (C := C) (G := G)) :
    Function.Injective S.incl := by
  intro x y hxy
  have h := congrArg S.δ hxy
  simpa [δ_incl_apply] using h

/-! The basis color element in `C[G]` is set-like. -/
lemma isGroupLikeElem_single_one (g : G) :
    IsGroupLikeElem R (Finsupp.single g (1 : R) : SetLikeCoalgebra R G) where
  counit_eq_one := by
    simp [Finsupp.counit_single]
  comul_eq_tmul_self := by
    simp [Finsupp.comul_single]

/--
Each canonical color element `colorElem g` is set-like in `C`.

Paper reference: colors are chosen set-like elements.
-/
lemma colorElem_isGroupLike (S : ColoredCoalgebra (R := R) (C := C) (G := G)) (g : G) :
    IsGroupLikeElem R (S.colorElem g) :=
  (isGroupLikeElem_single_one (R := R) (G := G) g).map S.incl

end ColoredCoalgebra
end

section

variable (R : Type u) (C : Type v) (G : Type v)
variable [CommRing R] [AddCommGroup C] [Module R C] [Coalgebra R C]

namespace ColoredCoalgebra

/--
Reduced comultiplication in the paper notation:
`\bar Δ = (id - δ₀ ⊗ id - id ⊗ δ₀) ∘ Δ = Δ - ω_r - ω_l`.

Paper reference: definition "The reduced decomposition associated to the retraction `δ`"
in the subsubsection "Reduced comultiplication".
-/
def barComul (S : ColoredCoalgebra (R := R) (C := C) (G := G)) :
    C →ₗ[R] TensorProduct R C C :=
  Coalgebra.comul (R := R) (A := C) - S.omegaR - S.omegaL

@[simp] lemma barComul_apply (S : ColoredCoalgebra (R := R) (C := C) (G := G)) (x : C) :
    barComul (R := R) (C := C) (G := G) S x =
      Coalgebra.comul (R := R) (A := C) x - S.omegaR x - S.omegaL x := rfl

/--
Equivalent "factorized" expression of `barComul`:
`((id ⊗ id) - (δ₀ ⊗ id) - (id ⊗ δ₀)) ∘ Δ`.

This is the expanded linear-map form used for term-by-term cancellations in the
reduced-coassociativity proof strategy.
-/
lemma barComul_eq_id_sub (S : ColoredCoalgebra (R := R) (C := C) (G := G)) :
    barComul (R := R) (C := C) (G := G) S =
      (TensorProduct.map (LinearMap.id : C →ₗ[R] C) (LinearMap.id : C →ₗ[R] C) -
        TensorProduct.map S.colorProjector (LinearMap.id : C →ₗ[R] C) -
        TensorProduct.map (LinearMap.id : C →ₗ[R] C) S.colorProjector) ∘ₗ
          Coalgebra.comul (R := R) (A := C) := by
  ext x
  simp [barComul, omegaL, omegaR]
  abel

/--
Remaining `ω`-cancellation identities used in the reduced-coassociativity expansion.

Paper reference: these are the companion cancellation relations in the
"Reduced comultiplication" computation around Theorem `\label{1}`.

We package them explicitly to keep assumptions visible and avoid silently adding hypotheses.
-/
structure OmegaCompatibility
    (S : ColoredCoalgebra (R := R) (C := C) (G := G)) : Prop where
  assoc_comp_omegaL_rTensor_comp_comul :
    TensorProduct.assoc R C C C ∘ₗ S.omegaL.rTensor C ∘ₗ Coalgebra.comul (R := R) (A := C) =
      S.omegaR.lTensor C ∘ₗ Coalgebra.comul (R := R) (A := C)
  assoc_comp_comul_rTensor_comp_omegaR :
    TensorProduct.assoc R C C C ∘ₗ (Coalgebra.comul (R := R) (A := C)).rTensor C ∘ₗ S.omegaR =
      (Coalgebra.comul (R := R) (A := C)).lTensor C ∘ₗ S.omegaR
  assoc_comp_comul_rTensor_comp_omegaL :
    TensorProduct.assoc R C C C ∘ₗ (Coalgebra.comul (R := R) (A := C)).rTensor C ∘ₗ S.omegaL =
      (Coalgebra.comul (R := R) (A := C)).lTensor C ∘ₗ S.omegaL
  assoc_comp_omegaR_rTensor_comp_omegaR :
    TensorProduct.assoc R C C C ∘ₗ S.omegaR.rTensor C ∘ₗ S.omegaR =
      S.omegaR.lTensor C ∘ₗ S.omegaR
  assoc_comp_omegaR_rTensor_comp_omegaL :
    TensorProduct.assoc R C C C ∘ₗ S.omegaR.rTensor C ∘ₗ S.omegaL =
      S.omegaL.lTensor C ∘ₗ S.omegaR
  assoc_comp_omegaL_rTensor_comp_omegaR :
    TensorProduct.assoc R C C C ∘ₗ S.omegaL.rTensor C ∘ₗ S.omegaR =
      S.omegaR.lTensor C ∘ₗ S.omegaL
  assoc_comp_omegaL_rTensor_comp_omegaL :
    TensorProduct.assoc R C C C ∘ₗ S.omegaL.rTensor C ∘ₗ S.omegaL =
      S.omegaL.lTensor C ∘ₗ S.omegaL

/--
Full reduced coassociativity of `barComul`, assuming the complete family of `ω`-compatibility
relations bundled in `OmegaCompatibility`.
-/
lemma barComul_coassoc_of_omegaCompatibility
    (S : ColoredCoalgebra (R := R) (C := C) (G := G))
    (hω : OmegaCompatibility (R := R) (C := C) (G := G) S) :
    TensorProduct.assoc R C C C ∘ₗ (barComul (R := R) (C := C) (G := G) S).rTensor C ∘ₗ
      barComul (R := R) (C := C) (G := G) S =
    (barComul (R := R) (C := C) (G := G) S).lTensor C ∘ₗ
      barComul (R := R) (C := C) (G := G) S := by
  have hcoassoc := Coalgebra.coassoc (R := R) (A := C)
  have hωRΔ := assoc_comp_omegaR_rTensor_comp_comul (R := R) (C := C) (G := G) S
  simp [barComul, LinearMap.rTensor_sub, LinearMap.lTensor_sub,
    LinearMap.comp_sub, LinearMap.sub_comp,
    hcoassoc, hωRΔ,
    hω.assoc_comp_omegaL_rTensor_comp_comul,
    hω.assoc_comp_comul_rTensor_comp_omegaR,
    hω.assoc_comp_comul_rTensor_comp_omegaL,
    hω.assoc_comp_omegaR_rTensor_comp_omegaR,
    hω.assoc_comp_omegaR_rTensor_comp_omegaL,
    hω.assoc_comp_omegaL_rTensor_comp_omegaR,
    hω.assoc_comp_omegaL_rTensor_comp_omegaL]
  abel

/--
Left-bracketed codomain and map for iterates of the reduced comultiplication.

This avoids committing globally to a single tensor-power implementation while keeping
the left-associated iteration order explicit.
-/
structure BarComulIterate
    (S : ColoredCoalgebra (R := R) (C := C) (G := G)) where
  codomain : Type _
  [instAddCommGroup : AddCommGroup codomain]
  [instModule : Module R codomain]
  map : C →ₗ[R] codomain

attribute [instance] BarComulIterate.instAddCommGroup BarComulIterate.instModule

/--
`n`-fold left-bracketed iterate of `barComul`; `n = 0` is `barComul` itself.

Paper reference: this is the formalization of the iterates usually denoted `\bar Δ^N`.
-/
def barComulIterate
    (S : ColoredCoalgebra (R := R) (C := C) (G := G)) (n : ℕ) :
    BarComulIterate (R := R) (C := C) (G := G) S :=
  Nat.rec
    ({ codomain := TensorProduct R C C,
       map := barComul (R := R) (C := C) (G := G) S } :
        BarComulIterate (R := R) (C := C) (G := G) S)
    (fun _ I =>
      { codomain := TensorProduct R I.codomain C,
        map := I.map.rTensor C ∘ₗ barComul (R := R) (C := C) (G := G) S })
    n

/--
Conilpotence on `ker δ` using iterated reduced comultiplication.

Paper reference: this matches the conilpotence condition `\bar Δ^N(x)=0` for `x ∈ ker(δ)`.
-/
def IsConilpotentOnKer
    (S : ColoredCoalgebra (R := R) (C := C) (G := G)) : Prop :=
  ∀ x : C, S.δ x = 0 →
    ∃ n : ℕ,
      (barComulIterate (R := R) (C := C) (G := G) S n).map x =
        (0 : (barComulIterate (R := R) (C := C) (G := G) S n).codomain)

/--
A simply colored coalgebra with explicit `ω`-compatibility package and conilpotence on `ker δ`.
-/
structure SimplyColoredCoalgebra extends ColoredCoalgebra (R := R) (C := C) (G := G) where
  omegaCompatibility : OmegaCompatibility (R := R) (C := C) (G := G) toColoredCoalgebra
  conilpotent_onKer : IsConilpotentOnKer (R := R) (C := C) (G := G) toColoredCoalgebra

/--
Reduced coassociativity for a simply colored coalgebra.
-/
lemma barComul_coassoc
    (S : SimplyColoredCoalgebra (R := R) (C := C) (G := G)) :
    TensorProduct.assoc R C C C ∘ₗ
        (barComul (R := R) (C := C) (G := G) S.toColoredCoalgebra).rTensor C ∘ₗ
        barComul (R := R) (C := C) (G := G) S.toColoredCoalgebra =
      (barComul (R := R) (C := C) (G := G) S.toColoredCoalgebra).lTensor C ∘ₗ
        barComul (R := R) (C := C) (G := G) S.toColoredCoalgebra :=
  barComul_coassoc_of_omegaCompatibility (R := R) (C := C) (G := G)
    S.toColoredCoalgebra S.omegaCompatibility

end ColoredCoalgebra
end

end ColoredComonoid
end LeanColoredCoalgebras
