module

import Mathlib



#check Module.ext


/-!
# Definition and basic theorems about Hodge structures
-/



universe u v

-- We will start with integral, rational, and real Hodge structures
variable (R : Type*) [CommRing R] [Algebra R ℝ] [FaithfulSMul R ℝ]
variable (V : Type*) [AddCommGroup V] [Module R V]

#check (algebraMap R ℂ : R →+* ℂ)

open scoped TensorProduct
open scoped ComplexConjugate
#check TensorProduct

-- Decreasing Hodge filtration
variable (F : CategoryTheory.Filtration (ModuleCat.of ℂ (ℂ ⊗[R] V)) ℤᵒᵈ)

-- Increasing weight filtration
variable (W : CategoryTheory.Filtration (ModuleCat.of R V) ℤ)


namespace Complexification

open scoped TensorProduct
-- First we need to construct a conjugation map on the complexification of V
-- Notation for the "realification" of A
scoped notation: max A:max "[ℝ]" => ℝ ⊗[R] A
-- Notation for the "complexification" of A
scoped notation: max A:max "[ℂ]" => ℂ ⊗[R] A

end Complexification

open scoped Complexification



-- This is a bunch of stuff for complexification and conjugation maps

noncomputable def complexificationEquiv : ℂ ⊗[ℝ] (ℝ ⊗[R] V) ≃ₗ[ℂ] ℂ ⊗[R] V :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R ℝ ℂ ℂ V)

noncomputable def conjugate : ℂ ⊗[R] V →ₗ[ℝ] ℂ ⊗[R] V :=
  let e := (complexificationEquiv R V).restrictScalars ℝ
  let c := TensorProduct.congr Complex.conjAe.toLinearEquiv (LinearEquiv.refl ℝ (ℝ ⊗[R] V))
  ((e.symm.trans c).trans e).toLinearMap

@[simp]
theorem conjugate_tmul (z : ℂ) (v : V) :
    conjugate R V (z ⊗ₜ[R] v) = conj z ⊗ₜ[R] v := by
  simp [conjugate, complexificationEquiv]

noncomputable def conjugateSemilinear :
    ℂ ⊗[R] V →ₗ⋆[ℂ] ℂ ⊗[R] V where
  toFun := conjugate R V
  map_add' := map_add (conjugate R V)
  map_smul' z x := by
    induction x using TensorProduct.inductionOn with
    | tmul w v =>
      simp [TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy =>
      simp [smul_add, hx, hy]


/-- A Hodge filtration F of wieght n is a decreasing filtration such that complementary pieces
of F are conjugate-complementary in ℂ ⊗[R] V. -/
class IsHodgeFiltration (n : ℕ) : Prop where
  isMin : ∀ (p q : ℤ), p + q = n+1
    → IsCompl (F.ι.app (OrderDual.toDual p)).hom.range
      ((F.ι.app (OrderDual.toDual q)).hom.range.map (conjugateSemilinear R V))


class RealMixedHodgeStructure where
