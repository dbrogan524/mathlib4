module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.CategoryTheory.Filtration.Basic


#check Module.ext


/-!
# Definition and basic theorems about Hodge structures
-/





universe u v w

open scoped TensorProduct

/- I can't decide if I want to start with V : ModuleCat R and go from there,
or instead start with an assumption Module R V-/

section Complexification

/- First we need to construct a conjugation map on the complexification of V. To do this we
make some simplified notation for extension of scalars -/

public abbrev extend {R : Type*} [CommRing R] (V : Type*) [AddCommGroup V] [Module R V]
  (S : Type*) [CommRing S] [Algebra R S] := (S ⊗[R] V)

-- Notation for the entension of scalars.
notation:max V:max "[" S "]" => extend V S

variable (V: Type) [AddCommGroup V]
#check V[ℚ]
#check V[ℝ]
#check V[ℂ]

noncomputable def extend_iso {R : Type*} [CommRing R]
  (V : Type*) [AddCommGroup V] [Module R V]
  (S : Type u) [CommRing S] [Algebra R S]
  (T : Type u) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T] :
    extend (R := S) (extend (R := R) V S) T ≃ₗ[T] extend (R := R) V T :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T V

#check extend_iso ℤ ℚ ℝ

end Complexification


section Conjugation

variable {R : Type*} [CommRing R] [Algebra R ℝ]
variable (V : Type*) [AddCommGroup V] [Module R V]

noncomputable def conjMap : ℂ ⊗[R] V →ₗ[ℝ] ℂ ⊗[R] V :=
  TensorProduct.AlgebraTensorModule.rTensor R V Complex.conjAe.toLinearMap


end Conjugation


section PureHodgeStructures
-- We will start with integral, rational, and real Hodge structures
variable (R : Type u) [CommRing R] [Algebra R ℝ] [FaithfulSMul R ℝ]
variable (V : Type*) [AddCommGroup V] [Module R V]

#check (algebraMap R ℂ : R →+* ℂ)

-- Decreasing Hodge filtration
variable (F : ℤ → Submodule ℂ (ℂ ⊗[R] V)) {hF : Antitone F}

-- Increasing weight filtration
variable (W : ℤ → Submodule ℂ (ℂ ⊗[R] V)) {hW : Monotone W}


/-- A Hodge filtration F of wieght n is a decreasing filtration such that complementary pieces
of F are conjugate-complementary in V[ℂ]. -/
class IsHodgeFiltration (n : ℕ) : Prop where
    isCompl : ∀ (p : ℤ),
    IsCompl ((F p).restrictScalars ℝ)
      (((F (n + 1 - p)).restrictScalars ℝ).map (conjMap V))



noncomputable def FTriv : ℤ → Submodule ℂ (ℂ ⊗[ℝ] ℝ) := fun (n : ℤ) ↦ if n > 0 then ⊥ else ⊤


--class RealMixedHodgeStructure where
end PureHodgeStructures



theorem test : IsHodgeFiltration ℝ ℝ FTriv 0 := by
  constructor
  intro p
  simp
  wlog h : 0 < p with test
  · have : 1 - p > 0 := by omega
    specialize test (1 - p) this
    rw[show 1 - (1 - p) = p by omega] at test
    apply IsCompl.symm
    apply test
  · have : ¬p < 1 := by omega
    simp [FTriv, h, this]
    constructor <;> simp
    rw[LinearMap.range_eq_top_of_surjective]
    apply?






#min_imports
