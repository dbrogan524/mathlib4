module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.CategoryTheory.Filtration.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.TensorProduct.Finite


#check Module.ext


/-!
# Definition and basic theorems about Hodge structures
-/





universe u v w




open scoped TensorProduct

/- I can't decide if I want to start with V : ModuleCat R and go from there,
or instead start with an assumption Module R V-/
/-
noncomputable section Complexification

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

def extend_iso {R : Type*} [CommRing R]
  (V : Type*) [AddCommGroup V] [Module R V]
  (S : Type u) [CommRing S] [Algebra R S]
  (T : Type u) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T] :
    extend (R := S) (extend (R := R) V S) T ≃ₗ[T] extend (R := R) V T :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T V

#check extend_iso ℤ ℚ ℝ

end Complexification
-/

noncomputable section Conjugation

variable {A : Type*} [CommRing A] [Algebra A ℝ]
variable {V : Type*} [AddCommGroup V] [Module A V]

/-- Real linear conjugation map -/
def realConjMap : ℂ ⊗[A] V ≃ₗ[ℝ] ℂ ⊗[A] V :=
  TensorProduct.AlgebraTensorModule.congr
    Complex.conjAe.toLinearEquiv (LinearEquiv.refl A V)

/-- complex semilinear conjugation map -/
def conjMap : ℂ ⊗[A] V ≃ₗ⋆[ℂ] ℂ ⊗[A] V where
  __ := (realConjMap).toAddEquiv
  map_smul' c x := by
    induction x using TensorProduct.inductionOn with
    | tmul z v =>
      simp [realConjMap, TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => simp_all [smul_add]



end Conjugation




section PureHodgeStructures
-- We start with integral, rational, and real Hodge structures

/- Christian suggested defining complex Hodge structures using two filtrations F and Fbar
which together satisfy the isCompl condition for the correct indices. Maybe this is a better
starting place, and maybe I can infer that Fbar is the conjugate of F when I start with a module
over ℤ, ℚ, or ℝ. -/

/-- A Hodge filtration `F` of wieght `n` is a bounded decreasing filtration such that
`F p` and `F q` are conjugate-complementary if `p + q = n + 1`. -/
class IsPureHodgeFiltration
  (A : Type*) [CommRing A] [Algebra A ℝ] [FaithfulSMul A ℝ]
  (V : Type*) [AddCommGroup V] [Module A V] [IsNoetherian A V]
  (F : ℤ → Submodule ℂ (ℂ ⊗[A] V)) (n : ℤ) : Prop where
    decreasing : Antitone F
    bounded_below : ∃ (p : ℤ), F p = ⊥
    bounded_above : ∃ (p : ℤ), F p = ⊤
    is_compl : ∀ (p : ℤ),
      IsCompl (F p) (((F (n + 1 - p))).map (conjMap).toLinearMap)

/-- An R-Hodge structure is an A-module `V` together with a filtration `filt` satisfying
  `IsPureHodgeFiltration A V filt n` for some natural number `n`. -/
class PureHodgeStructure
  (A : Type*) [CommRing A] [Algebra A ℝ] [FaithfulSMul A ℝ]
  (V : Type*) [AddCommGroup V] [Module A V] [IsNoetherian A V] where
    weight : ℤ
    filt : ℤ → Submodule ℂ (ℂ ⊗[A] V)
    isHodge: IsPureHodgeFiltration A V filt weight


end PureHodgeStructures


section Maps

variable {A : Type*} [CommRing A] [Algebra A ℝ] [FaithfulSMul A ℝ]
variable {V : Type*} [AddCommGroup V] [Module A V] [IsNoetherian A V]

/-- Maps of pure hodge structures are just maps of the filtered modules -/
class PureHodgeMap [H : PureHodgeStructure A V]
  {W : Type*} [AddCommGroup W] [Module A W] [IsNoetherian A W]
  [K : PureHodgeStructure A W] where
    toFun : V →ₗ[A] W
    strict : Prop := ∀ p : ℤ, (H.filt p).map (toFun.baseChange ℂ) ≤ K.filt p

/-- The graded piece `(F p) ⧸ (F (p + 1))` -/
abbrev PureHodgeStructure.GradedPiece (H : PureHodgeStructure A V) :=
    fun (p : ℤ) ↦ (H.filt p) ⧸ (H.filt (p + 1)).submoduleOf (H.filt p)

/-- The subspace H^{p,n-p} -/
noncomputable abbrev PureHodgeStructure.HodgePiece (H : PureHodgeStructure A V) :=
    fun (p : ℤ) ↦ (H.filt p) ⊓ (((H.filt (H.weight - p))).map (conjMap).toLinearMap)



end Maps

section HodgeDecomposition

open scoped DirectSum

variable {A : Type*} [CommRing A] [Algebra A ℝ] [FaithfulSMul A ℝ]
variable {V : Type*} [AddCommGroup V] [Module A V] [IsNoetherian A V]
variable (H : PureHodgeStructure A V)

--theorem GradedPiece_iso_HodgePiece : ∀ (p : ℤ), H.GradedPiece p ≃ₗ[ℂ] H.HodgePiece p := sorry


-- Chat generated this. Rewrite more cleanly. Or write a different lemma that would be useful.
lemma Hodge_decomp_finite :
    Module.Finite ℂ (⨁ (p : ℤ), H.HodgePiece p) := by
  -- Noetherian implies finitely generated; base change preserves this.
  have : Module.Finite ℂ (ℂ ⊗[A] V) := inferInstance
  -- Subspaces of a finite-dimensional vector space are finite dimensional.
  have (p : ℤ) : Module.Finite ℂ (H.HodgePiece p) := inferInstance
  obtain ⟨b, hb⟩ := H.isHodge.bounded_below
  have hF (p : ℤ) (hp : b ≤ p) : H.filt p = ⊥ := by
    apply bot_unique
    simpa only [hb] using H.isHodge.decreasing hp
  let s := Finset.Ioo (H.weight - b) b
  have hzero (p : ℤ) (hp : p ∉ s) : H.HodgePiece p = ⊥ := by
    by_cases hbp : b ≤ p
    · simp [PureHodgeStructure.HodgePiece, hF p hbp]
    · have hpb : b ≤ H.weight - p := by
        simp only [s, Finset.mem_Ioo] at hp
        omega
      simp [PureHodgeStructure.HodgePiece, hF _ hpb]
  -- Extension by zero from the finite product is surjective.
  apply Module.Finite.of_surjective
    (DFinsupp.lmk (R := ℂ) (M := fun p ↦ ↥(H.HodgePiece p)) s)
  intro x
  refine ⟨fun p ↦ x p, ?_⟩
  apply DFinsupp.ext
  intro p
  change (if p ∈ s then x p else 0) = x p
  split_ifs with hp
  · rfl
  · have : Subsingleton (H.HodgePiece p) := by
      rw [hzero p hp]
      infer_instance
    exact Subsingleton.elim _ _

lemma hodge_piece_inf_eq_bot {p q : ℤ} : p ≠ q →  (H.HodgePiece p) ⊓ (H.HodgePiece q) = ⊥ := by
  intro hp
  wlog! h : q < p generalizing p q
  · have h' : p < q := lt_of_le_of_ne h hp
    rw [inf_comm]
    exact this hp.symm h'
  rw [PureHodgeStructure.HodgePiece, PureHodgeStructure.HodgePiece]
  have h' : q + 1 ≤ p := by omega
  rw [← le_bot_iff]
  calc
    (H.filt p ⊓ (H.filt (H.weight - p)).map conjMap.toLinearMap) ⊓
        (H.filt q ⊓ (H.filt (H.weight - q)).map conjMap.toLinearMap) ≤
        H.filt p ⊓ (H.filt (H.weight - q)).map conjMap.toLinearMap :=
      inf_le_inf inf_le_left inf_le_right
    _ ≤ H.filt (q + 1) ⊓ (H.filt (H.weight - q)).map conjMap.toLinearMap :=
      inf_le_inf_right _ (H.isHodge.decreasing h')
    _ = ⊥ := by
      simpa using (H.isHodge.is_compl (q + 1)).inf_eq_bot



#check DirectSum.coeLinearMap_of
#check DirectSum.IsInternal
#check DirectSum.isInternal_biSup_submodule_of_iSupIndep
#check DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
#check DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
#check sSupIndep
#check iSupIndep_map_orderIso_iff
#check iSupIndep.linearEquiv
#check Pairwise
#check Function.onFun
#check Submodule.completeLattice
#check Order.Frame
#check Subtype.restrict
#check LinearMap.range_eq_map
#check Submodule.map
#check DirectSum.setToSet
#check Set.univ
#check DirectSum.lsetToSet
#check Set.Iic
#check DirectSum.of
#check DirectSum.unique
#check DirectSum.component
#check DirectSum.map


noncomputable def invDecompMap : (⨁ (p : ℤ), H.HodgePiece p) →ₗ[ℂ] ℂ ⊗[A] V :=
  DirectSum.coeLinearMap H.HodgePiece

def inc (p : ℤ) : Set.Iic p → ℤ := fun p ↦ p

def inc' (p : ℤ) : (⨁ (r : Set.Iic p), H.HodgePiece r) →ₗ[ℂ] (⨁ (p : ℤ), H.HodgePiece p) := by
  intro i
  --DirectSum.setToSet H.HodgePiece (Set.Iic p) (Set.univ) (Set.subset_univ _)

theorem test : ∀ (p : ℤ), (invDecompMap H)'' (⨁ (r : Set.Iic p), H.HodgePiece r) = H.filt p := by




/-
lemma invDecompMap_equiv : (⨁ (p : ℤ), H.HodgePiece p) ≃ₗ[ℂ] ℂ ⊗[A] V := by
  have : Pairwise (Function.onFun Disjoint H.HodgePiece) :=
    fun ?_ ?_ hpq ↦ disjoint_iff.mpr (hodge_piece_inf_eq_bot H hpq)
  apply iSupIndep.linearEquiv
  have : iSupIndep H.HodgePiece := iSupIndep_iff_pairwiseDisjoint.2 this



noncomputable def PureHodgeStructure.decomp : ℂ ⊗[A] V ≃ₗ[ℂ] ⨁ (p : ℤ), H.HodgePiece p := by
  apply (iSupIndep.linearEquiv ?_ ?_).symm
  change iSupIndep H.HodgePiece
  · rw[iSupIndep_iff_pairwiseDisjoint]
-/



#check DirectSum.coeLinearMap

end HodgeDecomposition


section Examples



def TrivialFilt {A : Type*} [CommRing A] [Algebra A ℝ] [FaithfulSMul A ℝ]
  (V : Type*) [AddCommGroup V] [Module A V] : ℤ → Submodule ℂ (ℂ ⊗[A] V) :=
    fun (n : ℤ) ↦ if n > 0 then ⊥ else ⊤

lemma TrivialFiltIsHodge {A : Type*} [CommRing A] [Algebra A ℝ] [FaithfulSMul A ℝ]
  (V : Type*) [AddCommGroup V] [Module A V] [IsNoetherian A V]
  : IsPureHodgeFiltration A V (TrivialFilt V) 0 := by
    constructor
    · intro p q hpq
      by_cases hp : p ≤ 0
      · rw[show TrivialFilt V p = ⊤ by simp[TrivialFilt, hp]]
        exact le_top
      · have : q > 0 := by omega
        simp [TrivialFilt, this]
    · use 1; simp [TrivialFilt]
    · use 0; simp [TrivialFilt]
    · intro p
      simp
      by_cases hp : p > 0
      · have : ¬p < 1 := by omega
        simp [TrivialFilt, hp, this]
        constructor <;> simp
      · have : p < 1 := by omega
        simp [TrivialFilt, hp, this]
        constructor <;> simp

/-- The trivial Hodge structure of weight 0 on an `A` module `V`. -/
instance TrivialHodgeStructure (A : Type*) [CommRing A] [Algebra A ℝ] [FaithfulSMul A ℝ]
  (V : Type*) [AddCommGroup V] [Module A V] [IsNoetherian A V] : PureHodgeStructure A V where
  weight := 0
  filt := TrivialFilt V
  isHodge := TrivialFiltIsHodge V


/-- The Tate twise of a pure Hodge Structure `H` by an integer `r` is a Hodge structure
on the same underlying module of H, with a shifted filtration and weight -/
abbrev PureHodgeStructure.Twist {A : Type*} [CommRing A] [Algebra A ℝ] [FaithfulSMul A ℝ]
  {V : Type*} [AddCommGroup V] [Module A V] [IsNoetherian A V]
  (H : PureHodgeStructure A V) (r : ℤ) : PureHodgeStructure A V where
  weight := H.weight - 2 * r
  filt := fun p ↦ H.filt (p + r)
  isHodge := by
    constructor
    · intro i j hij
      have : i + r ≤ j + r := by omega
      exact H.isHodge.decreasing this
    · obtain ⟨p, hp⟩ := H.isHodge.bounded_below
      use p - r; simpa
    · obtain ⟨p, hp⟩ := H.isHodge.bounded_above
      use p - r; simpa
    · intro p
      rw[show H.weight - 2 * r + 1 - p + r = H.weight + 1 - (p + r) by omega]
      exact H.isHodge.is_compl (p + r)






end Examples







#min_imports
