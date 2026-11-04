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




section HodgeFiltration
-- We start with complex Hodge structures

/-- A Hodge filtration pair `(F, Fbar)` of weight `n` is a bounded decreasing filtration such that
`F p` and `Fbar q` are conjugate-complementary if `p + q = n + 1`. -/
class IsPureHodgeFiltPair
  {V : Type*} [AddCommGroup V] [Module ℂ V] [IsNoetherian ℂ V]
  (filt : ℤ → Submodule ℂ V) (filtBar : ℤ → Submodule ℂ V) (n : ℤ) : Prop where
    decreasing : Antitone filt
    bounded_below : ∃ (p : ℤ), filt p = ⊥
    bounded_above : ∃ (p : ℤ), filt p = ⊤
    decreasing_bar : Antitone filtBar
    bounded_below_bar : ∃ (p : ℤ), filtBar p = ⊥
    bounded_above_bar : ∃ (p : ℤ), filtBar p = ⊤
    is_compl : ∀ (p : ℤ),
      IsCompl (filt p) (filtBar (n + 1 - p))

/-- The class of pure Hodge structures of weight `n` on `V`. A pure complex Hodge structure
is a ℂ-vector space `V` together with two decreasing filtrations `filt` and `filtBar` satisfying
`IsPureHodgeFiltPair V filt filtBar n`. -/
class PureCHodgeStructure
  (V : Type*) [AddCommGroup V] [Module ℂ V] [IsNoetherian ℂ V] where
    weight : ℤ
    filt : ℤ → Submodule ℂ V
    filtBar : ℤ → Submodule ℂ V
    isHodge: IsPureHodgeFiltPair filt filtBar weight


/-- The graded piece `(F p) ⧸ (F (p + 1))` -/
abbrev PureCHodgeStructure.GradedPiece {V : Type*} [AddCommGroup V] [Module ℂ V] [IsNoetherian ℂ V]
  (H : PureCHodgeStructure V) :=
    fun (p : ℤ) ↦ (H.filt p) ⧸ (H.filt (p + 1)).submoduleOf (H.filt p)

/-- The subspace H^{p,n-p} -/
abbrev PureCHodgeStructure.HodgePiece
  {V : Type*} [AddCommGroup V] [Module ℂ V] [IsNoetherian ℂ V] (H : PureCHodgeStructure V) :=
    fun (p : ℤ) ↦ (H.filt p) ⊓ (H.filtBar (H.weight - p))


end HodgeFiltration


section Maps
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [IsNoetherian ℂ V]

/-- Maps of pure hodge structures are just maps of the underlying filtered modules -/
class PureCHodgeMap [H : PureCHodgeStructure V]
  {W : Type*} [AddCommGroup W] [Module ℂ W] [IsNoetherian ℂ W]
  [K : PureCHodgeStructure W] where
    toFun : V →ₗ[ℂ] W
    strict : Prop := ∀ p : ℤ, (H.filt p).map toFun ≤ K.filt p
    strict_bar : Prop := ∀ p : ℤ, (H.filtBar p).map toFun ≤ K.filtBar p




end Maps

section HodgeDecomposition

open scoped DirectSum

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [IsNoetherian ℂ V]
variable (H : PureCHodgeStructure V)

--theorem GradedPiece_iso_HodgePiece : ∀ (p : ℤ), H.GradedPiece p ≃ₗ[ℂ] H.HodgePiece p := sorry


noncomputable def partialDecompMap (p : ℤ) : (H.HodgePiece p × H.filt (p + 1)) →ₗ[ℂ] H.filt p :=
  (Submodule.inclusion (show H.HodgePiece p ≤ H.filt p from inf_le_left)).coprod
    (Submodule.inclusion (H.isHodge.decreasing (show p ≤ p + 1 by omega)))

lemma partialDecompMap_injective : ∀ (p : ℤ), Function.Injective (partialDecompMap H p) := by
  intro p
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, y⟩ hxy
  have hsum : (x : V) + (y : V) = 0 := congrArg Subtype.val hxy
  have hx : (x : V) = 0 := Submodule.disjoint_def.mp (H.isHodge.is_compl p).disjoint x x.property (by
    have heq : (x : V) = -(y : V) := eq_neg_of_add_eq_zero_left hsum
    rw [heq]
    exact (H.filt (p + 1)).neg_mem y.property)
  have hy : (y : V) = 0 := by simpa [hx] using hsum
  exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)



--GPT generated
noncomputable def partialDecompIso (p : ℤ) :
    (H.HodgePiece p × H.filt (p + 1)) ≃ₗ[ℂ] H.filt p := by
  let f : H.HodgePiece p × H.filt (p + 1) →ₗ[ℂ] H.filt p :=
    (Submodule.inclusion
      (show H.HodgePiece p ≤ H.filt p from inf_le_left)).coprod
      (Submodule.inclusion
        (H.isHodge.decreasing (show p ≤ p + 1 by omega)))
  have hcompl : IsCompl (H.filt (p + 1)) (H.filtBar (H.weight - p)) := by
    simpa only [show H.weight + 1 - (p + 1) = H.weight - p by omega] using
      H.isHodge.is_compl (p + 1)
  have hle : H.filt (p + 1) ≤ H.filt p :=
    H.isHodge.decreasing (by omega)
  have hsup : H.HodgePiece p ⊔ H.filt (p + 1) = H.filt p := by
    change H.filt p ⊓ H.filtBar (H.weight - p) ⊔ H.filt (p + 1) = H.filt p
    rw [inf_sup_assoc_of_le _ hle, sup_comm, hcompl.sup_eq_top, inf_top_eq]
  have hdisj : Disjoint (H.HodgePiece p) (H.filt (p + 1)) :=
    hcompl.disjoint.symm.mono_left inf_le_right
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · -- Injectivity: disjointness of the summands forces the kernel to be zero.
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ hxy
    have hsum : (x : V) + (y : V) = 0 := congrArg Subtype.val hxy
    have hx : (x : V) = 0 := Submodule.disjoint_def.mp hdisj x x.property (by
      have heq : (x : V) = -(y : V) := eq_neg_of_add_eq_zero_left hsum
      rw [heq]
      exact (H.filt (p + 1)).neg_mem y.property)
    have hy : (y : V) = 0 := by simpa [hx] using hsum
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  · -- Surjectivity: the supremum equality expresses every element as a sum.
    intro z
    have hz : (z : V) ∈ H.HodgePiece p ⊔ H.filt (p + 1) := by
      rw [hsup]
      exact z.property
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hz
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext hxy⟩



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
#check inf_sup_assoc_of_le
#check eq_sup_of_le


lemma partial_sup : ∀ (p : ℤ), H.HodgePiece p ⊔ (H.filt (p+1)) = H.filt p :=
  inf_sup_assoc_of_le (H.filt p)





lemma partial_Hodge_decomp : ∀ (p : ℤ), H.filt p = (H.HodgePiece p ⊕ H.filt (p+1)) := by





noncomputable def invDecompMap : (⨁ (p : ℤ), H.HodgePiece p) →ₗ[ℂ] ℂ ⊗[A] V :=
  DirectSum.coeLinearMap H.HodgePiece

noncomputable def maptest (p : ℤ) : (⨁ (r : Set.Ici p), H.HodgePiece r) →ₗ[ℂ] ℂ ⊗[A] V :=
  DirectSum.coeLinearMap (fun r : Set.Ici p ↦ H.HodgePiece r)


-- GPT generated
noncomputable def toFiltration (p : ℤ) :
    (⨁ r : Set.Ici p, H.HodgePiece r) →ₗ[ℂ] H.filt p :=
  DirectSum.toModule ℂ _ _ (fun r ↦
    Submodule.inclusion
      (show H.HodgePiece r ≤ H.filt p from
        inf_le_left.trans (H.isHodge.decreasing r.property)))




def inc (p : ℤ) : Set.Ici p → ℤ := fun p ↦ p

def inc' (p : ℤ) : (⨁ (r : Set.Ici p), H.HodgePiece r) →ₗ[ℂ] (⨁ (p : ℤ), H.HodgePiece p) := by
  intro i
  --DirectSum.setToSet H.HodgePiece (Set.Iic p) (Set.univ) (Set.subset_univ _)

theorem test : ∀ (p : ℤ), (invDecompMap H)'' (⨁ (r : Set.Ici p), H.HodgePiece r) = H.filt p := by




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
