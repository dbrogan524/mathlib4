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
variable [H : PureCHodgeStructure V]


lemma HodgePiece_bounded_below : ∃ (p : ℤ), ∀ (r : ℤ), r < p → H.HodgePiece r = ⊥ := by
  obtain ⟨p, hp⟩ := H.isHodge.bounded_below_bar
  use H.weight - p
  intro r hr
  rw[eq_bot_iff]
  calc
    H.HodgePiece r = H.filt r ⊓ H.filtBar (H.weight - r) := by rfl
    _ ≤ H.filtBar (H.weight - r)  := inf_le_right
    _ ≤ H.filtBar p := H.isHodge.decreasing_bar (by omega)
    _ = ⊥ := hp

lemma HodgePiece_bounded_above : ∃ (p : ℤ), ∀ (r : ℤ), r > p → H.HodgePiece r = ⊥ := by
  obtain ⟨p, hp⟩ := H.isHodge.bounded_below
  use p
  intro r hr
  rw[eq_bot_iff]
  calc
    H.HodgePiece r = H.filt r ⊓ H.filtBar (H.weight - r) := by rfl
    _ ≤ H.filt r := inf_le_left
    _ ≤ H.filt p := H.isHodge.decreasing (by omega)
    _ = ⊥ := hp

lemma HodgePiece_inf_filt_eq_bot : ∀ (p : ℤ), (H.HodgePiece p) ⊓ (H.filt (p + 1)) = ⊥ := by
  intro p
  rw[← disjoint_iff]
  apply Disjoint.mono_left (b := H.filtBar (H.weight - p)) inf_le_right
  simpa using (H.isHodge.is_compl (p + 1)).disjoint.symm

lemma HodgePiece_sup_filt_eq_filt : ∀ (p : ℤ), H.HodgePiece p ⊔ (H.filt (p + 1)) = H.filt p := by
  intro p
  calc
    H.HodgePiece p ⊔ (H.filt (p + 1))
      = H.filt p ⊓ H.filtBar (H.weight - p) ⊔ H.filt (p + 1) := by rfl
    _ = H.filt p ⊓ (H.filtBar (H.weight - p) ⊔ H.filt (p + 1)) := by
      rw[inf_sup_assoc_of_le _ (H.isHodge.decreasing (by omega))]
    _ = H.filt p ⊓ (H.filtBar (H.weight + 1 - (p + 1)) ⊔ H.filt (p + 1)) := by simp
    _ = H.filt p ⊓ ⊤ := by rw[(H.isHodge.is_compl (p + 1)).symm.sup_eq_top]
    _ = H.filt p := by rw [inf_top_eq]

-- The goal is to show F p = H^{p,n-p} ⊕ F^{p+1} and then use induction to prove the
-- full Hodge decomposition.
-- noncomputable def partialDecompMap (p : ℤ) : (H.HodgePiece p × H.filt (p + 1)) →ₗ[ℂ] H.filt p :=
--   (Submodule.inclusion (show H.HodgePiece p ≤ H.filt p from inf_le_left)).coprod
--     (Submodule.inclusion (H.isHodge.decreasing (show p ≤ p + 1 by omega)))

noncomputable def partialDecompMap (p : ℤ) : (H.HodgePiece p × H.filt (p + 1)) →ₗ[ℂ] V :=
  (H.HodgePiece p).subtype.coprod (H.filt (p+1)).subtype

open LinearMap Submodule in
lemma injective_partialDecompMap : ∀ (p : ℤ), Function.Injective (partialDecompMap (V := V) p) := by
  intro p
  unfold partialDecompMap
  rw[← ker_eq_bot, ker_coprod_of_disjoint_range, ker_subtype, ker_subtype, prod_bot]
  rw[disjoint_iff, range_subtype, range_subtype]
  exact HodgePiece_inf_filt_eq_bot p

open LinearMap Submodule in
lemma partialDecompMap_range_eq_filt : ∀ (p : ℤ), (partialDecompMap p).range = H.filt p := by
  intro p
  unfold partialDecompMap
  rw[range_coprod, range_subtype, range_subtype]
  exact HodgePiece_sup_filt_eq_filt p

noncomputable def partialHodgeDecomp (p : ℤ) :
  (H.HodgePiece p × H.filt (p + 1)) ≃ₗ[ℂ] H.filt p := by
  rw[← partialDecompMap_range_eq_filt p]
  exact LinearEquiv.ofInjective (partialDecompMap p) (injective_partialDecompMap p)


#check DirectSum.lof
#check Subsingleton
#check Submodule.bot

noncomputable def Hodge_decomp_iso (p : ℤ) :
  (⨁ (q : Set.Ici p), H.HodgePiece q) ≃ₗ[ℂ] H.filt p := by
  let b₀ := Classical.choose (HodgePiece_bounded_above (H := H)) + 1
  have hb₀ (q : ℤ) (hq : b₀ ≤ q) : H.HodgePiece q = ⊥ :=
    Classical.choose_spec (HodgePiece_bounded_above) q (by omega)
  let b := max p b₀
  have hb (q : ℤ) (hq : b ≤ q) : H.HodgePiece q = ⊥ :=
    hb₀ q ((le_max_right p b₀).trans hq)
  have hp : p ≤ b := le_max_left p b₀
  induction p, hp using Int.leInductionDown (m := b) with
  | base =>
    have : (⨁ (q : Set.Ici b), H.HodgePiece q) ≃ₗ[ℂ] H.HodgePiece b := by
      rw[DirectSum.isoOfEq]
    rw[this]
    exact partialHodgeDecomp b
  | pred n hn ih => sorry



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


/-- The Tate twist of a pure Hodge Structure `H` by an integer `r` is a Hodge structure
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
