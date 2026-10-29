import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechTotalAugmentation
import ModularCurves.ForMathlib.TotalComplexUpNatDecomposition
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Čech Degree One Descent

+# Degree-one descent into the original sheaf Čech total

The vertical differential is the ordinary Čech differential.  We use
`δ ξ = d h`, so the degree-one component is `(ξ, h)`.  A family written with
`ξᵢ - ξⱼ = d Hᵢⱼ` is inserted by taking `h = -H`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace EnvelopeProperty.DI.CechDegreeOneDescent

universe v u

section Bicomplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (B : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) [B.HasTotal (.up ℕ)]
variable {M : C}

/-- The two original degree-one components, with the native total signs. -/
def degreeOneComponent (ξ : M ⟶ (B.X 1).X 0) (h : M ⟶ (B.X 0).X 1) :
    M ⟶ (B.total (.up ℕ)).X 1 :=
  ξ ≫ B.ιTotal (.up ℕ) 1 0 1 rfl + h ≫ B.ιTotal (.up ℕ) 0 1 1 rfl

/-- The local differential, pair difference and triple cocycle close the total cochain. -/
theorem degreeOneComponent_closed
    (ξ : M ⟶ (B.X 1).X 0) (h : M ⟶ (B.X 0).X 1)
    (hξ : ξ ≫ (B.d 1 2).f 0 = 0)
    (hpair : h ≫ (B.d 0 1).f 1 = ξ ≫ (B.X 1).d 0 1)
    (htriple : h ≫ (B.X 0).d 1 2 = 0) :
    degreeOneComponent B ξ h ≫ (B.total (.up ℕ)).d 1 2 = 0 := by
  simp only [degreeOneComponent, add_comp, Category.assoc]
  rw [B.ιTotal_d_upNat 1 0, B.ιTotal_d_upNat 0 1]
  simp only [pow_one, pow_zero, one_smul, comp_add]
  simp only [← Category.assoc, hξ, htriple, zero_comp, zero_add, add_zero]
  rw [hpair]
  simp

/-- A genuine morphism from the complex concentrated in degree one. -/
def degreeOneMap [HasZeroObject C]
    (ξ : M ⟶ (B.X 1).X 0) (h : M ⟶ (B.X 0).X 1)
    (hξ : ξ ≫ (B.d 1 2).f 0 = 0)
    (hpair : h ≫ (B.d 0 1).f 1 = ξ ≫ (B.X 1).d 0 1)
    (htriple : h ≫ (B.X 0).d 1 2 = 0) :
    (HomologicalComplex.single C (.up ℕ) 1).obj M ⟶ B.total (.up ℕ) :=
  HomologicalComplex.mkHomFromSingle (degreeOneComponent B ξ h) (by
    intro k hk
    have hk' : k = 2 := by simpa using hk.symm
    subst k
    exact degreeOneComponent_closed B ξ h hξ hpair htriple)

@[reassoc (attr := simp)]
theorem degreeOneComponent_π_one_zero
    (ξ : M ⟶ (B.X 1).X 0) (h : M ⟶ (B.X 0).X 1) :
    degreeOneComponent B ξ h ≫ B.πTotalUpNat 1 0 1 = ξ := by
  simp [degreeOneComponent]

@[reassoc (attr := simp)]
theorem degreeOneComponent_π_zero_one
    (ξ : M ⟶ (B.X 1).X 0) (h : M ⟶ (B.X 0).X 1) :
    degreeOneComponent B ξ h ≫ B.πTotalUpNat 0 1 1 = h := by
  simp [degreeOneComponent]

/-- The first-quadrant total has a genuine projection onto its Čech-zero row. -/
def zeroRowProjection : B.total (.up ℕ) ⟶ B.flip.X 0 where
  f q := B.πTotalUpNat q 0 q
  comm' q q' hq := by
    have hq' : q' = q + 1 := by simpa using hq.symm
    subst q'
    change B.πTotalUpNat q 0 q ≫ (B.d q (q + 1)).f 0 =
      (B.total (.up ℕ)).d q (q + 1) ≫ B.πTotalUpNat (q + 1) 0 (q + 1)
    symm
    simpa using B.total_d_πTotalUpNat q (q + 1) 0 (by omega)

set_option backward.isDefEq.respectTransparency false in
/-- Projection retains exactly the original ξ component as a cochain map. -/
theorem degreeOneMap_zeroRowProjection [HasZeroObject C]
    (ξ : M ⟶ (B.X 1).X 0) (h : M ⟶ (B.X 0).X 1)
    (hξ : ξ ≫ (B.d 1 2).f 0 = 0)
    (hpair : h ≫ (B.d 0 1).f 1 = ξ ≫ (B.X 1).d 0 1)
    (htriple : h ≫ (B.X 0).d 1 2 = 0) :
    degreeOneMap B ξ h hξ hpair htriple ≫ zeroRowProjection B =
      HomologicalComplex.mkHomFromSingle (K := B.flip.X 0) ξ (by
        intro k hk
        have hk' : k = 2 := by simpa using hk.symm
        subst k
        exact hξ) := by
  apply HomologicalComplex.from_single_hom_ext
  dsimp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.mkHomFromSingle_f]
  change (degreeOneMap B ξ h hξ hpair htriple).f 1 ≫ B.πTotalUpNat 1 0 1 = _
  simp only [degreeOneMap, HomologicalComplex.mkHomFromSingle_f, Category.assoc,
    degreeOneComponent_π_one_zero]

end Bicomplex

end EnvelopeProperty.DI.CechDegreeOneDescent
