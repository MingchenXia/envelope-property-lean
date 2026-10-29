import EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsFamily
import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingOriginal
import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingLabels
import Mathlib.Data.List.OfFn

/-! # The actual whole original auxiliary family as its genuine finite raw list

The SAME original row/copy indices order the actual original line, degree and
inclusion section. Every original branch ideal is proved on the SAME list;
no section, root or original cyclic factor is replaced by a certificate.
-/

open AlgebraicGeometry CategoryTheory Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalNormalization.OriginalData
open CanonicalGeometry NadelAuxiliaryMulticover NadelAuxiliaryBranchSectionsData
open NadelAuxiliaryBranchSectionsFamily NadelAdaptedChartMatching
variable {X : Scheme.{u}} (F : X.DivisorFamily) (n : ℕ) (L : F.ι → X.Modules) (m : F.ι → ℕ)
  (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶ tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))

/-- Each SAME original section defines its genuine original global cyclic datum. -/
def member (ij : Joined.Index F n) : AuxiliarySection X :=
  auxiliarySection (L ij.1) (m ij.1) (F.component ij.1) (σ ij.1 ij.2)

/-- The actual finite list for the WHOLE original fibre-product multicover. -/
def data : List (AuxiliarySection X) :=
  List.ofFn (fun j => member F n L m σ ((Joined.ordering F n).symm j))

/-- The actual whole list retains exactly ALL original row/copy positions. -/
theorem length_data : (data F n L m σ).length = Fintype.card (Joined.Index F n) := List.length_ofFn

/-- The SAME original pair at every actual native raw-list position. -/
def position (i : Fin (data F n L m σ).length) : Joined.Index F n :=
  (Joined.ordering F n).symm (Fin.cast (length_data F n L m σ) i)

/-- Every original whole raw-list datum is literally its SAME original
line, degree and inclusion section; no cyclic factor is replaced. -/
theorem get_data (i : Fin (data F n L m σ).length) :
    (data F n L m σ).get i = member F n L m σ (position F n L m σ i) := by
  exact List.get_ofFn _ i

/-- Every actual list factor retains the SAME original line. -/
theorem get_line (i : Fin (data F n L m σ).length) :
    ((data F n L m σ).get i).line = L (position F n L m σ i).1 := by rw [get_data]; rfl

/-- Every actual list factor retains the SAME original root degree. -/
theorem get_degree (i : Fin (data F n L m σ).length) :
    ((data F n L m σ).get i).degree = m (position F n L m σ i).1 := by rw [get_data]; rfl

variable (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)

include hL in
/-- Genuine original line invertibility is retained at EVERY native list position. -/
theorem get_isInvertible (i : Fin (data F n L m σ).length) :
    IsInvertible ((data F n L m σ).get i).line := by rw [get_line]; exact hL _

/-- The actual original auxiliary divisor at the SAME original row/copy index. -/
abbrev ideals (i : F.ι) (j : Fin (n + 1)) : X.IdealSheafData :=
  sectionIdeal (L i) (hL i) (m i) (F.component i) (hD i) (σ i j)

/-- The SAME original branch label in the genuinely joined original family. -/
def branchIndex (i : Fin (data F n L m σ).length) :
    (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (ideals F n L m σ hL hD)).ι :=
  NadelAuxiliaryBranchSectionsSnc.originalIndex F n (ideals F n L m σ hL hD) (position F n L m σ i).1

/-- The SAME original auxiliary divisor label, retaining EVERY original copy. -/
def auxiliaryIndex (i : Fin (data F n L m σ).length) :
    (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (ideals F n L m σ hL hD)).ι :=
  NadelAuxiliaryBranchSectionsSnc.auxiliaryIndex F n (ideals F n L m σ hL hD)
    (position F n L m σ i).1 (position F n L m σ i).2

private abbrev branchIdeal (E : AuxiliarySection X) (hE : IsInvertible E.line) : X.IdealSheafData :=
  LineSectionZeroIdeal.zeroIdeal (bundleTensorPower E.line E.degree)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hE E.degree) E.sectionHom

private theorem branchIdeal_congr (E E' : AuxiliarySection X) (h : E = E')
    (hE : IsInvertible E.line) (hE' : IsInvertible E'.line) : branchIdeal E hE = branchIdeal E' hE' := by
  cases h
  rfl

/-- The WHOLE original branch ideal at each SAME raw-list position is the
product of the SAME original D_i and actual original auxiliary section ideal. -/
theorem get_branch (i : Fin (data F n L m σ).length) :
    LineSectionZeroIdeal.zeroIdeal
      (bundleTensorPower ((data F n L m σ).get i).line ((data F n L m σ).get i).degree)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible (get_isInvertible F n L m σ hL i)
        ((data F n L m σ).get i).degree) ((data F n L m σ).get i).sectionHom =
      F.component (position F n L m σ i).1 * ideals F n L m σ hL hD
        (position F n L m σ i).1 (position F n L m σ i).2 := by
  exact (branchIdeal_congr ((data F n L m σ).get i) (member F n L m σ (position F n L m σ i))
      (get_data F n L m σ i) (get_isInvertible F n L m σ hL i) (hL _)).trans
    (auxiliarySection_branch (L (position F n L m σ i).1) (hL _) (m (position F n L m σ i).1)
      (F.component (position F n L m σ i).1) (hD _) (σ _ (position F n L m σ i).2))


/-- The WHOLE same original raw branch ideal has the true original joined
SNC-family labels, internally proved from its actual original section. -/
theorem get_joined_branch (i : Fin (data F n L m σ).length) :
    LineSectionZeroIdeal.zeroIdeal
      (bundleTensorPower ((data F n L m σ).get i).line ((data F n L m σ).get i).degree)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible (get_isInvertible F n L m σ hL i)
        ((data F n L m σ).get i).degree) ((data F n L m σ).get i).sectionHom =
      (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (ideals F n L m σ hL hD)).component
        (branchIndex F n L m σ hL hD i) *
      (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (ideals F n L m σ hL hD)).component
        (auxiliaryIndex F n L m σ hL hD i) := by
  simpa only [branchIndex, auxiliaryIndex, NadelAuxiliaryBranchSectionsSnc.component_originalIndex,
    NadelAuxiliaryBranchSectionsSnc.component_auxiliaryIndex] using get_branch F n L m σ hL hD i

end EnvelopeProperty.Vanishing.NadelGlobalNormalization.OriginalData
