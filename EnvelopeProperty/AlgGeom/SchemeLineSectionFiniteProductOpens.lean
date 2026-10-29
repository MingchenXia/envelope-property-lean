import EnvelopeProperty.AlgGeom.SchemeLineSectionProductOpens
import Mathlib.Data.List.OfFn

/-! # Actual finite tuple section products retain original Cech intersections

Every actual finite tuple of original H-power sections has a constructed
actual original product section of the genuine sum power. Its literal
nonzero open is the SAME categorical finite intersection. All degree and
open identifications are proved internally from actual original products.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeLineSectionFiniteProductOpens
open CanonicalGeometry SchemeLineSectionEvaluation SchemeLineSectionUnitFrames
open SchemeModuleCechLineSectionLocalization SchemeLineSectionProductOpens
open SchemeProjectiveSectionOpenBasis
attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev PowerDatum {X : Scheme.{u}} (H : X.Modules) :=
  Σ d : ℕ, unitObj X ⟶ bundleTensorPower H d

private def listDegree {X : Scheme.{u}} {H : X.Modules} (l : List (PowerDatum H)) : ℕ :=
  (l.map Sigma.fst).sum

private def listPowerSection {X : Scheme.{u}} (H : X.Modules) :
    (l : List (PowerDatum H)) → unitObj X ⟶ bundleTensorPower H (listDegree l)
  | [] => 𝟙 (unitObj X)
  | a :: l => powerSectionProduct H a.1 (listDegree l) a.2 (listPowerSection H l)

private theorem unit_identity_open (X : Scheme.{u}) :
    sectionOpen (unitObj X) isInvertible_unit (𝟙 (unitObj X)) = ⊤ := by
  rw [sectionOpen_eq_basicOpen_of_frame _ _ _ (Iso.refl _)]
  have h : frameScalar (Iso.refl (unitObj X)) (𝟙 (unitObj X)) = (1 : Γ(X, ⊤)) := rfl
  rw [h, Scheme.basicOpen_one]

private theorem listPowerSection_mem {X : Scheme.{u}} (H : X.Modules) (hH : IsInvertible H)
    (l : List (PowerDatum H)) (x : X) :
    x ∈ sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH (listDegree l))
      (listPowerSection H l) ↔
      ∀ a ∈ l, x ∈ sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH a.1) a.2 := by
  induction l with
  | nil =>
    change x ∈ sectionOpen (unitObj X) isInvertible_unit (𝟙 (unitObj X)) ↔ _
    rw [unit_identity_open]
    simp
  | cons a l ih =>
    change x ∈ sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH (a.1 + listDegree l))
      (powerSectionProduct H a.1 (listDegree l) a.2 (listPowerSection H l)) ↔ _
    rw [powerSectionProduct_open H hH]
    change (x ∈ sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH a.1) a.2 ∧
      x ∈ sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH (listDegree l))
        (listPowerSection H l)) ↔ _
    rw [ih]
    simp only [List.forall_mem_cons]

/-- The actual sum of the original finite tuple's original power degrees. -/
def tupleSectionDegree {m : ℕ} (d : Fin m → ℕ) : ℕ := (List.ofFn d).sum

private theorem tuple_degree_eq {X : Scheme.{u}} (H : X.Modules) {m : ℕ}
    (d : Fin m → ℕ) (s : ∀ i, unitObj X ⟶ bundleTensorPower H (d i)) :
    listDegree (List.ofFn (fun i => (⟨d i, s i⟩ : PowerDatum H))) = tupleSectionDegree d := by
  simp only [listDegree, List.map_ofFn, tupleSectionDegree]
  rfl

/-- The actual finite product of the SAME original tuple's power sections,
transported only by the internally proved equality of actual sum degrees. -/
def tuplePowerSection {X : Scheme.{u}} (H : X.Modules) {m : ℕ}
    (d : Fin m → ℕ) (s : ∀ i, unitObj X ⟶ bundleTensorPower H (d i)) :
    unitObj X ⟶ bundleTensorPower H (tupleSectionDegree d) :=
  listPowerSection H (List.ofFn (fun i => (⟨d i, s i⟩ : PowerDatum H))) ≫
    (eqToIso (congrArg (bundleTensorPower H) (tuple_degree_eq H d s))).hom

/-- The literal actual original finite product-section open is EXACTLY the
SAME native Cech tuple intersection, with no supplied product/open matching. -/
theorem tuplePowerSection_open {X : Scheme.{u}} (H : X.Modules) (hH : IsInvertible H) {m : ℕ}
    (d : Fin m → ℕ) (s : ∀ i, unitObj X ⟶ bundleTensorPower H (d i)) :
    sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH (tupleSectionDegree d))
      (tuplePowerSection H d s) =
      ∏ᶜ fun i : Fin m => sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH (d i)) (s i) := by
  let l := List.ofFn (fun i => (⟨d i, s i⟩ : PowerDatum H))
  have hOpen : sectionOpen _
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH (tupleSectionDegree d))
      (tuplePowerSection H d s) =
    sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH (listDegree l))
      (listPowerSection H l) :=
    sectionOpen_postcompose_iso
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH (listDegree l))
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH (tupleSectionDegree d))
      (listPowerSection H l) (eqToIso (congrArg (bundleTensorPower H) (tuple_degree_eq H d s)))
  rw [hOpen]
  have hPi : (∏ᶜ fun i : Fin m => sectionOpen _
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH (d i)) (s i)) =
      ⨅ i : Fin m, sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH (d i)) (s i) :=
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (Preorder.isLimitIInf _)).to_eq
  rw [hPi]
  ext x
  refine (listPowerSection_mem H hH l x).trans ?_
  dsimp only [l]
  simp only [List.forall_mem_ofFn_iff, Opens.coe_iInf, Set.mem_iInter]
  rfl

/-- EVERY nonempty original tuple of positive degrees has a genuinely
positive actual total degree, internally produced from the original tuple. -/
theorem tupleSectionDegree_pos {n : ℕ} (d : Fin (n + 1) → ℕ) (hd : ∀ i, 0 < d i) :
    0 < tupleSectionDegree d := by
  have h0 := hd 0
  simp only [tupleSectionDegree, List.ofFn_succ, List.sum_cons]
  omega

end EnvelopeProperty.SchemeLineSectionFiniteProductOpens
