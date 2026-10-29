/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealSubvarietyModels
import EnvelopeProperty.Berkovich.SchemeModelIdealSupport
import Hironaka.Scheme.BlowUp.Glue.BlowUp
import Hironaka.Scheme.BlowUp.Glue.Global
import Hironaka.Scheme.BlowUp.Glue.Trivial
import Hironaka.Scheme.BlowUp.ProductCenter

/-!
# Constructed simultaneous Cartier ideal models

The actual blowup of the product of two genuine variety-product ideals makes
both original ideals invertible, in every characteristic. Properness is derived
from the actual Noetherian polynomial base. Native Gauss points lift through the
actual off-centre isomorphism; geometric pullback retains the entire original
ideal logarithms. Invertibility gives actual regular local equations computing
the intrinsic Cartier ideal function.

No normal modification, equivariance, polarization, nefness, or local positivity
is claimed here. Those additional geometric producers remain separate work.
-/

open scoped Classical Polynomial NNReal ENNReal Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {Y Z : Scheme.{u}} {f : Y ⟶ Spec (CommRingCat.of R)}

/-- Actual invertibility supplies a regular affine defining equation computing
the entire intrinsic proper-centre model logarithm. -/
theorem exists_regular_generator_modelIdealLog [IsProper f]
    (I : Y.IdealSheafData) (hI : I.IsInvertible) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) :
    ∃ (U : Y.affineOpens) (hc : center hb y ∈ U.1) (g : Γ(Y, U)),
      g ∈ nonZeroDivisors Γ(Y, U) ∧ I.ideal U = Ideal.span {g} ∧
      modelIdealLog I hb y =
        ENNReal.log (SchemeValuedPoint.eval y.1 U.1
          (support_mem_of_center_mem hb y U.1 hc) g : ℝ≥0∞) := by
  obtain ⟨U, hc, g, hg, hgen⟩ := hI (center hb y)
  refine ⟨U, hc, g, hg, hgen, ?_⟩
  have hn := modelIdealNorm_eq_generators I hb y U hc {g} (by simpa using hgen)
  simpa only [modelIdealLog, Finset.sup_singleton] using congrArg ENNReal.log hn

/-- An actual isomorphism over an actual open lifts a whole valued point in
that open. The source point is constructed through the two true open schemes. -/
def liftThroughOpenIso (μ : Z ⟶ Y) (W : Y.Opens) [IsIso (μ ∣_ W)]
    (y : RelativeSchemeValuedPoint v f) (hy : y.1.point ∈ W) :
    RelativeSchemeValuedPoint v (μ ≫ f) := by
  let q := (restrictionHomeomorph W f).symm ⟨y, hy⟩
  have he : (μ ∣_ W) ≫ (W.ι ≫ f) = (μ ⁻¹ᵁ W).ι ≫ (μ ≫ f) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  let e := isoOverHomeomorph (v := v) (asIso (μ ∣_ W)) he
  exact map (μ ⁻¹ᵁ W).ι rfl (e.symm q)

/-- The constructed open-isomorphism lift preserves the entire original valued
point, including the actual residue valuation and prescribed base point. -/
theorem map_liftThroughOpenIso (μ : Z ⟶ Y) (W : Y.Opens) [IsIso (μ ∣_ W)]
    (y : RelativeSchemeValuedPoint v f) (hy : y.1.point ∈ W) :
    map μ rfl (liftThroughOpenIso μ W y hy) = y := by
  let q := (restrictionHomeomorph W f).symm ⟨y, hy⟩
  have he : (μ ∣_ W) ≫ (W.ι ≫ f) = (μ ⁻¹ᵁ W).ι ≫ (μ ≫ f) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  let e := isoOverHomeomorph (v := v) (asIso (μ ∣_ W)) he
  have hq : map (μ ∣_ W) he (e.symm q) = q := by
    change e (e.symm q) = q
    exact e.apply_symm_apply q
  have hy' : map W.ι rfl q = y :=
    congrArg Subtype.val ((restrictionHomeomorph W f).apply_symm_apply ⟨y, hy⟩)
  apply Subtype.ext
  change SchemeValuedPoint.map μ (SchemeValuedPoint.map (μ ⁻¹ᵁ W).ι (e.symm q).1) = y.1
  calc SchemeValuedPoint.map μ (SchemeValuedPoint.map (μ ⁻¹ᵁ W).ι (e.symm q).1) =
      SchemeValuedPoint.map W.ι (SchemeValuedPoint.map (μ ∣_ W) (e.symm q).1) := by
        rw [← SchemeValuedPoint.map_comp, ← SchemeValuedPoint.map_comp, morphismRestrict_ι]
    _ = SchemeValuedPoint.map W.ι q.1 :=
      congrArg (fun z => SchemeValuedPoint.map W.ι z.1) hq
    _ = y.1 := congrArg Subtype.val hy'

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

namespace EnvelopeProperty.ProjSubvariety
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : X.NativeProductModel.IdealSheafData)
open ProjBerk Scheme.IdealSheafData

/-- The actual characteristic-free simultaneous principalization is the blowup
of the product of the two original ideal sheaves on the actual variety product. -/
abbrev simultaneousIdealBlowup : Scheme.{u} := (I * J).blowUp

/-- The actual original projection of the constructed blowup. -/
def simultaneousIdealBlowupProjection : X.simultaneousIdealBlowup I J ⟶ X.NativeProductModel :=
  (I * J).blowUpπ

/-- Properness follows from genuine local Noetherianity of the constructed
variety product; neither properness nor a principalizing scheme is an input. -/
instance simultaneousIdealBlowupProjection_isProper :
    IsProper (X.simultaneousIdealBlowupProjection I J) :=
  blowUp.isProper_π (I * J)

/-- The actual whole polynomial-base structure on the constructed blowup. -/
def simultaneousIdealBlowupStructure :
    X.simultaneousIdealBlowup I J ⟶ Spec (CommRingCat.of k[X]) :=
  X.simultaneousIdealBlowupProjection I J ≫ X.nativeProductStructure

instance simultaneousIdealBlowupStructure_isProper :
    IsProper (X.simultaneousIdealBlowupStructure I J) := by
  dsimp [simultaneousIdealBlowupStructure]
  infer_instance

/-- Both original ideals become actual effective Cartier ideals on their
constructed common blowup. -/
theorem simultaneousIdealBlowup_isInvertible :
    (I.comap (X.simultaneousIdealBlowupProjection I J)).IsInvertible ∧
      (J.comap (X.simultaneousIdealBlowupProjection I J)).IsInvertible := by
  have h := blowUp.isInvertible_comap_π (I * J)
  rw [comap_mul] at h
  exact IsInvertible.of_mul h

/-- The actual simultaneous blowup is an isomorphism off its genuine centre. -/
instance simultaneousIdealBlowupProjection_isIso_off_centre :
    IsIso (X.simultaneousIdealBlowupProjection I J ∣_ (I * J).support.compl) :=
  blowUp.isIso_π_restrict_compl_support (I * J)

/-- Finiteness of the two actual logarithms puts the genuine Gauss point off
the actual blowup centre. -/
theorem nativeProductGaussPoint_notMem_productSupport (w : X.an)
    (hI : RelativeSchemeValuedPoint.modelIdealLog I gaussModelCoefficient_le_one
      (X.nativeProductGaussPoint w) ≠ ⊥)
    (hJ : RelativeSchemeValuedPoint.modelIdealLog J gaussModelCoefficient_le_one
      (X.nativeProductGaussPoint w) ≠ ⊥) :
    (X.nativeProductGaussPoint w).1.point ∈ (I * J).support.compl := by
  have hI' := (RelativeSchemeValuedPoint.modelIdealLog_eq_bot_iff I
    gaussModelCoefficient_le_one (X.nativeProductGaussPoint w)).not.mp hI
  have hJ' := (RelativeSchemeValuedPoint.modelIdealLog_eq_bot_iff J
    gaussModelCoefficient_le_one (X.nativeProductGaussPoint w)).not.mp hJ
  rw [support_mul]
  change ¬ ((X.nativeProductGaussPoint w).1.point ∈ I.support ∨
    (X.nativeProductGaussPoint w).1.point ∈ J.support)
  exact not_or.mpr ⟨hI', hJ'⟩

/-- The actual original Gauss point lifted through the constructed simultaneous
blowup's actual off-centre isomorphism. -/
def simultaneousIdealBlowupGaussPoint (w : X.an)
    (hI : RelativeSchemeValuedPoint.modelIdealLog I gaussModelCoefficient_le_one
      (X.nativeProductGaussPoint w) ≠ ⊥)
    (hJ : RelativeSchemeValuedPoint.modelIdealLog J gaussModelCoefficient_le_one
      (X.nativeProductGaussPoint w) ≠ ⊥) :
    RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.simultaneousIdealBlowupStructure I J) :=
  RelativeSchemeValuedPoint.liftThroughOpenIso (X.simultaneousIdealBlowupProjection I J)
    (I * J).support.compl (X.nativeProductGaussPoint w)
    (X.nativeProductGaussPoint_notMem_productSupport I J w hI hJ)

/-- The constructed blowup lift retains the full original native variety Gauss point. -/
theorem map_simultaneousIdealBlowupGaussPoint (w : X.an)
    (hI : RelativeSchemeValuedPoint.modelIdealLog I gaussModelCoefficient_le_one
      (X.nativeProductGaussPoint w) ≠ ⊥)
    (hJ : RelativeSchemeValuedPoint.modelIdealLog J gaussModelCoefficient_le_one
      (X.nativeProductGaussPoint w) ≠ ⊥) :
    RelativeSchemeValuedPoint.map (X.simultaneousIdealBlowupProjection I J) rfl
      (X.simultaneousIdealBlowupGaussPoint I J w hI hJ) = X.nativeProductGaussPoint w :=
  RelativeSchemeValuedPoint.map_liftThroughOpenIso _ _ _ _

/-- Genuine geometric pullback preserves the entire original model logarithm
at the actual constructed simultaneous-blowup Gauss lift. -/
theorem modelIdealLog_simultaneousIdealBlowup_comap
    (K : X.NativeProductModel.IdealSheafData) (w : X.an)
    (hI : RelativeSchemeValuedPoint.modelIdealLog I gaussModelCoefficient_le_one
      (X.nativeProductGaussPoint w) ≠ ⊥)
    (hJ : RelativeSchemeValuedPoint.modelIdealLog J gaussModelCoefficient_le_one
      (X.nativeProductGaussPoint w) ≠ ⊥) :
    RelativeSchemeValuedPoint.modelIdealLog
      (K.comap (X.simultaneousIdealBlowupProjection I J)) gaussModelCoefficient_le_one
      (X.simultaneousIdealBlowupGaussPoint I J w hI hJ) =
      RelativeSchemeValuedPoint.modelIdealLog K gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) := by
  rw [RelativeSchemeValuedPoint.modelIdealLog_comap K
    (X.simultaneousIdealBlowupProjection I J) rfl gaussModelCoefficient_le_one
    (X.simultaneousIdealBlowupGaussPoint I J w hI hJ), X.map_simultaneousIdealBlowupGaussPoint]

/-- Actual PL data alone construct a proper simultaneous blowup, two effective
Cartier ideals, and the exact original logarithm-difference formula at its
genuinely lifted Gauss points. All finiteness data are produced existentially. -/
theorem IsPL.exists_simultaneousCartierIdeal_models {φ : X.an → ℝ} (hφ : X.IsPL φ) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ) (I J : X.NativeProductModel.IdealSheafData)
      (hfin : ∀ w : X.an,
        RelativeSchemeValuedPoint.modelIdealLog I gaussModelCoefficient_le_one
          (X.nativeProductGaussPoint w) ≠ ⊥ ∧
        RelativeSchemeValuedPoint.modelIdealLog J gaussModelCoefficient_le_one
          (X.nativeProductGaussPoint w) ≠ ⊥),
      (I.comap (X.simultaneousIdealBlowupProjection I J)).IsInvertible ∧
      (J.comap (X.simultaneousIdealBlowupProjection I J)).IsInvertible ∧
      ∀ w : X.an, (((r : ℝ) * φ w : ℝ) : EReal) =
        RelativeSchemeValuedPoint.modelIdealLog
          (I.comap (X.simultaneousIdealBlowupProjection I J)) gaussModelCoefficient_le_one
          (X.simultaneousIdealBlowupGaussPoint I J w (hfin w).1 (hfin w).2) -
        RelativeSchemeValuedPoint.modelIdealLog
          (J.comap (X.simultaneousIdealBlowupProjection I J)) gaussModelCoefficient_le_one
          (X.simultaneousIdealBlowupGaussPoint I J w (hfin w).1 (hfin w).2) + ((C : ℝ) : EReal) := by
  obtain ⟨r, hr, C, I, J, hfin, heq⟩ := IsPL.exists_nativeProductIdeal_models X hφ
  refine ⟨r, hr, C, I, J, hfin, (X.simultaneousIdealBlowup_isInvertible I J).1,
    (X.simultaneousIdealBlowup_isInvertible I J).2, fun w => ?_⟩
  simpa only [X.modelIdealLog_simultaneousIdealBlowup_comap] using heq w

end EnvelopeProperty.ProjSubvariety
