import EnvelopeProperty.Vanishing.NadelBlowupCanonicalSheafCoordinates
import EnvelopeProperty.AlgGeom.CartierInvertibleSheaves
import EnvelopeProperty.AlgGeom.IdealModulePullbackComp
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Membership

/-! # The actual native affine canonical Cartier-image comparison -/

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalSheafChart
open CoordinateSubspace affineBlowUpAlgebra CanonicalGeometry
open NadelBlowupCanonicalSheafCoordinates NadelBlowupCanonicalSheafImage

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n r : ℕ) (j : Fin n)

abbrev sourceRing := CommRingCat.of (ULift.{0} (MvPolynomial (Fin n) k))
abbrev targetRing := CommRingCat.of (MvPolynomial (Fin n) k)
def sourceBase := affineStructuralMap k (sourceRing k n)
def chartMap := Spec.map (CommRingCat.ofHom (chartAlgebraMap k n r j).toRingHom)

theorem sourceBase_smooth : SmoothOfRelativeDimension n (sourceBase k n) := by
  rw [sourceBase, affineStructuralMap, affineBaseRingMap, HasRingHomProperty.Spec_iff
    (P := @SmoothOfRelativeDimension.{u} n), CommRingCat.hom_ofHom]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  apply isStandardSmoothOfRelativeDimension_algebraMap_of_algEquiv (sourceAlgebraEquiv k n).symm
  have h := ringHom_isStandardSmoothOfRelativeDimension_algebraMap_mvPolynomial k (Fin n)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using h

theorem targetBase_smooth : SmoothOfRelativeDimension n (chartMap k n r j ≫ sourceBase k n) := by
  unfold chartMap sourceBase
  rw [affineAlgebraMap_structuralSquare k (sourceRing k n) (targetRing k n)
    (chartAlgebraMap k n r j)]
  exact smoothOfRelativeDimension_Spec_map_algebraMap_mvPolynomial k n

attribute [local instance] sourceBase_smooth targetBase_smooth

def sourceBasis :
    letI := affineChartAlgebra (sourceBase k n) ⊤
    Module.Basis (Fin n) Γ(Spec (sourceRing k n), ⊤)
      (KaehlerDifferential k Γ(Spec (sourceRing k n), ⊤)) :=
  affineGammaSpecEtaleBasis k (sourceRing k n)
    (fun i => (sourceAlgebraEquiv k n).symm (X i)) (source_coordinates_etale k n)

def targetBasis :
    letI := affineChartAlgebra (chartMap k n r j ≫ sourceBase k n) ⊤
    Module.Basis (Fin n) Γ(Spec (targetRing k n), ⊤)
      (KaehlerDifferential k Γ(Spec (targetRing k n), ⊤)) := by
  let := affineChartAlgebra (chartMap k n r j ≫ sourceBase k n) ⊤
  let e := affineGammaSpecAlgEquivOfStructuralEq k (targetRing k n)
    (chartMap k n r j ≫ sourceBase k n)
    (affineAlgebraMap_structuralSquare k (sourceRing k n) (targetRing k n) (chartAlgebraMap k n r j))
  exact Char0.etaleDifferentialBasis (fun i => e (X i))
    (Char0.etaleCoordinates_map_algEquiv e X (coordinates_etale k n))

def imageIdeal : (Spec (targetRing k n)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.span {(Scheme.ΓSpecIso (targetRing k n)).inv.hom (X j ^ (r - 1))})

def targetFrame : canonicalLineSheaf (chartMap k n r j ≫ sourceBase k n) n ≅
    unitObj (Spec (targetRing k n)) :=
  affineCanonicalFrameIso _ n (targetBasis k n r j)

def framedDifferential : (pullback (chartMap k n r j)).obj (canonicalLineSheaf (sourceBase k n) n) ⟶
    unitObj (Spec (targetRing k n)) :=
  exteriorCotangentSheafPullbackMap (sourceBase k n) (chartMap k n r j) n ≫
    (targetFrame k n r j).hom

private instance pulledCanonical_quasicoherent :
    ((pullback (chartMap k n r j)).obj (canonicalLineSheaf (sourceBase k n) n)).IsQuasicoherent :=
  ((canonicalLineSheaf_isInvertible (sourceBase k n) n).pullback (chartMap k n r j)).isQuasicoherent

theorem framedImage_eq (hj : j.val < r) (hrn : r ≤ n) :
    QuasicoherentImageIdeal.imageIdeal _ (framedDifferential k n r j) = imageIdeal k n r j := by
  have ht := framedImage_ideal_top (sourceBase k n) (chartMap k n r j) n
    (sourceBasis k n) (targetBasis k n r j)
  have hn := native_jacobianIdeal k n r j hj hrn
  have htop : (QuasicoherentImageIdeal.imageIdeal _ (framedDifferential k n r j)).ideal
      ⟨⊤, isAffineOpen_top _⟩ = (imageIdeal k n r j).ideal ⟨⊤, isAffineOpen_top _⟩ :=
    ht.trans (hn.trans (ofIdealTop_ideal_top _).symm)
  exact le_antisymm (Scheme.IdealSheafData.le_of_isAffine htop.le)
    (Scheme.IdealSheafData.le_of_isAffine htop.ge)

theorem imageIdeal_isInvertible : (imageIdeal k n r j).IsInvertible := by
  apply isInvertible_ofIdealTop_span_singleton
  apply map_mem_nonZeroDivisors_of_ringEquiv
    (Scheme.ΓSpecIso (targetRing k n)).symm.commRingCatIsoToRingEquiv
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (X_ne_zero j))

/-- Whole Cartier-image untwisting for actual original line modules.  The
concrete coordinate consumer below derives its image and regularity internally. -/
private theorem exists_iso_of_framed_image {Y : Scheme.{u}} [IsIntegral Y]
    (M N : Y.Modules) [M.IsQuasicoherent] (hM : IsInvertible M)
    (δ : M ⟶ N) (e : N ≅ unitObj Y) (I : Y.IdealSheafData)
    (hI : I.IsInvertible) (himage : QuasicoherentImageIdeal.imageIdeal M (δ ≫ e.hom) = I) :
    ∃ κ : M ≅ tensorObj N I.toModules,
      κ.hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap N I.toModules I.toModulesInclusion = δ := by
  let α := δ ≫ e.hom
  let J := QuasicoherentImageIdeal.imageIdeal M α
  have hJ : J.IsInvertible := by
    change (QuasicoherentImageIdeal.imageIdeal M (δ ≫ e.hom)).IsInvertible
    rw [himage]
    exact hI
  let eM := IntegralLineImageModules.lineImageIso hM α hJ
  let eJ := Scheme.IdealSheafData.toModulesEqualityIso J I himage
  let t := SchemeFramedIdealImage.tensorFrameIso N I.toModules e
  refine ⟨eM ≪≫ eJ ≪≫ t.symm, ?_⟩
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc]
  have ht := congrArg (fun q => (eM ≪≫ eJ ≪≫ t.symm).hom ≫ q)
    (SchemeFramedIdealImage.tensorFrameIso_inclusion N I.toModules e I.toModulesInclusion)
  refine ht.symm.trans ?_
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  change eM.hom ≫ eJ.hom ≫ t.inv ≫ t.hom ≫ I.toModulesInclusion = _
  rw [t.inv_hom_id_assoc]
  exact (congrArg (fun q => eM.hom ≫ q)
    (Scheme.IdealSheafData.toModulesEqualityIso_hom_inclusion J I himage)).trans
      (IntegralLineImageModules.lineImageIso_hom_inclusion hM α hJ)

/-- The actual pulled canonical line is the actual target canonical line
times its original exceptional Cartier image; the actual original whole
differential is retained after the actual inclusion, without an input comparison. -/
theorem exists_canonical_ideal_iso (hj : j.val < r) (hrn : r ≤ n) :
    ∃ e : (pullback (chartMap k n r j)).obj (canonicalLineSheaf (sourceBase k n) n) ≅
        tensorObj (canonicalLineSheaf (chartMap k n r j ≫ sourceBase k n) n)
          (imageIdeal k n r j).toModules,
      e.hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap _ _
        (imageIdeal k n r j).toModulesInclusion =
          exteriorCotangentSheafPullbackMap (sourceBase k n) (chartMap k n r j) n := by
  exact exists_iso_of_framed_image _ _
    ((canonicalLineSheaf_isInvertible (sourceBase k n) n).pullback (chartMap k n r j))
    (exteriorCotangentSheafPullbackMap (sourceBase k n) (chartMap k n r j) n)
    (targetFrame k n r j) (imageIdeal k n r j)
    (imageIdeal_isInvertible k n r j) (framedImage_eq k n r j hj hrn)

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalSheafChart
