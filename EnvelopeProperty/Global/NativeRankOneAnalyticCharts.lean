import EnvelopeProperty.Global.NativeRankOneAnalyticPoint

/-! # Whole original affine chart values on the SAME actual native rank-one point -/
open scoped Classical NNReal Topology
open Topology MvPolynomial AlgebraicGeometry CategoryTheory
open EnvelopeProperty.Berkovich
noncomputable section
universe u
namespace EnvelopeProperty.MultiModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

/-- The true native homogeneous-fraction section isomorphism of the SAME original coordinate open. -/
def nativeRankOneHomogeneousSectionsIso (i : Fin (X.M 0 + 1)) :
    CommRingCat.of (X.nativeRankOneChartRing i) ≅
      Γ(X.nativeRankOneScheme, X.nativeRankOneCoordinateOpen i) :=
  Proj.basicOpenIsoAway X.nativeTotalGrading (X.coordElem ⟨0, i⟩)
    (X.nativeRankOneCoordinate_mem i) (by decide : 0 < (1 : ℕ))

/-- The genuine native local section ring is the SAME whole original chart algebra. -/
def nativeRankOneOriginalSectionsIso (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    CommRingCat.of (X.chartAlg j) ≅
      Γ(X.nativeRankOneScheme, X.nativeRankOneCoordinateOpen (j 0)) :=
  (X.nativeRankOneChartEquiv j hj).toCommRingCatIso.symm.trans
    (X.nativeRankOneHomogeneousSectionsIso (j 0))

/-- The actual affine native point chart is the ENTIRE original affine chart spectrum. -/
def nativeRankOneAbsoluteChartHomeomorph (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    {y : SchemeValuedPoint X.nativeRankOneScheme //
      y.point ∈ X.nativeRankOneCoordinateOpen (j 0)} ≃ₜ Spectrum (X.chartAlg j) :=
  (SchemeValuedPoint.affineOpenSpectrumHomeomorph
    (X.nativeRankOneCoordinateOpen_isAffine (j 0))).trans
      (Spectrum.ringEquivHomeomorph (X.nativeRankOneOriginalSectionsIso j hj).commRingCatIsoToRingEquiv)

/-- Every original chart-ring element retains its SAME true native local section value. -/
theorem nativeRankOneAbsoluteChartHomeomorph_val_apply (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0)
    (y : {y : SchemeValuedPoint X.nativeRankOneScheme //
      y.point ∈ X.nativeRankOneCoordinateOpen (j 0)}) (a : X.chartAlg j) :
    (X.nativeRankOneAbsoluteChartHomeomorph j hj y).val a =
      SchemeValuedPoint.eval y.1 (X.nativeRankOneCoordinateOpen (j 0)) y.2
        ((X.nativeRankOneOriginalSectionsIso j hj).hom a) :=
  SchemeValuedPoint.affineOpenSpectrumHomeomorph_val_apply
    (X.nativeRankOneCoordinateOpen_isAffine (j 0)) y _

/-- Every original rank-one denominator monomial is the SAME original coordinate power. -/
theorem nativeRankOne_chartMono_eq_pow (j : X.ChartIndex) (a : Fin 1 →₀ ℕ) :
    X.chartMono j a = X.coordElem ⟨0, j 0⟩ ^ a.degree := by
  have ha : a = a.degree • Finsupp.single (0 : Fin 1) 1 := by
    have hsingle : a = Finsupp.single 0 (a 0) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      simp
    have hd : a.degree = a 0 := by rw [hsingle]; simp
    simpa only [Finsupp.smul_single, smul_eq_mul, mul_one, hd] using hsingle
  conv_lhs => rw [ha]
  rw [X.chartMono_nsmul, X.chartMono_single]

/-- EVERY original chart coefficient has its original chart seminorm value on the true native point. -/
theorem nativeRankOnePoint_eval_originalChart (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) (x : X.chartDomain j) (a : X.chartAlg j) :
    SchemeValuedPoint.eval (X.nativeRankOnePoint x.1) (X.nativeRankOneCoordinateOpen (j 0))
      ((X.nativeRankOneSupport_mem_coordinateOpen x.1 (j 0)).mpr
        ((mem_chartDomain_iff.mp x.2) 0))
      ((X.nativeRankOneOriginalSectionsIso j hj).hom a) =
      (X.chartHomeomorph j hj x).val a := by
  obtain ⟨b, f, hf, ha⟩ := (X.mem_chartAlg_iff hj).mp a.property
  let p : X.S := X.ofPiece hf
  have hp : p ∈ X.nativeTotalGrading (b.degree • (1 : ℕ)) := by
    change (monomial b f).IsHomogeneous (b.degree • (1 : ℕ))
    exact MvPolynomial.isHomogeneous_monomial f (by simp)
  let q := HomogeneousLocalization.Away.mk X.nativeTotalGrading
    (X.nativeRankOneCoordinate_mem (j 0)) b.degree p hp
  have he : X.nativeRankOneChartEquiv j hj q = a := by
    change X.nativeRankOneChartDehom j hj q = a
    rw [X.nativeRankOneChartDehom_mk j hj]
    apply Subtype.ext
    exact (X.dehom_monomial j b f).trans ha.symm
  have he' : (X.nativeRankOneChartEquiv j hj).symm a = q := by
    rw [← he, RingEquiv.symm_apply_apply]
  change SchemeValuedPoint.eval (X.nativeRankOnePoint x.1) _ _
    (Proj.awayToSection X.nativeTotalGrading (X.coordElem ⟨0, j 0⟩)
      ((X.nativeRankOneChartEquiv j hj).symm a)) = _
  rw [he']
  erw [X.nativeRankOnePoint_eval_mk]
  change x.1.1.val (X.ofPiece hf) / x.1.1.val (X.coordElem ⟨0, j 0⟩) ^ b.degree = _
  rw [X.chartHomeomorph_apply, X.chartMap_val_eq hj (mem_chartDomain_iff.mp x.2) a hf ha,
    X.nativeRankOne_chartMono_eq_pow, map_pow]

end EnvelopeProperty.MultiModel
