import EnvelopeProperty.Global.NativeRankOneModel

/-! # The actual native chart is the SAME original rank-one chart algebra -/
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.MultiModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

private theorem finOneExponent_eq_single (a : Fin 1 →₀ ℕ) :
    a = Finsupp.single 0 a.degree := by
  have ha : a = Finsupp.single 0 (a 0) := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp
  have hd : a.degree = a 0 := by rw [ha]; simp
  rw [hd]
  exact ha

/-- A SAME original homogeneous rank-one polynomial is its single original monomial. -/
theorem rankOne_homogeneous_eq_monomial (d : ℕ) (p : MvPolynomial (Fin 1) K)
    (hp : p.IsHomogeneous d) :
    p = monomial (Finsupp.single 0 d) (p.coeff (Finsupp.single 0 d)) := by
  ext a
  by_cases ha : a = Finsupp.single 0 d
  · subst a
    simp
  · have hd : a.degree ≠ d := by
      intro h
      exact ha ((finOneExponent_eq_single a).trans (congrArg (Finsupp.single 0) h))
    rw [hp.coeff_eq_zero hd]
    simp [MvPolynomial.coeff_monomial, Ne.symm ha]

/-- The original dehomogenization is injective at zero on each original homogeneous piece. -/
theorem rankOne_dehom_eq_zero (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) (d : ℕ)
    (p : MvPolynomial (Fin 1) K) (hp : p.IsHomogeneous d) :
    X.dehom j p = 0 ↔ p = 0 := by
  rw [rankOne_homogeneous_eq_monomial d p hp, X.dehom_monomial]
  simp [div_eq_zero_iff, chartDen_ne_zero hj]

/-- The actual original dehomogenization takes the original algebra into its original chart. -/
def nativeRankOneChartInput (j : X.ChartIndex) : X.S →+* X.chartAlg j where
  toFun p := ⟨X.dehom j p, ⟨p, p.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- The SAME original chart coordinate dehomogenizes to one. -/
theorem nativeRankOneChartInput_coordinate (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    X.nativeRankOneChartInput j (X.coordElem ⟨0, j 0⟩) = 1 := by
  apply Subtype.ext
  change X.dehom j (monomial (Finsupp.single 0 1) (X.coord 0 (j 0))) = 1
  rw [X.dehom_monomial, X.chartDen_single]
  exact div_self (hj 0)

/-- The actual original chart map extended through the actual ordinary localization. -/
def nativeRankOneOrdinaryDehom (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    Localization.Away (X.coordElem ⟨0, j 0⟩) →+* X.chartAlg j :=
  IsLocalization.Away.lift (X.coordElem ⟨0, j 0⟩)
    (show IsUnit (X.nativeRankOneChartInput j (X.coordElem ⟨0, j 0⟩)) by
      rw [X.nativeRankOneChartInput_coordinate j hj]
      exact isUnit_one)

/-- Restriction of the genuine localization map to the native degree-zero homogeneous chart. -/
def nativeRankOneChartDehom (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    X.nativeRankOneChartRing (j 0) →+* X.chartAlg j :=
  (X.nativeRankOneOrdinaryDehom j hj).comp
    (algebraMap (X.nativeRankOneChartRing (j 0))
      (Localization.Away (X.coordElem ⟨0, j 0⟩)))

/-- Every native homogeneous fraction retains the SAME original dehomogenized numerator. -/
theorem nativeRankOneChartDehom_mk (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) (d : ℕ) (p : X.S)
    (hp : p ∈ X.nativeTotalGrading (d • (1 : ℕ))) :
    X.nativeRankOneChartDehom j hj
      (HomogeneousLocalization.Away.mk X.nativeTotalGrading
        (X.nativeRankOneCoordinate_mem (j 0)) d p hp) = X.nativeRankOneChartInput j p := by
  have h := congrArg (X.nativeRankOneOrdinaryDehom j hj)
    (IsLocalization.mk'_spec (Localization.Away (X.coordElem ⟨0, j 0⟩)) p
      (⟨X.coordElem ⟨0, j 0⟩ ^ d, d, rfl⟩ : Submonoid.powers (X.coordElem ⟨0, j 0⟩)))
  simp only [map_mul, map_pow] at h
  simp only [nativeRankOneOrdinaryDehom, IsLocalization.Away.lift_eq,
    X.nativeRankOneChartInput_coordinate j hj, one_pow, mul_one] at h
  change X.nativeRankOneOrdinaryDehom j hj
    (Localization.mk p (⟨X.coordElem ⟨0, j 0⟩ ^ d, d, rfl⟩ :
      Submonoid.powers (X.coordElem ⟨0, j 0⟩))) = _
  rw [Localization.mk_eq_mk']
  exact h

/-- The actual homogeneous chart map is injective on the ENTIRE native chart ring. -/
theorem nativeRankOneChartDehom_injective (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    Function.Injective (X.nativeRankOneChartDehom j hj) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply le_antisymm ?_ bot_le
  intro z hz
  change z = 0
  change X.nativeRankOneChartDehom j hj z = 0 at hz
  obtain ⟨d, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    X.nativeTotalGrading (X.nativeRankOneCoordinate_mem (j 0)) z
  rw [X.nativeRankOneChartDehom_mk j hj] at hz
  have hpz : p = 0 := by
    apply Subtype.ext
    apply (X.rankOne_dehom_eq_zero j hj d (p : MvPolynomial (Fin 1) K)
      (by simpa only [smul_eq_mul, mul_one] using
        (X.mem_nativeTotalGrading _ _).mp hp)).mp
    exact congrArg (fun a : X.chartAlg j => (a : K)) hz
  apply HomogeneousLocalization.val_injective (Submonoid.powers (X.coordElem ⟨0, j 0⟩))
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero, hpz]
  exact Localization.mk_zero _

/-- Every element of the SAME original chart is an actual native homogeneous fraction. -/
theorem nativeRankOneChartDehom_surjective (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    Function.Surjective (X.nativeRankOneChartDehom j hj) := by
  intro y
  obtain ⟨a, f, hf, hy⟩ := (X.mem_chartAlg_iff hj).mp y.property
  let p : X.S := ⟨monomial a f, hf⟩
  have hp : p ∈ X.nativeTotalGrading (a.degree • (1 : ℕ)) := by
    change (monomial a f).IsHomogeneous (a.degree • (1 : ℕ))
    exact MvPolynomial.isHomogeneous_monomial f (by simp)
  refine ⟨HomogeneousLocalization.Away.mk X.nativeTotalGrading
    (X.nativeRankOneCoordinate_mem (j 0)) a.degree p hp, ?_⟩
  rw [X.nativeRankOneChartDehom_mk j hj]
  apply Subtype.ext
  change X.dehom j (monomial a f) = (y : K)
  exact (X.dehom_monomial j a f).trans hy.symm

/-- The actual whole native degree-zero localization is the SAME original chart algebra. -/
def nativeRankOneChartEquiv (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    X.nativeRankOneChartRing (j 0) ≃+* X.chartAlg j :=
  RingEquiv.ofBijective (X.nativeRankOneChartDehom j hj)
    ⟨X.nativeRankOneChartDehom_injective j hj, X.nativeRankOneChartDehom_surjective j hj⟩

/-- The actual original-coordinate open is the spectrum of the SAME original chart algebra. -/
def nativeRankOneOriginalChartIso (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    (X.nativeRankOneCoordinateOpen (j 0)).toScheme ≅ Spec (.of (X.chartAlg j)) :=
  (X.nativeRankOneHomogeneousChartIso (j 0)).trans
    (Scheme.Spec.mapIso (X.nativeRankOneChartEquiv j hj).toCommRingCatIso.symm.op)

/-- The whole chart comparison retains the SAME original coefficient inclusion. -/
theorem nativeRankOneChartEquiv_coefficients (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) (a : k) :
    X.nativeRankOneChartEquiv j hj
      (HomogeneousLocalization.fromZeroRingHom X.nativeTotalGrading
        (Submonoid.powers (X.coordElem ⟨0, j 0⟩)) (X.nativeRankOneCoefficients a)) =
      algebraMap k (X.chartAlg j) a := by
  change X.nativeRankOneOrdinaryDehom j hj
    (Localization.mk (algebraMap k X.S a) (1 : Submonoid.powers (X.coordElem ⟨0, j 0⟩))) = _
  rw [Localization.mk_eq_mk', IsLocalization.mk'_one]
  change IsLocalization.Away.lift _ _ (algebraMap X.S _ (algebraMap k X.S a)) = _
  rw [IsLocalization.Away.lift_eq]
  apply Subtype.ext
  exact (X.dehom j).commutes a

private theorem specMapRingEquiv_hom {B C : Type u} [CommRing B] [CommRing C]
    (e : B ≃+* C) :
    Scheme.Spec.map e.toCommRingCatIso.hom.op = Spec.map (CommRingCat.ofHom e.toRingHom) := rfl

/-- The WHOLE original chart isomorphism is over the SAME original coefficient field. -/
theorem nativeRankOneOriginalChartIso_structure (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    (X.nativeRankOneOriginalChartIso j hj).inv ≫
      (X.nativeRankOneCoordinateOpen (j 0)).ι ≫ X.nativeRankOneStructure =
      Spec.map (CommRingCat.ofHom (algebraMap k (X.chartAlg j))) := by
  simp only [nativeRankOneOriginalChartIso, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, Iso.symm_inv, nativeRankOneStructure, Category.assoc,
    nativeRankOneHomogeneousChartIso, nativeRankOneCoordinateOpen,
    nativeRankOneScheme, nativeRankOneChartRing]
  have ht := Proj.awayι_toSpecZero_assoc X.nativeTotalGrading (X.coordElem ⟨0, j 0⟩)
    (X.nativeRankOneCoordinate_mem (j 0)) (by decide : 0 < (1 : ℕ))
    (Spec.map (CommRingCat.ofHom X.nativeRankOneCoefficients))
  simp only [Proj.awayι, Category.assoc] at ht
  erw [ht]
  rw [specMapRingEquiv_hom]
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact X.nativeRankOneChartEquiv_coefficients j hj a

end EnvelopeProperty.MultiModel
