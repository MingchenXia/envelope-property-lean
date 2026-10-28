import EnvelopeProperty.AlgGeom.ArithmeticSmoothProjectiveOriginalFamily
import EnvelopeProperty.DeligneIllusie.WittTwoSchemeAffineRestrictions

/-! # An actual Witt family at an internally produced arithmetic closed point -/
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.ArithmeticProjectiveWittFamily
open ProjBerk ArithmeticProjectiveOriginalFamily ArithmeticSmoothProjectiveOriginalFamily
open ArithmeticSmoothCoefficientBase DeligneIllusie

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}}
variable (j : X ⟶ NativeProjectiveScheme k N) [IsClosedImmersion j] (extra : Finset k)

/-- Only internally produced coefficient-stage and closed-point data; the geometric family is fixed by j. -/
structure ProducedStage (bound : ℕ) where
  stage : Subalgebra ℤ k
  contains : coefficientBase j extra ≤ stage
  arithmeticSmooth : Algebra.Smooth ℤ stage
  finiteType : Algebra.FiniteType ℤ stage
  familySmooth : Smooth (scalarProjection j extra stage contains)
  element : stage
  nonzero : element ≠ 0
  point : MaximalSpectrum (localizedCoefficientRing stage element nonzero)
  prime : ℕ
  primeFact : Fact prime.Prime
  prime_gt : bound < prime
  residueChar : CharP ((localizedCoefficientRing stage element nonzero) ⧸ point.asIdeal) prime
  residueFinite : Finite ((localizedCoefficientRing stage element nonzero) ⧸ point.asIdeal)
  lifted :
    letI : Fact prime.Prime := primeFact
    letI : Field ((localizedCoefficientRing stage element nonzero) ⧸ point.asIdeal) :=
      Ideal.Quotient.field point.asIdeal
    localizedCoefficientRing stage element nonzero →+*
      WittTwo.Ring prime ((localizedCoefficientRing stage element nonzero) ⧸ point.asIdeal)
  reduction :
    letI : Fact prime.Prime := primeFact
    letI : Field ((localizedCoefficientRing stage element nonzero) ⧸ point.asIdeal) :=
      Ideal.Quotient.field point.asIdeal
    (WittTwo.reduction prime _).comp lifted = Ideal.Quotient.mk point.asIdeal

/-- The original smooth family and bound internally produce all actual coefficient and Witt-point data. -/
theorem nonempty_producedStage [CharZero k] (p : X ⟶ Spec (.of k))
    (hjp : j ≫ nativeStructureMap = p) [Smooth p] (bound : ℕ) :
    Nonempty (ProducedStage j extra bound) := by
  obtain ⟨S, hRS, hBaseSmooth, hFT, hFamilySmooth, -, -, -, -, -⟩ :=
    exists_smooth_projective_arithmetic_family j extra p hjp
  let : Algebra.FiniteType ℤ S := hFT
  obtain ⟨r, hr, m, ell, hp, hBound, hc, hf, lifted, hred, -⟩ :=
    exists_produced_witt_point S bound
  exact ⟨⟨S, hRS, hBaseSmooth, hFT, hFamilySmooth, r, hr, m, ell, hp, hBound,
    hc, hf, lifted, hred⟩⟩

/-- A chosen stage of the actual original family, with every target datum constructed internally. -/
def producedStage [CharZero k] (p : X ⟶ Spec (.of k))
    (hjp : j ≫ nativeStructureMap = p) [Smooth p] (bound : ℕ) : ProducedStage j extra bound :=
  Classical.choice (nonempty_producedStage j extra p hjp bound)

namespace ProducedStage
variable {j extra} {bound : ℕ} (D : ProducedStage j extra bound)

/-- The ACTUAL further image localization supplied by the existing Witt-point producer. -/
def base : Subalgebra ℤ k := localizedCoefficientRing D.stage D.element D.nonzero

/-- All original coefficients remain in that actual further localization. -/
theorem contains_base : coefficientBase j extra ≤ D.base :=
  D.contains.trans (le_localizedCoefficientRing D.stage D.element D.nonzero)

/-- The literal finite residue field of the actual produced closed point. -/
def residueField : Type u := D.base ⧸ D.point.asIdeal

instance residueField_field : Field D.residueField := Ideal.Quotient.field D.point.asIdeal
instance residueField_char : CharP D.residueField D.prime := D.residueChar
instance residueField_finite : Finite D.residueField := D.residueFinite
instance prime_fact : Fact D.prime.Prime := D.primeFact

/-- The actual truncated length-two Witt coefficient ring at the same produced point. -/
abbrev wittRing : Type u := WittTwo.Ring D.prime D.residueField

/-- The entire actual coefficient lift, not a family-lifting certificate. -/
def coefficientLift : D.base →+* D.wittRing := D.lifted

/-- Its whole reduction is exactly the SAME original residue quotient map. -/
theorem coefficientLift_reduction :
    (WittTwo.reduction D.prime D.residueField).comp D.coefficientLift =
      Ideal.Quotient.mk D.point.asIdeal := D.reduction

/-- The same complete coefficient equality in the actual spectrum category. -/
theorem coefficientLift_specReduction :
    Spec.map (CommRingCat.ofHom (WittTwo.reduction D.prime D.residueField)) ≫
        Spec.map (CommRingCat.ofHom D.coefficientLift) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk D.point.asIdeal)) := by
  rw [← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom D.coefficientLift_reduction

end ProducedStage

attribute [local instance] MvPolynomial.gradedAlgebra

private def scalarTransition {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)) (φ : R →+* S) (ψ : S →+* T) :
    pullback q (Spec.map (CommRingCat.ofHom (ψ.comp φ))) ⟶
      pullback q (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ)) (by
      rw [Category.assoc, ← Spec.map_comp]
      exact pullback.condition)

private theorem scalarTransition_fst {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)) (φ : R →+* S) (ψ : S →+* T) :
    scalarTransition q φ ψ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp only [scalarTransition, pullback.lift_fst]

private theorem scalarTransition_snd {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)) (φ : R →+* S) (ψ : S →+* T) :
    scalarTransition q φ ψ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ) := by
  simp only [scalarTransition, pullback.lift_snd]

private theorem scalarTransition_isPullback {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)) (φ : R →+* S) (ψ : S →+* T) :
    IsPullback (scalarTransition q φ ψ) (pullback.snd _ _) (pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom ψ)) := by
  have ho : IsPullback (scalarTransition q φ ψ ≫ pullback.fst _ _) (pullback.snd _ _) q
      (Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ)) := by
    rw [scalarTransition_fst, ← Spec.map_comp]
    exact IsPullback.of_hasPullback _ _
  exact ho.of_right (scalarTransition_snd q φ ψ) (IsPullback.of_hasPullback _ _)

private theorem smooth_scalarExtension {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)) (φ : R →+* S) (ψ : S →+* T)
    [Smooth (pullback.snd q (Spec.map (CommRingCat.ofHom φ)))] :
    Smooth (pullback.snd q (Spec.map (CommRingCat.ofHom (ψ.comp φ)))) :=
  MorphismProperty.of_isPullback (scalarTransition_isPullback q φ ψ) inferInstance

section ProjectiveBaseChange
variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ} {Y : Scheme.{u}}
  (i : Y ⟶ NativeProjectiveScheme R n) (q : Y ⟶ Spec (.of R))
  (hi : i ≫ nativeStructureMap = q) (φ : R →+* S)

private def ambientScalarMap :
    pullback q (Spec.map (CommRingCat.ofHom φ)) ⟶
      pullback (nativeStructureMap (R := R) (n := n)) (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.map q (Spec.map (CommRingCat.ofHom φ)) nativeStructureMap
    (Spec.map (CommRingCat.ofHom φ)) i (𝟙 _) (𝟙 _) (by simpa using hi.symm) (by simp)

private theorem ambientScalarMap_fst :
    ambientScalarMap i q hi φ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ i := by
  simp only [ambientScalarMap, pullback.map, pullback.lift_fst]

private theorem ambientScalarMap_snd :
    ambientScalarMap i q hi φ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp only [ambientScalarMap, pullback.map, pullback.lift_snd, Category.comp_id]

private theorem ambientScalarMap_isPullback :
    IsPullback (pullback.fst q (Spec.map (CommRingCat.ofHom φ))) (ambientScalarMap i q hi φ)
      i (pullback.fst _ _) := by
  apply IsPullback.of_bot
    (v₂₁ := pullback.snd (nativeStructureMap (R := R) (n := n)) (Spec.map (CommRingCat.ofHom φ)))
    (v₂₂ := nativeStructureMap) ?_ (ambientScalarMap_fst i q hi φ).symm
    (IsPullback.of_hasPullback _ _)
  rw [ambientScalarMap_snd, hi]
  exact IsPullback.of_hasPullback _ _

private def changedEmbedding :
    pullback q (Spec.map (CommRingCat.ofHom φ)) ⟶ NativeProjectiveScheme S n :=
  ambientScalarMap i q hi φ ≫ (nativeCoefficientBaseChangeIso (n := n) φ).inv

private theorem changedEmbedding_closed [IsClosedImmersion i] :
    IsClosedImmersion (changedEmbedding i q hi φ) := by
  let : IsClosedImmersion (ambientScalarMap i q hi φ) :=
    MorphismProperty.of_isPullback (ambientScalarMap_isPullback i q hi φ) inferInstance
  change IsClosedImmersion (ambientScalarMap i q hi φ ≫ (nativeCoefficientBaseChangeIso (n := n) φ).inv)
  infer_instance

private theorem changedEmbedding_projection :
    changedEmbedding i q hi φ ≫ nativeStructureMap = pullback.snd _ _ := by
  have he : (nativeCoefficientBaseChangeIso (n := n) φ).inv ≫ nativeStructureMap =
      pullback.snd _ _ := by
    rw [← nativeCoefficientBaseChangeIso_hom_snd φ, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  change (ambientScalarMap i q hi φ ≫ (nativeCoefficientBaseChangeIso (n := n) φ).inv) ≫ _ = _
  rw [Category.assoc, he, ambientScalarMap_snd]

end ProjectiveBaseChange

namespace ProducedStage
variable {j extra} {bound : ℕ} (D : ProducedStage j extra bound)

/-- The same whole arithmetic family at the ACTUAL further Witt-point localization. -/
def baseFamily : Scheme.{u} := scalarFamily j extra D.base D.contains_base

/-- Its literal structure projection. -/
def baseProjection : D.baseFamily ⟶ Spec (.of D.base) := scalarProjection j extra D.base D.contains_base

/-- Smoothness is transported from the produced smooth family stage by actual scalar base change. -/
theorem baseProjection_smooth : Smooth D.baseProjection := by
  let : Smooth (pullback.snd (familyProjection j extra)
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion D.contains).toRingHom))) := D.familySmooth
  exact smooth_scalarExtension (familyProjection j extra) (Subalgebra.inclusion D.contains).toRingHom
    (Subalgebra.inclusion (le_localizedCoefficientRing D.stage D.element D.nonzero)).toRingHom

/-- The actual original quotient embedding at that same further base. -/
def baseEmbedding : D.baseFamily ⟶ NativeProjectiveScheme D.base N :=
  scalarEmbedding j extra D.base D.contains_base

/-- The original whole X still recovers from the same arithmetic family over the original k. -/
def originalBaseChangeIso (p : X ⟶ Spec (.of k)) (hjp : j ≫ nativeStructureMap = p) :
    X ≅ pullback D.baseProjection (Spec.map (CommRingCat.ofHom (algebraMap D.base k))) :=
  scalarFamilyBaseChangeIso j extra D.base D.contains_base p hjp

/-- Its arithmetic-family projection is the same entire original coefficient map. -/
theorem originalBaseChangeIso_hom_fst (p : X ⟶ Spec (.of k)) (hjp : j ≫ nativeStructureMap = p) :
    (D.originalBaseChangeIso p hjp).hom ≫ pullback.fst _ _ =
      scalarOriginalMap j extra D.base D.contains_base p hjp :=
  scalarFamilyBaseChangeIso_hom_fst j extra D.base D.contains_base p hjp

/-- Its field projection is precisely the same original p. -/
theorem originalBaseChangeIso_hom_snd (p : X ⟶ Spec (.of k)) (hjp : j ≫ nativeStructureMap = p) :
    (D.originalBaseChangeIso p hjp).hom ≫ pullback.snd _ _ = p :=
  scalarFamilyBaseChangeIso_hom_snd j extra D.base D.contains_base p hjp

/-- The actual Witt family is the literal base change along the produced coefficient lift. -/
def wittFamily : Scheme.{u} := pullback D.baseProjection (Spec.map (CommRingCat.ofHom D.coefficientLift))

/-- The genuine structure projection to the literal Witt coefficient ring. -/
def wittProjection : D.wittFamily ⟶ Spec (.of D.wittRing) := pullback.snd _ _

/-- The SAME actual Witt family is smooth; no target smoothness input is supplied. -/
theorem wittProjection_smooth : Smooth D.wittProjection := by
  let : Smooth D.baseProjection := D.baseProjection_smooth
  change Smooth (pullback.snd D.baseProjection (Spec.map (CommRingCat.ofHom D.coefficientLift)))
  infer_instance

/-- Its actual closed projective embedding is constructed from the original quotient embedding. -/
def wittEmbedding : D.wittFamily ⟶ NativeProjectiveScheme D.wittRing N :=
  changedEmbedding D.baseEmbedding D.baseProjection
    (scalarEmbedding_projection j extra D.base D.contains_base) D.coefficientLift

/-- The true ambient pullback proves closedness. -/
theorem wittEmbedding_isClosedImmersion : IsClosedImmersion D.wittEmbedding := by
  let : IsClosedImmersion D.baseEmbedding := scalarEmbedding_isClosedImmersion j extra D.base D.contains_base
  exact changedEmbedding_closed _ _ _ _

/-- The embedding factors the same whole Witt-family projection. -/
theorem wittEmbedding_projection : D.wittEmbedding ≫ nativeStructureMap = D.wittProjection :=
  changedEmbedding_projection _ _ _ _

/-- The canonical Witt family is genuinely projective. -/
theorem wittProjection_projective : IsProjectiveFactorization D.wittProjection :=
  ⟨N, D.wittEmbedding, D.wittEmbedding_isClosedImmersion, D.wittEmbedding_projection⟩

/-- Its properness follows from that actual projective factorization. -/
theorem wittProjection_proper : IsProper D.wittProjection := D.wittProjection_projective.isProper

/-- The SAME actual residue fibre, using the actual quotient of the actual further base. -/
def residueFamily : Scheme.{u} :=
  pullback D.baseProjection (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk D.point.asIdeal)))

/-- Its exact original residue-field structure projection. -/
def residueProjection : D.residueFamily ⟶ Spec (.of D.residueField) := pullback.snd _ _

/-- The actual residue family is smooth over its actual finite residue field. -/
theorem residueProjection_smooth : Smooth D.residueProjection := by
  let : Smooth D.baseProjection := D.baseProjection_smooth
  change Smooth (pullback.snd D.baseProjection
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk D.point.asIdeal))))
  infer_instance

/-- The actual original quotient embedding at the literal residue field. -/
def residueEmbedding : D.residueFamily ⟶ NativeProjectiveScheme D.residueField N :=
  changedEmbedding D.baseEmbedding D.baseProjection
    (scalarEmbedding_projection j extra D.base D.contains_base) (Ideal.Quotient.mk D.point.asIdeal)

/-- Its canonical ambient coefficient square proves closedness. -/
theorem residueEmbedding_isClosedImmersion : IsClosedImmersion D.residueEmbedding := by
  let : IsClosedImmersion D.baseEmbedding := scalarEmbedding_isClosedImmersion j extra D.base D.contains_base
  exact changedEmbedding_closed _ _ _ _

/-- This actual embedding factors the same residue structure morphism. -/
theorem residueEmbedding_projection : D.residueEmbedding ≫ nativeStructureMap = D.residueProjection :=
  changedEmbedding_projection _ _ _ _

/-- The same residue fibre is projective over its actual finite field. -/
theorem residueProjection_projective : IsProjectiveFactorization D.residueProjection :=
  ⟨N, D.residueEmbedding, D.residueEmbedding_isClosedImmersion, D.residueEmbedding_projection⟩

/-- Its actual properness is retained. -/
theorem residueProjection_proper : IsProper D.residueProjection := D.residueProjection_projective.isProper

/-- Whole reduction into the produced Witt family, constructed from the same two original projections. -/
def reductionMap : D.residueFamily ⟶ D.wittFamily :=
  pullback.lift (pullback.fst _ _)
    (D.residueProjection ≫ Spec.map (CommRingCat.ofHom (WittTwo.reduction D.prime D.residueField))) (by
      rw [Category.assoc, D.coefficientLift_specReduction]
      exact pullback.condition)

/-- The whole original projection to the arithmetic family is unchanged. -/
theorem reductionMap_fst :
    D.reductionMap ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp only [reductionMap, pullback.lift_fst]

/-- The whole coefficient reduction is the actual Witt reduction. -/
theorem reductionMap_projection :
    D.reductionMap ≫ D.wittProjection =
      D.residueProjection ≫ Spec.map (CommRingCat.ofHom (WittTwo.reduction D.prime D.residueField)) := by
  simp only [reductionMap, wittProjection, pullback.lift_snd]

/-- The actual reduction square is cartesian with the SAME whole original residue fibre. -/
theorem isPullback_reductionMap :
    IsPullback D.reductionMap D.residueProjection D.wittProjection
      (Spec.map (CommRingCat.ofHom (WittTwo.reduction D.prime D.residueField))) := by
  have ho : IsPullback (D.reductionMap ≫ pullback.fst _ _) D.residueProjection D.baseProjection
      (Spec.map (CommRingCat.ofHom (WittTwo.reduction D.prime D.residueField)) ≫
        Spec.map (CommRingCat.ofHom D.coefficientLift)) := by
    rw [D.reductionMap_fst, D.coefficientLift_specReduction]
    exact IsPullback.of_hasPullback _ _
  exact ho.of_right D.reductionMap_projection (IsPullback.of_hasPullback _ _)

/-- The canonical whole reduction comparison has the SAME actual residue fibre as its source. -/
def reductionIso : D.residueFamily ≅ pullback D.wittProjection
    (Spec.map (CommRingCat.ofHom (WittTwo.reduction D.prime D.residueField))) :=
  D.isPullback_reductionMap.isoPullback

/-- Its first projection is exactly the constructed whole reduction map. -/
theorem reductionIso_hom_fst :
    D.reductionIso.hom ≫ pullback.fst _ _ = D.reductionMap :=
  D.isPullback_reductionMap.isoPullback_hom_fst

/-- Its second projection is exactly the SAME residue-field structure map. -/
theorem reductionIso_hom_snd :
    D.reductionIso.hom ≫ pullback.snd _ _ = D.residueProjection :=
  D.isPullback_reductionMap.isoPullback_hom_snd

attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoSourceResidue.twistSMul WittTwoRelativeLift.residueCopyAlgebra
  WittTwoLiftDifference.frobeniusAlgebra
  WittTwoOriginalCotangentMaps.originalResidueRing WittTwoOriginalCotangentMaps.residueAlgebra

/-- Every actual affine-open section algebra of the produced Witt family is genuinely smooth. -/
theorem affine_sections_smooth {U : D.wittFamily.Opens} (hU : IsAffineOpen U) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra D.wittProjection U
    Algebra.Smooth D.wittRing Γ(D.wittFamily,U) := by
  let : Smooth D.wittProjection := D.wittProjection_smooth
  exact WittTwoSchemeAffineRestrictions.affine_smooth D.wittProjection hU

/-- An actual whole relative Frobenius lift is internally produced on every actual affine open. -/
theorem exists_affineLift {U : D.wittFamily.Opens} (hU : IsAffineOpen U) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra D.wittProjection U
    ∃ F : WittTwoLiftDifference.Lift D.prime D.residueField Γ(D.wittFamily,U), ∀ t,
      algebraMap Γ(D.wittFamily,U)
          (WittTwoSmoothDifferentials.ResidueAlgebra D.prime D.residueField Γ(D.wittFamily,U)) (F t) =
        WittTwoRelativeLift.residueFrobenius D.prime D.residueField Γ(D.wittFamily,U) t := by
  let : Smooth D.wittProjection := D.wittProjection_smooth
  exact WittTwoSchemeAffineRestrictions.exists_affineLift D.prime D.residueField D.wittProjection hU

/-- An actual affine restriction has a produced relative lift with BOTH whole original equalities. -/
theorem exists_restrictedLift {U V : D.wittFamily.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (i : U ⟶ V) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra D.wittProjection V
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra D.wittProjection U
    ∀ (F : WittTwoLiftDifference.Lift D.prime D.residueField Γ(D.wittFamily,V))
      (_hF : ∀ t, algebraMap Γ(D.wittFamily,V)
          (WittTwoSmoothDifferentials.ResidueAlgebra D.prime D.residueField Γ(D.wittFamily,V)) (F t) =
        WittTwoRelativeLift.residueFrobenius D.prime D.residueField Γ(D.wittFamily,V) t),
    ∃ G : WittTwoLiftDifference.Lift D.prime D.residueField Γ(D.wittFamily,U),
      (∀ t, algebraMap Γ(D.wittFamily,U)
          (WittTwoSmoothDifferentials.ResidueAlgebra D.prime D.residueField Γ(D.wittFamily,U)) (G t) =
        WittTwoRelativeLift.residueFrobenius D.prime D.residueField Γ(D.wittFamily,U) t) ∧
      (∀ t, (D.wittFamily.presheaf.map i.op) (F t) =
        G (WittTwoLiftDifferenceNaturality.twistMap D.prime D.residueField
          (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom D.wittProjection i) t)) := by
  let : Smooth D.wittProjection := D.wittProjection_smooth
  exact WittTwoSchemeAffineRestrictions.exists_restrictedLift D.prime D.residueField
    D.wittProjection hU hV i

end ProducedStage

/-- Only the original smooth projective data and a bound are supplied; the genuine Witt family is produced. -/
theorem exists_genuine_witt_family [CharZero k] (p : X ⟶ Spec (.of k))
    (hjp : j ≫ nativeStructureMap = p) [Smooth p] (bound : ℕ) :
    ∃ D : ProducedStage j extra bound,
      Smooth D.wittProjection ∧ IsProjectiveFactorization D.wittProjection ∧ IsProper D.wittProjection ∧
      Smooth D.residueProjection ∧ IsProjectiveFactorization D.residueProjection ∧
      IsPullback D.reductionMap D.residueProjection D.wittProjection
        (Spec.map (CommRingCat.ofHom (WittTwo.reduction D.prime D.residueField))) ∧
      Nonempty (X ≅ pullback D.baseProjection (Spec.map (CommRingCat.ofHom (algebraMap D.base k)))) := by
  let D := producedStage j extra p hjp bound
  exact ⟨D, D.wittProjection_smooth, D.wittProjection_projective, D.wittProjection_proper,
    D.residueProjection_smooth, D.residueProjection_projective, D.isPullback_reductionMap,
    ⟨D.originalBaseChangeIso p hjp⟩⟩

end EnvelopeProperty.ArithmeticProjectiveWittFamily
