import EnvelopeProperty.AlgGeom.SchemeFiniteFlatDegrees
import EnvelopeProperty.AlgGeom.CurveLineDegreeBaseChange
import EnvelopeProperty.AlgGeom.FiniteProjectivePort.FiniteProjectivePreservation

/-! # True intrinsic line degree scaling of SAME original finite curve morphisms -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.CurveFiniteMapDegrees
open CurveLineDegrees SchemeCoherentEulerCharacteristic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual finite map internally gives a genuine projective factorization of the SAME original composite. -/
theorem finite_comp_projectiveFactorization {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (hp : IsProjectiveFactorization p)
    (f : Y ⟶ X) [IsFinite f] : IsProjectiveFactorization (f ≫ p) := by
  obtain ⟨n, i, hi, hbase⟩ := hp
  have hdj : DeJongAlterations.IsProjectiveOver p := by
    refine ⟨n, i, hi, ?_⟩
    convert hbase using 1
    unfold MvPolynomial.homogeneousProjπ DeJongAlterations.projectiveSpaceStructure
    congr 1
  obtain ⟨m, j, hj, hbase'⟩ :=
    DeJongAlterations.Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite p hdj f
  refine ⟨m, j, hj, ?_⟩
  convert hbase' using 1
  unfold MvPolynomial.homogeneousProjπ DeJongAlterations.projectiveSpaceStructure
  congr 1

/-- The SAME original finite closed geometric comap ideal has its true Euler degree scaled by native generic rank. -/
theorem degree_comap_toModules {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X]
    (f : Y ⟶ X) [IsFinite f] [Flat f]
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (I : X.IdealSheafData) [IsFinite (I.subschemeι ≫ p)] :
    letI : IsProper p := hp.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    letI : IsProper (f ≫ p) := (finite_comp_projectiveFactorization p hp f).isProper
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ p)
    degree (f ≫ p) (I.comap f).toModules = (f.finrank (genericPoint X) : ℤ) * degree p I.toModules := by
  let : IsProper p := hp.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hq := finite_comp_projectiveFactorization p hp f
  let : IsProper (f ≫ p) := hq.isProper
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ p)
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from (f ≫ p)]; infer_instance⟩
  let := SchemeFiniteFlatDegrees.comapSubscheme_isFinite f p I
  change normalizedEulerCharacteristic _ _ = _ * normalizedEulerCharacteristic _ _
  rw [GeometricIdealEulerDegree.normalizedEulerCharacteristic_toModules _ _ hq,
    GeometricIdealEulerDegree.normalizedEulerCharacteristic_toModules _ _ hp]
  have h := SchemeFiniteFlatDegrees.finrank_fieldSections_comap f p hp I
  rw [show (I.comap f).subschemeι ≫ f ≫ p = (I.comap f).subschemeι ≫ (f ≫ p) from rfl] at h
  rw [h, Nat.cast_mul]
  ring

/-- Actual flat pullback of the SAME original finite Cartier ratio scales its genuine full Euler degree. -/
theorem degree_pullback_ratio {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X]
    (f : Y ⟶ X) [IsFinite f] [Flat f]
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (I J : X.IdealSheafData) (hI : I.IsInvertible) (hJ : J.IsInvertible)
    [IsFinite (I.subschemeι ≫ p)] [IsFinite (J.subschemeι ≫ p)] :
    letI : IsProper p := hp.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    letI : IsProper (f ≫ p) := (finite_comp_projectiveFactorization p hp f).isProper
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ p)
    degree (f ≫ p) ((Scheme.Modules.pullback f).obj (I.ratioModule J)) =
      (f.finrank (genericPoint X) : ℤ) * degree p (I.ratioModule J) := by
  let : IsProper p := hp.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have hq := finite_comp_projectiveFactorization p hp f
  let : IsProper (f ≫ p) := hq.isProper
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ p)
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from (f ≫ p)]; infer_instance⟩
  let := SchemeFiniteFlatDegrees.comapSubscheme_isFinite f p I
  let := SchemeFiniteFlatDegrees.comapSubscheme_isFinite f p J
  rw [degree_eq_of_iso _ (CurveLineDegreeBaseChange.ratioPullbackComapIso f I J hI hJ)]
  change normalizedEulerCharacteristic _ _ = _ * normalizedEulerCharacteristic _ _
  rw [GeometricIdealEulerDegree.normalizedEulerCharacteristic_ratioModule _ _ (hJ.comap_of_flat f) _ hq,
    GeometricIdealEulerDegree.normalizedEulerCharacteristic_ratioModule I J hJ p hp]
  have hi := degree_comap_toModules f p hp I
  have hj := degree_comap_toModules f p hp J
  change normalizedEulerCharacteristic (f ≫ p) (I.comap f).toModules =
    _ * normalizedEulerCharacteristic p I.toModules at hi
  change normalizedEulerCharacteristic (f ≫ p) (J.comap f).toModules =
    _ * normalizedEulerCharacteristic p J.toModules at hj
  rw [hi, hj, mul_sub]

/-- EVERY SAME original invertible curve line has its TRUE degree scaled by
the native generic rank of the SAME finite flat map; no source regularity or line comparison premise. -/
theorem degree_pullback {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X]
    (f : Y ⟶ X) [IsFinite f] [Flat f]
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules) (hL : IsInvertible L) :
    letI : IsProper p := hp.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    letI : IsProper (f ≫ p) := (finite_comp_projectiveFactorization p hp f).isProper
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ p)
    degree (f ≫ p) ((Scheme.Modules.pullback f).obj L) =
      (f.finrank (genericPoint X) : ℤ) * degree p L := by
  let : IsProper p := hp.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsProper (f ≫ p) := (finite_comp_projectiveFactorization p hp f).isProper
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ p)
  obtain ⟨I, J, hI, hJ, ⟨e⟩⟩ := ProjectiveLineCartierRatio.exists_cartier_ratio p hp L hL
  let : IsFinite (I.subschemeι ≫ p) := CurveCartierIdealDegrees.subscheme_comp_isFinite p hdim I hI
  let : IsFinite (J.subschemeι ≫ p) := CurveCartierIdealDegrees.subscheme_comp_isFinite p hdim J hJ
  rw [degree_eq_of_iso _ ((Scheme.Modules.pullback f).mapIso e), degree_eq_of_iso p e]
  exact degree_pullback_ratio f p hp I J hI hJ

/-- Actual normal curve geometry internally derives flatness of the SAME original finite dominant map. -/
theorem degree_pullback_of_normalCurve {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) [IsFinite f] [IsDominant f]
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim X ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (L : X.Modules) (hL : IsInvertible L) :
    letI : IsProper p := hp.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    letI : IsProper (f ≫ p) := (finite_comp_projectiveFactorization p hp f).isProper
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ p)
    degree (f ≫ p) ((Scheme.Modules.pullback f).obj L) =
      (f.finrank (genericPoint X) : ℤ) * degree p L := by
  let : IsProper p := hp.isProper
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let := NormalCurveDominantFlat.flat f hdim hNormal
  exact degree_pullback f p hp hdim L hL

/-- Actual dominance derives strict positivity of the SAME original finite normal-curve map's native generic rank. -/
theorem genericRank_pos {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] (f : Y ⟶ X) [IsFinite f] [IsDominant f]
    (hdim : topologicalKrullDim X ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    0 < f.finrank (genericPoint X) := by
  let := NormalCurveDominantFlat.flat f hdim hNormal
  have h := Scheme.Hom.one_le_finrank_map f (genericPoint Y)
  rw [DominantFunctionFieldMaps.genericPoint_map f] at h
  exact h

/-- Nonnegative degree of EVERY SAME original line is detected by its TRUE
pullback to the SAME actual finite dominant normal-curve map, with positive factor derived. -/
theorem degree_pullback_nonneg_iff_of_normalCurve {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) [IsFinite f] [IsDominant f]
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim X ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (L : X.Modules) (hL : IsInvertible L) :
    letI : IsProper p := hp.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    letI : IsProper (f ≫ p) := (finite_comp_projectiveFactorization p hp f).isProper
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ p)
    0 ≤ degree (f ≫ p) ((Scheme.Modules.pullback f).obj L) ↔ 0 ≤ degree p L := by
  let : IsProper p := hp.isProper
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsProper (f ≫ p) := (finite_comp_projectiveFactorization p hp f).isProper
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ p)
  rw [degree_pullback_of_normalCurve f p hp hdim hNormal L hL]
  have h : (0 : ℤ) < f.finrank (genericPoint X) := by exact_mod_cast genericRank_pos f hdim hNormal
  exact mul_nonneg_iff_of_pos_left h

end EnvelopeProperty.CurveFiniteMapDegrees
