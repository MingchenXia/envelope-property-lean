import EnvelopeProperty.AlgGeom.SchemeFieldDegreeBaseChange
import EnvelopeProperty.AlgGeom.CurveLineDegrees
import EnvelopeProperty.AlgGeom.CartierRatioPullback
import EnvelopeProperty.Projective.FactorizationBaseChange

/-! # SAME original curve line degree under ANY original field extension -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.CurveLineDegreeBaseChange
open FlatGlobalSections SchemeCoherentEulerCharacteristic CurveLineDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k E : Type u} [Field k] [Field E] [Algebra k E]
    {X : Scheme.{u}}

private theorem scalarProjection_flat (p : X ⟶ Spec (.of k)) :
    Flat (firstProjection (S := E) p) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let : Flat b := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  infer_instance

/-- The genuine SAME original geometric comap finite ideal retains its intrinsic full Euler degree. -/
theorem degree_comap_toModules (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (I : X.IdealSheafData) [IsFinite (I.subschemeι ≫ p)] :
    letI : IsProper p := hp.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    letI : IsProper (structureMap (S := E) p) := (ProjectiveFactorizationBaseChange.baseChange p hp).isProper
    letI : CompactSpace (baseChange (S := E) p) :=
      QuasiCompact.compactSpace_of_compactSpace (structureMap (S := E) p)
    degree (structureMap (S := E) p) (I.comap (firstProjection (S := E) p)).toModules =
      degree p I.toModules := by
  let : IsProper p := hp.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have hq := ProjectiveFactorizationBaseChange.baseChange (S := E) p hp
  let : IsProper (structureMap (S := E) p) := hq.isProper
  let : CompactSpace (baseChange (S := E) p) :=
    QuasiCompact.compactSpace_of_compactSpace (structureMap (S := E) p)
  let : (baseChange (S := E) p).IsSeparated :=
    ⟨by rw [← terminal.comp_from (structureMap (S := E) p)]; infer_instance⟩
  let := SchemeFieldDegreeBaseChange.comapSubscheme_isFinite (E := E) p I
  change normalizedEulerCharacteristic _ _ = normalizedEulerCharacteristic _ _
  rw [GeometricIdealEulerDegree.normalizedEulerCharacteristic_toModules _ _ hq,
    GeometricIdealEulerDegree.normalizedEulerCharacteristic_toModules _ _ hp,
    SchemeFieldDegreeBaseChange.finrank_fieldSections_comapSubscheme]

/-- The true whole original Cartier line pullback retains its SAME intrinsic degree. -/
theorem degree_pullback_toModules (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (I : X.IdealSheafData) (hI : I.IsInvertible) [IsFinite (I.subschemeι ≫ p)] :
    letI : IsProper p := hp.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    letI : IsProper (structureMap (S := E) p) := (ProjectiveFactorizationBaseChange.baseChange p hp).isProper
    letI : CompactSpace (baseChange (S := E) p) :=
      QuasiCompact.compactSpace_of_compactSpace (structureMap (S := E) p)
    degree (structureMap (S := E) p)
      ((Scheme.Modules.pullback (firstProjection (S := E) p)).obj I.toModules) = degree p I.toModules := by
  let : IsProper p := hp.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsProper (structureMap (S := E) p) := (ProjectiveFactorizationBaseChange.baseChange p hp).isProper
  let : CompactSpace (baseChange (S := E) p) :=
    QuasiCompact.compactSpace_of_compactSpace (structureMap (S := E) p)
  let := scalarProjection_flat (E := E) p
  rw [degree_eq_of_iso _ (hI.flatPullbackModuleIso (firstProjection (S := E) p))]
  exact degree_comap_toModules p hp I

/-- Native true tensor/dual/Cartier pullbacks give the WHOLE ratio of the SAME geometric comap ideals. -/
def ratioPullbackComapIso {Y : Scheme.{u}} (f : Y ⟶ X) [Flat f]
    (I J : X.IdealSheafData) (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    (Scheme.Modules.pullback f).obj (I.ratioModule J) ≅ (I.comap f).ratioModule (J.comap f) :=
  I.ratioPullbackIso J hJ f ≪≫
    tensorObjCongr (hI.flatPullbackModuleIso f) (dualIsoObj (hJ.flatPullbackModuleIso f).symm)

/-- The SAME actual Cartier-ratio line has invariant intrinsic degree under ANY field extension. -/
theorem degree_pullback_ratio (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (I J : X.IdealSheafData) (hI : I.IsInvertible) (hJ : J.IsInvertible)
    [IsFinite (I.subschemeι ≫ p)] [IsFinite (J.subschemeι ≫ p)] :
    letI : IsProper p := hp.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    letI : IsProper (structureMap (S := E) p) := (ProjectiveFactorizationBaseChange.baseChange p hp).isProper
    letI : CompactSpace (baseChange (S := E) p) :=
      QuasiCompact.compactSpace_of_compactSpace (structureMap (S := E) p)
    degree (structureMap (S := E) p)
      ((Scheme.Modules.pullback (firstProjection (S := E) p)).obj (I.ratioModule J)) = degree p (I.ratioModule J) := by
  let : IsProper p := hp.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have hq := ProjectiveFactorizationBaseChange.baseChange (S := E) p hp
  let : IsProper (structureMap (S := E) p) := hq.isProper
  let : CompactSpace (baseChange (S := E) p) :=
    QuasiCompact.compactSpace_of_compactSpace (structureMap (S := E) p)
  let : (baseChange (S := E) p).IsSeparated :=
    ⟨by rw [← terminal.comp_from (structureMap (S := E) p)]; infer_instance⟩
  let := scalarProjection_flat (E := E) p
  let := SchemeFieldDegreeBaseChange.comapSubscheme_isFinite (E := E) p I
  let := SchemeFieldDegreeBaseChange.comapSubscheme_isFinite (E := E) p J
  rw [degree_eq_of_iso _ (ratioPullbackComapIso (firstProjection (S := E) p) I J hI hJ)]
  change normalizedEulerCharacteristic _ _ = normalizedEulerCharacteristic _ _
  rw [GeometricIdealEulerDegree.normalizedEulerCharacteristic_ratioModule _ _
      (hJ.comap_of_flat (firstProjection (S := E) p)) _ hq,
    GeometricIdealEulerDegree.normalizedEulerCharacteristic_ratioModule I J hJ p hp]
  exact congrArg₂ (fun a b : ℤ => a - b) (degree_comap_toModules p hp I)
    (degree_comap_toModules p hp J)

/-- EVERY SAME original line on ANY original integral projective curve has
its TRUE intrinsic degree preserved by ANY field extension. No reducedness or
integrality of the actual scalar-pulled scheme is assumed or needed. -/
theorem degree_pullback [IsIntegral X] (p : X ⟶ Spec (.of k))
    (hp : IsProjectiveFactorization p) (hdim : topologicalKrullDim X ≤ 1)
    (L : X.Modules) (hL : IsInvertible L) :
    letI : IsProper p := hp.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    letI : IsProper (structureMap (S := E) p) := (ProjectiveFactorizationBaseChange.baseChange p hp).isProper
    letI : CompactSpace (baseChange (S := E) p) :=
      QuasiCompact.compactSpace_of_compactSpace (structureMap (S := E) p)
    degree (structureMap (S := E) p) ((Scheme.Modules.pullback (firstProjection (S := E) p)).obj L) =
      degree p L := by
  let : IsProper p := hp.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsProper (structureMap (S := E) p) := (ProjectiveFactorizationBaseChange.baseChange p hp).isProper
  let : CompactSpace (baseChange (S := E) p) :=
    QuasiCompact.compactSpace_of_compactSpace (structureMap (S := E) p)
  obtain ⟨I, J, hI, hJ, ⟨e⟩⟩ := ProjectiveLineCartierRatio.exists_cartier_ratio p hp L hL
  let : IsFinite (I.subschemeι ≫ p) := CurveCartierIdealDegrees.subscheme_comp_isFinite p hdim I hI
  let : IsFinite (J.subschemeι ≫ p) := CurveCartierIdealDegrees.subscheme_comp_isFinite p hdim J hJ
  rw [degree_eq_of_iso _ ((Scheme.Modules.pullback (firstProjection (S := E) p)).mapIso e), degree_eq_of_iso p e]
  exact degree_pullback_ratio p hp I J hI hJ

end EnvelopeProperty.CurveLineDegreeBaseChange
