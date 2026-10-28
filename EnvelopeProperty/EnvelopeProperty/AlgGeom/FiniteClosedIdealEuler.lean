import EnvelopeProperty.AlgGeom.SchemeCoherentEulerAffine
import ModularCurves.EllipticCurve.PoleSheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Genuine finite closed-ideal Euler formula on the SAME original scheme -/
open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FiniteClosedIdealEuler
open SchemeCoherentEulerIndex SchemeCoherentEulerCharacteristic SchemeCoherentEulerAffine
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X D : Scheme.{u}}

private theorem structureQuasicoherent (Y : Scheme.{u}) :
    SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) (unitObj Y) := by
  let e : SheafOfModules.free.{u} (R := Y.ringCatSheaf) PUnit ≅ SheafOfModules.unit.{u} Y.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit.{u} Y.ringCatSheaf)
  obtain ⟨q⟩ := SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData
    (M := SheafOfModules.free.{u} (R := Y.ringCatSheaf) PUnit)
  exact (SheafOfModules.QuasicoherentData.ofIsIso.{u, u, u, u}
    (R := Y.ringCatSheaf) e.hom q).isQuasicoherent

private theorem structureFiniteType (Y : Scheme.{u}) :
    SheafOfModules.IsFiniteType (R := Y.ringCatSheaf) (unitObj Y) := by
  let e : SheafOfModules.free.{u} (R := Y.ringCatSheaf) PUnit ≅ SheafOfModules.unit.{u} Y.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit.{u} Y.ringCatSheaf)
  let G := SheafOfModules.free.generatingSections (R := Y.ringCatSheaf) PUnit
  have : IsIso e.hom := inferInstance
  let H := G.ofEpi e.hom
  let q : SheafOfModules.LocalGeneratorsData.{u} (R := Y.ringCatSheaf) (unitObj Y) :=
    H.localGeneratorsData
  have hq : SheafOfModules.LocalGeneratorsData.IsFiniteType (R := Y.ringCatSheaf) q := by
    constructor
    intro V
    constructor
    change Finite PUnit
    infer_instance
  exact SheafOfModules.IsFiniteType.mk (R := Y.ringCatSheaf) ⟨q, hq⟩

/-- The actual original whole structure-module map of the original closed immersion. -/
abbrev quotientMap (g : D ⟶ X) : unitObj X ⟶ (pushforward g).obj (unitObj D) :=
  SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom

/-- Actual affine section surjectivity gives true sheaf local surjectivity of the ORIGINAL map. -/
theorem quotientMap_isLocallySurjective (g : D ⟶ X) [IsClosedImmersion g] :
    Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf X.ringCatSheaf).map (quotientMap g)) := by
  constructor
  intro W s x hx
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := W) (x := x) hx
  refine ⟨V, homOfLE hVW, ?_, hxV⟩
  exact g.app_surjective V hV _

/-- The actual original closed quotient map is a true module-sheaf epimorphism. -/
instance quotientMap_epi (g : D ⟶ X) [IsClosedImmersion g] : Epi (quotientMap g) := by
  let := quotientMap_isLocallySurjective g
  exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map inferInstance

/-- The SAME actual native ideal, original structure line and true quotient form the actual sequence. -/
abbrev sequence (g : D ⟶ X) : ShortComplex X.Modules :=
  ShortComplex.mk (ModularCurves.idealModuleToUnit g) (quotientMap g)
    (kernel.condition (quotientMap g))

/-- The actual original whole native ideal sequence is genuinely short exact. -/
theorem sequence_shortExact (g : D ⟶ X) [IsClosedImmersion g] : (sequence g).ShortExact :=
  { exact := ShortComplex.exact_kernel (quotientMap g)
    mono_f := by change Mono (kernel.ι (quotientMap g)); infer_instance
    epi_g := quotientMap_epi g }

/-- The SAME original closed subscheme has genuinely finite-dimensional actual global sections. -/
theorem fieldSections_finite (g : D ⟶ X) [IsClosedImmersion g]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f) :
    Module.Finite k (SchemeCoherentEulerIndex.fieldSections (g ≫ f) (unitObj D)) := by
  let : (unitObj D).IsQuasicoherent := structureQuasicoherent D
  let : (unitObj D).IsFiniteType := structureFiniteType D
  let Q := (pushforward g).obj (unitObj D)
  let : Q.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom g
  let : Q.IsFiniteType := isFiniteType_pushforward_of_isClosedImmersion g
  let : Module.Finite k ((ModuleCat.restrictScalars (baseScalar (k := k))).obj
      (baseSections f ((pushforward g).obj (unitObj D)))) :=
    SchemeCoherentEulerIndex.fieldSections_finite f hf Q
  exact Module.Finite.equiv
    ((ModuleCat.restrictScalars (baseScalar (k := k))).mapIso
      (baseSectionsPushforwardIso g f (unitObj D))).symm.toLinearEquiv

/-- The actual native ideal of a finite closed subscheme has normalized
Euler characteristic minus its TRUE original field degree. Every finiteness,
quasicoherence, exactness and affine comparison is derived from actual geometry. -/
theorem normalizedEulerCharacteristic_idealModule (g : D ⟶ X) [IsClosedImmersion g]
    [CompactSpace X] [X.IsSeparated] (f : X ⟶ Spec (.of k))
    (hf : IsProjectiveFactorization f) [IsFinite (g ≫ f)] :
    normalizedEulerCharacteristic f (ModularCurves.idealModule g) =
      -(Module.finrank k (SchemeCoherentEulerIndex.fieldSections (g ≫ f) (unitObj D)) : ℤ) := by
  let : IsProper f := hf.isProper
  let : LocallyOfFiniteType f := inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsAffine D := isAffine_of_isAffineHom (g ≫ f)
  let : (unitObj D).IsQuasicoherent := structureQuasicoherent D
  let : (unitObj D).IsFiniteType := structureFiniteType D
  let Q := (pushforward g).obj (unitObj D)
  let : Q.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom g
  let : Q.IsFiniteType := isFiniteType_pushforward_of_isClosedImmersion g
  let : (unitObj X).IsQuasicoherent := structureQuasicoherent X
  let : (unitObj X).IsFiniteType := structureFiniteType X
  let : (ModularCurves.idealModule g).IsQuasicoherent := isQuasicoherent_kernel (quotientMap g)
  let : (ModularCurves.idealModule g).IsFiniteType := isFiniteType_kernel (quotientMap g)
  have h := eulerCharacteristic_add f hf (sequence g) (sequence_shortExact g)
  have hp := eulerCharacteristic_pushforward g f (unitObj D)
  have hd := eulerCharacteristic_eq_finrank_sections (g ≫ f) (unitObj D)
  unfold normalizedEulerCharacteristic
  change eulerCharacteristic f (ModularCurves.idealModule g) - eulerCharacteristic f (unitObj X) = _
  change eulerCharacteristic f (unitObj X) =
    eulerCharacteristic f (ModularCurves.idealModule g) + eulerCharacteristic f Q at h
  change eulerCharacteristic (g ≫ f) (unitObj D) = eulerCharacteristic f Q at hp
  rw [← hp, hd] at h
  omega

/-- Actual isomorphic finite closed ideals have the SAME true original field degree. -/
theorem finrank_eq_of_idealModule_iso {E : Scheme.{u}} (g : D ⟶ X) (h : E ⟶ X)
    [IsClosedImmersion g] [IsClosedImmersion h] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    [IsFinite (g ≫ f)] [IsFinite (h ≫ f)]
    (e : ModularCurves.idealModule g ≅ ModularCurves.idealModule h) :
    Module.finrank k (SchemeCoherentEulerIndex.fieldSections (g ≫ f) (unitObj D)) =
      Module.finrank k (SchemeCoherentEulerIndex.fieldSections (h ≫ f) (unitObj E)) := by
  have he := normalizedEulerCharacteristic_eq_of_iso f e
  rw [normalizedEulerCharacteristic_idealModule g f hf,
    normalizedEulerCharacteristic_idealModule h f hf] at he
  omega

end EnvelopeProperty.FiniteClosedIdealEuler
