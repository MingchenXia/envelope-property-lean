import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationCartierTrivialization
import EnvelopeProperty.Global.NativeTestConfigurationFibreOneCompatibility

/-! # Actual original action/fibre geometry for model polarization transport

All schemes, original actions, actual fibre-one data and the whole unit-open
trivialization remain the original native ones. The whole unit-open module
comparison will be DERIVED from source linearization, not supplied.
-/

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj LaurentPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open NativeTestConfiguration Scheme.Modules CanonicalGeometry
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X)

/-- The actual original total-model action over the same original field. -/
def originalTestConfigurationTotalAction :
    ProjBerk.nativeMultiplicativeGroup k ⊗ totalOver k C.projection ⟶
      totalOver k C.projection := by
  let := C.action
  exact ModObj.smul (M := ProjBerk.nativeMultiplicativeGroup k)
    (X := totalOver k C.projection)

/-- The actual DERIVED fibre product iso followed by the SAME original
fibre-one inclusion; this is an actual map into the source action space. -/
def originalTestConfigurationActionFibreMap : C.unitOpenOver ⟶
    ProjBerk.nativeMultiplicativeGroup k ⊗ totalOver k C.projection :=
  C.unitOpenFibreIso.hom ≫
    (ProjBerk.nativeMultiplicativeGroup k ◁ C.fibreOneInclusion)

/-- The actual original whole-unit-open projection onto its SAME fibre one. -/
def originalTestConfigurationFibreProjection : C.unitOpenOver ⟶
    fibreOneOver k C.projection :=
  C.unitOpenFibreIso.hom ≫
    snd (ProjBerk.nativeMultiplicativeGroup k) (fibreOneOver k C.projection)

/-- The actual source-action-space second projection factors through the
SAME original fibre-one inclusion on the entire original unit open. -/
theorem originalTestConfigurationActionFibreMap_snd :
    originalTestConfigurationActionFibreMap C ≫
        snd (ProjBerk.nativeMultiplicativeGroup k) (totalOver k C.projection) =
      originalTestConfigurationFibreProjection C ≫ C.fibreOneInclusion := by
  simp only [originalTestConfigurationActionFibreMap,
    originalTestConfigurationFibreProjection, Category.assoc, whiskerLeft_snd]

/-- The actual source action composed with the constructed fibre-action
map is EXACTLY the SAME original whole unit-open inclusion. -/
theorem originalTestConfigurationActionFibreMap_action :
    originalTestConfigurationActionFibreMap C ≫ originalTestConfigurationTotalAction C =
      C.unitOpenInclusion := by
  let := C.action
  let := C.groupPullbackModObj
  let : ModObj (ProjBerk.nativeMultiplicativeGroup k)
      (ProjBerk.nativeMultiplicativeGroup k) := ModObj.regular _
  let : IsModHom (ProjBerk.nativeMultiplicativeGroup k) C.groupPullbackParameter :=
    C.groupPullbackParameter_isModHom
  let : IsModHom (ProjBerk.nativeMultiplicativeGroup k) C.groupPullbackProjection :=
    C.groupPullbackProjection_isModHom
  have h : (ProjBerk.nativeMultiplicativeGroup k ◁ C.fibreOneInclusion) ≫
      originalTestConfigurationTotalAction C =
      C.groupPullbackFibreIso.inv ≫ C.groupPullbackProjection := by
    change _ =
      ((fst (ProjBerk.nativeMultiplicativeGroup k) (fibreOneOver k C.projection)) •
        (snd (ProjBerk.nativeMultiplicativeGroup k) (fibreOneOver k C.projection) ≫
          C.fibreOneGroupLift)) ≫ C.groupPullbackProjection
    rw [IsModHom.map_smul]
    simp only [Category.assoc, C.fibreOneGroupLift_projection]
    change (ProjBerk.nativeMultiplicativeGroup k ◁ C.fibreOneInclusion) ≫
      ModObj.smul (M := ProjBerk.nativeMultiplicativeGroup k)
        (X := totalOver k C.projection) = _
    rw [Hom.smul_def]
    congr 1
  change (C.unitOpenFibreIso.hom ≫
    (ProjBerk.nativeMultiplicativeGroup k ◁ C.fibreOneInclusion)) ≫
      originalTestConfigurationTotalAction C = _
  rw [Category.assoc, h]
  simp only [NativeTestConfiguration.TestConfiguration.unitOpenFibreIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact C.groupPullbackOpenIso_inv_projection

/-- The actual original fibre projection followed by the ORIGINAL
fibre-one identification is exactly the frozen whole unit-open projection. -/
theorem originalTestConfigurationFibreProjection_original :
    (originalTestConfigurationFibreProjection C ≫ C.fibreOneIso.hom).left =
      originalTestConfigurationUnitProjection C := by
  change (C.unitOpenFibreIso.hom ≫
      snd (ProjBerk.nativeMultiplicativeGroup k) (fibreOneOver k C.projection) ≫
        C.fibreOneIso.hom).left =
    (C.unitOpenIso.hom ≫ fst X (ProjBerk.nativeMultiplicativeGroup k)).left
  simp only [NativeTestConfiguration.TestConfiguration.unitOpenIso, Iso.trans_hom,
    Category.assoc, braiding_hom_fst, whiskerLeftIso_hom, whiskerLeft_snd]

/-- A true source linearization and a true original fibre identification
construct the whole pullback comparison through actual geometric morphism
identities. No comparison on U is supplied. -/
def originalLinearizedFibrePullbackIso
    {Y U A F V : Scheme.{u}} (j : U ⟶ Y) (a b : A ⟶ Y) (t : U ⟶ A)
    (i : F ⟶ Y) (r : U ⟶ F) (e : F ⟶ V) (p : U ⟶ V)
    (hact : t ≫ a = j) (hsnd : t ≫ b = r ≫ i) (hp : r ≫ e = p)
    (M : Y.Modules) (L : V.Modules)
    (linearization : (Scheme.Modules.pullback a).obj M ≅
      (Scheme.Modules.pullback b).obj M)
    (fibreIdentification : (Scheme.Modules.pullback i).obj M ≅
      (Scheme.Modules.pullback e).obj L) :
    (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback p).obj L := by
  let eAction : (Scheme.Modules.pullback j).obj M ≅
      (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback a).obj M) :=
    ((Scheme.Modules.pullbackCongr hact.symm).app M) ≪≫
      ((Scheme.Modules.pullbackComp t a).app M).symm
  let eFibre : (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback b).obj M) ≅
      (Scheme.Modules.pullback r).obj ((Scheme.Modules.pullback i).obj M) :=
    ((Scheme.Modules.pullbackComp t b).app M) ≪≫
      ((Scheme.Modules.pullbackCongr hsnd).app M) ≪≫
        ((Scheme.Modules.pullbackComp r i).app M).symm
  let eProjection : (Scheme.Modules.pullback r).obj
      ((Scheme.Modules.pullback e).obj L) ≅ (Scheme.Modules.pullback p).obj L :=
    ((Scheme.Modules.pullbackComp r e).app L) ≪≫
      ((Scheme.Modules.pullbackCongr hp).app L)
  exact eAction ≪≫ (Scheme.Modules.pullback t).mapIso linearization ≪≫ eFibre ≪≫
    (Scheme.Modules.pullback r).mapIso fibreIdentification ≪≫ eProjection

/-- The SAME original total-model polarization on the whole unit open is
identified with the SAME original p*L. Only original SOURCE data are supplied:
linearization on the full action space, and the original fibre-one module
identification. The whole-unit-open comparison itself is DERIVED. -/
def originalTestConfigurationPolarizationUnitIso
    (M : C.total.Modules) (L : X.left.Modules)
    (linearization :
      (Scheme.Modules.pullback (originalTestConfigurationTotalAction C).left).obj M ≅
        (Scheme.Modules.pullback
          (snd (ProjBerk.nativeMultiplicativeGroup k) (totalOver k C.projection)).left).obj M)
    (fibreOneIdentification :
      (Scheme.Modules.pullback C.fibreOneInclusion.left).obj M ≅
        (Scheme.Modules.pullback C.fibreOneIso.hom.left).obj L) :
    (Scheme.Modules.pullback C.unitOpen.ι).obj M ≅
      (Scheme.Modules.pullback (originalTestConfigurationUnitProjection C)).obj L :=
  originalLinearizedFibrePullbackIso C.unitOpen.ι
    (originalTestConfigurationTotalAction C).left
    (snd (ProjBerk.nativeMultiplicativeGroup k) (totalOver k C.projection)).left
    (originalTestConfigurationActionFibreMap C).left C.fibreOneInclusion.left
    (originalTestConfigurationFibreProjection C).left C.fibreOneIso.hom.left
    (originalTestConfigurationUnitProjection C)
    (congrArg (fun f => f.left) (originalTestConfigurationActionFibreMap_action C))
    (congrArg (fun f => f.left) (originalTestConfigurationActionFibreMap_snd C))
    (originalTestConfigurationFibreProjection_original C) M L
    linearization fibreOneIdentification

/-- The actual original total-model polarization tensor powers retain the
DERIVED whole original unit-open comparison, in every degree including zero. -/
def originalTestConfigurationModelPowerUnitIso
    (M : C.total.Modules) (L : X.left.Modules)
    (linearization :
      (Scheme.Modules.pullback (originalTestConfigurationTotalAction C).left).obj M ≅
        (Scheme.Modules.pullback
          (snd (ProjBerk.nativeMultiplicativeGroup k) (totalOver k C.projection)).left).obj M)
    (fibreOneIdentification :
      (Scheme.Modules.pullback C.fibreOneInclusion.left).obj M ≅
        (Scheme.Modules.pullback C.fibreOneIso.hom.left).obj L) (m : ℕ) :
    (Scheme.Modules.pullback C.unitOpen.ι).obj (bundleTensorPower M m) ≅
      (Scheme.Modules.pullback (originalTestConfigurationUnitProjection C)).obj
        (bundleTensorPower L m) :=
  TestConfigurationSectionTransport.polarizationPowerIso C.unitOpen.ι
    (originalTestConfigurationUnitProjection C) M L
    (originalTestConfigurationPolarizationUnitIso C M L linearization fibreOneIdentification) m

/-- True base-linear whole-section transport of every SAME original model
power over exactly the SAME original Laurent parameter map. -/
def originalTestConfigurationModelPowerSectionsIso
    (M : C.total.Modules) (L : X.left.Modules)
    (linearization :
      (Scheme.Modules.pullback (originalTestConfigurationTotalAction C).left).obj M ≅
        (Scheme.Modules.pullback
          (snd (ProjBerk.nativeMultiplicativeGroup k) (totalOver k C.projection)).left).obj M)
    (fibreOneIdentification :
      (Scheme.Modules.pullback C.fibreOneInclusion.left).obj M ≅
        (Scheme.Modules.pullback C.fibreOneIso.hom.left).obj L) (m : ℕ) :
    originalBaseSections (originalTestConfigurationUnitParameter C)
        ((Scheme.Modules.pullback C.unitOpen.ι).obj (bundleTensorPower M m)) ≅
      originalBaseSections (originalTestConfigurationUnitParameter C)
        ((Scheme.Modules.pullback (originalTestConfigurationUnitProjection C)).obj
          (bundleTensorPower L m)) :=
  originalBaseWholeModuleIso (originalTestConfigurationUnitParameter C)
    (originalTestConfigurationModelPowerUnitIso C M L linearization fibreOneIdentification m)

/-- EVERY original whole section of EVERY actual original total-model power
on the SAME unit open has UNIQUE finite ORIGINAL Laurent coefficients.
Neither a whole-unit-open polarization comparison nor a decomposition is input. -/
theorem exists_unique_original_testConfiguration_model_power_laurent_expansion
    [IsProper X.hom] (M : C.total.Modules) (L : X.left.Modules)
    (hL : Scheme.Modules.IsInvertible L)
    (linearization :
      (Scheme.Modules.pullback (originalTestConfigurationTotalAction C).left).obj M ≅
        (Scheme.Modules.pullback
          (snd (ProjBerk.nativeMultiplicativeGroup k) (totalOver k C.projection)).left).obj M)
    (fibreOneIdentification :
      (Scheme.Modules.pullback C.fibreOneInclusion.left).obj M ≅
        (Scheme.Modules.pullback C.fibreOneIso.hom.left).obj L) (m : ℕ)
    (s : originalBaseSections (originalTestConfigurationUnitParameter C)
      ((Scheme.Modules.pullback C.unitOpen.ι).obj (bundleTensorPower M m))) :
    ∃! c : ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m),
      c.sum (fun n a => (LaurentPolynomial.T n : k[T;T⁻¹]) •
        (originalTestConfigurationModelPowerSectionsIso C M L linearization
          fibreOneIdentification m).inv
          (show originalBaseSections (originalTestConfigurationUnitParameter C)
            ((Scheme.Modules.pullback (originalTestConfigurationUnitProjection C)).obj
              (bundleTensorPower L m)) from
            affinePullbackUnitTop (originalTestConfigurationUnitProjection C)
              (bundleTensorPower L m) a)) = s := by
  let e := originalTestConfigurationModelPowerSectionsIso C M L linearization
    fibreOneIdentification m
  have hsum (c : ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m)) :
      e.hom (c.sum (fun n a => (LaurentPolynomial.T n : k[T;T⁻¹]) • e.inv
        (show originalBaseSections (originalTestConfigurationUnitParameter C)
          ((Scheme.Modules.pullback (originalTestConfigurationUnitProjection C)).obj
            (bundleTensorPower L m)) from
          affinePullbackUnitTop (originalTestConfigurationUnitProjection C)
            (bundleTensorPower L m) a))) =
      c.sum (fun n a => (LaurentPolynomial.T n : k[T;T⁻¹]) •
        (show originalBaseSections (originalTestConfigurationUnitParameter C)
          ((Scheme.Modules.pullback (originalTestConfigurationUnitProjection C)).obj
            (bundleTensorPower L m)) from
          affinePullbackUnitTop (originalTestConfigurationUnitProjection C)
            (bundleTensorPower L m) a)) := by
    simp only [Finsupp.sum, map_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    exact (e.hom.hom.map_smul _ _).trans
      (congrArg (fun a => (LaurentPolynomial.T n : k[T;T⁻¹]) • a)
        (ConcreteCategory.congr_hom e.inv_hom_id _))
  obtain ⟨c, hc, huniq⟩ :=
    exists_unique_original_testConfiguration_unit_power_laurent_expansion C L hL m (e.hom s)
  refine ⟨c, ?_, ?_⟩
  · apply (ConcreteCategory.bijective_of_isIso e.hom).1
    change e.hom (c.sum (fun n a => (LaurentPolynomial.T n : k[T;T⁻¹]) • e.inv
      (show originalBaseSections (originalTestConfigurationUnitParameter C)
        ((Scheme.Modules.pullback (originalTestConfigurationUnitProjection C)).obj
          (bundleTensorPower L m)) from
        affinePullbackUnitTop (originalTestConfigurationUnitProjection C)
          (bundleTensorPower L m) a))) = e.hom s
    rw [hsum]
    exact hc
  · intro d hd
    apply huniq d
    rw [← hsum]
    exact congrArg (fun a => e.hom a) hd

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
