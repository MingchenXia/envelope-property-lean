import EnvelopeProperty.AlgGeom.ProjectiveHomogeneousSections
import EnvelopeProperty.AlgGeom.LineSectionZeroIdeal
import EnvelopeProperty.Berkovich.SchemeLinePullbackSections

/-! # Actual zero-ideal support of the same original homogeneous section and its closed pullback -/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial HomogeneousLocalization
open Scheme.Modules
universe u

namespace EnvelopeProperty.ProjectiveHomogeneousSectionZeroLocus

open SchemeLineSectionEvaluation
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem sectionHom_atOne {X : Scheme.{u}} {M : X.Modules}
    (α : unitObj X ⟶ M) :
    SchemeModuleGlobalSections.sectionHom M (α.val.app (op ⊤) (1 : Γ(X, ⊤))) = α := by
  apply M.unitHomEquiv.injective
  change M.unitHomEquiv (M.unitHomEquiv.symm (ModularCurves.moduleSectionsOfTop M
    (α.val.app (op ⊤) (1 : Γ(X, ⊤))))) = M.unitHomEquiv α
  rw [Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro V
  let a := (homOfLE (show V.unop ≤ (⊤ : X.Opens) from le_top)).op
  have h := PresheafOfModules.naturality_apply α.val a (1 : Γ(X, ⊤))
  change α.val.app V (X.presheaf.map a (1 : Γ(X, ⊤))) =
    M.presheaf.map a (α.val.app (op ⊤) (1 : Γ(X, ⊤))) at h
  rw [map_one] at h
  exact h.symm

private theorem unitEndomorphism_atOne {X : Scheme.{u}} (r : Γ(X, ⊤)) :
    (ModularCurves.unitEndomorphismOfTopSection r).val.app (op ⊤) (1 : Γ(X, ⊤)) = r := by
  rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
  simp only [homOfLE_refl, op_id, one_mul]
  change (X.presheaf.map (𝟙 (op (⊤ : X.Opens)))).hom r = r
  rw [X.presheaf.map_id]
  rfl

private theorem affineOpenTopSection_eq {X : Scheme.{u}} (U : X.affineOpens) (c : Γ(X, U.1)) :
    ModularCurves.affineOpenTopSection U c = U.1.topIso.inv.hom c := by
  rw [ModularCurves.affineOpenTopSection, Scheme.Opens.ι_appIso]
  rfl

/-- The actual whole pullback-frame scalar determines the SAME original affine zero ideal. -/
theorem zeroIdeal_ideal_of_pullbackFrame {X : Scheme.{u}} (M : X.Modules) (hM : IsInvertible M)
    (α : unitObj X ⟶ M) (U : X.affineOpens)
    (e : (Scheme.Modules.pullback U.1.ι).obj M ≅ unitObj U.1.toScheme)
    (r : Γ(U.1.toScheme, ⊤))
    (hr : pullbackSectionHom U.1.ι α ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection r) :
    (LineSectionZeroIdeal.zeroIdeal M hM α).ideal U =
      Ideal.span ({U.1.topIso.hom.hom r} : Set Γ(X, U.1)) := by
  let s := α.val.app (op ⊤) (1 : Γ(X, ⊤))
  let eR := restrictIsoOfPullbackIso M U.1 e
  let eO := overTrivializationOfRestrictIso M U.1 eR
  rw [LineSectionZeroIdeal.zeroIdeal_ideal_of_frame M hM α U eO]
  apply congrArg (fun c : Γ(X, U.1) => Ideal.span ({c} : Set Γ(X, U.1)))
  have hres : α.val.app (op U.1) (1 : Γ(X, U.1)) =
      M.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s := by
    have h := PresheafOfModules.naturality_apply α.val
      (homOfLE (le_top : U.1 ≤ ⊤)).op (1 : Γ(X, ⊤))
    change α.val.app (op U.1) (X.presheaf.map _ (1 : Γ(X, ⊤))) =
      M.presheaf.map _ s at h
    simpa only [map_one] using h
  have hc : eO.hom.val.app (op (Over.mk (𝟙 U.1)))
      (α.val.app (op U.1) (1 : Γ(X, U.1))) =
        ModularCurves.localTrivializationCoefficient M U eR s := by
    rw [hres]
    exact ModularCurves.overTrivializationCoefficient_overTrivializationOfRestrictIso M U eR s
  have he : pullbackIsoOfRestrictIso M U.1 eR = e := by
    apply Iso.ext
    let c := restrictFunctorIsoPullback U.1.ι
    change (c.app M).inv ≫ (c.app M).hom ≫ e.hom = e.hom
    exact (c.app M).inv_hom_id_assoc e.hom
  have hs := SchemeLineSectionEvaluation.sectionHom_localScalar M U eR s
  have hα : SchemeModuleGlobalSections.sectionHom M s = α := sectionHom_atOne α
  rw [he, hα] at hs
  have hv := congrArg
    (fun a : unitObj U.1.toScheme ⟶ unitObj U.1.toScheme =>
      a.val.app (op ⊤) (1 : Γ(U.1.toScheme, ⊤))) (hs.symm.trans hr)
  rw [unitEndomorphism_atOne, unitEndomorphism_atOne] at hv
  have hv' := congrArg U.1.topIso.hom.hom hv
  rw [affineOpenTopSection_eq] at hv'
  exact hc.trans ((ConcreteCategory.congr_hom U.1.topIso.inv_hom_id _).symm.trans hv')

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The unit locus of the SAME original whole F/X_i is exactly the original D+(F) inside its original chart. -/
theorem coefficient_basicOpen_iff (i : Fin (n + 1))
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous 1)
    (x : Proj (homogeneousSubmodule (Fin (n + 1)) R)) (hx : x ∈ coordinateOpen (R := R) i) :
    x ∈ (Proj (homogeneousSubmodule (Fin (n + 1)) R)).basicOpen
      (ProjectiveHomogeneousSections.coefficient i 1 F hF) ↔
        x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F := by
  let G := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
  let U := coordinateOpen (R := R) i
  let a := ProjectiveHomogeneousSections.fraction i 1 F hF
  have ha : Away.isLocalizationElem (MvPolynomial.isHomogeneous_X R i) hF = a := by
    dsimp only [a]
    apply HomogeneousLocalization.val_injective
    simp only [Away.isLocalizationElem, ProjectiveHomogeneousSections.fraction, pow_one]
  have hcomp : Proj.basicOpenToSpec G (X i) ≫
      Proj.awayι G (X i) (MvPolynomial.isHomogeneous_X R i) (by decide : 0 < (1 : ℕ)) = U.ι := by
    change (Proj.basicOpenIsoSpec G (X i) (MvPolynomial.isHomogeneous_X R i) (by decide)).hom ≫
      (Proj.basicOpenIsoSpec G (X i) (MvPolynomial.isHomogeneous_X R i) (by decide)).inv ≫ U.ι = U.ι
    exact Iso.hom_inv_id_assoc _ _
  let y : U.toScheme := ⟨x, hx⟩
  let c := ProjectiveHomogeneousSections.coefficient i 1 F hF
  let z := Proj.basicOpenToSpec G (X i) y
  have hleft : U.toSpecΓ y ∈ PrimeSpectrum.basicOpen c ↔
      x ∈ (Proj G).basicOpen c := by
    exact Iff.of_eq (congrArg (fun V : U.toScheme.Opens => y ∈ V)
      (Scheme.Opens.toSpecΓ_preimage_basicOpen U c))
  have hmiddle : z ∈ PrimeSpectrum.basicOpen a ↔
      U.toSpecΓ y ∈ PrimeSpectrum.basicOpen c := by
    rfl
  have hright : z ∈ PrimeSpectrum.basicOpen a ↔ x ∈ Proj.basicOpen G F := by
    have h := Proj.awayι_preimage_basicOpen G (MvPolynomial.isHomogeneous_X R i)
      (by decide : 0 < (1 : ℕ)) hF (by decide : 0 < (1 : ℕ))
    rw [ha] at h
    have hm :
        Proj.awayι G (X i) (MvPolynomial.isHomogeneous_X R i) (by decide) z ∈ Proj.basicOpen G F ↔
          z ∈ PrimeSpectrum.basicOpen a :=
      Iff.of_eq (congrArg (fun V : (Spec (.of (Away G (X i)))).Opens => z ∈ V) h)
    have hp : Proj.awayι G (X i) (MvPolynomial.isHomogeneous_X R i) (by decide) z = x :=
      congrArg (fun f => f y) hcomp
    exact hm.symm.trans (by rw [hp])
  exact hleft.symm.trans (hmiddle.symm.trans hright)

/-- The actual whole native homogeneous section has its original coordinate fraction in its actual pullback frame. -/
theorem homogeneousSection_localScalar (i j : Fin (n + 1))
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous 1) :
    pullbackSectionHom (coordinateOpen (R := R) i).ι
      (ProjectiveHomogeneousSections.sectionHom j 1 F hF) ≫
      (pullbackIsoOfRestrictIso (coordinateHyperplaneTwist (R := R) j 1) (coordinateOpen (R := R) i)
        (coordinateHyperplaneTwistTrivialization (R := R) i j 1)).hom =
      ModularCurves.unitEndomorphismOfTopSection
        (Scheme.Modules.openTopSection (coordinateOpen (R := R) i)
          (ProjectiveHomogeneousSections.coefficient i 1 F hF)) := by
  let M := coordinateHyperplanePoleSheafPower (R := R) j 1
  let U : (Proj (homogeneousSubmodule (Fin (n + 1)) R)).affineOpens :=
    ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
  let e := coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j 1
  have hc : ModularCurves.localTrivializationCoefficient M U e
      (ProjectiveHomogeneousSections.homogeneousSection j 1 F hF) =
        ProjectiveHomogeneousSections.coefficient i 1 F hF :=
    (ModularCurves.overTrivializationCoefficient_overTrivializationOfRestrictIso M U e _).symm.trans
      (ProjectiveHomogeneousSections.section_coefficient i j 1 F hF)
  have h := SchemeLineSectionEvaluation.sectionHom_localScalar M U e
    (ProjectiveHomogeneousSections.homogeneousSection j 1 F hF)
  rw [hc] at h
  simpa only [M, U, e, ProjectiveHomogeneousSections.sectionHom,
    coordinateHyperplaneTwist, coordinateHyperplaneTwistTrivialization,
    ModularCurves.affineOpenTopSection, Scheme.Modules.openTopSection] using h

end EnvelopeProperty.ProjectiveHomogeneousSectionZeroLocus
