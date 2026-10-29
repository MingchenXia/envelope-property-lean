import EnvelopeProperty.Vanishing.RelativePositiveHodgeVanishing
import EnvelopeProperty.Vanishing.WittKodairaComparison

/-! # Original relative ample Kodaira under an actual Witt special-fibre isomorphism

The actual affine-base map supplies projectivity. Both original field structures,
the original line, and its whole positive cohomology are retained. The global
Witt decomposition is proved internally, with no caller DI certificate.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
universe u
namespace EnvelopeProperty.Vanishing.RelativeWittKodairaComparison
open Cartier CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem subsingleton_H_of_moduleIso {Y : Scheme.{u}} {M N : Y.Modules}
    (e : M ≅ N) (q : ℕ) (hN : Subsingleton (CategoryTheory.Sheaf.H N.sheaf q)) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf q) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology Y) q).mapIso
    ((SheafOfModules.toSheaf Y.ringCatSheaf).mapIso e)
  have hzero : Subsingleton ((CategoryTheory.Sheaf.functorH
      (_root_.Opens.grothendieckTopology Y) q).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N)) := hN
  let := hzero
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.hom).1 (Subsingleton.elim _ _)⟩

variable {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Xlift : Scheme.{u}}
    (fLift : Xlift ⟶ Spec (.of (DeligneIllusie.WittTwo.Ring p k)))
    (n : ℕ) [SmoothOfRelativeDimension n fLift] [IsSeparated fLift]

/-- The original absolute canonical twist vanishes for every actual relatively
ample line, transported through the actual field-compatible Witt special-fibre
isomorphism. No properness over the field or external DI input is supplied. -/
theorem kodaira_of_specialFibreIso (hn : n < p) {Y : Scheme.{u}}
    (fY : Y ⟶ Spec (.of k)) (gY : Y ⟶ Spec (.of R))
    (e : Y ≅ DeligneIllusieInput.specialFibre p k fLift)
    (he : e.hom ≫ DeligneIllusieInput.specialFibreStructure p k fLift = fY)
    (L : Y.Modules) (hL : SchemeLineAmpleness.IsAmple gY L) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (canonicalLineSheaf fY n ⊗ L : Y.Modules).sheaf (q + 1)) := by
  let f₀ := DeligneIllusieInput.specialFibreStructure p k fLift
  let g₀ := e.inv ≫ gY
  let L₀ := (Scheme.Modules.pullback e.inv).obj L
  have hL₀ : SchemeLineAmpleness.IsAmple g₀ L₀ :=
    SchemeIsoGeometry.isAmple_pullback e.symm gY hL
  let : SmoothOfRelativeDimension n f₀ :=
    DeligneIllusieInput.specialFibre_smoothOfRelativeDimension p k fLift n
  have hW : Subsingleton (CategoryTheory.Sheaf.H
      (canonicalLineSheaf f₀ n ⊗ L₀).sheaf (q + 1)) :=
    RelativePositiveHodgeVanishing.kodaira_of_wittLift p fLift n hn g₀ L₀ hL₀ q
  let : (canonicalLineSheaf f₀ n).IsQuasicoherent :=
    SmoothExteriorFiniteType.isQuasicoherent f₀ n n
  let : (canonicalLineSheaf f₀ n ⊗ L₀).IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight
      (canonicalLineSheaf f₀ n) L₀ hL₀.isInvertible
  have hpull : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback e.hom).obj (canonicalLineSheaf f₀ n ⊗ L₀)).sheaf
        (q + 1)) :=
    (SchemeIsoGeometry.pullback_subsingleton_H_iff e g₀ hL₀.isProjectiveFactorization
      (canonicalLineSheaf f₀ n ⊗ L₀) q).mpr hW
  exact subsingleton_H_of_moduleIso
    (WittKodairaComparison.canonicalOriginalLineIso e fY f₀ he L n).symm
    (q + 1) hpull

/-- The same original relative ample Kodaira theorem in the explicit sheafified
coherent tensor object, retaining the original affine-base and field maps. -/
theorem kodaira_tensorObj_of_specialFibreIso (hn : n < p) {Y : Scheme.{u}}
    (fY : Y ⟶ Spec (.of k)) (gY : Y ⟶ Spec (.of R))
    (e : Y ≅ DeligneIllusieInput.specialFibre p k fLift)
    (he : e.hom ≫ DeligneIllusieInput.specialFibreStructure p k fLift = fY)
    (L : Y.Modules) (hL : SchemeLineAmpleness.IsAmple gY L) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (Scheme.Modules.tensorObj (canonicalLineSheaf fY n) L).sheaf (q + 1)) := by
  exact subsingleton_H_of_moduleIso
    (ModularCurves.monoidalTensorObjIso (canonicalLineSheaf fY n) L).symm (q + 1)
      (kodaira_of_specialFibreIso p fLift n hn fY gY e he L hL q)

end EnvelopeProperty.Vanishing.RelativeWittKodairaComparison
