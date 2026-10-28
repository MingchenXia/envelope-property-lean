import EnvelopeProperty.Vanishing.PositiveHodgeVanishing
import EnvelopeProperty.Vanishing.SchemeIsoGeometry

/-! # Original Kodaira groups under an actual literal-special-fibre isomorphism

The only imported vanishing theorem input is the fixed-prime, fixed-field
Witt DI input. The original ample line, structural triangle, canonical
object and native cohomology comparison are constructed and retained.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section
universe u w w'

namespace EnvelopeProperty.Vanishing.WittKodairaComparison

open Cartier CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory

set_option backward.isDefEq.respectTransparency false

/-- The actual inverse pullbacks of the original module cancel through
native composition, the original inverse equation, and native identity pullback. -/
def inversePullbackLineIso {Y Z : Scheme.{u}} (e : Y ≅ Z) (L : Y.Modules) :
    (Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback e.inv).obj L) ≅ L :=
  (Scheme.Modules.pullbackComp e.hom e.inv).app L ≪≫
    (Scheme.Modules.pullbackCongr e.hom_inv_id).app L ≪≫
      (Scheme.Modules.pullbackId Y).app L

/-- The original canonical twist and original line return from the actual
inverse pullback, with both original field structures retained. -/
def canonicalOriginalLineIso {k : Type u} [Field k] {Y Z : Scheme.{u}}
    (e : Y ≅ Z) (fY : Y ⟶ Spec (.of k)) (fZ : Z ⟶ Spec (.of k))
    (he : e.hom ≫ fZ = fY) (L : Y.Modules) (n : ℕ) :
    (Scheme.Modules.pullback e.hom).obj
        (canonicalLineSheaf fZ n ⊗ (Scheme.Modules.pullback e.inv).obj L) ≅
      canonicalLineSheaf fY n ⊗ L :=
  SchemeIsoGeometry.canonicalTwistPullbackIso e fY fZ he
      ((Scheme.Modules.pullback e.inv).obj L) n ≪≫
    (Iso.refl _ ⊗ᵢ inversePullbackLineIso e L)

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
    (hDI : DeligneIllusieInput.WittDecompositionInput.{u,w} p k)
    {Xlift : Scheme.{u}}
    (fLift : Xlift ⟶ Spec (.of (DeligneIllusie.WittTwo.Ring p k)))
    (n : ℕ) [SmoothOfRelativeDimension n fLift] [IsSeparated fLift]
    [HasDerivedCategory.{w} (SchemeRelativeFrobenius.twist p
      (DeligneIllusieInput.specialFibreStructure p k fLift)).Modules]
    [HasDerivedCategory.{w'} (TopCat.Sheaf AddCommGrpCat.{u}
      (SchemeRelativeFrobenius.twist p
        (DeligneIllusieInput.specialFibreStructure p k fLift)))]

include hDI

/-- Witt Kodaira vanishing for the original scheme and original ample
line under an actual compatible isomorphism to the literal special fibre. -/
theorem kodaira_of_specialFibreIso (hn : n < p) {Y : Scheme.{u}}
    (fY : Y ⟶ Spec (.of k))
    (e : Y ≅ DeligneIllusieInput.specialFibre p k fLift)
    (he : e.hom ≫ DeligneIllusieInput.specialFibreStructure p k fLift = fY)
    (L : Y.Modules) (hL : SchemeLineAmpleness.IsAmple fY L) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H (canonicalLineSheaf fY n ⊗ L : Y.Modules).sheaf
      (q + 1)) := by
  let f₀ := DeligneIllusieInput.specialFibreStructure p k fLift
  let L₀ := (Scheme.Modules.pullback e.inv).obj L
  have hL₀ : SchemeLineAmpleness.IsAmple f₀ L₀ :=
    SchemeIsoGeometry.isAmple_pullback_of_triangle e.symm f₀ fY
      (SchemeIsoGeometry.inv_structure e fY f₀ he) hL
  let : SmoothOfRelativeDimension n f₀ :=
    DeligneIllusieInput.specialFibre_smoothOfRelativeDimension p k fLift n
  have hW : Subsingleton (CategoryTheory.Sheaf.H
      (canonicalLineSheaf f₀ n ⊗ L₀).sheaf (q + 1)) :=
    PositiveHodgeVanishing.kodaira_of_wittLift (p := p) hDI fLift n hn L₀ hL₀ q
  let : (canonicalLineSheaf f₀ n).IsQuasicoherent :=
    SmoothExteriorFiniteType.isQuasicoherent f₀ n n
  let : (canonicalLineSheaf f₀ n ⊗ L₀).IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight
      (canonicalLineSheaf f₀ n) L₀ hL₀.isInvertible
  have hpull : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback e.hom).obj (canonicalLineSheaf f₀ n ⊗ L₀)).sheaf
        (q + 1)) :=
    (SchemeIsoGeometry.pullback_subsingleton_H_iff e f₀ hL₀.isProjectiveFactorization
      (canonicalLineSheaf f₀ n ⊗ L₀) q).mpr hW
  exact subsingleton_H_of_moduleIso (canonicalOriginalLineIso e fY f₀ he L n).symm
    (q + 1) hpull

/-- The same original Kodaira group in the explicit sheafified coherent
tensor object, through the proved native monoidal comparison. -/
theorem kodaira_tensorObj_of_specialFibreIso (hn : n < p) {Y : Scheme.{u}}
    (fY : Y ⟶ Spec (.of k))
    (e : Y ≅ DeligneIllusieInput.specialFibre p k fLift)
    (he : e.hom ≫ DeligneIllusieInput.specialFibreStructure p k fLift = fY)
    (L : Y.Modules) (hL : SchemeLineAmpleness.IsAmple fY L) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (Scheme.Modules.tensorObj (canonicalLineSheaf fY n) L).sheaf (q + 1)) := by
  exact subsingleton_H_of_moduleIso
    (ModularCurves.monoidalTensorObjIso (canonicalLineSheaf fY n) L).symm (q + 1)
      (kodaira_of_specialFibreIso p hDI fLift n hn fY e he L hL q)

end EnvelopeProperty.Vanishing.WittKodairaComparison
