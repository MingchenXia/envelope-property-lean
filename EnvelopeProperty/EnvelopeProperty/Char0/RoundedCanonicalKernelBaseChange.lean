import EnvelopeProperty.AlgGeom.FlatSectionKernel
import EnvelopeProperty.AlgGeom.ProperLocalSectionDetection
import EnvelopeProperty.Char0.SpecPushedRoundedCanonicalKernel
import DeJongAlterations.StableModification.Cohomology.PullbackQcoh

/-!
# The whole original rounded-canonical quotient kernel after flat base change

The SAME original quotient differential and actual pullback unit are retained.
The coefficient extension need not be smooth over the original field: the
object above it is the actual pullback of the original quotient module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open EnvelopeProperty.CanonicalGeometry
open EnvelopeProperty.FlatSectionKernel

namespace EnvelopeProperty.Char0.RoundedCanonicalModule
universe u
noncomputable section

variable {k : Type u} [Field k] (A : CommRingCat.{u}) [Algebra k A]
    {Y : Scheme.{u}} (g : Y ⟶ Spec A) {n : ℕ}
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)

/-- The ENTIRE original geometric kernel is the actual coefficient kernel
of the SAME original quotient differential section, with its literal coefficient action. -/
theorem specPushedQuotientKernel_eq_sectionKernel :
    let f := affineStructuralMap k A
    letI : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
    let M := quotient f g n J hJ q
    let m : AffineModuleFlatBaseChange.sections g M :=
      (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤) (1 : Γ(Y, ⊤))
    specPushedQuotientKernel A g z hz J hJ q = sectionKernel g M m := by
  let f := affineStructuralMap k A
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  let α := quotientDifferentialSection f g n J hJ q
  ext a
  refine (mem_specPushedQuotientKernel_iff A g z hz J hJ q a).trans ?_
  change α.val.app (.op ⊤) (ProperBirationalSections.coefficientMap g a) = 0 ↔
    (ProperBirationalSections.coefficientMap g a) • (α.val.app (.op ⊤) (1 : Γ(Y, ⊤))) = 0
  have h := (α.val.app (.op ⊤)).hom.map_smul (ProperBirationalSections.coefficientMap g a)
    (1 : Γ(Y, ⊤))
  simpa only [smul_eq_mul, mul_one] using Iff.of_eq (congrArg (fun w => w = 0) h)

variable {S : Type u} [CommRing S] [Algebra A S]

/-- Actual flat H0 base change identifies the WHOLE original rounded-canonical
kernel extension with the coefficient kernel of its SAME actual pulled section. -/
theorem map_specPushedQuotientKernel_eq [Module.Flat A S] [CompactSpace Y] [Y.IsSeparated]
    [SmoothOfRelativeDimension n (g ≫ affineStructuralMap k A)] :
    let f := affineStructuralMap k A
    letI : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
    let M := quotient f g n J hJ q
    let m : AffineModuleFlatBaseChange.sections g M :=
      (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤) (1 : Γ(Y, ⊤))
    (specPushedQuotientKernel A g z hz J hJ q).map (algebraMap A S) =
      sectionKernel (FlatGlobalSections.structureMap (S := S) g)
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) g)).obj M)
          (pulledSection (S := S) g M m) := by
  let f := affineStructuralMap k A
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  let M := quotient f g n J hJ q
  let : M.IsQuasicoherent := quotient_isQuasicoherent f g n J hJ q
  rw [specPushedQuotientKernel_eq_sectionKernel]
  exact map_sectionKernel_eq (S := S) g M _

/-- EVERY extended coefficient is tested on ALL of the actual base change
against the actual original pulled quotient differential section. -/
theorem mem_map_specPushedQuotientKernel_iff [Module.Flat A S] [CompactSpace Y]
    [Y.IsSeparated] [SmoothOfRelativeDimension n (g ≫ affineStructuralMap k A)] (s : S) :
    let f := affineStructuralMap k A
    letI : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
    let M := quotient f g n J hJ q
    let m : AffineModuleFlatBaseChange.sections g M :=
      (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤) (1 : Γ(Y, ⊤))
    s ∈ (specPushedQuotientKernel A g z hz J hJ q).map (algebraMap A S) ↔
      (ProperBirationalSections.coefficientMap
        (FlatGlobalSections.structureMap (S := S) g) s) •
          pulledSection (S := S) g M m = 0 := by
  rw [map_specPushedQuotientKernel_eq]
  exact mem_sectionKernel_iff _ _ _ s

/-- Actual properness and a local flat coefficient ring detect membership in
the WHOLE extended original kernel by actual CLOSED closed-fibre module germs. -/
theorem mem_map_specPushedQuotientKernel_iff_closedFiber_germs [Module.Flat A S]
    [IsLocalRing S] [IsProper g]
    [SmoothOfRelativeDimension n (g ≫ affineStructuralMap k A)] (s : S) :
    let f := affineStructuralMap k A
    letI : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
    let M := quotient f g n J hJ q
    let m : AffineModuleFlatBaseChange.sections g M :=
      (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤) (1 : Γ(Y, ⊤))
    let N := (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) g)).obj M
    s ∈ (specPushedQuotientKernel A g z hz J hJ q).map (algebraMap A S) ↔
      ∀ y : FlatGlobalSections.baseChange (S := S) g, IsClosed ({y} : Set _) →
        FlatGlobalSections.structureMap (S := S) g y = IsLocalRing.closedPoint S →
          N.presheaf.germ ⊤ y trivial
            ((ProperBirationalSections.coefficientMap
              (FlatGlobalSections.structureMap (S := S) g) s) •
                pulledSection (S := S) g M m) = 0 := by
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from g]; infer_instance⟩
  let f := affineStructuralMap k A
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  let M := quotient f g n J hJ q
  let : M.IsQuasicoherent := quotient_isQuasicoherent f g n J hJ q
  let N := (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) g)).obj M
  let : N.IsQuasicoherent := inferInstance
  refine (mem_map_specPushedQuotientKernel_iff A g z hz J hJ q s).trans ?_
  exact ProperLocalSectionDetection.section_eq_zero_iff_closedPoint_closedFiber_germs
    (FlatGlobalSections.structureMap (S := S) g) N _

end
end EnvelopeProperty.Char0.RoundedCanonicalModule
