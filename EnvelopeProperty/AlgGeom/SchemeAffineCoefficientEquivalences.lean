import EnvelopeProperty.AlgGeom.SchemeFunctionFieldPullbackCoefficients
import Hironaka.Scheme.IdealSheaf.Derivative.BaseChange

/-! # Actual affine-section isomorphisms preserve literal original coefficient structures -/

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
noncomputable section
universe u
namespace EnvelopeProperty.SchemeAffineCoefficientEquivalences
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k]

private theorem appLE_top {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.appLE ⊤ ⊤ le_top = f.appTop := by
  simpa only [Scheme.Hom.preimage_top] using (f.appLE_eq_app (U := ⊤))

private def topSectionMap {X Y : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ Spec (.of k)) :
    letI := q.sectionsAlgebra ⊤
    letI := (f ≫ q).sectionsAlgebra ⊤
    Γ(Y, ⊤) →ₐ[k] Γ(X, ⊤) := by
  letI := q.sectionsAlgebra ⊤
  letI := (f ≫ q).sectionsAlgebra ⊤
  refine { f.appTop.hom with commutes' := ?_ }
  intro a
  rw [Scheme.Hom.algebraMap_sectionsAlgebra, Scheme.Hom.algebraMap_sectionsAlgebra,
    appLE_top, appLE_top]
  exact congrArg (fun z => ((Scheme.ΓSpecIso (.of k)).inv ≫ z).hom a)
    (Scheme.Hom.comp_appTop f q).symm

/-- The native spectrum section isomorphism retains the SAME original coefficient algebra. -/
def specSections (A : Type u) [CommRing A] [Algebra k A] :
    letI := (Spec.map (CommRingCat.ofHom (algebraMap k A))).sectionsAlgebra ⊤
    A ≃ₐ[k] Γ(Spec (.of A), ⊤) := by
  letI := (Spec.map (CommRingCat.ofHom (algebraMap k A))).sectionsAlgebra ⊤
  refine { (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro a
  rw [Scheme.Hom.algebraMap_sectionsAlgebra, appLE_top]
  exact congrArg (fun z => z.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k A)))

/-- Every genuine original affine scheme isomorphism induces the literal original coefficient isomorphism. -/
def isoSections {Y : Scheme.{u}} (A : Type u) [CommRing A] [Algebra k A]
    (e : Y ≅ Spec (.of A)) :
    letI := (e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k A))).sectionsAlgebra ⊤
    A ≃ₐ[k] Γ(Y, ⊤) := by
  let q := Spec.map (CommRingCat.ofHom (algebraMap k A))
  letI := q.sectionsAlgebra ⊤
  letI := (e.hom ≫ q).sectionsAlgebra ⊤
  let φ := (topSectionMap e.hom q).comp (specSections (k := k) A).toAlgHom
  apply AlgEquiv.ofBijective φ
  exact (ConcreteCategory.bijective_of_isIso e.hom.appTop).comp
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv.bijective

/-- The genuine whole open top-section isomorphism retains the SAME original field coefficients. -/
def openSections {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) (U : X.Opens) :
    letI := (U.ι ≫ p).sectionsAlgebra ⊤
    letI := p.sectionsAlgebra U
    Γ(U.toScheme, ⊤) ≃ₐ[k] Γ(X, U) := by
  letI := (U.ι ≫ p).sectionsAlgebra ⊤
  letI := p.sectionsAlgebra U
  refine { U.topIso.commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro a
  rw [Scheme.Hom.algebraMap_sectionsAlgebra, Scheme.Hom.algebraMap_sectionsAlgebra, appLE_top]
  exact congrArg (fun z => ((Scheme.ΓSpecIso (.of k)).inv ≫ z).hom a)
    (Scheme.Opens.ι_comp_appTop_topIso_hom p U)

end EnvelopeProperty.SchemeAffineCoefficientEquivalences
