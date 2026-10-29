import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.RingHom.Etale

/-! # Original formal etaleness is retained in the SAME native spectrum section square -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace EnvelopeProperty
universe u

private theorem originalIsoFormallyEtale {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Bijective φ) : φ.FormallyEtale := by
  let := φ.toAlgebra
  let : Algebra.Etale R S := (RingHom.Etale.of_bijective hφ).toAlgebra
  change Algebra.FormallyEtale R S
  infer_instance

/-- ANY actual original formally etale ring map has its SAME actual native spectrum
whole global-section map formally etale; all coefficient comparisons are internally derived. -/
theorem spec_appTop_formallyEtale {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : φ.hom.FormallyEtale) : (Spec.map φ).appTop.hom.FormallyEtale := by
  have hR := originalIsoFormallyEtale (Scheme.ΓSpecIso R).hom.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom)
  have hS := originalIsoFormallyEtale (Scheme.ΓSpecIso S).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).inv)
  have heq : (Spec.map φ).appTop.hom =
      (Scheme.ΓSpecIso S).inv.hom.comp (φ.hom.comp (Scheme.ΓSpecIso R).hom.hom) := by
    ext a
    obtain ⟨r, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2 a
    change (Spec.map φ).appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) =
      (Scheme.ΓSpecIso S).inv.hom (φ.hom ((Scheme.ΓSpecIso R).hom.hom
        ((Scheme.ΓSpecIso R).inv.hom r)))
    rw [Iso.inv_hom_id_apply]
    exact (congrArg (fun e : R ⟶ Scheme.Γ.obj (.op (Spec S)) => e.hom r)
      (Scheme.ΓSpecIso_inv_naturality φ)).symm
  rw [heq]
  exact (hR.comp hφ).comp hS

end EnvelopeProperty
