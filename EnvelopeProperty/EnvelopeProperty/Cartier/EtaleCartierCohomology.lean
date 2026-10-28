import EnvelopeProperty.Cartier.EtaleExteriorBaseChange
import EnvelopeProperty.Cartier.PolynomialCartierCohomology
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Genuine whole native etale Cartier cohomology -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleCartierCohomology
open CategoryTheory Limits
universe u

/-- Actual flat scalar extension commutes with the WHOLE genuine native homology of EVERY
original complex. Exactness is DERIVED from the actual ring map flatness. -/
def flatHomologyIso {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (C : CochainComplex (ModuleCat.{u} A) ℕ) (q : ℕ) :
    (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology q ≅
      (ModuleCat.extendScalars f).obj (C.homology q) := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u} f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact (C.sc q).mapHomologyIso (ModuleCat.extendScalars f)

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP R p] [CharP B p]

/-- The SAME actual original etale Frobenius complex homology is the native extension of the
SAME original polynomial Frobenius complex homology. No homology comparison is assumed. -/
def frobeniusHomologyIso (q : ℕ) :
    (EtaleDeRham.frobeniusComplex v hv p).homology q ≅
      (ModuleCat.extendScalars (MvPolynomial.aeval (R := R) v).toRingHom).obj
        ((PolynomialDeRham.frobeniusComplex (σ := Fin n) R p).homology q) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat B) (ComplexShape.up ℕ) q).mapIso
      (EtaleExteriorBaseChange.frobeniusComplexIso v hv p)).symm ≪≫
    flatHomologyIso (MvPolynomial.aeval (R := R) v).toRingHom (RingHom.Etale.iff_flat_and_formallyUnramified.mp hv).1
      (PolynomialDeRham.frobeniusComplex (σ := Fin n) R p) q

variable {k : Type u} [Field k] [Algebra k B] [CharP k p] [PerfectRing k p]

/-- Genuine all-degree Cartier cohomology on the SAME actual original etale coordinate ring.
Every original module and native differential/homology is retained, without a Cartier premise. -/
def cartierIso (w : Fin n → B) (hw : (MvPolynomial.aeval (R := k) w).toRingHom.Etale) (q : ℕ) :
    (EtaleDeRham.frobeniusComplex w hw p).homology q ≅
      ModuleCat.of B (⋀[B]^q (KaehlerDifferential k B)) :=
  frobeniusHomologyIso w hw p q ≪≫
    (ModuleCat.extendScalars (MvPolynomial.aeval (R := k) w).toRingHom).mapIso
      (PolynomialCartierCohomology.cartierIso k p q) ≪≫
        EtaleExteriorBaseChange.exteriorIso w hw q

end EnvelopeProperty.Cartier.EtaleCartierCohomology
