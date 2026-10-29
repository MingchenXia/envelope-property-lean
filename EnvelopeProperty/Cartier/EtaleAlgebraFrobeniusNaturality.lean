import EnvelopeProperty.Cartier.EtaleAlgebraFrobeniusComplex
import EnvelopeProperty.Cartier.EtaleDifferentialNaturality

/-! # SAME whole original Frobenius complexes along EVERY original algebra map, including zero -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleAlgebraFrobeniusNaturality
open CategoryTheory
universe u
variable {k A B : Type u} [Field k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

private def originalFormMap (q : ℕ) :
    ModuleCat.of A (⋀[A]^q (KaehlerDifferential k A)) ⟶
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        (ModuleCat.of B (⋀[B]^q (KaehlerDifferential k B))) :=
  ModuleCat.ofHom (Char0.canonicalDifferentialLinearMap (k := k) (R := A) (A := B) q)

/-- The SAME actual canonical exterior map is truly linear with original Frobenius scalars,
including zero algebras, without target characteristic/nonzero/map-flatness assumptions. -/
def formMap (q : ℕ) :
    EtaleAlgebraFrobeniusComplex.formModule (k := k) (B := A) p q ⟶
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        (EtaleAlgebraFrobeniusComplex.formModule (k := k) (B := B) p q) :=
  (ModuleCat.restrictScalars (AlgebraFrobenius.map k A p)).map
      (originalFormMap (k := k) (A := A) (B := B) q) ≫
    (ModuleCat.restrictScalarsComp (AlgebraFrobenius.map k A p) (algebraMap A B)).inv.app _ ≫
    (ModuleCat.restrictScalarsCongr
      (AlgebraFrobenius.naturality k A p (algebraMap A B))).hom.app _ ≫
    (ModuleCat.restrictScalarsComp (algebraMap A B) (AlgebraFrobenius.map k B p)).hom.app _

/-- EVERY original form retains exactly its SAME native canonical coefficient-map image. -/
theorem formMap_apply (q : ℕ)
    (a : EtaleAlgebraFrobeniusComplex.formModule (k := k) (B := A) p q) :
    formMap (k := k) (A := A) (B := B) p q a =
      Char0.canonicalDifferentialLinearMap (k := k) (R := A) (A := B) q a := rfl

variable {n m : ℕ} (v : Fin n → A) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (w : Fin m → B) (hw : (MvPolynomial.aeval (R := k) w).toRingHom.Etale)

/-- Genuine whole original coefficient cochain map includes EVERY original algebra,
ZERO internally, and the SAME original differential on EVERY form in EVERY degree. -/
def complexMap : EtaleAlgebraFrobeniusComplex.complex v hv p ⟶
    ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (EtaleAlgebraFrobeniusComplex.complex w hw p) where
  f q := formMap (k := k) (A := A) (B := B) p q
  comm' q r h := by
    have hr : q+1 = r := h
    subst r
    simp only [EtaleAlgebraFrobeniusComplex.complex,
      Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact EtaleDifferentialNaturality.differential_canonicalMap v hv w hw q a

/-- The ACTUAL whole original cochain morphism retains EVERY original form/coefficient. -/
theorem complexMap_f_apply (q : ℕ) (a : (EtaleAlgebraFrobeniusComplex.complex v hv p).X q) :
    (complexMap p v hv w hw).f q a =
      Char0.canonicalDifferentialLinearMap (k := k) (R := A) (A := B) q a := rfl

end EnvelopeProperty.Cartier.EtaleAlgebraFrobeniusNaturality
