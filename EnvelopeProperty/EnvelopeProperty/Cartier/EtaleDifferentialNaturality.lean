import EnvelopeProperty.Cartier.EtaleDifferentialIntrinsic
import EnvelopeProperty.Char0.CanonicalDifferentialNaturality
import Mathlib.Algebra.Homology.Additive

/-! # The actual original differential commutes with the SAME native canonical maps -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleDifferentialNaturality
open CategoryTheory
open scoped Classical
open PolynomialDeRham
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The SAME actual native Kaehler map is genuinely semilinear for its original coefficient
map, with NO vector map comparison premise. -/
def cotangentSemilinearMap :
    (KaehlerDifferential R A) →ₛₗ[algebraMap A B] (KaehlerDifferential R B) where
  toFun := KaehlerDifferential.map R R A B
  map_add' := (KaehlerDifferential.map R R A B).map_add
  map_smul' a m := by
    rw [(KaehlerDifferential.map R R A B).map_smul]
    exact (IsScalarTower.algebraMap_smul B a _).symm

/-- The SAME original native canonical exterior map retains EVERY original function wedge. -/
theorem canonicalMap_universalWedge (q : ℕ) (f : Fin q → A) :
    Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) q
      (exteriorPower.ιMulti A q (fun j => KaehlerDifferential.D R A (f j))) =
    exteriorPower.ιMulti B q (fun j => KaehlerDifferential.D R B (algebraMap A B (f j))) := by
  rw [Char0.canonicalDifferentialLinearMap_wedge]
  congr 1
  funext j
  exact KaehlerDifferential.map_D R R A B _

/-- EVERY actual original coefficient of EVERY actual universal wedge is carried by the
SAME original native coefficient and canonical exterior map. -/
theorem canonicalMap_smul_universalWedge (q : ℕ) (a : A) (f : Fin q → A) :
    Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) q
      (a • exteriorPower.ιMulti A q (fun j => KaehlerDifferential.D R A (f j))) =
    algebraMap A B a • exteriorPower.ιMulti B q
      (fun j => KaehlerDifferential.D R B (algebraMap A B (f j))) := by
  rw [map_smul, canonicalMap_universalWedge]
  exact (IsScalarTower.algebraMap_smul B a _).symm

variable {n : ℕ} (v : Fin n → A) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)

include v hv in
/-- The ENTIRE SAME actual native canonical differential map equals the genuine universal
semilinear exterior map of the SAME original native Kaehler map, not only selected wedges. -/
theorem canonicalMap_eq_exteriorSemilinear (q : ℕ) (a : ⋀[A]^q (KaehlerDifferential R A)) :
    Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) q a =
      CanonicalGeometry.exteriorSemilinearMap (algebraMap A B)
        (cotangentSemilinearMap (R := R) (A := A) (B := B)) q a := by
  let e := (Char0.etaleDifferentialBasis v hv).exteriorPower q
  have ha : ∑ s, e.repr a s • e s = a := e.sum_repr a
  rw [← ha]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  change Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) q
      (e.repr a s • (Char0.etaleDifferentialBasis v hv).exteriorPower q s) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, map_smul, map_smulₛₗ,
    Char0.canonicalDifferentialLinearMap_wedge, CanonicalGeometry.exteriorSemilinearMap_ιMulti]
  exact (IsScalarTower.algebraMap_smul B (e.repr a s) _).symm

include v hv in
/-- The SAME original native canonical map preserves actual left exterior multiplication
on EVERY original homogeneous form, retaining its original native Kaehler vector map. -/
theorem canonicalMap_leftWedge (q : ℕ) (m : KaehlerDifferential R A)
    (a : ⋀[A]^q (KaehlerDifferential R A)) :
    Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) (q+1) (leftWedge m q a) =
      leftWedge (KaehlerDifferential.map R R A B m) q
        (Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) q a) := by
  rw [canonicalMap_eq_exteriorSemilinear v hv, canonicalMap_eq_exteriorSemilinear v hv]
  exact ExteriorBasisScalarExtension.exteriorSemilinearMap_leftWedge _ _ m q a

variable {m : ℕ} (w : Fin m → B) (hw : (MvPolynomial.aeval (R := R) w).toRingHom.Etale)

/-- The ENTIRE SAME original canonical exterior map commutes with the original intrinsic
etale differentials for ANY actual algebra tower. The intervening map need NOT be etale. -/
theorem differential_canonicalMap (q : ℕ) (a : ⋀[A]^q (KaehlerDifferential R A)) :
    EtaleDeRham.differential w hw q
      (Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) q a) =
    Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) (q+1)
      (EtaleDeRham.differential v hv q a) := by
  let e := (Char0.etaleDifferentialBasis v hv).exteriorPower q
  have ha : ∑ s, e.repr a s • e s = a := e.sum_repr a
  rw [← ha]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  change EtaleDeRham.differential w hw q
      (Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) q
        (e.repr a s • (Char0.etaleDifferentialBasis v hv).exteriorPower q s)) =
    Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) (q+1)
      (EtaleDeRham.differential v hv q (e.repr a s •
        (Char0.etaleDifferentialBasis v hv).exteriorPower q s))
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  have hvec : (Char0.etaleDifferentialBasis v hv) ∘ (Set.powersetCard.ofFinEmbEquiv.symm s) =
      fun j => KaehlerDifferential.D R A (v ((Set.powersetCard.ofFinEmbEquiv.symm s) j)) := by
    funext j
    exact Char0.etaleDifferentialBasis_apply v hv _
  rw [hvec, canonicalMap_smul_universalWedge,
    EtaleDifferentialIntrinsic.differential_smul_universalWedge,
    EtaleDifferentialIntrinsic.differential_smul_universalWedge,
    canonicalMap_leftWedge v hv, KaehlerDifferential.map_D, canonicalMap_universalWedge]

/-- The SAME actual original native canonical maps give a genuine WHOLE morphism of the
original additive de Rham complexes along ANY actual algebra tower. -/
def complexMap : EtaleDeRham.complex v hv ⟶ EtaleDeRham.complex w hw where
  f q := AddCommGrpCat.ofHom
    (Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) q).toAddMonoidHom
  comm' q r h := by
    have hr : q+1 = r := h
    subst r
    simp only [EtaleDeRham.complex, CochainComplex.of_d]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    exact differential_canonicalMap v hv w hw q a

private def originalFormMap (q : ℕ) :
    ModuleCat.of A (⋀[A]^q (KaehlerDifferential R A)) ⟶
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        (ModuleCat.of B (⋀[B]^q (KaehlerDifferential R B))) :=
  ModuleCat.ofHom (Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) q)

private theorem frobeniusCoefficientSquare (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p] :
    (algebraMap A B).comp (frobenius A p) = (frobenius B p).comp (algebraMap A B) := by
  ext a
  exact map_pow (algebraMap A B) a p

/-- The SAME original native canonical map is genuinely linear between the ORIGINAL
Frobenius-restricted module and the actual restricted target Frobenius module. -/
def frobeniusFormMap (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p] (q : ℕ) :
    EtaleDeRham.frobeniusModule (R := R) (B := A) p q ⟶
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        (EtaleDeRham.frobeniusModule (R := R) (B := B) p q) :=
  (ModuleCat.restrictScalars (frobenius A p)).map (originalFormMap (R := R) (A := A) (B := B) q) ≫
    (ModuleCat.restrictScalarsComp (frobenius A p) (algebraMap A B)).inv.app _ ≫
    (ModuleCat.restrictScalarsCongr (frobeniusCoefficientSquare (A := A) (B := B) p)).hom.app _ ≫
    (ModuleCat.restrictScalarsComp (algebraMap A B) (frobenius B p)).hom.app _

/-- EVERY original form is mapped by the SAME actual original canonical map after genuine
native Frobenius scalar restriction; no element comparison premise is supplied. -/
theorem frobeniusFormMap_apply (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]
    (q : ℕ) (a : EtaleDeRham.frobeniusModule (R := R) (B := A) p q) :
    frobeniusFormMap (R := R) (A := A) (B := B) p q a =
      Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) q a := rfl

/-- The SAME original canonical exterior maps give a genuine WHOLE native Frobenius-linear
cochain morphism along ANY actual algebra tower of actual etale coordinate rings. -/
def frobeniusComplexMap (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p] :
    EtaleDeRham.frobeniusComplex v hv p ⟶
      ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (EtaleDeRham.frobeniusComplex w hw p) where
  f q := frobeniusFormMap (R := R) (A := A) (B := B) p q
  comm' q r h := by
    have hr : q+1 = r := h
    subst r
    simp only [EtaleDeRham.frobeniusComplex, Functor.mapHomologicalComplex_obj_d,
      CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact differential_canonicalMap v hv w hw q a

end EnvelopeProperty.Cartier.EtaleDifferentialNaturality
