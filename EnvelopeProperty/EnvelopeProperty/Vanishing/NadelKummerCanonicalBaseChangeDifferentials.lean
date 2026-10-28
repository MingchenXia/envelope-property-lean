import EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChangeEtale
import EnvelopeProperty.AlgGeom.Canonical.ExteriorSheaf

/-! # The actual exterior Kähler maps in the canonical counit base-change square

The constructed top-frame maps are proved equal to the native exterior maps
of the original Kähler morphisms.  Thus the whole counit diagram is proved
for the genuine differential pullback maps, rather than assumed as input.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChange

open CategoryTheory CanonicalGeometry NadelKummerCanonicalTrace

universe u

section Kaehler
variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]

/-- The native original Kähler morphism as an actual scalar-changing map. -/
def kaehlerSemilinear :
    KaehlerDifferential K A →ₛₗ[algebraMap A B] KaehlerDifferential K B where
  toFun := KaehlerDifferential.map K K A B
  map_add' := map_add _
  map_smul' a w := by
    rw [map_smul]
    exact (IsScalarTower.algebraMap_smul B a (KaehlerDifferential.map K K A B w)).symm

/-- The actual scalar-changing Kähler morphism preserves the original universal differentials. -/
theorem kaehlerSemilinear_D (a : A) :
    kaehlerSemilinear (K := K) (A := A) (B := B) (KaehlerDifferential.D K A a) =
      KaehlerDifferential.D K B (algebraMap A B a) :=
  KaehlerDifferential.map_D K K A B a

end Kaehler

variable (R : Type u) [CommRing R] [Nontrivial R] {n : ℕ} (d : Fin n → ℕ)

/-- The actual original Kähler map to the coefficient-extended base chart. -/
def baseDifferentialMap (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S) :
    let _ := baseRAlgebra R S a
    KaehlerDifferential R (PolynomialRing R n) →ₛₗ[a] KaehlerDifferential R S := by
  let := baseRAlgebra R S a
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : IsScalarTower R (PolynomialRing R n) S := IsScalarTower.of_algebraMap_eq' rfl
  exact kaehlerSemilinear

/-- The actual original Kähler map to the literal coefficient-base-changed target. -/
def targetDifferentialMap (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S) :
    let _ := targetRAlgebra R d S a
    KaehlerDifferential R (PolynomialRing R n) →ₛₗ[powerBaseChangeRight R d S a]
      KaehlerDifferential R (powerBaseChangeRing R d S a) := by
  let := targetRAlgebra R d S a
  let : Algebra (PolynomialRing R n) (powerBaseChangeRing R d S a) :=
    (powerBaseChangeRight R d S a).toAlgebra
  let : IsScalarTower R (PolynomialRing R n) (powerBaseChangeRing R d S a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact kaehlerSemilinear

/-- The genuine exterior map of the actual base Kähler morphism. -/
def baseExteriorMap (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S) :
    canonicalModule R n →ₛₗ[a] baseCanonicalModule R S a := by
  let := baseRAlgebra R S a
  exact exteriorSemilinearMap a (baseDifferentialMap R S a) n

/-- The genuine exterior map of the actual target Kähler morphism. -/
def targetExteriorMap (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S) :
    canonicalModule R n →ₛₗ[powerBaseChangeRight R d S a] targetCanonicalModule R d S a := by
  let := targetRAlgebra R d S a
  exact exteriorSemilinearMap (powerBaseChangeRight R d S a) (targetDifferentialMap R d S a) n

omit [Nontrivial R] in
/-- The actual exterior Kähler map sends the old ordered base wedge to its genuine new wedge. -/
theorem baseExteriorMap_generator (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) :
    baseExteriorMap R S a (canonicalGenerator R n) = baseCanonicalGenerator R S a ha := by
  let := baseRAlgebra R S a
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : IsScalarTower R (PolynomialRing R n) S := IsScalarTower.of_algebraMap_eq' rfl
  rw [canonicalGenerator_eq_wedge, baseExteriorMap, exteriorSemilinearMap_ιMulti,
    baseCanonicalGenerator_eq_wedge]
  congr 1
  funext j
  exact kaehlerSemilinear_D (MvPolynomial.X j)

omit [Nontrivial R] in
/-- The actual exterior Kähler map sends the old ordered target wedge to its genuine new wedge. -/
theorem targetExteriorMap_generator (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) :
    targetExteriorMap R d S a (canonicalGenerator R n) = targetCanonicalGenerator R d S a ha := by
  let := targetRAlgebra R d S a
  let : Algebra (PolynomialRing R n) (powerBaseChangeRing R d S a) :=
    (powerBaseChangeRight R d S a).toAlgebra
  let : IsScalarTower R (PolynomialRing R n) (powerBaseChangeRing R d S a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  rw [canonicalGenerator_eq_wedge, targetExteriorMap, exteriorSemilinearMap_ιMulti,
    targetCanonicalGenerator_eq_wedge]
  congr 1
  funext j
  exact kaehlerSemilinear_D (MvPolynomial.X j)

omit [Nontrivial R] in
/-- The base top-frame map is proved to be the genuine whole exterior Kähler morphism. -/
theorem baseExteriorMap_eq_frame (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) :
    baseExteriorMap R S a = baseTopFrameMap R S a ha := by
  apply (polynomialCanonicalBasis R n).ext
  intro j
  cases j
  change baseExteriorMap R S a (canonicalGenerator R n) =
    baseTopFrameMap R S a ha (canonicalGenerator R n)
  rw [baseExteriorMap_generator R S a ha]
  simpa only [one_smul, map_one] using (baseTopFrameMap_generator R S a ha 1).symm

omit [Nontrivial R] in
/-- The target top-frame map is proved to be the genuine whole exterior Kähler morphism. -/
theorem targetExteriorMap_eq_frame (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) :
    targetExteriorMap R d S a = targetTopFrameMap R d S a ha := by
  apply (polynomialCanonicalBasis R n).ext
  intro j
  cases j
  change targetExteriorMap R d S a (canonicalGenerator R n) =
    targetTopFrameMap R d S a ha (canonicalGenerator R n)
  rw [targetExteriorMap_generator R d S a ha]
  simpa only [one_smul, map_one] using (targetTopFrameMap_generator R d S a ha 1).symm

/-- The native canonical counit square commutes for the actual exterior Kähler maps on every old top form. -/
theorem etaleCanonicalCounit_exterior_naturality (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) (w : canonicalModule R n) :
    etaleCanonicalCounit R d S a ha (targetExteriorMap R d S a w) =
      baseExteriorMap R S a (canonicalCounit R d w) := by
  rw [targetExteriorMap_eq_frame R d S a ha, baseExteriorMap_eq_frame R S a ha]
  exact etaleCanonicalCounit_frame_naturality R d S a ha w

end EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChange
