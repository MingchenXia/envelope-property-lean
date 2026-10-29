import EnvelopeProperty.Cartier.EtaleCohomologyCoefficientMaps

/-! # The same entire coefficient maps preserve all original de Rham cohomology products -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleCohomologyCoefficientProducts
open CategoryTheory
open scoped Classical
open PolynomialDeRham
universe u

private theorem tupleZero_product {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (r : ℕ) (t : Fin 0 → M) (b : ⋀[A]^r M) :
    EtaleGradedLeibniz.wedgeProduct 0 r (exteriorPower.ιMulti A 0 t) b = b := by
  apply Subtype.ext
  change ExteriorAlgebra.ιMulti A 0 t * (b : ExteriorAlgebra A M) = _
  rw [ExteriorAlgebra.ιMulti_zero_apply, one_mul]

private theorem tupleSucc {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (q : ℕ) (t : Fin (q+1) → M) :
    exteriorPower.ιMulti A (q+1) t =
      leftWedge (t 0) q (exteriorPower.ιMulti A q (Matrix.vecTail t)) := by
  rw [ExteriorBasisScalarExtension.leftWedge_ιMulti]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem semilinear_tuple_product {A B M N : Type u} [CommRing A] [CommRing B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (f : A →+* B) (φ : M →ₛₗ[f] N) (q : ℕ) (t : Fin q → M) (r : ℕ) (b : ⋀[A]^r M) :
    CanonicalGeometry.exteriorSemilinearMap f φ (r+q)
      (EtaleGradedLeibniz.wedgeProduct q r (exteriorPower.ιMulti A q t) b) =
    EtaleGradedLeibniz.wedgeProduct q r
      (CanonicalGeometry.exteriorSemilinearMap f φ q (exteriorPower.ιMulti A q t))
      (CanonicalGeometry.exteriorSemilinearMap f φ r b) := by
  induction q with
  | zero =>
    rw [tupleZero_product, CanonicalGeometry.exteriorSemilinearMap_ιMulti, tupleZero_product]
    rfl
  | succ q ih =>
    rw [tupleSucc, EtaleGradedLeibniz.wedgeProduct_leftWedge]
    change CanonicalGeometry.exteriorSemilinearMap f φ ((r+q)+1)
      (leftWedge (t 0) (r+q)
        (EtaleGradedLeibniz.wedgeProduct q r (exteriorPower.ιMulti A q (Matrix.vecTail t)) b)) = _
    rw [ExteriorBasisScalarExtension.exteriorSemilinearMap_leftWedge,
      ExteriorBasisScalarExtension.exteriorSemilinearMap_leftWedge,
      EtaleGradedLeibniz.wedgeProduct_leftWedge, ih]

private theorem semilinear_product {A B M N : Type u} [CommRing A] [CommRing B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (f : A →+* B) (φ : M →ₛₗ[f] N) (q r : ℕ) (a : ⋀[A]^q M) (b : ⋀[A]^r M) :
    CanonicalGeometry.exteriorSemilinearMap f φ (r+q) (EtaleGradedLeibniz.wedgeProduct q r a b) =
    EtaleGradedLeibniz.wedgeProduct q r (CanonicalGeometry.exteriorSemilinearMap f φ q a)
      (CanonicalGeometry.exteriorSemilinearMap f φ r b) := by
  have ha : a ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A q (M := M))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨t, rfl⟩ := ha
    exact semilinear_tuple_product f φ q t r b
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y _ _ hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | smul c x _ hx => simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, hx]

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
variable {n m : ℕ} (v : Fin n → A) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
variable (w : Fin m → B) (hw : (MvPolynomial.aeval (R := R) w).toRingHom.Etale)

include v hv in
/-- The SAME entire original native canonical exterior map preserves EVERY homogeneous
product along ANY original coefficient map, not merely coordinate wedges. -/
theorem canonicalMap_wedgeProduct (q r : ℕ)
    (a : ⋀[A]^q (KaehlerDifferential R A)) (b : ⋀[A]^r (KaehlerDifferential R A)) :
    Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) (r+q)
      (EtaleGradedLeibniz.wedgeProduct q r a b) =
    EtaleGradedLeibniz.wedgeProduct q r
      (Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) q a)
      (Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) r b) := by
  rw [EtaleDifferentialNaturality.canonicalMap_eq_exteriorSemilinear v hv,
    EtaleDifferentialNaturality.canonicalMap_eq_exteriorSemilinear v hv,
    EtaleDifferentialNaturality.canonicalMap_eq_exteriorSemilinear v hv]
  exact semilinear_product _ _ q r a b

variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

/-- EVERY pair of ACTUAL original cycles has its SAME entire product retained by the
actual coefficient map; closedness is genuinely retained, not supplied anew. -/
theorem cycleProduct_map (q r : ℕ) (a : EtaleCohomologyProducts.cycles v hv p q)
    (b : EtaleCohomologyProducts.cycles v hv p r) :
    (EtaleCohomologyCoefficientMaps.cycleMap v hv w hw p (r+q)).hom
      (EtaleCohomologyProducts.cycleProduct v hv p q r a b) =
    EtaleCohomologyProducts.cycleProduct w hw p q r
      ((EtaleCohomologyCoefficientMaps.cycleMap v hv w hw p q).hom a)
      ((EtaleCohomologyCoefficientMaps.cycleMap v hv w hw p r).hom b) := by
  apply Subtype.ext
  exact canonicalMap_wedgeProduct v hv q r a.val b.val

/-- BOTH entire original quotient arguments retain their SAME actual product through the
actual coefficient map. No representative, product or boundary comparison is assumed. -/
theorem cohomologyProduct_map (q r : ℕ) (a : EtaleCohomologyProducts.cohomology v hv p q)
    (b : EtaleCohomologyProducts.cohomology v hv p r) :
    (EtaleCohomologyCoefficientMaps.cohomologyMap v hv w hw p (r+q)).hom
      (EtaleCohomologyProducts.cohomologyProduct v hv p q r a b) =
    EtaleCohomologyProducts.cohomologyProduct w hw p q r
      ((EtaleCohomologyCoefficientMaps.cohomologyMap v hv w hw p q).hom a)
      ((EtaleCohomologyCoefficientMaps.cohomologyMap v hv w hw p r).hom b) := by
  induction a using Submodule.Quotient.induction_on with
  | _ a =>
    induction b using Submodule.Quotient.induction_on with
    | _ b =>
      exact congrArg (Submodule.Quotient.mk (p := EtaleCohomologyProducts.boundaries w hw p (r+q)))
        (cycleProduct_map v hv w hw p q r a b)

end EnvelopeProperty.Cartier.EtaleCohomologyCoefficientProducts
