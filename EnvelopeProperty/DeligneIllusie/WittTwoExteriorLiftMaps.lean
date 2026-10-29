import EnvelopeProperty.DeligneIllusie.WittTwoOriginalCotangentMaps
import EnvelopeProperty.Cartier.EtaleDifferentialIntrinsic
import EnvelopeProperty.Cartier.EtaleAlgebraFrobeniusComplex
import EnvelopeProperty.Cartier.ExteriorBasisScalarExtension

/-!
# Witt Two Exterior Lift Maps

Actual whole exterior lift maps into the SAME original all-algebra Frobenius de Rham complex. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.DeligneIllusie.WittTwoExteriorLiftMaps
open CategoryTheory Limits
open scoped TensorProduct
open Cartier.PolynomialDeRham
universe u

private theorem nativeWedgeOne {B M : Type u} [CommRing B] [AddCommGroup M] [Module B M]
    (q : ℕ) (m : M) (w : ⋀[B]^q M) :
    Cartier.EtaleGradedLeibniz.wedgeProduct 1 q ((exteriorPower.oneEquiv B M).symm m) w =
      leftWedge m q w := by
  rw [exteriorPower.oneEquiv_symm_apply]
  apply Subtype.ext
  change ExteriorAlgebra.ιMulti B 1 (fun _ => m) * (w : ExteriorAlgebra B M) =
    ExteriorAlgebra.ι B m * w
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

private theorem nativeClosedTuple {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
    (q : ℕ) (t : Fin q → KaehlerDifferential R B)
    (h : ∀ j, Cartier.EtaleDeRham.differential v hv 1
      ((exteriorPower.oneEquiv B (KaehlerDifferential R B)).symm (t j)) = 0) :
    Cartier.EtaleDeRham.differential v hv q (exteriorPower.ιMulti B q t) = 0 := by
  induction q with
  | zero =>
    have ht : t = fun _ : Fin 0 => KaehlerDifferential.D R B 0 := funext fun j => Fin.elim0 j
    rw [ht]
    exact Cartier.EtaleDifferentialIntrinsic.differential_universalWedge v hv 0 (fun _ => 0)
  | succ q ih =>
    have heq : exteriorPower.ιMulti B (q+1) t =
        Cartier.EtaleGradedLeibniz.wedgeProduct 1 q
          ((exteriorPower.oneEquiv B (KaehlerDifferential R B)).symm (t 0))
          (exteriorPower.ιMulti B q (fun j => t j.succ)) := by
      rw [nativeWedgeOne, Cartier.ExteriorBasisScalarExtension.leftWedge_ιMulti]
      congr 1
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    rw [heq]
    apply Subtype.ext
    have hd := Cartier.EtaleGradedLeibniz.differential_wedgeProduct v hv 1 q
      ((exteriorPower.oneEquiv B (KaehlerDifferential R B)).symm (t 0))
      (exteriorPower.ιMulti B q (fun j => t j.succ))
    rw [h 0, ih (fun j => t j.succ) (fun j => h j.succ)] at hd
    simpa only [Submodule.coe_zero, zero_mul, mul_zero, smul_zero, add_zero] using hd

private theorem nativeMapClosed (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {B : Type u} [CommRing B] [Algebra k B] {n : ℕ}
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (φ : KaehlerDifferential k B →ₛₗ[Cartier.AlgebraFrobenius.map k B p] KaehlerDifferential k B)
    (hφ : ∀ w, Cartier.EtaleDeRham.differential v hv 1
      ((exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm (φ w)) = 0)
    (q : ℕ) (w : ⋀[B]^q (KaehlerDifferential k B)) :
    Cartier.EtaleDeRham.differential v hv q
      (CanonicalGeometry.exteriorSemilinearMap (Cartier.AlgebraFrobenius.map k B p) φ q w) = 0 := by
  have hw : w ∈ Submodule.span B (Set.range (exteriorPower.ιMulti B q (M := KaehlerDifferential k B))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨t, rfl⟩ := hw
    rw [CanonicalGeometry.exteriorSemilinearMap_ιMulti]
    exact nativeClosedTuple v hv q _ (fun j => hφ (t j))
  | zero => rw [map_zero, map_zero]
  | add w z _ _ hw hz => rw [map_add, map_add, hw, hz, add_zero]
  | smul b w _ hw =>
    rw [LinearMap.map_smulₛₗ, Cartier.AlgebraFrobenius.map_apply,
      Cartier.EtaleAlgebraFrobeniusComplex.differential_pow_smul, hw, smul_zero]

private def nativeRestrictedMap {B M N : Type u} [CommRing B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (F : B →+* B) (g : M →ₛₗ[F] N) :
    ModuleCat.of B M ⟶ (ModuleCat.restrictScalars F).obj (ModuleCat.of B N) := by
  let Y := (ModuleCat.restrictScalars F).obj (ModuleCat.of B N)
  letI := Y.isModule
  exact ModuleCat.ofHom (X := ModuleCat.of B M) (Y := Y)
    { toFun := g, map_add' := g.map_add, map_smul' := g.map_smulₛₗ }

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoSourceResidue.twistSMul WittTwoRelativeLift.residueCopyAlgebra
  WittTwoLiftDifference.frobeniusAlgebra
variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A]
private abbrev B := WittTwoSmoothDifferentials.ResidueAlgebra p k A
attribute [local instance] WittTwoOriginalCotangentMaps.originalResidueRing
  WittTwoOriginalCotangentMaps.residueAlgebra
local instance originalCommSemiring : CommSemiring (B p k A) :=
  (WittTwoOriginalCotangentMaps.originalResidueRing p k A).toCommSemiring
local instance originalSemiring : Semiring (B p k A) :=
  (WittTwoOriginalCotangentMaps.originalResidueRing p k A).toCommSemiring.toSemiring
private abbrev N := KaehlerDifferential k (B p k A)
variable (f : WittTwoLiftDifference.Lift p k A)
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)

/-- The genuine SAME whole native exterior map in EVERY original degree. -/
def map (q : ℕ) : (⋀[B p k A]^q (N p k A)) →ₛₗ[Cartier.AlgebraFrobenius.map k (B p k A) p]
    (⋀[B p k A]^q (N p k A)) :=
  CanonicalGeometry.exteriorSemilinearMap (Cartier.AlgebraFrobenius.map k (B p k A) p)
    (WittTwoOriginalCotangentMaps.divided p k A f hf) q

/-- EVERY actual pure wedge retains EXACTLY the SAME original divided factors. -/
theorem map_ιMulti (q : ℕ) (t : Fin q → N p k A) :
    map p k A f hf q (exteriorPower.ιMulti (B p k A) q t) =
      exteriorPower.ιMulti (B p k A) q (WittTwoOriginalCotangentMaps.divided p k A f hf ∘ t) :=
  CanonicalGeometry.exteriorSemilinearMap_ιMulti _ _ q t

/-- The SAME entire actual exterior map preserves original left wedge multiplication. -/
theorem map_leftWedge (q : ℕ) (m : N p k A) (w : ⋀[B p k A]^q (N p k A)) :
    map p k A f hf (q+1) (leftWedge m q w) =
      leftWedge (WittTwoOriginalCotangentMaps.divided p k A f hf m) q (map p k A f hf q w) :=
  Cartier.ExteriorBasisScalarExtension.exteriorSemilinearMap_leftWedge _ _ m q w

variable {n : ℕ} (v : Fin n → B p k A)
  (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)

/-- EVERY original whole exterior lift image is an actual cycle in the SAME original complex. -/
theorem map_closed (q : ℕ) (w : ⋀[B p k A]^q (N p k A)) :
    Cartier.EtaleDeRham.differential v hv q (map p k A f hf q w) = 0 := by
  unfold map
  apply nativeMapClosed (B := B p k A) p k v hv
    (WittTwoOriginalCotangentMaps.divided p k A f hf)
  intro z
  rw [← WittTwoOriginalCotangentMaps.closedDerivative_apply p k A v hv
    (WittTwoOriginalCotangentMaps.divided p k A f hf z)]
  exact WittTwoOriginalCotangentMaps.divided_closed p k A f hf v hv z

/-- The SAME original exterior map is native B-linear into the SAME actual Frobenius form module. -/
def formMap (q : ℕ) : ModuleCat.of (B p k A) (⋀[B p k A]^q (N p k A)) ⟶
    Cartier.EtaleAlgebraFrobeniusComplex.formModule (k := k) (B := B p k A) p q :=
  nativeRestrictedMap _ (map p k A f hf q)

/-- The actual original exterior modules with their genuine zero differentials. -/
def zeroComplex : CochainComplex (ModuleCat (B p k A)) ℕ :=
  CochainComplex.of (fun q => ModuleCat.of (B p k A) (⋀[B p k A]^q (N p k A)))
    (fun _ => 0) (fun _ => by simp)

/-- The SAME genuine exterior lift maps form an actual map to the SAME ORIGINAL whole Frobenius de Rham complex. -/
def complexMap : zeroComplex p k A ⟶ Cartier.EtaleAlgebraFrobeniusComplex.complex v hv p where
  f q := formMap p k A f hf q
  comm' q r h := by
    have hr : q+1 = r := h
    subst r
    simp only [zeroComplex, Cartier.EtaleAlgebraFrobeniusComplex.complex, CochainComplex.of_d, zero_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    change Cartier.EtaleDeRham.differential v hv q (map p k A f hf q w) = 0
    exact map_closed p k A f hf v hv q w
end EnvelopeProperty.DeligneIllusie.WittTwoExteriorLiftMaps
