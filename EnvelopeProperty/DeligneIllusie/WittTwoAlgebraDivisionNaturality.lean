import EnvelopeProperty.DeligneIllusie.WittTwoAlgebraDivision

/-! # Actual original residue and kernel division under actual Witt algebra maps -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoAlgebraDivisionNaturality
open scoped TensorProduct
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
variable {A A' : Type u} [CommRing A] [CommRing A']
  [Algebra (WittTwo.Ring p k) A] [Algebra (WittTwo.Ring p k) A']
private abbrev B (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A] :=
  k ⊗[WittTwo.Ring p k] A

/-- The SAME actual original residue algebra map induced by the original Witt-algebra morphism. -/
def residueMap (β : A →ₐ[WittTwo.Ring p k] A') : B p k A →ₐ[k] B p k A' where
  toRingHom := (Algebra.TensorProduct.map (AlgHom.id (WittTwo.Ring p k) k) β).toRingHom
  commutes' c := by
    change (Algebra.TensorProduct.map (AlgHom.id (WittTwo.Ring p k) k) β)
      (c ⊗ₜ[WittTwo.Ring p k] (1 : A)) = c ⊗ₜ[WittTwo.Ring p k] (1 : A')
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]

/-- EVERY original pure tensor retains its actual coefficient and mapped original coordinate. -/
theorem residueMap_tmul (β : A →ₐ[WittTwo.Ring p k] A') (c : k) (a : A) :
    residueMap p k β (c ⊗ₜ[WittTwo.Ring p k] a) = c ⊗ₜ[WittTwo.Ring p k] β a := by
  change (Algebra.TensorProduct.map (AlgHom.id (WittTwo.Ring p k) k) β)
    (c ⊗ₜ[WittTwo.Ring p k] a) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

/-- The ENTIRE actual original residue square commutes on EVERY original algebra element. -/
theorem residueMap_reduction (β : A →ₐ[WittTwo.Ring p k] A') (a : A) :
    residueMap p k β (algebraMap A (B p k A) a) = algebraMap A' (B p k A') (β a) :=
  residueMap_tmul p k β 1 a

/-- Restrict the SAME actual original algebra map to the genuine original residue kernels. -/
def kernelMap (β : A →ₐ[WittTwo.Ring p k] A') :
    WittTwoAlgebraDivision.Kernel p k A →ₛₗ[β.toRingHom] WittTwoAlgebraDivision.Kernel p k A' where
  toFun x := ⟨β x.val, by
    change algebraMap A' (B p k A') (β x.val) = 0
    rw [← residueMap_reduction p k β x.val]
    rw [x.property, map_zero]⟩
  map_add' x y := Subtype.ext (β.map_add x.val y.val)
  map_smul' a x := Subtype.ext (β.map_mul a x.val)

/-- Every original kernel element keeps EXACTLY its actual algebra-map value. -/
theorem kernelMap_value (β : A →ₐ[WittTwo.Ring p k] A') (x : WittTwoAlgebraDivision.Kernel p k A) :
    (kernelMap p k β x).val = β x.val := rfl

variable [CharP k p]

/-- Actual prime multiples are carried to the SAME actual original prime multiples. -/
theorem kernelMap_primeElement (β : A →ₐ[WittTwo.Ring p k] A') (a : A) :
    kernelMap p k β (WittTwoAlgebraDivision.primeElement p k A a) =
      WittTwoAlgebraDivision.primeElement p k A' (β a) := by
  apply Subtype.ext
  change β ((p : A) * a) = (p : A') * β a
  rw [map_mul, map_natCast]

variable [PerfectRing k p]
  [Algebra.Smooth (WittTwo.Ring p k) A] [Algebra.Smooth (WittTwo.Ring p k) A']

/-- The SAME actual canonical coefficient division commutes on the ENTIRE genuine residue kernel. -/
theorem dividePrime_naturality (β : A →ₐ[WittTwo.Ring p k] A')
    (x : WittTwoAlgebraDivision.Kernel p k A) :
    WittTwoAlgebraDivision.dividePrimeLinear p k A' (kernelMap p k β x) =
      residueMap p k β (WittTwoAlgebraDivision.dividePrimeLinear p k A x) := by
  obtain ⟨a, rfl⟩ := WittTwoAlgebraDivision.kernel_prime p k A x
  rw [kernelMap_primeElement, WittTwoAlgebraDivision.dividePrime_primeElement,
    WittTwoAlgebraDivision.dividePrime_primeElement, residueMap_reduction]

end EnvelopeProperty.DeligneIllusie.WittTwoAlgebraDivisionNaturality
