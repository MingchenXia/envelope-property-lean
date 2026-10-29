import EnvelopeProperty.DeligneIllusie.WittTwoFlat
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Witt Two Module Division

Canonical linear division on actual flat Witt modules and its actual naturality. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopeProperty.DeligneIllusie.WittTwoModuleDivision

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]
variable (M : Type*) [AddCommGroup M] [Module (WittTwo.Ring p k) M]

/-- The actual range of original prime scalar multiplication. -/
def primeSubmodule : Submodule (WittTwo.Ring p k) M :=
  LinearMap.range (WittTwoFlat.primeSmul p k M)

/-- The actual module quotient by original prime multiples. -/
abbrev Reduction := M ⧸ primeSubmodule p k M

/-- An original prime multiple regarded as an element of the original range. -/
def primeMultiple (m : M) : primeSubmodule p k M :=
  ⟨WittTwoFlat.primeSmul p k M m, ⟨m, rfl⟩⟩

variable [Module.Flat (WittTwo.Ring p k) M]

/-- Canonical division as an original linear equivalence pM ≃ M/pM. -/
def dividePrimeEquiv : primeSubmodule p k M ≃ₗ[WittTwo.Ring p k] Reduction p k M :=
  (WittTwoFlat.primeSmul p k M).quotKerEquivRange.symm.trans
    (Submodule.quotEquivOfEq _ _ (WittTwoFlat.primeSmul_exact p k M).linearMap_ker_eq)

/-- Canonical division gives the original class of every original preimage. -/
theorem dividePrime_primeMultiple (m : M) :
    dividePrimeEquiv p k M (primeMultiple p k M m) =
      (primeSubmodule p k M).mkQ m := by
  simp only [dividePrimeEquiv, primeMultiple, primeSubmodule, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply]
  rfl

variable {M} {N : Type*} [AddCommGroup N] [Module (WittTwo.Ring p k) N]

/-- The actual original linear map on prime images. -/
def primeMap (T : M →ₗ[WittTwo.Ring p k] N) :
    primeSubmodule p k M →ₗ[WittTwo.Ring p k] primeSubmodule p k N :=
  (T.comp (primeSubmodule p k M).subtype).codRestrict _ (by
    rintro ⟨x, m, rfl⟩
    exact ⟨T m, (T.map_smul _ m).symm⟩)

/-- The actual quotient map induced by the same original linear map. -/
def reductionMap (T : M →ₗ[WittTwo.Ring p k] N) :
    Reduction p k M →ₗ[WittTwo.Ring p k] Reduction p k N :=
  (primeSubmodule p k M).mapQ (primeSubmodule p k N) T (by
    rintro x ⟨m, rfl⟩
    exact ⟨T m, (T.map_smul _ m).symm⟩)

omit [Module.Flat (WittTwo.Ring p k) M] [CharP k p] [PerfectRing k p] in
private theorem primeMap_primeMultiple (T : M →ₗ[WittTwo.Ring p k] N) (m : M) :
    primeMap p k T (primeMultiple p k M m) = primeMultiple p k N (T m) := by
  apply Subtype.ext
  exact T.map_smul _ m

variable [Module.Flat (WittTwo.Ring p k) N]

/-- The whole canonical divided maps commute with every original linear map. -/
theorem dividePrime_naturality (T : M →ₗ[WittTwo.Ring p k] N) :
    (dividePrimeEquiv p k N).toLinearMap.comp (primeMap p k T) =
      (reductionMap p k T).comp (dividePrimeEquiv p k M).toLinearMap := by
  apply LinearMap.ext
  rintro ⟨x, m, rfl⟩
  change dividePrimeEquiv p k N (primeMap p k T (primeMultiple p k M m)) =
    reductionMap p k T (dividePrimeEquiv p k M (primeMultiple p k M m))
  rw [primeMap_primeMultiple, dividePrime_primeMultiple, dividePrime_primeMultiple]
  rfl

end EnvelopeProperty.DeligneIllusie.WittTwoModuleDivision
