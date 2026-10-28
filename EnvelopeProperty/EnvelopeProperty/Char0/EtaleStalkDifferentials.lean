/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.EtaleDifferentials
import EnvelopeProperty.Char0.RelativeDifferentialJacobian
import EnvelopeProperty.Char0.SNCAffineFactors

/-!
# Actual differential bases and prime boundary germs in stalks

The adapted affine chart functions give both the actual differential basis in
the stalk and prime boundary germs there. These are produced from the actual
étale map, localization property and SNC regular-parameter data.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory Module IsLocalRing Ideal
open scoped Classical

universe u

variable {k : Type u} [Field k] {Y : Scheme.{u}} {n : ℕ}

/-- An actual affine étale chart produces the actual stalk differential basis by localization. -/
def schemeEtaleStalkDifferentialBasis (f : Y ⟶ Spec (.of k)) (U : Y.affineOpens)
    (v : Fin n → Γ(Y, U.1)) (hv : Etale (toAffineSpace f U.1 v)) (x : Y) (hx : x ∈ U.1) :
    letI := f.stalkAlgebra x
    Basis (Fin n) (Y.presheaf.stalk x) (KaehlerDifferential k (Y.presheaf.stalk x)) := by
  let _ := f.sectionsAlgebra U.1
  let _ := f.stalkAlgebra x
  let _ := Y.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := f.isScalarTower_sectionsAlgebra_stalk U.1 hx
  have := U.2.isLocalization_stalk ⟨x, hx⟩
  have : Algebra.FormallyEtale Γ(Y, U.1) (Y.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  exact differentialBasisBaseChange (schemeEtaleDifferentialBasis f U v hv)

/-- The produced stalk basis consists of the differentials of the original coordinate germs. -/
theorem schemeEtaleStalkDifferentialBasis_apply (f : Y ⟶ Spec (.of k)) (U : Y.affineOpens)
    (v : Fin n → Γ(Y, U.1)) (hv : Etale (toAffineSpace f U.1 v)) (x : Y) (hx : x ∈ U.1)
    (i : Fin n) :
    letI := f.stalkAlgebra x
    schemeEtaleStalkDifferentialBasis f U v hv x hx i =
      KaehlerDifferential.D k (Y.presheaf.stalk x) (Y.presheaf.germ U.1 x hx (v i)) := by
  let _ := f.sectionsAlgebra U.1
  let _ := f.stalkAlgebra x
  let _ := Y.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := f.isScalarTower_sectionsAlgebra_stalk U.1 hx
  have := U.2.isLocalization_stalk ⟨x, hx⟩
  have : Algebra.FormallyEtale Γ(Y, U.1) (Y.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  rw [schemeEtaleStalkDifferentialBasis, differentialBasisBaseChange_apply,
    schemeEtaleDifferentialBasis_apply, KaehlerDifferential.map_D]
  rfl

/-- Every actual boundary germ in an adapted affine chart is prime in the actual regular stalk. -/
theorem prime_snc_affine_boundary_germ (f : Y ⟶ Spec (.of k)) [Smooth f]
    (F : Scheme.DivisorFamily Y) (hF : F.IsSnc) (U : Y.affineOpens) (x : Y) (hx : x ∈ U.1)
    (v : Fin n → Γ(Y, U.1))
    (c : {i : F.ι // x ∈ (F.component i).support} → Fin n)
    (hc : ∀ i, (F.component i.1).ideal U = span {v (c i)}) :
    ∀ i, Prime (Y.presheaf.germ U.1 x hx (v (c i))) := by
  have := isRegularLocalRing_stalk f x
  obtain ⟨m, z, hz, c₀, _, hFz⟩ := hF.2 x
  intro i
  have hspan : span {Y.presheaf.germ U.1 x hx (v (c i))} = span {z (c₀ i)} := by
    rw [← hFz i, Scheme.IdealSheafData.stalkIdeal_eq_map_germ _ U hx,
      hc i, Ideal.map_span, Set.image_singleton]
  have hassoc := Ideal.span_singleton_eq_span_singleton.mp hspan
  exact hassoc.prime_iff.mpr (prime_of_parameters hz.1.symm hz.2 (c₀ i))

end EnvelopeProperty.Char0
