import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # Dominance over the polynomial line from a genuine nonempty central fibre -/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial
noncomputable section
universe u

namespace EnvelopeProperty.PolynomialDominanceFromCentralFiber

/-- The actual zero-section morphism maps the unique field point to the ideal (X). -/
theorem zeroSectionPoint_asIdeal {k : Type u} [Field k] :
    ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
      (IsLocalRing.closedPoint k)).asIdeal = Ideal.span {(Polynomial.X : k[X])} := by
  rw [show IsLocalRing.closedPoint k = (⊥ : PrimeSpectrum k) from Subsingleton.elim _ _]
  change Ideal.comap (Polynomial.evalRingHom (0 : k)) (⊥ : Ideal k) = _
  rw [← RingHom.ker_eq_comap_bot, Polynomial.ker_evalRingHom]
  simp

/-- A genuine central point together with nonvanishing at the original generic point
forces dominance over k[X]; no finiteness, normality or flatness premise is needed. -/
theorem isDominant_of_zeroSectionPoint {k : Type u} [Field k] {D : Scheme.{u}}
    [IsIntegral D] (p : D ⟶ Spec (.of k[X])) (z₀ : D)
    (hz₀ : p z₀ = (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
      (IsLocalRing.closedPoint k))
    (ht : (Polynomial.X : k[X]) ∉ (p (genericPoint D)).asIdeal) : IsDominant p := by
  have hle : (p (genericPoint D)).asIdeal ≤ (p z₀).asIdeal :=
    (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr
      ((PrimeSpectrum.le_iff_specializes _ _).mpr
        ((genericPoint_specializes z₀).map p.continuous))
  have hzIdeal : (p z₀).asIdeal = Ideal.span {(Polynomial.X : k[X])} := by
    rw [hz₀]
    exact zeroSectionPoint_asIdeal
  have hbot : (p (genericPoint D)).asIdeal = ⊥ := by
    by_contra hne
    let : (p (genericPoint D)).asIdeal.IsPrime := (p (genericPoint D)).isPrime
    have hm : (p (genericPoint D)).asIdeal.IsMaximal :=
      IsPrime.to_maximal_ideal hne
    have he := hm.eq_of_le (p z₀).isPrime.ne_top hle
    apply ht
    rw [he, hzIdeal]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hη : p (genericPoint D) = genericPoint (Spec (.of k[X])) := by
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    exact hbot
  rw [isDominant_iff]
  change Dense (Set.range p)
  apply Dense.mono (s₁ := {genericPoint (Spec (.of k[X]))})
  · exact Set.singleton_subset_iff.mpr ⟨genericPoint D, hη⟩
  · exact dense_iff_closure_eq.mpr (genericPoint_spec (Spec (.of k[X]))).def

/-- The actual whole nonempty central-fibre triangle internally supplies the central
point; only its original generic nonvanishing is additionally required. -/
theorem isDominant_of_centralFiber {k : Type u} [Field k] {D C : Scheme.{u}}
    [IsIntegral D] [Nonempty C] (p : D ⟶ Spec (.of k[X])) (g : C ⟶ D)
    (q : C ⟶ Spec (.of k))
    (hc : g ≫ p = q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (ht : (Polynomial.X : k[X]) ∉ (p (genericPoint D)).asIdeal) : IsDominant p := by
  let c : C := Classical.choice inferInstance
  apply isDominant_of_zeroSectionPoint p (g c) _ ht
  have he := congrArg (fun a : C ⟶ Spec (.of k[X]) => a c) hc
  change p (g c) = (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))) (q c)
    at he
  exact he.trans (congrArg
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (Subsingleton.elim (q c) (IsLocalRing.closedPoint k)))

end EnvelopeProperty.PolynomialDominanceFromCentralFiber

