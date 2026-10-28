/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.BlowupChartHomSurjective

/-!
# Exact bihomogeneous kernel of the original blowup chart map

For a nonzero original chart denominator, a bihomogeneous form vanishes in
the actual fraction-adjoin chart exactly when it belongs to the original
Rees ideal. This is the kernel-clearing producer needed for inverse chart
points; no such inverse is assumed.
-/

open MvPolynomial
noncomputable section
namespace EnvelopeProperty.ProjSubvariety.BlowupCenter
universe u
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (B : V.BlowupCenter M') (i : Fin (M + 1))
    [IsDomain (ProjBerk.QuotChartAlg V.ideal (X i) 1)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On bihomogeneous forms the genuine chart kernel is exactly the original
blowup ideal, using the actual nonzero fractional denominator. -/
theorem fc_chartHom_eq_zero_iff_mem_ideal
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg0 : g ≠ 0)
    {a b : ℕ} {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    B.chartHom i g F = 0 ↔ F ∈ B.ideal := by
  refine ⟨fun hz => ?_, fun hI => B.chartHom_eq_zero_of_mem g hI⟩
  apply (B.mem_ideal_iff_of_isWeightedHomogeneous hF).2
  let A := ProjBerk.QuotChartAlg V.ideal (X i) 1
  have hG := B.aeval_quotChartMk_X_G i
  have key := @coe_dehomHom_of_isWeightedHomogeneous k _ _ _ _ _ M M'
    (B.centerSet i) g (fun j => ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j))
    (B.centerGen i) (B.centerGen_mem_centerSet i) B.G
  have he := key hG hF
  change (B.chartHom i g F : FractionRing A) =
    (algebraMap A (FractionRing A) g)⁻¹ ^ b *
      algebraMap A (FractionRing A)
        ((aeval fun j => ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j)) (B.subst F)) at he
  rw [hz] at he
  have hgF : algebraMap A (FractionRing A) g ≠ 0 :=
    fun h => hg0 ((IsFractionRing.injective A (FractionRing A)) (by simpa only [map_zero] using h))
  have hc := (mul_eq_zero.1 he.symm).resolve_left (pow_ne_zero b (inv_ne_zero hgF))
  have hcoef : (aeval fun j => ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j)) (B.subst F) = 0 := by
    apply IsFractionRing.injective A (FractionRing A)
    simpa only [map_zero] using hc
  have hhom := B.isHomogeneous_subst hF
  rw [aeval_quotChartMk_X i hhom] at hcoef
  exact (ProjBerk.quotChartMk_eq_zero_iff (X_notMem_ideal_of_isDomain (V := V) i)
    (by simpa only [mul_one] using hhom)).1 hcoef

end EnvelopeProperty.ProjSubvariety.BlowupCenter
