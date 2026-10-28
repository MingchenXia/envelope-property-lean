import BingWangEntropy.NativeProjectiveFano
import BingWangEntropy.AffineChartSectionExtension
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Nullstellensatz

/-!
# Actual projective Noetherian local algebra and genuine complex points

The literal projective embedding supplies native finite type and quasi-compactness.
The actual affine section modules are finite over their actual Noetherian rings.
Native maximal quotients and the algebraic closedness of the complex field
produce actual scheme points; no point-existence premise is added.
-/

open CategoryTheory AlgebraicGeometry Algebra TopologicalSpace
open scoped Topology

namespace BingWangEntropy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual projective structural map gives native locally Noetherian geometry. -/
theorem ClosedProjectiveEmbedding.isLocallyNoetherian {X : Scheme}
    {f : X ⟶ Spec (.of ℂ)} (e : ClosedProjectiveEmbedding f) : IsLocallyNoetherian X := by
  let := e.locallyOfFiniteType
  exact LocallyOfFiniteType.isLocallyNoetherian f

/-- The actual projective embedding gives native Noetherianness, using genuine quasi-compactness. -/
theorem ClosedProjectiveEmbedding.isNoetherian {X : Scheme}
    {f : X ⟶ Spec (.of ℂ)} (e : ClosedProjectiveEmbedding f) : IsNoetherian X := by
  let := e.quasiCompact
  let := e.isLocallyNoetherian
  let : CompactSpace X := isCompact_univ_iff.mp (by
    simpa only [Set.preimage_univ] using
      f.isSpectralMap.2 (s := Set.univ) isOpen_univ isCompact_univ)
  exact AlgebraicGeometry.IsNoetherian.mk

/-- Actual projective structure-sheaf stalks are native Noetherian rings. -/
theorem ClosedProjectiveEmbedding.stalk_isNoetherian {X : Scheme}
    {f : X ⟶ Spec (.of ℂ)} (e : ClosedProjectiveEmbedding f) (x : X) :
    IsNoetherianRing (X.presheaf.stalk x) := by
  let := e.isLocallyNoetherian
  infer_instance

/-- Every actual affine coordinate ring is Noetherian. -/
theorem ClosedProjectiveEmbedding.affineSections_isNoetherian {X : Scheme}
    {f : X ⟶ Spec (.of ℂ)} (e : ClosedProjectiveEmbedding f)
    {U : X.Opens} (hU : IsAffineOpen U) : IsNoetherianRing Γ(X, U) :=
  e.isLocallyNoetherian.component_noetherian ⟨U, hU⟩

/-- Actual affine line-sheaf sections are Noetherian modules over their actual coordinate ring. -/
theorem ClosedProjectiveEmbedding.affineLineSections_isNoetherian {X : Scheme}
    {f : X ⟶ Spec (.of ℂ)} (e : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) {U : X.Opens} (hU : IsAffineOpen U) :
    IsNoetherian Γ(X, U) Γ(L, U) := by
  let := e.affineSections_isNoetherian hU
  let := a.affineOpenSections_finite hU
  infer_instance

/-- Every actual tensor-power affine section module is Noetherian over the actual coordinate ring. -/
theorem ClosedProjectiveEmbedding.affinePowerSections_isNoetherian {X : Scheme}
    {f : X ⟶ Spec (.of ℂ)} (e : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) {U : X.Opens} (hU : IsAffineOpen U) (m : ℕ) :
    IsNoetherian Γ(X, U) Γ(bundleTensorPower L m, U) :=
  e.affineLineSections_isNoetherian (a.tensorPower m) hU

/-- The actual maximal quotient of a finite-type complex algebra is genuinely the complex field. -/
def finiteTypeComplexResidueAlgEquiv (A : Type) [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] (I : Ideal A) [I.IsMaximal] : (A ⧸ I) ≃ₐ[ℂ] ℂ := by
  let := Ideal.Quotient.field I
  let := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ I)
  let φ : (A ⧸ I) →ₐ[ℂ] ℂ := IsAlgClosed.lift
  exact AlgEquiv.ofBijective φ ⟨φ.injective, fun z => ⟨algebraMap ℂ (A ⧸ I) z, φ.commutes z⟩⟩

/-- A genuine nontrivial finite-type complex algebra has an actual complex algebra point. -/
theorem finiteTypeComplexAlgebraPoint_nonempty (A : Type) [CommRing A] [Nontrivial A]
    [Algebra ℂ A] [Algebra.FiniteType ℂ A] : Nonempty (ComplexAlgebraPoint A) := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal A
  let := hI
  exact ⟨(finiteTypeComplexResidueAlgEquiv A I).toAlgHom.comp (Ideal.Quotient.mkₐ ℂ I)⟩

/-- Every integral locally finite-type complex scheme has a genuine point over its literal structural map. -/
theorem integralFiniteTypeSchemeComplexPoint_nonempty {X : Scheme} [IsIntegral X]
    (f : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType f] : Nonempty (SchemeComplexPoint f) := by
  obtain ⟨R, g, hg, y, hy⟩ := X.exists_Spec_apply_eq (genericPoint X)
  let : Nontrivial R := by
    refine ⟨⟨1, 0, ?_⟩⟩
    intro h
    apply y.isPrime.ne_top
    apply (Ideal.eq_top_iff_one y.asIdeal).mpr
    rw [h]
    exact y.asIdeal.zero_mem
  let c : ComplexAffineChart X := ⟨R, g, hg⟩
  let := affinePointFieldAlgebra (g ≫ f)
  let := complexAffineChart_finiteType f c
  obtain ⟨q⟩ := finiteTypeComplexAlgebraPoint_nonempty R
  exact ⟨complexAffineChartPointMap f c ((affineSchemePointEquivOfStructure (g ≫ f)).symm q)⟩

/-- Actual smooth projective Fano geometry gives actual analytic point nonemptiness. -/
theorem SmoothProjectiveFano.complexPoint_nonempty {n : ℕ} (F : SmoothProjectiveFano n) :
    Nonempty (SchemeComplexPoint F.structureMap) := by
  let := F.projective.locallyOfFiniteType
  exact integralFiniteTypeSchemeComplexPoint_nonempty F.structureMap

end

end BingWangEntropy
