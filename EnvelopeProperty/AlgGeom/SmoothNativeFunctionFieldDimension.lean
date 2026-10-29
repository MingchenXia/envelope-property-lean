import EnvelopeProperty.AlgGeom.SchemeFunctionFieldSubalgebras
import EnvelopeProperty.AlgGeom.Canonical.SmoothCanonicalCharts
import Hironaka.Algebra.RegularSmooth.Trdeg
import Hironaka.Resolution.Algebraic.Kol07.Thm36.RelativeDimensionConstancy

/-! # Genuine actual smooth relative dimension from original native function-field degree -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.SmoothNativeFunctionFieldDimension

private theorem differentialRank_of_standardSmooth
    (F A K : Type u) [Field F] [CommRing A] [IsDomain A] [Field K]
    [Algebra F A] [Algebra F K] [Algebra A K] [IsScalarTower F A K]
    [IsFractionRing A K] (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n F A] :
    Module.rank K (KaehlerDifferential F K) = n := by
  let b := CanonicalGeometry.standardSmoothDifferentialBasis F A n
  let bK := b.ofIsLocalizedModule K (nonZeroDivisors A) (KaehlerDifferential.map F F A K)
  let bK' : Module.Basis (ULift.{u} (Fin n)) K (KaehlerDifferential F K) :=
    bK.reindex Equiv.ulift.symm
  simpa using bK'.mk_eq_rank''.symm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- SAME actual original smooth integral scheme has relative dimension equal
to its true native function-field transcendence degree over original perfect F. -/
theorem relativeDimension_eq_trdeg {F : Type u} [Field F] [PerfectField F]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of F)) [Smooth f]
    (d : ℕ) (htr : letI := f.stalkAlgebra (genericPoint X); Algebra.trdeg F X.functionField = d) :
    SmoothOfRelativeDimension d f := by
  obtain ⟨n,hn⟩ := Hironaka.Resolution.exists_smoothOfRelativeDimension_of_irreducibleSpace f
  let := hn
  obtain ⟨U,hU,V,hV,hx,e,hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) (genericPoint X)
  have hUt : U = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = f (genericPoint X) := by
      let : Subsingleton (Spec (.of F)) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
      exact Subsingleton.elim _ _
    rw [hy]
    exact e hx
  subst U
  let := f.sectionsAlgebra V
  let := f.stalkAlgebra (genericPoint X)
  let : Nonempty V := ⟨⟨genericPoint X,hx⟩⟩
  let : Algebra Γ(X,V) X.functionField := (X.germToFunctionField V).hom.toAlgebra
  let : IsFractionRing Γ(X,V) X.functionField := functionField_isFractionRing_of_isAffineOpen X V hV
  let : IsScalarTower F Γ(X,V) X.functionField := f.isScalarTower_sectionsAlgebra_stalk V hx
  have hs : Algebra.IsStandardSmoothOfRelativeDimension n F Γ(X,V) := by
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact (show RingHom.IsStandardSmoothOfRelativeDimension (n+0) _ from
      hf.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv
        (Scheme.ΓSpecIso (.of F)).symm.commRingCatIsoToRingEquiv))
  let := hs
  have hr := differentialRank_of_standardSmooth F Γ(X,V) X.functionField n
  let : Algebra.FiniteType F Γ(X,V) := f.finiteType_sectionsAlgebra hV
  let : Algebra.EssFiniteType Γ(X,V) X.functionField :=
    Algebra.EssFiniteType.of_isLocalization X.functionField (nonZeroDivisors Γ(X,V))
  let : Algebra.EssFiniteType F X.functionField := Algebra.EssFiniteType.comp F Γ(X,V) X.functionField
  have hd := Algebra.rank_kaehlerDifferential_eq_trdeg_of_perfectField F X.functionField
  have hnd : n = d := by exact_mod_cast hr.symm.trans (hd.trans htr)
  subst n
  exact hn

end EnvelopeProperty.SmoothNativeFunctionFieldDimension
