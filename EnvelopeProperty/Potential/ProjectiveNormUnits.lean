import EnvelopeProperty.Berkovich.ProjectiveNormForm

/-! # Actual finite-projective norm unit detection without a global basis -/

noncomputable section
namespace EnvelopeProperty

/-- A unit intrinsic determinant gives actual surjectivity, using the constructed
finite free retract rather than a global free basis of the original module. -/
theorem surjective_of_isUnit_projectiveDet {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (f : Module.End R M) (hf : IsUnit (projectiveDet R M f)) : Function.Surjective f := by
  let s := FiniteFreeSplitting.ofFiniteProjective (R := R) (M := M)
  have hs : IsUnit (LinearMap.det (s.stabilized f)) := by
    simpa only [projectiveDet_eq_split s,FiniteFreeSplitting.det] using hf
  have hsunit : IsUnit (s.stabilized f) :=
    (LinearMap.isUnit_iff_isUnit_det (s.stabilized f)).mpr hs
  have hsurj : Function.Surjective (s.stabilized f) :=
    ((Module.End.isUnit_iff (s.stabilized f)).mp hsunit).surjective
  intro x
  obtain ⟨v,hv⟩ := hsurj (s.i x)
  refine ⟨s.p v,?_⟩
  have hp := congrArg s.p hv
  simpa [FiniteFreeSplitting.stabilized] using hp

/-- The genuine intrinsic norm detects actual algebra units, including varying rank. -/
theorem isUnit_projectiveNorm_iff {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Finite R A] [Module.Projective R A] (a : A) :
    IsUnit (projectiveNorm R A a) ↔ IsUnit a := by
  constructor
  · intro ha
    obtain ⟨b,hb⟩ := surjective_of_isUnit_projectiveDet (Algebra.lmul R A a) ha 1
    exact isUnit_iff_exists_inv.mpr ⟨b,hb⟩
  · intro ha
    exact ha.map (projectiveNorm R A)

end EnvelopeProperty
