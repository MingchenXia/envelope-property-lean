import EnvelopeProperty.AlgGeom.Canonical.NativeInvertibility

/-! # Native original invertibility constructs an actual original over-site line atlas -/

open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace EnvelopeProperty.CanonicalGeometry
universe u
noncomputable section

/-- The ORIGINAL native invertibility cover yields a genuine original
line atlas with SAME actual over-site frames, without any atlas certificate. -/
def invertibleLineAtlas {X : Scheme.{u}} (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) : LineBundleAtlas L := by
  let ι := Classical.choose hL
  let U := Classical.choose (Classical.choose_spec hL)
  have hU : ⨆ i : ι, U i = ⊤ := (Classical.choose_spec (Classical.choose_spec hL)).1
  have htriv := (Classical.choose_spec (Classical.choose_spec hL)).2
  refine ⟨ι, U, ?_, fun i => ?_⟩
  · intro x
    apply Opens.mem_iSup.mp
    rw [hU]
    trivial
  · exact Scheme.Modules.overTrivializationOfRestrictIso L (U i)
      (Scheme.Modules.restrictIsoOfPullbackIso L (U i) (Classical.choice (htriv i)))

end
end EnvelopeProperty.CanonicalGeometry
