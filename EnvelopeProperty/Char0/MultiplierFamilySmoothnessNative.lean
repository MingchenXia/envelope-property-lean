import EnvelopeProperty.Char0.MultiplierFamilySmoothnessNativeCharts

/-! # Actual original algebra charts imply smoothness of the SAME whole native scheme -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
universe u
namespace EnvelopeProperty.Char0.MultiplierFamilySmoothness
open ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The actual original inverse-coordinate affine schemes form a genuine cover of the SAME native variety. -/
def nativeAffineCover : X.NativeScheme.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (Fin (M + 1))
    (fun j => Spec (.of Γ(X.NativeScheme, nativeChartOpen X j)))
    (fun j => (nativeChartOpen_isAffine X j).fromSpec)
    (by
      intro x
      have hp : X.nativeInclusion x ∈ ⨆ j : Fin (M + 1), nativeCoordinateOpen (R := k) j := by
        have htop : (⨆ j : Fin (M + 1), nativeCoordinateOpen (R := k) j) = ⊤ := by
          apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
          rw [irrelevant_eq_idealOfVars, MvPolynomial.idealOfVars]
        rw [htop]
        trivial
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hp
      have hx : x ∈ Set.range (nativeChartOpen_isAffine X j).fromSpec := by
        rw [(nativeChartOpen_isAffine X j).range_fromSpec]
        exact hj
      obtain ⟨y, hy⟩ := hx
      exact ⟨j, y, hy⟩)
    (fun _ => inferInstance)

/-- The ORIGINAL algebraic HasSmoothCharts condition DERIVES actual smoothness of the SAME
native field structure. No native smoothness, chosen model, atlas or coordinate certificate is supplied. -/
theorem nativeStructure_smooth (hs : X.HasSmoothCharts) : Smooth X.nativeStructure := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) (nativeAffineCover X)).mpr
  intro j
  exact nativeChart_smooth X hs j

end EnvelopeProperty.Char0.MultiplierFamilySmoothness
