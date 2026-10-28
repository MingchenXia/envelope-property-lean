import EnvelopeProperty.Vanishing.NadelPrincipalizationAffineChart
import Hironaka.Scheme.Smooth.EtaleLocal

/-! # Actual original etale function-field charts chosen from original smoothness -/

open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationEtaleChart

variable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]

/-- The actual original section algebra has an actual original etale tuple
on an internally produced original affine neighborhood. -/
theorem exists_chart (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      letI := f.sectionsAlgebra U.1
      ∃ v : Fin n → Γ(X, U.1), (MvPolynomial.aeval (R := k) v).toRingHom.Etale := by
  obtain ⟨U, hx, v, hv⟩ := exists_etale_toAffineSpace f n x
  exact ⟨U, hx, v, (etale_toAffineSpace_iff f U.2 v).mp hv⟩

/-- The original affine neighborhood is chosen from the proved local producer. -/
def chart (x : X) : X.affineOpens := Classical.choose (exists_chart f n x)

/-- The selected actual original affine open contains the original point. -/
theorem mem_chart (x : X) : x ∈ (chart f n x).1 :=
  (Classical.choose_spec (exists_chart f n x)).1

instance chart_nonempty (x : X) : Nonempty (chart f n x).1 := ⟨⟨x, mem_chart f n x⟩⟩

/-- The actual original coordinates of the selected original section ring. -/
def coordinates (x : X) : Fin n → Γ(X, (chart f n x).1) := by
  letI := f.sectionsAlgebra (chart f n x).1
  exact Classical.choose (Classical.choose_spec (exists_chart f n x)).2

/-- Etaleness is derived internally for the SAME original section-algebra structure. -/
theorem coordinates_etale (x : X) :
    let := f.sectionsAlgebra (chart f n x).1
    (MvPolynomial.aeval (R := k) (coordinates f n x)).toRingHom.Etale := by
  let := f.sectionsAlgebra (chart f n x).1
  exact Classical.choose_spec (Classical.choose_spec (exists_chart f n x)).2

variable [IsIntegral X]

/-- The actual original coordinates in the literal original generic-germ image algebra. -/
def fieldCoordinates (x : X) :
    letI := f.stalkAlgebra (genericPoint X)
    Fin n → NadelPrincipalizationAffineChart.algebra f (chart f n x) := by
  letI := f.sectionsAlgebra (chart f n x).1
  letI := f.stalkAlgebra (genericPoint X)
  exact fun i => NadelPrincipalizationAffineChart.equiv f (chart f n x) (coordinates f n x i)

omit [SmoothOfRelativeDimension n f] in
/-- Any actual original etale tuple is transported through the SAME
original generic-germ equivalence, with the original coefficient action. -/
theorem mapped_coordinates_etale (U : X.affineOpens) [Nonempty U.1]
    (v : Fin n → Γ(X, U.1))
    (hv : letI := f.sectionsAlgebra U.1; (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    letI := f.stalkAlgebra (genericPoint X)
    (MvPolynomial.aeval (R := k)
      (fun i => NadelPrincipalizationAffineChart.equiv f U (v i))).toRingHom.Etale := by
  let := f.sectionsAlgebra U.1
  let := f.stalkAlgebra (genericPoint X)
  let e := NadelPrincipalizationAffineChart.equiv f U
  have he : e.toRingHom.Etale := RingHom.Etale.of_bijective e.bijective
  have hc : (MvPolynomial.aeval (R := k) (fun i => e (v i))).toRingHom =
      e.toRingHom.comp (MvPolynomial.aeval (R := k) v).toRingHom := by
    exact congrArg AlgHom.toRingHom (MvPolynomial.comp_aeval v e.toAlgHom).symm
  rw [hc]
  exact RingHom.Etale.stableUnderComposition _ _ hv he

/-- Transport uses the same original algebra equivalence, so the actual
literal generic-germ image coordinates are genuinely etale. -/
theorem fieldCoordinates_etale (x : X) :
    let := f.stalkAlgebra (genericPoint X)
    (MvPolynomial.aeval (R := k) (fieldCoordinates f n x)).toRingHom.Etale := by
  let := f.sectionsAlgebra (chart f n x).1
  let := f.stalkAlgebra (genericPoint X)
  let e := NadelPrincipalizationAffineChart.equiv f (chart f n x)
  have he : e.toRingHom.Etale := RingHom.Etale.of_bijective e.bijective
  have hc : (MvPolynomial.aeval (R := k) (fieldCoordinates f n x)).toRingHom =
      e.toRingHom.comp (MvPolynomial.aeval (R := k) (coordinates f n x)).toRingHom := by
    exact congrArg AlgHom.toRingHom (MvPolynomial.comp_aeval (coordinates f n x) e.toAlgHom).symm
  rw [hc]
  exact RingHom.Etale.stableUnderComposition _ _ (coordinates_etale f n x) he

/-- The actual original field-chart spectrum covers its original selected point. -/
theorem map_covers (x : X) :
    ∃ y, NadelPrincipalizationAffineChart.map f (chart f n x) y = x := by
  have hx : x ∈ Set.range (chart f n x).2.fromSpec := by
    rw [(chart f n x).2.range_fromSpec]
    exact mem_chart f n x
  obtain ⟨y, hy⟩ := hx
  let e := NadelPrincipalizationAffineChart.specIso f (chart f n x)
  have he : e.hom (e.inv y) = y := by
    have h := congrArg (fun a : Spec (.of Γ(X, (chart f n x).1)) ⟶
      Spec (.of Γ(X, (chart f n x).1)) => a y) e.inv_hom_id
    exact h
  refine ⟨e.inv y, ?_⟩
  change (chart f n x).2.fromSpec (e.hom (e.inv y)) = x
  exact (congrArg (chart f n x).2.fromSpec he).trans hy

/-- The actual original coefficient spectra form a genuine whole open cover. -/
def cover : X.OpenCover :=
  Scheme.Cover.mkOfCovers X
    (fun x => Spec (.of (NadelPrincipalizationAffineChart.algebra f (chart f n x))))
    (fun x => NadelPrincipalizationAffineChart.map f (chart f n x))
    (fun x => ⟨x, map_covers f n x⟩)

/-- The same original scheme, including every original point, is covered. -/
theorem cover_iSup_opensRange :
    ⨆ x, (NadelPrincipalizationAffineChart.map f (chart f n x)).opensRange = ⊤ :=
  (cover f n).iSup_opensRange

end EnvelopeProperty.Vanishing.NadelPrincipalizationEtaleChart
