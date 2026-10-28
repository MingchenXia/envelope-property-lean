import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionSectionPowers
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionFixedCutUniformLocalGeneration
import EnvelopeProperty.AlgGeom.ProjectiveLineClosedPointEvaluation
import Lean

/-! A nonzero original power section with ample actual cut restriction
internally produces finite generators of all large original divisible powers. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion
open CanonicalGeometry SchemeLineSectionEvaluation
attribute [local instance] Scheme.Modules.monoidalCategory

/- Read-only reference to the exact original compiled support theorem.
No imported environment or provider is mutated; the resulting term is an
ordinary original kernel constant, with its native owner and kind checked. -/
open Lean Elab Term in
elab "existingClosedPointZeroSupport%" : term => do
  let env := (← getEnv).setExporting false
  let expected := `EnvelopeProperty.AlgGeom.ProjectiveLineClosedPointEvaluation
  let anchor := `EnvelopeProperty.ProjectiveLineClosedPointEvaluation.fiber_finite_finrank_eq_residue
  let some idx := env.getModuleIdxFor? anchor | throwError "Missing original native provider"
  unless env.header.moduleNames[idx]! == expected do throwError "Wrong native provider"
  let wanted := "_private.EnvelopeProperty.AlgGeom.ProjectiveLineClosedPointEvaluation.0.EnvelopeProperty.ProjectiveLineClosedPointEvaluation.zero_pullback_mem_support"
  let candidates := env.header.moduleData[idx]!.constNames.filter (fun n => n.toString == wanted)
  unless candidates.size == 1 do throwError "Nonunique original kernel Name"
  let n := candidates[0]!
  unless env.getModuleIdxFor? n == some idx do throwError "Wrong private owner"
  let some ci := env.find? n | throwError "Missing actual original theorem"
  unless ci.isTheorem && ci.levelParams.length == 1 do throwError "Unexpected original theorem kind or universe telescope"
  Lean.Meta.mkConstWithFreshMVarLevels n

private theorem sectionPostcomposeIso_frame {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N : X.Modules} (t : unitObj X ⟶ M) (e : M ≅ N)
    (ht : IsIso (pullbackSectionHom f t)) :
    IsIso (pullbackSectionHom f (t ≫ e.hom)) := by
  let F := Scheme.Modules.pullback f
  have h : pullbackSectionHom f (t ≫ e.hom) =
      pullbackSectionHom f t ≫ F.map e.hom :=
    (congrArg (fun a => (pullbackUnitIso f).inv ≫ a) (F.map_comp t e.hom)).trans
      (Category.assoc (pullbackUnitIso f).inv (F.map t) (F.map e.hom)).symm
  let := ht
  have hi : IsIso (pullbackSectionHom f t ≫ F.map e.hom) := inferInstance
  exact h.symm ▸ hi

/-- The original section powers frame the complement of the actual cut,
while original cut lifts frame its support. Compactness constructs actual
finite generators of every sufficiently large SAME divisible power. -/
theorem exists_eventual_divisible_generatingSections_of_cutAmple
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (L : X.Modules) (hL : IsInvertible L) (r : ℕ) (hr : 0 < r)
    (s : unitObj X ⟶ bundleTensorPower L r) (hs : s ≠ 0) :
    let I := LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) s
    SchemeLineAmpleness.IsAmple (I.subschemeι ≫ p)
      ((Scheme.Modules.pullback I.subschemeι).obj L) →
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      ∃ G : (bundleTensorPower L (r * q)).GeneratingSections, G.IsFiniteType := by
  classical
  dsimp only
  intro hI
  let I := LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) s
  let hp := ProjectiveFactorizationRingIso.of_isProjective p
  let : IsProper p := hp.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨N, hN⟩ :=
    SeshadriAmplenessCriterionFixedCutUniformLocalGeneration.exists_eventual_cut_point_open_singleton_generatingSections
      p (unitObj X) L isInvertible_unit hL r hr s hs hI
  refine ⟨N + 1, ?_⟩
  intro q hq
  have hNr : N ≤ r * N := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right N (show 1 ≤ r from hr)
  have hbound : N + r ≤ r * q :=
    (Nat.add_le_add_right hNr r).trans
      ((Nat.mul_succ r N).symm.le.trans (Nat.mul_le_mul_left r hq))
  let n := r * q - r
  have hnr : n + r = r * q := Nat.sub_add_cancel (by omega)
  have hNn : N ≤ n := by omega
  let ι := {x : X // IsClosed ({x} : Set X)}
  have hlocal (x : ι) : ∃ (t : unitObj X ⟶ bundleTensorPower L (r * q))
      (U : X.Opens), x.1 ∈ U ∧ IsIso (pullbackSectionHom U.ι t) := by
    by_cases hx : x.1 ∈ I.support
    · obtain ⟨t, _ht, U, hxU, hi, _⟩ := hN n hNn x.1 hx
      let e : unitObj X ⊗ bundleTensorPower L (n + r) ≅ bundleTensorPower L (r * q) :=
        ((ModularCurves.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl _) ≪≫
          λ_ (bundleTensorPower L (n + r)) ≪≫
            eqToIso (congrArg (bundleTensorPower L) hnr)
      exact ⟨t ≫ e.hom, U, hxU, sectionPostcomposeIso_frame U.ι t e hi⟩
    · have ht : pullbackSectionHom (X.fromSpecResidueField x.1) s ≠ 0 := by
        intro hz
        exact hx (existingClosedPointZeroSupport% x.1 (bundleTensorPower L r)
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) s hz)
      obtain ⟨U, hxU, hi⟩ :=
        SchemeLineSectionFiberOpenFrame.exists_open_isIso_of_pullbackSectionHom_ne_zero
          (bundleTensorPower L r) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r)
          s x.1 ht
      exact ⟨sectionPowerHom L r s q, U, hxU,
        isIso_pullback_sectionPowerHom U.ι L r s hi q⟩
  choose t U hxU hi using hlocal
  have hclosed : ∀ x : X, IsClosed ({x} : Set X) → ∃ i : ι, x ∈ U i := by
    intro x hx
    exact ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  exact exists_finite_generatingSections_of_openSectionIsos (bundleTensorPower L (r * q))
    U t (open_cover_of_closedPoint_cover U hclosed) hi

/-- One genuine positive original power is actually finitely globally generated;
the original section and same-cut ampleness are ordinary geometric inputs. -/
theorem exists_positive_power_generatingSections_of_cutAmple
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (L : X.Modules) (hL : IsInvertible L) (r : ℕ) (hr : 0 < r)
    (s : unitObj X ⟶ bundleTensorPower L r) (hs : s ≠ 0) :
    let I := LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) s
    SchemeLineAmpleness.IsAmple (I.subschemeι ≫ p)
      ((Scheme.Modules.pullback I.subschemeι).obj L) →
    ∃ b : ℕ, 0 < b ∧
      ∃ G : (bundleTensorPower L b).GeneratingSections, G.IsFiniteType := by
  dsimp only
  intro hI
  obtain ⟨Q, hQ⟩ := exists_eventual_divisible_generatingSections_of_cutAmple p L hL r hr s hs hI
  exact ⟨r * (Q + 1), Nat.mul_pos hr (Nat.zero_lt_succ Q), hQ (Q + 1) (Nat.le_succ Q)⟩

#check @exists_eventual_divisible_generatingSections_of_cutAmple
#print axioms exists_eventual_divisible_generatingSections_of_cutAmple
#check @exists_positive_power_generatingSections_of_cutAmple
#print axioms exists_positive_power_generatingSections_of_cutAmple
end EnvelopeProperty.SeshadriAmplenessCriterion
