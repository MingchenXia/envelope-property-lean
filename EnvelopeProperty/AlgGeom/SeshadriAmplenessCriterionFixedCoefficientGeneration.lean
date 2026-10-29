import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionFixedCutUniformLocalGeneration
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionSectionPowers
import EnvelopeProperty.AlgGeom.SchemeGeneratorFrameNeighborhoods

/-! # Actual fixed-coefficient global generation at a common positive power

The supplied original generated power and pointwise original ample cuts are
ordinary geometric intermediate inputs. All sections, covers, deficit powers,
common exponent and finite evaluation epimorphism are constructed internally.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace Scheme.Modules
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterionFixedCoefficientGeneration
open CanonicalGeometry SchemeLineSectionEvaluation SchemeTensorSectionHoms
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem exists_multiple_openFrame_of_cut
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (E L : X.Modules) (hE : IsInvertible E) (hL : IsInvertible L)
    (b : ℕ) (hb : 0 < b) (x : X)
    (r : ℕ) (hr : 0 < r) (s : unitObj X ⟶ bundleTensorPower L r) (hs : s ≠ 0) :
    let I := LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) s
    x ∈ I.support →
    SchemeLineAmpleness.IsAmple (I.subschemeι ≫ p)
      ((Scheme.Modules.pullback I.subschemeι).obj L) →
    ∃ m : ℕ, 0 < m ∧ ∃ (U : X.Opens)
      (t : unitObj X ⟶ E ⊗ bundleTensorPower L (b * m)),
      x ∈ U ∧ IsIso (pullbackSectionHom U.ι t) := by
  dsimp only
  intro hx hI
  obtain ⟨N, hN⟩ :=
    SeshadriAmplenessCriterionFixedCutUniformLocalGeneration.exists_eventual_cut_point_open_singleton_generatingSections
      p E L hE hL r hr s hs hI
  let m := N + r + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hb1 : 1 ≤ b := hb
  have hmb : m ≤ b * m := by
    simpa only [one_mul] using Nat.mul_le_mul_right m hb1
  have hbm : N + r ≤ b * m := (show N + r ≤ m by dsimp [m]; omega).trans hmb
  have hn : N ≤ b * m - r := by omega
  have hnr : b * m - r + r = b * m := by omega
  have hlocal := hN (b * m - r) hn x hx
  rw [hnr] at hlocal
  obtain ⟨t, _ht, U, hxU, htU, _G, _hG⟩ := hlocal
  exact ⟨m, hm, U, t, hxU, htU⟩

/-- A genuinely generated original positive power and actual ample cuts at
every original closed point internally produce finite actual global generators
of SAME E tensor L^n for one positive n. No desired cover or generators of the
fixed-coefficient twist are supplied. -/
theorem exists_positive_power_fixedCoefficient_generatingSections
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (E L : X.Modules) (hE : IsInvertible E) (hL : IsInvertible L)
    (b : ℕ) (hb : 0 < b) (G : (bundleTensorPower L b).GeneratingSections)
    (hcuts : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ r : ℕ, 0 < r ∧ ∃ s : unitObj X ⟶ bundleTensorPower L r, s ≠ 0 ∧
        let I := LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r)
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) s
        x ∈ I.support ∧ SchemeLineAmpleness.IsAmple (I.subschemeι ≫ p)
          ((Scheme.Modules.pullback I.subschemeι).obj L)) :
    ∃ n : ℕ, 0 < n ∧ ∃ H : (E ⊗ bundleTensorPower L n).GeneratingSections,
      H.IsFiniteType := by
  classical
  let hp := ProjectiveFactorizationRingIso.of_isProjective p
  let : IsProper p := hp.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let κ := {x : X // IsClosed ({x} : Set X)}
  have hlocal (x : κ) : ∃ m : ℕ, 0 < m ∧ ∃ (U : X.Opens)
      (t : unitObj X ⟶ E ⊗ bundleTensorPower L (b * m)),
      x.1 ∈ U ∧ IsIso (pullbackSectionHom U.ι t) := by
    obtain ⟨r, hr, s, hs, hx, hI⟩ := hcuts x.1 x.2
    exact exists_multiple_openFrame_of_cut p E L hE hL b hb x.1 r hr s hs hx hI
  choose m hm U t hxU hIso using hlocal
  have hclosed : ∀ x : X, IsClosed ({x} : Set X) → ∃ i : κ, x ∈ U i :=
    fun x hx => ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  have hcover := SeshadriAmplenessCriterion.open_cover_of_closedPoint_cover U hclosed
  have hall : (Set.univ : Set X) ⊆ ⋃ i : κ, (U i : Set X) := by
    intro x _
    obtain ⟨i, hi⟩ := hcover x
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨a, ha⟩ := isCompact_univ.elim_finite_subcover
    (fun i : κ => (U i : Set X)) (fun i => (U i).isOpen) hall
  let M := max (a.sup m) 1
  have hfinitecover : ∀ x : X, ∃ i : κ, i ∈ a ∧ x ∈ U i := by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ha (Set.mem_univ x))
    obtain ⟨hia, hxi⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hia, hxi⟩
  have hcommon (x : X) : ∃ (W : X.Opens)
      (v : unitObj X ⟶ E ⊗ bundleTensorPower L (b * M)),
      x ∈ W ∧ IsIso (pullbackSectionHom W.ι v) := by
    obtain ⟨i, hi, hxi⟩ := hfinitecover x
    have hmi : m i ≤ M := (Finset.le_sup (f := m) hi).trans (le_max_left (a.sup m) 1)
    let q := M - m i
    obtain ⟨H, _hH⟩ :=
      SeshadriAmplenessCriterion.exists_finite_generatingSections_multiple_of_generatingSections
        L hL b G q
    obtain ⟨V, hxV, j, hj⟩ := SchemeGeneratorFrameNeighborhoods.exists_affine_generator_frame
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL (b * q)) H x
    let u := SchemeGeneratingSectionsUnit.generatorHom H j
    let W := U i ⊓ V.1
    have hleft : W ≤ U i := inf_le_left
    have hright : W ≤ V.1 := inf_le_right
    have htW : IsIso (pullbackSectionHom W.ι (t i)) :=
      SchemeLineSectionFactorization.isIso_pullbackSectionHom_factor
        (X.homOfLE hleft) (U i).ι W.ι (X.homOfLE_ι hleft) (t i) (hIso i)
    have huW : IsIso (pullbackSectionHom W.ι u) :=
      SchemeLineSectionFactorization.isIso_pullbackSectionHom_factor
        (X.homOfLE hright) V.1.ι W.ι (X.homOfLE_ι hright) u hj
    let w := tensorSectionHom (t i) u
    have hw : IsIso (pullbackSectionHom W.ι w) :=
      SeshadriAmplenessCriterion.isIso_pullback_tensorSectionHom W.ι (t i) u htW huW
    have heq : b * m i + b * q = b * M := by
      dsimp [q]
      rw [← Nat.mul_add, Nat.add_sub_of_le hmi]
    let e : (E ⊗ bundleTensorPower L (b * m i)) ⊗ bundleTensorPower L (b * q) ≅
        E ⊗ bundleTensorPower L (b * M) :=
      α_ E (bundleTensorPower L (b * m i)) (bundleTensorPower L (b * q)) ≪≫
        (Iso.refl E ⊗ᵢ TensorPowerBaseIdealGrading.tensorPowerAddIso L (b * m i) (b * q)) ≪≫
        eqToIso (congrArg (fun n => E ⊗ bundleTensorPower L n) heq)
    have he : pullbackSectionHom W.ι (w ≫ e.hom) =
        pullbackSectionHom W.ι w ≫ (Scheme.Modules.pullback W.ι).map e.hom := by
      simp only [pullbackSectionHom, Functor.map_comp, Category.assoc]
    have hv : IsIso (pullbackSectionHom W.ι (w ≫ e.hom)) := by
      rw [he]
      let := hw
      infer_instance
    exact ⟨W, w ≫ e.hom, ⟨hxi, hxV⟩, hv⟩
  choose W v hxW hIsoW using hcommon
  obtain ⟨H, hH⟩ := SeshadriAmplenessCriterion.exists_finite_generatingSections_of_openSectionIsos
    (E ⊗ bundleTensorPower L (b * M)) W v (fun x => ⟨x, hxW x⟩) hIsoW
  exact ⟨b * M, Nat.mul_pos hb (lt_of_lt_of_le (by decide : 0 < 1) (le_max_right (a.sup m) 1)), H, hH⟩

#print axioms exists_multiple_openFrame_of_cut
#print axioms exists_positive_power_fixedCoefficient_generatingSections
end EnvelopeProperty.SeshadriAmplenessCriterionFixedCoefficientGeneration
