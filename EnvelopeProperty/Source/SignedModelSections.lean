import EnvelopeProperty.Source.SignedPivotCoefficients

/-! # Signed-degree sections of a presentation are the sections of its model

Let `q c: X → ℙ^{d_c}` be a presentation of an integral scheme `X` over `k` (`q 0` a closed
immersion) and `𝒫 = FiniteProjectiveNativeFieldModels.model q p hp` its multiprojective model in
`K(X)`, with coordinates `z^{(c)}_a = X_a/X_{z_c}`. For every `n ∈ ℤ^{r+1}`,

  `Γ(X, ⨂_c q_c^* 𝒪(n_c)) ≃ R_n(𝒫) = {g ∈ K(X): g / z̃_j^n ∈ A_j for every chart j}`

via the pivot coefficient (`signedWholeSectionsEquiv`, `lem:pm-signed-sections`). This is the
signed-degree generalization of `OriginalProjectiveWholeTensorModelSections`
(`wholeSectionsEquiv`, nonnegative degrees), with the same proof:
* a global section `s` has chart coefficients `s_j ∈ Γ(X, U_j) ≅ A_j` and
  `s_j = coefficient(s) / z̃_j^n` (`germ_signedChartCoefficient`), so
  `coefficient(s) ∈ R_n(𝒫)` by `MultiModel.mem_sections_iff_chart_fractions`;
* the coefficient is injective (the generic germ of a section of an invertible sheaf determines
  it);
* conversely, for `g ∈ R_n(𝒫)` the local sections `(g / z̃_j^n) ε_j` over the charts `U_j` have
  the same generic coordinate `g`, hence agree on overlaps, and glue to a global section with
  coefficient `g`.
The only change from the nonnegative case is the normalization: instead of the global pivot
section `∏_c X_{z_c}^{n_c}` (which does not exist for negative `n_c`), the generic frame of the
pivot chart is used (`signedCoefficient`).
-/

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace Opposite
open Scheme.Modules Alterations
open scoped Classical
noncomputable section
universe u
namespace EnvelopeProperty.Variety
open CanonicalGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {r : ℕ} (d : Fin (r + 1) → ℕ)
  (q : ∀ c, X ⟶ projectiveSpace k (d c)) (p : X ⟶ Spec (.of k))
  (hp : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = p) [IsClosedImmersion (q 0)]
  (t : ∀ c, Fin (d c + 1)) (n : Fin (r + 1) → ℤ)

private def chartBaseEquiv (b : X ⟶ Spec (.of k))
    (hb : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = b) (h : b = p) (j : ∀ c, Fin (d c + 1)) :
    (letI := b.stalkAlgebra (genericPoint X);
      (FiniteProjectiveNativeFieldModels.model q b hb).chartAlg j) ≃+*
      (letI := p.stalkAlgebra (genericPoint X);
        (FiniteProjectiveNativeFieldModels.model q p hp).chartAlg j) := by
  cases h
  exact RingEquiv.refl _

private theorem chartBaseEquiv_coe (b : X ⟶ Spec (.of k))
    (hb : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = b) (h : b = p) (j : ∀ c, Fin (d c + 1))
    (x : (letI := b.stalkAlgebra (genericPoint X);
      (FiniteProjectiveNativeFieldModels.model q b hb).chartAlg j)) :
    ((chartBaseEquiv d q p hp b hb h j x :
      (letI := p.stalkAlgebra (genericPoint X);
        (FiniteProjectiveNativeFieldModels.model q p hp).chartAlg j)) : X.functionField) =
      (x : X.functionField) := by
  cases h
  rfl

/-- The chart ring `Γ(X, U_j)` is the model chart algebra `A_j` (`wholeChartSectionsEquiv`, transported to the base `p`). -/
def signedChartSectionsEquiv (j : ∀ c, Fin (d c + 1))
    (hj : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c))) :
    letI := p.stalkAlgebra (genericPoint X)
    Γ(X, signedJointOpen d q p hp j) ≃+*
        (FiniteProjectiveNativeFieldModels.model q p hp).chartAlg j := by
  let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
  let base := f ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
  let := base.stalkAlgebra (genericPoint X)
  let := base.sectionsAlgebra
      (f ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
  exact
      (OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv q p hp j hj).toRingEquiv.trans
    (chartBaseEquiv d q p hp _ _ (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp) j)

theorem signedChartSectionsEquiv_apply (j : ∀ c, Fin (d c + 1))
    (hj : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)))
    (b : Γ(X, signedJointOpen d q p hp j)) :
    letI := signedJointOpen_nonempty d q p hp j hj
    letI := p.stalkAlgebra (genericPoint X)
    ((signedChartSectionsEquiv d q p hp j hj b :
      (FiniteProjectiveNativeFieldModels.model q p hp).chartAlg j) : X.functionField) =
      X.germToFunctionField (signedJointOpen d q p hp j) b := by
  let := signedJointOpen_nonempty d q p hp j hj
  let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
  let base := f ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
  let := base.stalkAlgebra (genericPoint X)
  let := base.sectionsAlgebra
      (f ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
  exact (chartBaseEquiv_coe d q p hp _ _
    (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp) j _).trans
      (OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv_apply q p hp j hj b)

theorem model_coord_ne_zero_of_nonempty (j : ∀ c, Fin (d c + 1))
    (hj : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c))) :
    letI := p.stalkAlgebra (genericPoint X)
    ∀ c, (FiniteProjectiveNativeFieldModels.model q p hp).coord c (j c) ≠ 0 := by
  let := p.stalkAlgebra (genericPoint X)
  intro c
  let : Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (FiniteProjectiveNativeFieldModels.pivot q c)) :=
    (FiniteProjectiveNativeFieldModels.chartSite (q c)).property
  let := hj c
  exact ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero (q c)
    (FiniteProjectiveNativeFieldModels.pivot q c) (j c)

theorem nonempty_of_model_coord_ne_zero (j : ∀ c, Fin (d c + 1)) :
    letI := p.stalkAlgebra (genericPoint X)
    (∀ c, (FiniteProjectiveNativeFieldModels.model q p hp).coord c (j c) ≠ 0) →
      ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)) := by
  let := p.stalkAlgebra (genericPoint X)
  intro hj c
  let : Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (FiniteProjectiveNativeFieldModels.pivot q c)) :=
    (FiniteProjectiveNativeFieldModels.chartSite (q c)).property
  exact (ProjectiveNativeCoordinateChartSupport.coordinate_ne_zero_iff_nonempty (q c)
    (FiniteProjectiveNativeFieldModels.pivot q c) (j c)).mp (hj c)

/-- The pivot coefficient of every global section of `L(n)` is a model section of degree `n`. -/
theorem signedCoefficient_mem_sections (s : Γ(signedProjectiveLine d q t n, ⊤)) :
    letI := p.stalkAlgebra (genericPoint X)
    signedCoefficient d q t n s ∈ (FiniteProjectiveNativeFieldModels.model q p hp).sections n := by
  let := p.stalkAlgebra (genericPoint X)
  let P := FiniteProjectiveNativeFieldModels.model q p hp
  apply (P.mem_sections_iff_chart_fractions _ _).mpr
  intro j hj
  have hJ := nonempty_of_model_coord_ne_zero d q p hp j hj
  let := signedJointOpen_nonempty d q p hp j hJ
  rw [← germ_signedChartCoefficient d q p hp t n j hJ s]
  have h := (signedChartSectionsEquiv d q p hp j hJ
      (signedChartCoefficient d q p hp t n j s)).property
  rwa [signedChartSectionsEquiv_apply d q p hp j hJ] at h

/-- Every model section of degree `n` is the pivot coefficient of a global section of `L(n)`,
by gluing the local sections `(g / z̃_j^n) ε_j`. -/
theorem signedCoefficient_surjective :
    letI := p.stalkAlgebra (genericPoint X)
    ∀ g : (FiniteProjectiveNativeFieldModels.model q p hp).sections n,
      ∃ s : Γ(signedProjectiveLine d q t n, ⊤), signedCoefficient d q t n s =
          (g : X.functionField) := by
  let := p.stalkAlgebra (genericPoint X)
  let P := FiniteProjectiveNativeFieldModels.model q p hp
  let L := signedProjectiveLine d q t n
  have hL := signedProjectiveLine_isInvertible d q t n
  let J := {j : (∀ c, Fin (d c + 1)) // ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c))}
  let U (j : J) : X.Opens := signedJointOpen d q p hp j.val
  have hU (j : J) : Nonempty (U j) := signedJointOpen_nonempty d q p hp j.val j.property
  intro g
  let G (j : J) : P.chartAlg j.val :=
    ⟨(g : X.functionField) / P.chartDenZ j.val n,
      P.div_chartDenZ_mem_chartAlg (model_coord_ne_zero_of_nonempty d q p hp j.val j.property)
        g.property⟩
  let c (j : J) : Γ(X, U j) := (signedChartSectionsEquiv d q p hp j.val j.property).symm (G j)
  let S (j : J) : Γ(L, U j) := ModularCurves.overTrivializationSection _ _
    (signedOverFrameOn d q t n j.val (U j) (signedJointOpen_le d q p hp j.val)) (c j)
  have hcoeff (j : J) :
      letI := hU j
      X.germToFunctionField (U j) (c j) = (g : X.functionField) / P.chartDenZ j.val n := by
    let := hU j
    have he : signedChartSectionsEquiv d q p hp j.val j.property (c j) = G j :=
      (signedChartSectionsEquiv d q p hp j.val j.property).apply_symm_apply (G j)
    exact (signedChartSectionsEquiv_apply d q p hp j.val j.property (c j)).symm.trans
      (congrArg Subtype.val he)
  have hT (j : J) :
      letI := hU j
      signedGenericFrame d q t n (bundleGenericGerm L (U j) (S j)) = (g : X.functionField) := by
    let := hU j
    have hden : P.chartDenZ j.val n ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun c _ =>
        zpow_ne_zero _ (model_coord_ne_zero_of_nonempty d q p hp j.val j.property c))
    refine (signedGenericFrame_sectionOn d q t n j.val j.property (U j)
      (signedJointOpen_le d q p hp j.val) (c j)).trans ?_
    rw [hcoeff j, ← chartDenZ_eq_inv_prod d q p hp n j.val j.property]
    exact div_mul_cancel₀ _ hden
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    obtain ⟨j, hj⟩ := exists_mem_signedJointOpen d q p hp x
    have hJ : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)) :=
      fun c => ⟨⟨x, signedJointOpen_le d q p hp j c hj⟩⟩
    exact Opens.mem_iSup.mpr ⟨⟨j, hJ⟩, hj⟩
  have hcompat (j l : J) : L.presheaf.map (Opens.infLELeft (U j) (U l)).op (S j) =
      L.presheaf.map (Opens.infLERight (U j) (U l)).op (S l) := by
    let := hU j
    let := hU l
    have hj : genericPoint X ∈ U j := genericPoint_mem_nonempty_open _
    have hl : genericPoint X ∈ U l := genericPoint_mem_nonempty_open _
    let : Nonempty (U j ⊓ U l : X.Opens) := ⟨⟨genericPoint X, ⟨hj, hl⟩⟩⟩
    apply bundleGenericGerm_injective hL (U j ⊓ U l)
    apply (signedGenericFrame d q t n).injective
    have h₁ : bundleGenericGerm L (U j ⊓ U l)
        (L.presheaf.map (Opens.infLELeft (U j) (U l)).op (S j)) =
        bundleGenericGerm L (U j) (S j) :=
      L.presheaf.germ_res_apply (Opens.infLELeft (U j) (U l)) (genericPoint X)
        (genericPoint_mem_nonempty_open _) (S j)
    have h₂ : bundleGenericGerm L (U j ⊓ U l)
        (L.presheaf.map (Opens.infLERight (U j) (U l)).op (S l)) =
        bundleGenericGerm L (U l) (S l) :=
      L.presheaf.germ_res_apply (Opens.infLERight (U j) (U l)) (genericPoint X)
        (genericPoint_mem_nonempty_open _) (S l)
    rw [h₁, h₂]
    exact (hT j).trans (hT l).symm
  obtain ⟨s, hs, _⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨L.presheaf, L.isSheaf⟩ U ⊤
    (fun _ => homOfLE le_top) hcover S hcompat
  refine ⟨s, ?_⟩
  let z : J := ⟨signedPivot d q, signedPivot_nonempty d q⟩
  let := hU z
  have hres : bundleGenericGerm L ⊤ s = bundleGenericGerm L (U z) (S z) := by
    rw [← hs z]
    exact (L.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X)
      (genericPoint_mem_nonempty_open (U z)) s).symm
  change signedGenericFrame d q t n (bundleGenericGerm L ⊤ s) = _
  rw [hres]
  exact hT z

/-- **Signed sections are model sections** (`lem:pm-signed-sections`):
`Γ(X, ⨂_c q_c^* 𝒪(n_c)) ≃ R_n(𝒫)` for every `n ∈ ℤ^{r+1}`, via the pivot coefficient. -/
def signedWholeSectionsEquiv :
    letI := p.stalkAlgebra (genericPoint X)
    Γ(signedProjectiveLine d q t n, ⊤) ≃
        (FiniteProjectiveNativeFieldModels.model q p hp).sections n := by
  let := p.stalkAlgebra (genericPoint X)
  refine Equiv.ofBijective (fun s => ⟨signedCoefficient d q t n s,
    signedCoefficient_mem_sections d q p hp t n s⟩) ⟨?_, ?_⟩
  · intro s v h
    exact signedCoefficient_injective d q t n (congrArg Subtype.val h)
  · intro g
    obtain ⟨s, hs⟩ := signedCoefficient_surjective d q p hp t n g
    exact ⟨s, Subtype.ext hs⟩

/-- The equivalence is the pivot coefficient. -/
theorem signedWholeSectionsEquiv_apply (s : Γ(signedProjectiveLine d q t n, ⊤)) :
    letI := p.stalkAlgebra (genericPoint X)
    ((signedWholeSectionsEquiv d q p hp t n s :
      (FiniteProjectiveNativeFieldModels.model q p hp).sections n) : X.functionField) =
        signedCoefficient d q t n s := rfl

theorem signedCoefficient_signedWholeSectionsEquiv_symm :
    letI := p.stalkAlgebra (genericPoint X)
    ∀ g : (FiniteProjectiveNativeFieldModels.model q p hp).sections n,
      signedCoefficient d q t n ((signedWholeSectionsEquiv d q p hp t n).symm g) =
        (g : X.functionField) := by
  let := p.stalkAlgebra (genericPoint X)
  intro g
  exact congrArg Subtype.val ((signedWholeSectionsEquiv d q p hp t n).apply_symm_apply g)

end EnvelopeProperty.Variety
