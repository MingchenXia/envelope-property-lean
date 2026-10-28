import EnvelopeProperty.Local.PLGaussPairedSurfaceGeometry
import DeJongAlterations.Geometry.CartierDominantPullback
import EnvelopeProperty.AlgGeom.ClosedImmersionStalkQuotients
import EnvelopeProperty.AlgGeom.SchemeResidueCoefficientTowers
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Actual Cartier and uniformizer parameters on the original paired surface

The selected component and finite curve map are produced by frozen Geometry3.
The entire original closed-immersion kernel, stalk maps, coefficient maps and
quotient formulas are retained. No local equation, field or norm comparison
certificate is an input to the final paired-data producer.
-/

noncomputable section
open scoped Classical Polynomial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open DeJongAlterations DeJongAlterations.Geometry

universe u

namespace EnvelopeProperty.PLGaussPairedSurfaceParameters

/-- The original lifted SNC component has its SAME whole Cartier kernel internally. -/
theorem closed_component_kernel_isEffectiveCartierDivisor
    {k : Type u} [Field k] {N : Scheme.{u}}
    (p : N ⟶ Spec (CommRingCat.of k)) (Z : Set N)
    (d : AlterationWithBoundary p Z) (E : DivisorComponent d.boundary)
    (j : CartierBoundaryComponentDimension.componentScheme d.boundary E ⟶ d.source)
    [IsClosedImmersion j]
    (hj : j ≫ d.inclusion = CartierBoundaryComponentDimension.componentInclusion d.boundary E) :
    IsEffectiveCartierDivisor j.ker := by
  classical
  let : IsVariety d.sourceStructure := d.sourceVariety
  let : IsVariety d.compactificationStructure := d.compactificationVariety
  let : IsOpenImmersion d.inclusion := d.isOpenImmersion
  let : IsLocallyNoetherian d.compactification :=
    LocallyOfFiniteType.isLocallyNoetherian d.compactificationStructure
  let A := CartierBoundaryComponentDimension.componentScheme d.boundary E
  let I := Scheme.IdealSheafData.vanishingIdeal E.val
  let ι := CartierBoundaryComponentDimension.componentInclusion d.boundary E
  let e := d.inclusion
  let y : d.source := Classical.choice inferInstance
  let : IsDominant e :=
    ⟨(IsOpenImmersion.isOpen_range e).dense ⟨e y, ⟨y, rfl⟩⟩⟩
  have hp : IsPullback j (𝟙 A) e ι :=
    IsPullback.of_vert_isIso_mono
      (show CommSq j (𝟙 A) e ι from ⟨hj.trans (Category.id_comp ι).symm⟩)
  have hker : j.ker = I.comap e := by
    calc
      _ = (hp.isoPullback.hom ≫ pullback.fst e ι).ker :=
        congrArg (fun f : A ⟶ d.source ↦ f.ker) hp.isoPullback_hom_fst.symm
      _ = (pullback.fst e ι).ker := Scheme.Hom.ker_comp_of_isIso _ _
      _ = ι.ker.comap e := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion ι e
      _ = I.comap e := congrArg (fun J : d.compactification.IdealSheafData ↦ J.comap e)
        (show ι.ker = I from I.ker_subschemeι)
  have hI : IsEffectiveCartierDivisor I :=
    SNCSubdivisorComponent.component_isEffectiveCartierDivisor
      d.boundary d.normalCrossings E
  have hJ := CartierDominantPullback.isEffectiveCartierDivisor_comap e I hI
  exact Eq.mp (congrArg (fun J : d.source.IdealSheafData ↦ IsEffectiveCartierDivisor J)
    hker.symm) hJ

/-- Original regular dimension-one curve stalks are genuine DVRs, with an actual closed point. -/
theorem regular_curve_stalks_and_closed_point {A : Scheme.{u}} [IsIntegral A]
    (hA : topologicalKrullDim A = 1) (hreg : IsRegularScheme A) :
    (∃ x₀ : A, x₀ ≠ genericPoint A ∧ IsClosed ({x₀} : Set A)) ∧
      ∀ x : A, x ≠ genericPoint A → IsDiscreteValuationRing (A.presheaf.stalk x) := by
  classical
  let : Nontrivial A := by
    by_contra h
    let : Subsingleton A := not_nontrivial_iff_subsingleton.mp h
    have hz : topologicalKrullDim A ≤ 0 := by
      change Order.krullDim (IrreducibleCloseds A) ≤ 0
      rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := A))]
      apply Order.krullDim_nonpos_iff_forall_isMax.mpr
      intro x y _
      exact (Subsingleton.elim y x).le
    rw [hA] at hz
    norm_num at hz
  obtain ⟨x₀, hx₀⟩ := exists_ne (genericPoint A)
  refine ⟨⟨x₀, hx₀, CurveFiniteClosedSubschemes.isClosed_singleton hA.le x₀ hx₀⟩, ?_⟩
  intro x hx
  let Q := A.presheaf.stalk x
  let : IsRegularLocalRing Q := hreg x
  have hdim : ringKrullDim Q = 1 := by
    rw [ringKrullDim_stalk_eq_coheight,
      CurveFiniteClosedSubschemes.coheight_eq_one hA.le x hx]
    rfl
  have hfin : Module.finrank (IsLocalRing.ResidueField Q) (IsLocalRing.CotangentSpace Q) = 1 := by
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace (R := Q)).mp (hreg x)
    rw [hdim] at h
    exact_mod_cast h
  exact (IsLocalRing.finrank_CotangentSpace_eq_one_iff (R := Q)).mp hfin

private theorem coefficientMap_comp_specMap
    {R₀ S₀ : Type u} [CommRing R₀] [CommRing S₀] {A : Scheme.{u}}
    (q : A ⟶ Spec (CommRingCat.of S₀)) (σ : R₀ →+* S₀) (x : A) :
    SchemeStalkCoefficients.coefficientMap (q ≫ Spec.map (CommRingCat.ofHom σ)) x =
      (SchemeStalkCoefficients.coefficientMap q x).comp σ := by
  have h : CommRingCat.ofHom
      (SchemeStalkCoefficients.coefficientMap (q ≫ Spec.map (CommRingCat.ofHom σ)) x) =
      CommRingCat.ofHom σ ≫ CommRingCat.ofHom (SchemeStalkCoefficients.coefficientMap q x) := by
    apply Spec.map_injective
    calc
      _ = A.fromSpecStalk x ≫ (q ≫ Spec.map (CommRingCat.ofHom σ)) :=
        (SchemeStalkCoefficients.fromSpecStalk_structureMap _ x).symm
      _ = (A.fromSpecStalk x ≫ q) ≫ Spec.map (CommRingCat.ofHom σ) :=
        (Category.assoc _ _ _).symm
      _ = Spec.map (CommRingCat.ofHom (SchemeStalkCoefficients.coefficientMap q x)) ≫
          Spec.map (CommRingCat.ofHom σ) :=
        congrArg (fun f ↦ f ≫ Spec.map (CommRingCat.ofHom σ))
          (SchemeStalkCoefficients.fromSpecStalk_structureMap q x)
      _ = _ := (Spec.map_comp _ _).symm
  exact congrArg CommRingCat.Hom.hom h

/-- Whole original Cartier kernel and actual curve uniformizers yield the literal original parameters. -/
theorem exists_original_cartier_parameters
    {k : Type u} [Field k] {R A : Scheme.{u}} [IsIntegral R] [IsIntegral A]
    (j : A ⟶ R) [IsClosedImmersion j] (hCartier : IsEffectiveCartierDivisor j.ker)
    (hA : topologicalKrullDim A = 1) (hreg : IsRegularScheme A)
    (b : R ⟶ Spec (CommRingCat.of k[X])) [IsProper b] [IsDominant b]
    (q : A ⟶ Spec (CommRingCat.of k))
    (hc : j ≫ b = q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (x : A) (hx : x ≠ genericPoint A) :
    ∃ π z : R.presheaf.stalk (j x),
      RingHom.ker (j.stalkMap x).hom = Ideal.span {π} ∧
      IsLocalRing.maximalIdeal (R.presheaf.stalk (j x)) = Ideal.span {π, z} ∧
      Prime π ∧ ¬ π ∣ z ∧
      SchemeStalkCoefficients.coefficientMap b (j x) Polynomial.X ≠ 0 ∧
      π ∣ SchemeStalkCoefficients.coefficientMap b (j x) Polynomial.X ∧
      IsDiscreteValuationRing (A.presheaf.stalk x) ∧
      ∃ e : (R.presheaf.stalk (j x) ⧸ Ideal.span {π}) ≃+* A.presheaf.stalk x,
        ∀ a : R.presheaf.stalk (j x), e (Ideal.Quotient.mk _ a) = j.stalkMap x a := by
  classical
  let S := R.presheaf.stalk (j x)
  let Q := A.presheaf.stalk x
  let ψ : S →+* Q := (j.stalkMap x).hom
  let ρ : k[X] →+* S := SchemeStalkCoefficients.coefficientMap b (j x)
  let : IsLocalHom ψ := j.toLRSHom.prop x
  have hψ : Function.Surjective ψ := j.stalkMap_surjective x
  obtain ⟨U, hy, f, hf, hIf⟩ := hCartier (j x)
  let : Nonempty U.1 := ⟨⟨j x, hy⟩⟩
  let : IsDomain Γ(R, U.1) := IsIntegral.component_integral U.1
  have hf0 : f ≠ 0 := by
    intro h
    exact zero_ne_one (hf.left (by simp [h]))
  let π : S := R.presheaf.germ U.1 (j x) hy f
  have hπ : π ≠ 0 := by
    intro h
    apply hf0
    apply germ_injective_of_isIntegral R (j x) hy
    exact h.trans (map_zero _).symm
  have hk : RingHom.ker ψ = Ideal.span {π} := by
    rw [ClosedImmersionStalkQuotients.stalkMap_ker_eq_map j U.1 U.2 x hy,
      hIf, Ideal.map_span, Set.image_singleton]
  have hprime : Prime π :=
    (Ideal.span_singleton_prime hπ).mp (hk ▸ RingHom.ker_isPrime ψ)
  have hQ := (regular_curve_stalks_and_closed_point hA hreg).2 x hx
  let : IsDiscreteValuationRing Q := hQ
  obtain ⟨zbar, hzbar⟩ := IsDiscreteValuationRing.exists_irreducible Q
  obtain ⟨z, hz⟩ := hψ zbar
  have hmap : (Ideal.span ({z} : Set S)).map ψ = IsLocalRing.maximalIdeal Q := by
    rw [Ideal.map_span, Set.image_singleton, hz, ← hzbar.maximalIdeal_eq]
  have hmax : IsLocalRing.maximalIdeal S = Ideal.span {π, z} := by
    calc
      _ = (IsLocalRing.maximalIdeal Q).comap ψ := (IsLocalRing.maximalIdeal_comap ψ).symm
      _ = ((Ideal.span ({z} : Set S)).map ψ).comap ψ :=
        congrArg (fun J : Ideal Q ↦ J.comap ψ) hmap.symm
      _ = Ideal.span {z} ⊔ RingHom.ker ψ := by
        simpa only [RingHom.ker_eq_comap_bot] using
          Ideal.comap_map_of_surjective ψ hψ (Ideal.span ({z} : Set S))
      _ = Ideal.span {z} ⊔ Ideal.span {π} := congrArg (fun J : Ideal S ↦ Ideal.span {z} ⊔ J) hk
      _ = Ideal.span {π, z} := by
        simpa only [Ideal.span_insert] using
          (sup_comm (Ideal.span ({z} : Set S)) (Ideal.span ({π} : Set S)))
  have hnot : ¬ π ∣ z := by
    intro hdiv
    have hmem : z ∈ Ideal.span ({π} : Set S) := Ideal.mem_span_singleton.mpr hdiv
    have hzero : ψ z = 0 := show z ∈ RingHom.ker ψ from hk.symm ▸ hmem
    exact hzbar.ne_zero (hz.symm.trans hzero)
  have ht : ρ Polynomial.X ≠ 0 := by
    intro h
    exact Polynomial.X_ne_zero
      ((SchemeStalkCoefficients.coefficientMap_injective b (j x)) (h.trans (map_zero ρ).symm))
  have hcmap : SchemeStalkCoefficients.coefficientMap (j ≫ b) x =
      (SchemeStalkCoefficients.coefficientMap q x).comp (Polynomial.evalRingHom (0 : k)) :=
    (congrArg (fun f : A ⟶ Spec (CommRingCat.of k[X]) ↦
      SchemeStalkCoefficients.coefficientMap f x) hc).trans
        (coefficientMap_comp_specMap q (Polynomial.evalRingHom (0 : k)) x)
  have hzero : ψ (ρ Polynomial.X) = 0 := by
    calc
      _ = SchemeStalkCoefficients.coefficientMap (j ≫ b) x Polynomial.X :=
        RingHom.congr_fun (SchemeResidueCoefficientTowers.stalkMap_coefficients j b x) Polynomial.X
      _ = SchemeStalkCoefficients.coefficientMap q x
          (Polynomial.evalRingHom (0 : k) Polynomial.X) := RingHom.congr_fun hcmap Polynomial.X
      _ = 0 := by simp
  have hdiv : π ∣ ρ Polynomial.X := by
    apply Ideal.mem_span_singleton.mp
    rw [← hk]
    exact hzero
  let e : (S ⧸ Ideal.span {π}) ≃+* Q :=
    ClosedImmersionStalkQuotients.principalStalkQuotientEquiv j U.1 U.2 f hIf x hy
  refine ⟨π, z, hk, hmax, hprime, hnot, ht, hdiv, hQ, e, ?_⟩
  intro a
  exact ClosedImmersionStalkQuotients.principalStalkQuotientEquiv_mk j U.1 U.2 f hIf x hy a

end EnvelopeProperty.PLGaussPairedSurfaceParameters

namespace EnvelopeProperty.PLGaussPairedSurfaceGeometry

/-- The same original paired-data geometry internally gives every literal Cartier/uniformizer parameter and quotient. -/
theorem exists_regular_paired_surface_parameters
    {k : Type u} [Field k] {n : ℕ} {N C₁ : Scheme.{u}} [IsIntegral N] [IsIntegral C₁]
    (i : N ⟶ ProjBerk.NativeProjectiveScheme k[X] n) [IsClosedImmersion i]
    [IsDominant (i ≫ ProjBerk.nativeStructureMap)]
    (hN : topologicalKrullDim N = 2)
    (q : C₁ ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (c : C₁ ⟶ N) [IsClosedImmersion c] (hC : topologicalKrullDim C₁ = 1)
    (hc : c ≫ (i ≫ ProjBerk.nativeStructureMap) =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (d : AlterationWithBoundary
      ((i ≫ ProjBerk.nativeStructureMap) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))
      ((i ≫ ProjBerk.nativeStructureMap) ⁻¹'
        PrimeSpectrum.zeroLocus ({Polynomial.X} : Set k[X]))) :
    IsRegularScheme d.source ∧ topologicalKrullDim d.source = 2 ∧
      topologicalKrullDim d.compactification = 2 ∧
      IsProper (d.alteration ≫ (i ≫ ProjBerk.nativeStructureMap)) ∧
      IsDominant (d.alteration ≫ (i ≫ ProjBerk.nativeStructureMap)) ∧
      Flat (d.alteration ≫ (i ≫ ProjBerk.nativeStructureMap)) ∧
      ∃ E : DivisorComponent d.boundary,
        IsRegularScheme (CartierBoundaryComponentDimension.componentScheme d.boundary E) ∧
        topologicalKrullDim (CartierBoundaryComponentDimension.componentScheme d.boundary E) = 1 ∧
        ∃ (j : CartierBoundaryComponentDimension.componentScheme d.boundary E ⟶ d.source)
          (g : CartierBoundaryComponentDimension.componentScheme d.boundary E ⟶ C₁),
          IsClosedImmersion j ∧ IsFinite g ∧ IsDominant g ∧
          IsProjectiveFactorization (g ≫ q) ∧
          j ≫ d.inclusion = CartierBoundaryComponentDimension.componentInclusion d.boundary E ∧
          j ≫ d.alteration = g ≫ c ∧
          j ≫ (d.alteration ≫ (i ≫ ProjBerk.nativeStructureMap)) =
            (g ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ∧
          (CartierBoundaryComponentDimension.componentInclusion d.boundary E) ≫
            d.compactificationStructure = g ≫ q ∧
          (∃ x₀ : CartierBoundaryComponentDimension.componentScheme d.boundary E,
            x₀ ≠ genericPoint (CartierBoundaryComponentDimension.componentScheme d.boundary E) ∧
            IsClosed ({x₀} : Set (CartierBoundaryComponentDimension.componentScheme d.boundary E))) ∧
          ∀ x : CartierBoundaryComponentDimension.componentScheme d.boundary E,
            x ≠ genericPoint (CartierBoundaryComponentDimension.componentScheme d.boundary E) →
            ∃ π z : d.source.presheaf.stalk (j x),
              RingHom.ker (j.stalkMap x).hom = Ideal.span {π} ∧
              IsLocalRing.maximalIdeal (d.source.presheaf.stalk (j x)) = Ideal.span {π, z} ∧
              Prime π ∧ ¬ π ∣ z ∧
              SchemeStalkCoefficients.coefficientMap
                (d.alteration ≫ (i ≫ ProjBerk.nativeStructureMap)) (j x) Polynomial.X ≠ 0 ∧
              π ∣ SchemeStalkCoefficients.coefficientMap
                (d.alteration ≫ (i ≫ ProjBerk.nativeStructureMap)) (j x) Polynomial.X ∧
              IsDiscreteValuationRing
                ((CartierBoundaryComponentDimension.componentScheme d.boundary E).presheaf.stalk x) ∧
              ∃ e : (d.source.presheaf.stalk (j x) ⧸ Ideal.span {π}) ≃+*
                  (CartierBoundaryComponentDimension.componentScheme d.boundary E).presheaf.stalk x,
                ∀ a : d.source.presheaf.stalk (j x),
                  e (Ideal.Quotient.mk _ a) = j.stalkMap x a := by
  classical
  obtain ⟨hreg, hR, hBar, hproper, hdom, hflat, E, hEreg, hEdim,
    j, g, hj, hg, hgdom, hgproj, hjfac, htriangle, hbase, hfield⟩ :=
    exists_regular_curve_over_central_curve i hN q hq c hC hc d
  let : IsClosedImmersion j := hj
  let : IsVariety d.sourceStructure := d.sourceVariety
  let : IsProper (d.alteration ≫ (i ≫ ProjBerk.nativeStructureMap)) := hproper
  let : IsDominant (d.alteration ≫ (i ≫ ProjBerk.nativeStructureMap)) := hdom
  have hCartier := PLGaussPairedSurfaceParameters.closed_component_kernel_isEffectiveCartierDivisor
    _ _ d E j hjfac
  have hpoint := (PLGaussPairedSurfaceParameters.regular_curve_stalks_and_closed_point hEdim hEreg).1
  refine ⟨hreg, hR, hBar, hproper, hdom, hflat, E, hEreg, hEdim,
    j, g, hj, hg, hgdom, hgproj, hjfac, htriangle, hbase, hfield, hpoint, ?_⟩
  intro x hx
  exact PLGaussPairedSurfaceParameters.exists_original_cartier_parameters
    j hCartier hEdim hEreg (d.alteration ≫ (i ≫ ProjBerk.nativeStructureMap))
    (g ≫ q) hbase x hx

end EnvelopeProperty.PLGaussPairedSurfaceGeometry
