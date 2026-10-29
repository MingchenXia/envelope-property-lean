import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalGaussCurveOrderSlopes
import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalSectionRegaugingUnitGauge
import EnvelopeProperty.Local.PLGaussCommonLeadingDegree

/-! # Original convex weights force the same central-curve Euler degree -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Filter IsLocalRing
open scoped Classical NNReal ENNReal Topology
universe u
namespace EnvelopeProperty.NumericalGaussCurveLineDegree
open Scheme.Modules SchemeLineSectionEvaluation Berkovich Berkovich.RelativeSchemeValuedPoint

private def fibreModule {Y : Scheme.{u}} (L : Y.Modules) (p : Y) :
    (Spec (CommRingCat.of (Y.residueField p))).Modules :=
  (pullback (Y.fromSpecResidueField p)).obj L

private theorem genericAt_transport {Y : Scheme.{u}} [IsIntegral Y]
    (L : Y.Modules) (p : Y) (hp : p = genericPoint Y) (q : Y) (hq : q = genericPoint Y)
    (ρ : Γ((pullback (Y.fromSpecResidueField (genericPoint Y))).obj L, ⊤)) :
    (show Γ(fibreModule L q, ⊤) from (hq.trans hp.symm).symm ▸
      (show Γ(fibreModule L p, ⊤) from GaussCentralLineNormalization.genericSectionAt L p hp ρ)) =
        GaussCentralLineNormalization.genericSectionAt L q hq ρ := by
  subst p
  subst q
  rfl

private theorem genericAt_ne_zero {Y : Scheme.{u}} [IsIntegral Y]
    (L : Y.Modules) (p : Y) (hp : p = genericPoint Y)
    (ρ : Γ((pullback (Y.fromSpecResidueField (genericPoint Y))).obj L, ⊤)) (hρ : ρ ≠ 0) :
    GaussCentralLineNormalization.genericSectionAt L p hp ρ ≠ 0 := by
  subst p
  exact hρ

private theorem weight_toReal (a : ℝ≥0) :
    (-ENNReal.log (a : ℝ≥0∞)).toReal = -Real.log (a : ℝ) := by
  by_cases ha : a = 0
  · subst a
    simp
  · rw [ENNReal.log_of_nnreal ha,EReal.toReal_neg_eq,EReal.toReal_coe]

private theorem exists_frame_at {Y : Scheme.{u}} (L : Y.Modules) (hL : IsInvertible L)
    (p : Y) :
    ∃ (V : Y.Opens) (_hp : p ∈ V)
      (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L), IsIso δ := by
  obtain ⟨ι,O,hO,hframe⟩ := hL
  have hp : p ∈ iSup O := by rw [hO]; trivial
  obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hp
  obtain ⟨e⟩ := hframe j
  exact ⟨O j,hj,e.inv,e.isIso_inv⟩

private theorem degree_real_weighted_order {k : Type u} [Field k]
    {C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [CompactSpace C]
    (p : C ⟶ Spec (CommRingCat.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim C ≤ 1)
    (hNormal : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (L : C.Modules) (hL : IsInvertible L)
    (σ : Γ((pullback (C.fromSpecResidueField (genericPoint C))).obj L, ⊤)) (hσ : σ ≠ 0) :
    (CurveLineDegrees.degree p L : ℝ) = ∑ᶠ x : C,
      GaussCommonLeadingDegree.residueWeight p x * (CurveGenericSectionOrders.order L hL σ x : ℝ) := by
  let d := CurveGenericSectionOrders.order L hL σ
  let weight := fun x : C =>
    letI := AffineSchemeLocalDegrees.residueAlgebra p x
    (Module.finrank k (C.residueField x) : ℤ)
  have hfinite := CurveGenericSectionOrders.hasFiniteSupport_order p hp hdim hNormal L hL σ hσ
  let S : Finset C := hfinite.toFinset
  have hout (x : C) (hx : x ∉ S) : d x = 0 := by
    by_contra hn
    exact hx (hfinite.mem_toFinset.mpr hn)
  have hsuppZ : Function.support (fun x => d x * weight x) ⊆ (S : Set C) := by
    intro x hx
    by_contra ho
    exact hx (by
      change d x * weight x = 0
      rw [hout x ho,zero_mul])
  have hsuppR : Function.support (fun x => GaussCommonLeadingDegree.residueWeight p x * (d x : ℝ)) ⊆
      (S : Set C) := by
    intro x hx
    by_contra ho
    exact hx (by
      change GaussCommonLeadingDegree.residueWeight p x * (d x : ℝ) = 0
      rw [hout x ho,Int.cast_zero,mul_zero])
  have hpoint (x : C) : (d x * weight x : ℝ) =
      GaussCommonLeadingDegree.residueWeight p x * (d x : ℝ) := by
    dsimp only [weight,GaussCommonLeadingDegree.residueWeight]
    push_cast
    ring
  have heuler := CurveGenericSectionOrders.degree_eq_finsum_order p hp hdim hNormal L hL σ hσ
  change CurveLineDegrees.degree p L = ∑ᶠ x : C,d x * weight x at heuler
  rw [finsum_eq_sum_of_support_subset _ hsuppZ] at heuler
  change (CurveLineDegrees.degree p L : ℝ) = ∑ᶠ x : C,GaussCommonLeadingDegree.residueWeight p x * (d x : ℝ)
  rw [finsum_eq_sum_of_support_subset _ hsuppR,heuler]
  push_cast
  exact Finset.sum_congr rfl (fun x _ => hpoint x)

private theorem paperRadius_pos : 0 < ProjBerk.gaussRadius := by
  change (0 : ℝ) < Real.exp (-1)
  exact Real.exp_pos _

private theorem paperRadius_lt_one : ProjBerk.gaussRadius < 1 := by
  change Real.exp (-1) < (1 : ℝ)
  exact Real.exp_lt_one_iff.mpr (by norm_num)

open ProjBerk

/-- ORIGINAL local convexity chooses the prescribed class ONCE and internally
proves the true whole line degree on every actual normal projective SNC central curve. -/
theorem exists_prescribedClass_curveDegree_nonneg
    {k : Type u} [Field k] [PerfectField k] {n : ℕ}
    (X : ProjSubvariety k n) (hX : X.IsProjNormal)
    {a : ℚ} (ha : 0 < a) {φ : X.an → ℝ} (hconv : X.IsLocallyConvexAll a φ) :
    ∃ (r d : ℕ) (_hr : 0 < r) (_hd : 0 < d), (d : ℚ) = r*a ∧
      ∃ (B : ℤ) (I J : X.NativeProductModel.IdealSheafData)
        (hfinAll : ∀ z : RelativeSchemeValuedPoint
            (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
          modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
          modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥),
        let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
        (∀ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
            (X.normalizedSimultaneousIdealBlowupStructure I J hfin),
          (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt I J hfin y) : ℝ) : EReal) =
            X.normalizedSimultaneousRatioWeightAt I J hfin y
              (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 + ((B : ℝ) : EReal)) ∧
        ∀ (j : Fin (n+1)),
        let M := X.normalizedSimultaneousTwistedRatioLine I J hfin j d
        ∀ (Y : Scheme.{u}) (base : Y ⟶ Spec (CommRingCat.of (Polynomial k)))
          [IsProper base] [IsDominant base] [IsIntegral Y]
          (g : Y ⟶ X.normalizedSimultaneousIdealBlowup I J hfin)
          (_hg : g ≫ X.normalizedSimultaneousIdealBlowupStructure I J hfin =
            base ≫ Spec.map (CommRingCat.ofHom (RingHom.id (Polynomial k))))
          (C : Scheme.{u}) [IsIntegral C] (i : C ⟶ Y) [IsClosedImmersion i]
          (hp : IsProjectiveFactorization
            (i ≫ base ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))
          (_hdim : topologicalKrullDim C ≤ 1)
          (_hNormal : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
          (_hη : Polynomial.X ∈ (base (i (genericPoint C))).asIdeal)
          (x₀ : C) (π₀ : Y.presheaf.stalk (i x₀)) (_hπ₀ : Prime π₀)
          (_hker₀ : RingHom.ker (i.stalkMap x₀).hom = Ideal.span {π₀})
          (_hSNC : ∀ x : C, x ≠ genericPoint C →
            ∃ π z : Y.presheaf.stalk (i x), Prime π ∧ ¬ π ∣ z ∧
              maximalIdeal (Y.presheaf.stalk (i x)) = Ideal.span {π,z} ∧
              RingHom.ker (i.stalkMap x).hom = Ideal.span {π}),
          let pC := i ≫ base ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
          letI : IsProper pC := hp.isProper
          letI : LocallyOfFiniteType pC := inferInstance
          letI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian pC
          letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace pC
          0 ≤ CurveLineDegrees.degree pC ((pullback i).obj ((pullback g).obj M)) := by
  obtain ⟨r,d,hr,hd,hda,B,I,J,hfinAll,heq,Hgauge⟩ :=
    NumericalSectionRegaugingUnitGauge.exists_prescribedClass_nativeRationalGauges X hX ha hconv
  let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
  refine ⟨r,d,hr,hd,hda,B,I,J,hfinAll,heq,?_⟩
  intro j M Y base hProper hDominant hIntegral g hg C hC i hClosed hp hdim hNormal hη x₀ π₀ hπ₀ hker₀ hSNC
  let pC := i ≫ base ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian base
  let : IsProper pC := hp.isProper
  let : LocallyOfFiniteType pC := inferInstance
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian pC
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace pC
  let L : Y.Modules := (pullback g).obj M
  let hL : IsInvertible L := (X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d).pullback g
  let LC : C.Modules := (pullback i).obj L
  let hLC : IsInvertible LC := hL.pullback i
  obtain ⟨U₀,hηU₀,δ₀,hδ₀⟩ := exists_frame_at L hL (i (genericPoint C))
  let : IsIso δ₀ := hδ₀
  let : Nonempty U₀ := ⟨⟨i (genericPoint C),hηU₀⟩⟩
  let σ := CentralGenericLineSectionLift.closedGenericSection i L U₀ hηU₀ δ₀
  have hσ : σ ≠ 0 := (NumericalGaussCurveSectionOrders.exists_twoFrame_intrinsicOrder
    (base := base) gaussModelCoefficient_le_one i L hL U₀ hηU₀ δ₀ x₀).1
  obtain ⟨y₀,hy₀,hcenter₀,U,hηU,δ,hδ,hcentral,hU,ρ,hρ,hρne,hOne⟩ :=
    GaussCentralLineNormalization.exists_prescribed_section_unit_norm base i x₀ π₀ hπ₀ hker₀ hη L hL σ hσ
  let : IsIso δ := hδ
  let : Nonempty U := hU
  let ρ₀ : Γ(genericLineModule y₀ L, ⊤) :=
    GaussCentralLineNormalization.genericSectionAt L y₀.1.point hy₀ ρ
  have hρ₀ : ρ₀ ≠ 0 := genericAt_ne_zero L y₀.1.point hy₀ ρ hρne
  obtain ⟨l,hF,hval,hFI,UN,δN,hδN,Vg,hVg,hVU,unit,hyVg,hgeneric,hnorm,huy₀,hu⟩ :=
    Hgauge j Y base g hg y₀ hy₀ ρ₀ hρ₀
  let dom := ((mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg ⁻¹'
    X.normalizedSimultaneousAdmissibleAnalyticLocus I J hfin (MvPolynomial.X l ^ d)) ∩
      {y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) base | y.1.point ∈ Vg})
  let w : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) base → EReal :=
    fun y => if hy : y.1.point ∈ Vg then
      -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y hL
        (NumericalSectionRegaugingUnitGauge.unitPullbackSectionValue g M UN δN Vg hVU unit y.1.point hy) : ℝ≥0∞)
      else ⊤
  change Berkovich.RelativeSchemeValuedPoint.IsConvexPLOn dom w at hu
  have hw (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) base)
      (hy : y.1.point = genericPoint Y) :
      w y = -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y hL
        (GaussCentralLineNormalization.genericSectionAt L y.1.point hy ρ) : ℝ≥0∞) := by
    obtain ⟨hyV,hvalue⟩ := hgeneric y hy
    have htransport := genericAt_transport L y₀.1.point hy₀ y.1.point hy ρ
    have hs := hvalue.trans htransport
    change (if hyV : y.1.point ∈ Vg then _ else ⊤) = _
    rw [dif_pos hyV]
    exact congrArg (fun s : Γ(genericLineModule y L, ⊤) =>
      -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y hL s : ℝ≥0∞)) hs
  have hwreal (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) base)
      (hy : y.1.point = genericPoint Y) :
      (w y).toReal = -Real.log ((modelLineNorm gaussModelCoefficient_le_one y hL
        (GaussCentralLineNormalization.genericSectionAt L y.1.point hy ρ) : ℝ≥0) : ℝ) :=
    (congrArg EReal.toReal (hw y hy)).trans (weight_toReal _)
  have hw₀ : w y₀ = 0 := (hw y₀ hy₀).trans (by rw [hOne]; simp)
  let : IsDiscreteValuationRing (Y.presheaf.stalk (i (genericPoint C))) :=
    GaussCommonVerticalStalks.componentStalk_isDVR i x₀ π₀ hπ₀ hker₀
  obtain ⟨y,hy,hcenter,Hcommon⟩ :=
    GaussCommonLeadingDegree.exists_common_leading_degree_nonneg i base hp x₀ π₀ hπ₀ hker₀ hη hdim hNormal hu
  have hyy₀ : y = y₀ := GaussCommonVerticalPoints.eq_of_same_verticalDVRCenter
    (f := base) (i (genericPoint C)) hη gaussRadius paperRadius_pos paperRadius_lt_one y y₀ hcenter hcenter₀
  have hyU : y ∈ dom := by rw [hyy₀]; exact huy₀
  have hwy : w y = 0 := hyy₀ ▸ hw₀
  obtain ⟨W,hW,hyW,hWU,V,hWV,m,units,K,hK,ϖ,e,Ut,A,UF,
    hϖ,he,htfac,hfac,hactive,hform,hbase,hfinite,hgen,hsum,Hlocal⟩ := Hcommon hyU
  let hVy := hWV y hyW
  let : Nonempty V := ⟨⟨y.1.point,hVy⟩⟩
  let β := fun j : (Fin m → ℚ) × ℚ => unitTropAffine units j y hVy
  let direction := fun (j : (Fin m → ℚ) × ℚ) (x : C) =>
    -(∑ l : Fin m, (j.1 l : ℝ) * ((C.ord (i.stalkMap (genericPoint C) (UF l)) x : ℝ) -
      (A l : ℝ) / (e : ℝ) * (C.ord (i.stalkMap (genericPoint C) Ut) x : ℝ)))
  let D := FiniteAffineMax.activeSlope K hK β direction
  have hDgeneric : D (genericPoint C) = 0 := hgen
  have hD (x : C) : D x = (CurveGenericSectionOrders.order LC hLC σ x : ℝ) := by
    by_cases hx : x = genericPoint C
    · subst x
      rw [hDgeneric,CurveGenericSectionOrders.order_generic,Int.cast_zero]
    · obtain ⟨π,z,hπ,hz,hm,hker⟩ := hSNC x hx
      obtain ⟨ht,hπt,hqy,c,hparam,htail,hlim⟩ := Hlocal x hx π z hπ hker hz hm
      let q := fun t : ℕ => GaussRegularSurfaceConvexProfiles.nativeWeightedPoint base (i x)
        π z hπ hz hm (t+1) (Nat.zero_lt_succ t) ht hπt gaussRadius paperRadius_pos paperRadius_lt_one
      let ε := fun t : ℕ => GaussRegularSurfaceConvexProfiles.nativeScale base (i x)
        π z hπ hz hm gaussRadius (t+1) (Nat.zero_lt_succ t)
      obtain ⟨T,hNorm⟩ := NumericalGaussCurveOrderSlopes.exists_eventual_modelNorm_intrinsicOrder
        i base L hL U hηU δ x π z hπ hz hm hker hdim hx ht hπt
          gaussRadius paperRadius_pos paperRadius_lt_one
      have hnormTail : ∀ᶠ t : ℕ in atTop,
          -Real.log ((modelLineNorm gaussModelCoefficient_le_one (q t) hL
            (GaussCentralLineNormalization.genericSectionAt L (q t).1.point
              (GaussRegularSurfaceConvexProfiles.nativeWeightedPoint_underlying base (i x)
                π z hπ hz hm (t+1) (Nat.zero_lt_succ t) ht hπt gaussRadius paperRadius_pos paperRadius_lt_one) ρ) : ℝ≥0) : ℝ) =
            ε t * (CurveGenericSectionOrders.order LC hLC σ x : ℝ) := by
        filter_upwards [eventually_ge_atTop T] with t htT
        have h := hNorm (t+1) (Nat.zero_lt_succ t) (Nat.lt_succ_of_le htT)
        rw [← hρ,hcentral] at h
        exact h
      obtain ⟨t,hprofile,hnormValue⟩ := (htail.and hnormTail).exists
      have hyq := GaussRegularSurfaceConvexProfiles.nativeWeightedPoint_underlying base (i x)
        π z hπ hz hm (t+1) (Nat.zero_lt_succ t) ht hπt gaussRadius paperRadius_pos paperRadius_lt_one
      have hε : 0 < ε t := GaussRegularSurfaceConvexProfiles.nativeScale_pos base (i x)
        π z hπ hz hm ht hπt gaussRadius paperRadius_pos paperRadius_lt_one (t+1) (Nat.zero_lt_succ t)
      have hquot := hprofile.2
      change ((w (q t)).toReal - (w y).toReal) / ε t = D x at hquot
      rw [hwy,EReal.toReal_zero,sub_zero,hwreal (q t) hyq,hnormValue] at hquot
      have hcancel : (ε t * (CurveGenericSectionOrders.order LC hLC σ x : ℝ)) / ε t =
          (CurveGenericSectionOrders.order LC hLC σ x : ℝ) := by field_simp [hε.ne']
      exact hquot.symm.trans hcancel
  have hdegree := degree_real_weighted_order pC hp hdim hNormal LC hLC σ hσ
  have hnonneg : 0 ≤ (CurveLineDegrees.degree pC LC : ℝ) := by
    calc
      0 ≤ ∑ᶠ x : C, GaussCommonLeadingDegree.residueWeight pC x * D x := hsum
      _ = ∑ᶠ x : C, GaussCommonLeadingDegree.residueWeight pC x *
          (CurveGenericSectionOrders.order LC hLC σ x : ℝ) :=
        finsum_congr (fun x => congrArg (fun t : ℝ => GaussCommonLeadingDegree.residueWeight pC x * t) (hD x))
      _ = (CurveLineDegrees.degree pC LC : ℝ) := hdegree.symm
  exact_mod_cast hnonneg

end EnvelopeProperty.NumericalGaussCurveLineDegree
