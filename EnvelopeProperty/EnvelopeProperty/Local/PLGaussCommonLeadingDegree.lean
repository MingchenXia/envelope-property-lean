import EnvelopeProperty.Local.PLGaussCommonLeadingProfiles
import EnvelopeProperty.AlgGeom.CurveRationalPrincipalBalance
import EnvelopeProperty.FiniteAffineMaxWeighted

/-! # Whole original residue-weighted degree of the SAME common leading slopes

All finite supports and balances come from actual normal projective-curve
principal divisors. No line-order, whole-line-degree, slope or norm match is input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Filter Order
open scoped Classical NNReal Topology

universe u
namespace EnvelopeProperty.GaussCommonLeadingDegree

/-- The true original residue field, with the true original coefficient action of p. -/
def residueWeight {k : Type u} [Field k] {C : Scheme.{u}}
    (p : C ⟶ Spec (CommRingCat.of k)) (x : C) : ℝ :=
  letI := AffineSchemeLocalDegrees.residueAlgebra p x
  (Module.finrank k (C.residueField x) : ℝ)

private theorem weight_mul_order {k : Type u} [Field k] {C : Scheme.{u}}
    [IsIntegral C] [IsLocallyNoetherian C] (p : C ⟶ Spec (CommRingCat.of k))
    (g : C.functionField) (x : C) :
    residueWeight p x * (C.ord g x : ℝ) =
      (CurveRationalPrincipalBalance.weightedOrder p g x : ℝ) := by
  dsimp only [residueWeight,CurveRationalPrincipalBalance.weightedOrder]
  push_cast
  ring

/-- The SAME original normal projective curve internally supplies actual finite support
and its true WHOLE residue-weighted principal balance, cast to the real numbers. -/
theorem principal_balance_real {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]
    (p : C ⟶ Spec (CommRingCat.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim C ≤ 1)
    (hNormal : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (g : C.functionField) (hg : g ≠ 0) :
    letI : IsProper p := hp.isProper
    letI : LocallyOfFiniteType p := inferInstance
    letI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian p
    Function.HasFiniteSupport (C.ord g) ∧
      (∑ᶠ x : C, residueWeight p x * (C.ord g x : ℝ)) = 0 := by
  classical
  let : IsProper p := hp.isProper
  let : LocallyOfFiniteType p := inferInstance
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  let : AlgebraicGeometry.IsNoetherian C :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  have hfinite := CurveRationalPrincipalBalance.hasFiniteSupport_ord hdim hNormal g hg
  let S : Finset C := hfinite.toFinset
  have hout (x : C) (hx : x ∉ S) : C.ord g x = 0 := by
    by_contra hn
    exact hx (hfinite.mem_toFinset.mpr hn)
  have hsuppZ : Function.support (CurveRationalPrincipalBalance.weightedOrder p g) ⊆ (S : Set C) := by
    intro x hx
    by_contra ho
    exact hx (by
      unfold CurveRationalPrincipalBalance.weightedOrder
      rw [hout x ho,zero_mul])
  have hsuppR : Function.support (fun x => residueWeight p x * (C.ord g x : ℝ)) ⊆ (S : Set C) := by
    intro x hx
    by_contra ho
    exact hx (by
      change residueWeight p x * (C.ord g x : ℝ) = 0
      rw [hout x ho,Int.cast_zero,mul_zero])
  have hz := CurveRationalPrincipalBalance.finsum_weightedOrder_eq_zero p hp hdim hNormal g hg
  rw [finsum_eq_sum_of_support_subset _ hsuppZ] at hz
  refine ⟨hfinite,?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsuppR]
  have hcast : (∑ x ∈ S, residueWeight p x * (C.ord g x : ℝ)) =
      ((∑ x ∈ S, CurveRationalPrincipalBalance.weightedOrder p g x : ℤ) : ℝ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro x _
    exact weight_mul_order p g x
  rw [hcast,hz,Int.cast_zero]

/-- TWO true principal balances give the actual WHOLE residue-weighted active slope inequality.
The actual original direction support is derived, and every original residue degree is retained. -/
theorem weighted_activeSlope_nonneg {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]
    (p : C ⟶ Spec (CommRingCat.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim C ≤ 1)
    (hNormal : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (n : ℕ) (B : Fin n → C.functionField) (hB : ∀ l, B l ≠ 0)
    (Bt : C.functionField) (hBt : Bt ≠ 0) (r : Fin n → ℝ)
    (I : Finset ((Fin n → ℚ) × ℚ)) (hI : I.Nonempty) (β : ((Fin n → ℚ) × ℚ) → ℝ) :
    letI : IsProper p := hp.isProper
    letI : LocallyOfFiniteType p := inferInstance
    letI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian p
    let s := fun (j : (Fin n → ℚ) × ℚ) (x : C) =>
      -(∑ l : Fin n, (j.1 l : ℝ) * ((C.ord (B l) x : ℝ) - r l * (C.ord Bt x : ℝ)))
    let D := FiniteAffineMax.activeSlope I hI β s
    Function.HasFiniteSupport D ∧ D (genericPoint C) = 0 ∧
      0 ≤ ∑ᶠ x : C, residueWeight p x * D x := by
  classical
  let : IsProper p := hp.isProper
  let : LocallyOfFiniteType p := inferInstance
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨hfiniteT,hbalanceT⟩ := principal_balance_real p hp hdim hNormal Bt hBt
  have hdata (l : Fin n) := principal_balance_real p hp hdim hNormal (B l) (hB l)
  let S : Finset C := (Finset.univ.biUnion (fun l => (hdata l).1.toFinset)) ∪ hfiniteT.toFinset
  have hOS (l : Fin n) (x : C) (hx : C.ord (B l) x ≠ 0) : x ∈ S :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr
      ⟨l,Finset.mem_univ _,(hdata l).1.mem_toFinset.mpr hx⟩))
  have hTS (x : C) (hx : C.ord Bt x ≠ 0) : x ∈ S :=
    Finset.mem_union.mpr (Or.inr (hfiniteT.mem_toFinset.mpr hx))
  have hout (x : C) (hx : x ∉ S) (l : Fin n) : C.ord (B l) x = 0 := by
    by_contra hn
    exact hx (hOS l x hn)
  have houtT (x : C) (hx : x ∉ S) : C.ord Bt x = 0 := by
    by_contra hn
    exact hx (hTS x hn)
  let γ := fun (l : Fin n) (x : C) => (C.ord (B l) x : ℝ) - r l * (C.ord Bt x : ℝ)
  let s := fun (j : (Fin n → ℚ) × ℚ) (x : C) => -(∑ l : Fin n, (j.1 l : ℝ) * γ l x)
  let D := FiniteAffineMax.activeSlope I hI β s
  have hzero (x : C) (ho : ∀ l, C.ord (B l) x = 0) (ht : C.ord Bt x = 0) : D x = 0 := by
    have hs : ∀ j, s j x = 0 := by intro j; simp [s,γ,ho,ht]
    simp only [D,FiniteAffineMax.activeSlope,hs,Finset.sup'_const]
  have hDS (x : C) (hx : x ∉ S) : D x = 0 := hzero x (hout x hx) (houtT x hx)
  have hDfinite : Function.HasFiniteSupport D := by
    apply S.finite_toSet.subset
    intro x hx
    by_contra hn
    exact hx (hDS x hn)
  have hordgen (g : C.functionField) : C.ord g (genericPoint C) = 0 := by
    apply C.ord_eq_zero_of_coheight_neq_one
    change coheight (⊤ : C) ≠ 1
    simp
  have hDgen : D (genericPoint C) = 0 := hzero _ (fun l => hordgen (B l)) (hordgen Bt)
  have hsuppT : Function.support (fun x => residueWeight p x * (C.ord Bt x : ℝ)) ⊆ (S : Set C) := by
    intro x hx
    by_contra ho
    exact hx (by
      change residueWeight p x * (C.ord Bt x : ℝ) = 0
      rw [houtT x ho,Int.cast_zero,mul_zero])
  have hsumT : ∑ x ∈ S, residueWeight p x * (C.ord Bt x : ℝ) = 0 := by
    rw [← finsum_eq_sum_of_support_subset _ hsuppT]
    exact hbalanceT
  have hsumB (l : Fin n) : ∑ x ∈ S, residueWeight p x * (C.ord (B l) x : ℝ) = 0 := by
    have hsupp : Function.support (fun x => residueWeight p x * (C.ord (B l) x : ℝ)) ⊆ (S : Set C) := by
      intro x hx
      by_contra ho
      exact hx (by
        change residueWeight p x * (C.ord (B l) x : ℝ) = 0
        rw [hout x ho l,Int.cast_zero,mul_zero])
    rw [← finsum_eq_sum_of_support_subset _ hsupp]
    exact (hdata l).2
  have hgamma (l : Fin n) : ∑ x ∈ S, residueWeight p x * γ l x = 0 := by
    calc
      _ = (∑ x ∈ S, residueWeight p x * (C.ord (B l) x : ℝ)) -
          r l * (∑ x ∈ S, residueWeight p x * (C.ord Bt x : ℝ)) := by
        rw [Finset.mul_sum,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        dsimp only [γ]
        ring
      _ = 0 := by rw [hsumB,hsumT,mul_zero,sub_zero]
  have hslope (j : (Fin n → ℚ) × ℚ) : ∑ x ∈ S, residueWeight p x * s j x = 0 := by
    dsimp only [s]
    simp_rw [mul_neg,Finset.mul_sum]
    rw [Finset.sum_neg_distrib,Finset.sum_comm]
    have heq : (∑ l : Fin n, ∑ x ∈ S, residueWeight p x * ((j.1 l : ℝ) * γ l x)) =
        ∑ l : Fin n, (j.1 l : ℝ) * (∑ x ∈ S, residueWeight p x * γ l x) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [heq]
    simp only [hgamma,mul_zero,Finset.sum_const_zero,neg_zero]
  have hn := FiniteAffineMax.sum_weighted_activeSlope_nonneg I hI S β s (residueWeight p)
    (fun x _ => Nat.cast_nonneg _) (fun j _ => hslope j)
  refine ⟨hDfinite,hDgen,?_⟩
  rw [finsum_eq_sum_of_support_subset _ (show Function.support
    (fun x => residueWeight p x * D x) ⊆ (S : Set C) from by
      intro x hx
      by_contra ho
      exact hx (by
        change residueWeight p x * D x = 0
        rw [hDS x ho,mul_zero]))]
  exact hn

section Main
open Berkovich
variable {Y : Scheme.{u}} [IsIntegral Y]
  {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]
  (i : C ⟶ Y) [IsClosedImmersion i]

local notation "D" => Y.presheaf.stalk (i (genericPoint C))

private theorem paperRadius_pos : 0 < ProjBerk.gaussRadius := by
  change (0 : ℝ) < Real.exp (-1)
  exact Real.exp_pos _

private theorem paperRadius_lt_one : ProjBerk.gaussRadius < 1 := by
  change Real.exp (-1) < (1 : ℝ)
  exact Real.exp_lt_one_iff.mpr (by norm_num)

/-- The SAME original common profiles have finite-support actual slopes and a
WHOLE original residue-degree-weighted nonnegative sum, from true principal balances. -/
theorem exists_common_leading_degree_nonneg
    (f : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsProper f] [IsDominant f]
    (hp : IsProjectiveFactorization
      (i ≫ f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))
    (x₀ : C) [IsNoetherianRing (Y.presheaf.stalk (i x₀))]
    (π₀ : Y.presheaf.stalk (i x₀)) (hπ₀ : Prime π₀)
    (hker₀ : RingHom.ker (i.stalkMap x₀).hom = Ideal.span {π₀})
    (hη : Polynomial.X ∈ (f (i (genericPoint C))).asIdeal)
    (hdim : topologicalKrullDim C ≤ 1)
    (hNormal : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    {U : Set (RelativeSchemeValuedPoint
      (gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius) f)}
    {u : RelativeSchemeValuedPoint
      (gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius) f → EReal}
    (hu : RelativeSchemeValuedPoint.IsConvexPLOn U u) :
    letI : IsProper (i ≫ f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) := hp.isProper
    letI : LocallyOfFiniteType (i ≫ f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) := inferInstance
    letI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian
      (i ≫ f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    ∃ y : RelativeSchemeValuedPoint
        (gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius) f,
      y.1.point = genericPoint Y ∧
      RelativeSchemeValuedPoint.center ProjBerk.gaussModelCoefficient_le_one y = i (genericPoint C) ∧
      (y ∈ U → ∃ W : Set (RelativeSchemeValuedPoint
          (gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius) f),
        IsOpen W ∧ ∃ hyW : y ∈ W, W ⊆ U ∧
        ∃ (V : Y.Opens) (hWV : ∀ w ∈ W, w.1.point ∈ V)
          (n : ℕ) (units : Fin n → Γ(Y,V)ˣ) (I : Finset ((Fin n → ℚ) × ℚ)) (hI : I.Nonempty),
          let hVy := hWV y hyW
          letI : Nonempty V := ⟨⟨y.1.point,hVy⟩⟩
          let β := fun j : (Fin n → ℚ) × ℚ => RelativeSchemeValuedPoint.unitTropAffine units j y hVy
          ∃ (ϖ : D) (e : ℕ) (Ut : Dˣ) (A : Fin n → ℤ) (UF : Fin n → Dˣ),
            Irreducible ϖ ∧ 0 < e ∧
            GaussRegularSurfaceConvexProfiles.stalkParameter f (i (genericPoint C)) = Ut * ϖ ^ e ∧
            (∀ l : Fin n, Y.germToFunctionField V (units l : Γ(Y,V)) =
              algebraMap D Y.functionField (UF l) * (algebraMap D Y.functionField ϖ) ^ (A l)) ∧
            (FiniteAffineMax.active I hI β).Nonempty ∧
            (∀ w (hw : w ∈ W),
              u w = ((I.sup' hI fun j => RelativeSchemeValuedPoint.unitTropAffine units j w (hWV w hw) : ℝ) : EReal)) ∧
            u y = ((I.sup' hI β : ℝ) : EReal) ∧
            let s := fun (j : (Fin n → ℚ) × ℚ) (x : C) =>
              -(∑ l : Fin n, (j.1 l : ℝ) * ((C.ord (i.stalkMap (genericPoint C) (UF l)) x : ℝ) -
                (A l : ℝ) / (e : ℝ) * (C.ord (i.stalkMap (genericPoint C) Ut) x : ℝ)))
            let Dcurve := FiniteAffineMax.activeSlope I hI β s
            Function.HasFiniteSupport Dcurve ∧ Dcurve (genericPoint C) = 0 ∧
            (0 ≤ ∑ᶠ x : C, residueWeight
              (i ≫ f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) x * Dcurve x) ∧
            ∀ (x : C) [IsNoetherianRing (Y.presheaf.stalk (i x))] (_hx : x ≠ genericPoint C)
              (π z : Y.presheaf.stalk (i x)) (hπ : Prime π)
              (_hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) (hz : ¬ π ∣ z)
              (hm : maximalIdeal (Y.presheaf.stalk (i x)) = Ideal.span {π,z}),
              ∃ (ht : GaussRegularSurfaceConvexProfiles.stalkParameter f (i x) ≠ 0)
                (hπt : π ∣ GaussRegularSurfaceConvexProfiles.stalkParameter f (i x)),
                GaussRegularSurfaceConvexProfiles.nativeVerticalPoint f (i x) π hπ ht hπt
                  ProjBerk.gaussRadius paperRadius_pos paperRadius_lt_one = y ∧
                let q := fun m : ℕ => GaussRegularSurfaceConvexProfiles.nativeWeightedPoint f (i x)
                  π z hπ hz hm (m+1) (Nat.zero_lt_succ m) ht hπt
                    ProjBerk.gaussRadius paperRadius_pos paperRadius_lt_one
                let ε := fun m : ℕ => GaussRegularSurfaceConvexProfiles.nativeScale f (i x)
                  π z hπ hz hm ProjBerk.gaussRadius (m+1) (Nat.zero_lt_succ m)
                ∃ c : ℕ,
                  (∀ᶠ m : ℕ in atTop,
                    GaussRegularSurfaceRealNorms.weightedParameterOrder π z hπ hz hm (m+1)
                      (Nat.zero_lt_succ m) (GaussRegularSurfaceConvexProfiles.stalkParameter f (i x)) =
                        e * (m+1) + c) ∧
                  (∀ᶠ m : ℕ in atTop,
                    u (q m) = ((I.sup' hI β + Dcurve x * ε m : ℝ) : EReal) ∧
                      ((u (q m)).toReal - (u y).toReal) / ε m = Dcurve x) ∧
                  Tendsto (fun m : ℕ => ((u (q m)).toReal - (u y).toReal) / ε m) atTop (𝓝 (Dcurve x))) := by
  classical
  let pC := i ≫ f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
  let : IsProper pC := hp.isProper
  let : LocallyOfFiniteType pC := inferInstance
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian pC
  obtain ⟨y,hygen,hycenter,Hcommon⟩ :=
    GaussCommonLeadingProfiles.exists_common_globalLeading_profiles i f x₀ π₀ hπ₀ hker₀ hη hdim hu
  refine ⟨y,hygen,hycenter,?_⟩
  intro hyU
  obtain ⟨W,hW,hyW,hWU,V,hWV,n,units,I,hI,ϖ,e,Ut,A,UF,
    hϖ,he,htfac,hfacF,hactive,hform,hbase,Hlocal⟩ := Hcommon hyU
  let hVy := hWV y hyW
  let : Nonempty V := ⟨⟨y.1.point,hVy⟩⟩
  let β := fun j : (Fin n → ℚ) × ℚ => RelativeSchemeValuedPoint.unitTropAffine units j y hVy
  let B := fun l : Fin n => i.stalkMap (genericPoint C) (UF l)
  let Bt := i.stalkMap (genericPoint C) Ut
  have hB (l : Fin n) : B l ≠ 0 :=
    ((UF l).isUnit.map (i.stalkMap (genericPoint C)).hom).ne_zero
  have hBt : Bt ≠ 0 := (Ut.isUnit.map (i.stalkMap (genericPoint C)).hom).ne_zero
  obtain ⟨hfinite,hgen,hsum⟩ := weighted_activeSlope_nonneg pC hp hdim hNormal
    n B hB Bt hBt (fun l => (A l : ℝ) / (e : ℝ)) I hI β
  refine ⟨W,hW,hyW,hWU,V,hWV,n,units,I,hI,ϖ,e,Ut,A,UF,
    hϖ,he,htfac,hfacF,hactive,hform,hbase,hfinite,hgen,hsum,?_⟩
  intro x hNoeth hx π z hπ hker hz hm
  let : IsNoetherianRing (Y.presheaf.stalk (i x)) := hNoeth
  obtain ⟨ht,hπt,hq,c,hparam,htail,hlim⟩ := Hlocal x hx π z hπ hker hz hm
  refine ⟨ht,hπt,hq,c,hparam,?_,?_⟩
  · simpa only [FiniteAffineMax.activeSlope] using htail
  · simpa only [FiniteAffineMax.activeSlope] using hlim

end Main

end EnvelopeProperty.GaussCommonLeadingDegree
