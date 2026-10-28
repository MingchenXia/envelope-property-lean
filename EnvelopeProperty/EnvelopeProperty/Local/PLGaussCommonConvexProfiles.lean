import EnvelopeProperty.Local.PLGaussCommonVerticalPoints

/-! # ONE original source-convex family across every original component point -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open scoped Classical NNReal Topology

universe u
namespace EnvelopeProperty.GaussCommonConvexProfiles
open Berkovich

private theorem eval_congr {X : Scheme.{u}} (a b : SchemeValuedPoint X) (h : a = b)
    (V : X.Opens) (ha : a.point ∈ V) (hb : b.point ∈ V) (s : Γ(X,V)) :
    SchemeValuedPoint.eval a V ha s = SchemeValuedPoint.eval b V hb s := by
  cases h
  rfl

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

private theorem family_profile (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X)
    [IsNoetherianRing (X.presheaf.stalk p)]
    (π z : X.presheaf.stalk p) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk p) = Ideal.span {π,z})
    (ht : GaussRegularSurfaceConvexProfiles.stalkParameter f p ≠ 0)
    (hπt : π ∣ GaussRegularSurfaceConvexProfiles.stalkParameter f p)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1)
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) r) f)
    (heq : GaussRegularSurfaceConvexProfiles.nativeVerticalPoint f p π hπ ht hπt r hr0 hr1 = y)
    (W : Set (RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) r) f))
    (hW : IsOpen W) (hyW : y ∈ W) (V : X.Opens)
    (hWV : ∀ w ∈ W, w.1.point ∈ V) (n : ℕ) (a : Fin n → Γ(X,V)ˣ)
    (I : Finset ((Fin n → ℚ) × ℚ)) (hI : I.Nonempty)
    (u : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) r) f → EReal)
    (hform : ∀ w (hw : w ∈ W),
      u w = ((I.sup' hI fun j => RelativeSchemeValuedPoint.unitTropAffine a j w (hWV w hw) : ℝ) : EReal)) :
    let hVy := hWV y hyW
    letI : Nonempty V := ⟨⟨y.1.point,hVy⟩⟩
    let F := fun i : Fin n => GaussRegularSurfaceConvexProfiles.genericFieldMap p
      (X.germToFunctionField V (a i : Γ(X,V)))
    let b := fun j : (Fin n → ℚ) × ℚ => RelativeSchemeValuedPoint.unitTropAffine a j y hVy
    let q := fun m : ℕ => GaussRegularSurfaceConvexProfiles.nativeWeightedPoint f p
      π z hπ hz hm (m+1) (Nat.zero_lt_succ m) ht hπt r hr0 hr1
    let ε := fun m : ℕ => GaussRegularSurfaceConvexProfiles.nativeScale f p
      π z hπ hz hm r (m+1) (Nat.zero_lt_succ m)
    ∃ (e c : ℕ) (A B : Fin n → ℤ)
      (v : Fin n → (GaussRegularSurfaceValuationOrders.verticalRing π hπ)ˣ),
      let s := fun (j : (Fin n → ℚ) × ℚ) (_ : Unit) =>
        -(∑ i : Fin n, (j.1 i : ℝ) * ((B i : ℝ) - (A i : ℝ) / (e : ℝ) * (c : ℝ)))
      let D := FiniteAffineMax.activeSlope I hI b s ()
      0 < e ∧ e = GaussRegularSurfaceRealNorms.verticalParameterOrder π hπ
        (GaussRegularSurfaceConvexProfiles.stalkParameter f p) ∧
      (∀ i : Fin n,
        F i = GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ (v i) *
          (algebraMap (X.presheaf.stalk p) (FractionRing (X.presheaf.stalk p)) π) ^ (A i) ∧
        GaussRegularSurfaceValuationFractions.verticalOrder π hπ (F i) = WithZero.exp (A i) ∧
        GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
          (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm
            (IsLocalRing.residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ) (v i))) =
              WithZero.exp (B i)) ∧
      u y = ((I.sup' hI b : ℝ) : EReal) ∧
      (∀ᶠ m : ℕ in atTop,
        GaussRegularSurfaceRealNorms.weightedParameterOrder π z hπ hz hm (m+1)
          (Nat.zero_lt_succ m) (GaussRegularSurfaceConvexProfiles.stalkParameter f p) = e * (m+1) + c ∧
        u (q m) = ((I.sup' hI b + D * ε m : ℝ) : EReal) ∧
          ((u (q m)).toReal - (u y).toReal) / ε m = D) ∧
      Tendsto (fun m : ℕ => ((u (q m)).toReal - (u y).toReal) / ε m) atTop (𝓝 D) := by
  let q0 := GaussRegularSurfaceConvexProfiles.nativeVerticalPoint f p π hπ ht hπt r hr0 hr1
  let hVy := hWV y hyW
  let : Nonempty V := ⟨⟨y.1.point,hVy⟩⟩
  have hV0 : q0.1.point ∈ V := by
    exact (congrArg (fun w => w.1.point ∈ V) heq).mpr hVy
  obtain ⟨e,c,A,B,v,he,heorder,horders,hunit⟩ :=
    GaussRegularSurfaceConvexProfiles.exists_unit_profiles f p π z hπ hz hm ht hπt r hr0 hr1 V hV0 n a
  let q := fun m : ℕ => GaussRegularSurfaceConvexProfiles.nativeWeightedPoint f p
    π z hπ hz hm (m+1) (Nat.zero_lt_succ m) ht hπt r hr0 hr1
  let ε := fun m : ℕ => GaussRegularSurfaceConvexProfiles.nativeScale f p
    π z hπ hz hm r (m+1) (Nat.zero_lt_succ m)
  let b := fun j : (Fin n → ℚ) × ℚ => RelativeSchemeValuedPoint.unitTropAffine a j y hVy
  let s := fun (j : (Fin n → ℚ) × ℚ) (_ : Unit) =>
    -(∑ i : Fin n, (j.1 i : ℝ) * ((B i : ℝ) - (A i : ℝ) / (e : ℝ) * (c : ℝ)))
  let D := FiniteAffineMax.activeSlope I hI b s ()
  have hbase (i : Fin n) :
      Real.log (SchemeValuedPoint.eval q0.1 V hV0 (a i : Γ(X,V)) : ℝ) =
      Real.log (SchemeValuedPoint.eval y.1 V hVy (a i : Γ(X,V)) : ℝ) :=
    congrArg (fun v : ℝ≥0 => Real.log (v : ℝ))
      (eval_congr q0.1 y.1 (congrArg Subtype.val heq) V hV0 hVy (a i : Γ(X,V)))
  have h0 : u y = ((I.sup' hI b : ℝ) : EReal) := hform y hyW
  obtain ⟨δ,hδ,hmax⟩ := FiniteAffineMax.exists_pos_eventual_max I hI {()} b s
  have hlim : Tendsto q atTop (𝓝 y) :=
    (congrArg (fun w => Tendsto q atTop (𝓝 w)) heq).mp
      (GaussRegularSurfaceConvexProfiles.tendsto_nativeWeightedPoint f p π z hπ hz hm ht hπt r hr0 hr1)
  have hWtail : ∀ᶠ m : ℕ in atTop, q m ∈ W := hlim.eventually (hW.mem_nhds hyW)
  have hsmall : ∀ᶠ m : ℕ in atTop, ε m < δ :=
    (GaussRegularSurfaceConvexProfiles.tendsto_nativeScale f p π z hπ hz hm ht hπt r).eventually
      (gt_mem_nhds hδ)
  have hprofile : ∀ᶠ m : ℕ in atTop, u (q m) = ((I.sup' hI b + D * ε m : ℝ) : EReal) := by
    filter_upwards [hunit,hWtail,hsmall] with m hmU hmW hmδ
    have hterm (j : (Fin n → ℚ) × ℚ) :
        RelativeSchemeValuedPoint.unitTropAffine a j (q m) (hWV (q m) hmW) = b j + s j () * ε m := by
      have hsum : (∑ i : Fin n, (j.1 i : ℝ) * Real.log
          (SchemeValuedPoint.eval (q m).1 V (hWV (q m) hmW) (a i : Γ(X,V)) : ℝ)) =
          (∑ i : Fin n, (j.1 i : ℝ) * Real.log
            (SchemeValuedPoint.eval y.1 V hVy (a i : Γ(X,V)) : ℝ)) -
          (∑ i : Fin n, (j.1 i : ℝ) * ((B i : ℝ) - (A i : ℝ) / (e : ℝ) * (c : ℝ))) * ε m := by
        rw [Finset.sum_mul,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        have hlog := (hmU.2 i (hWV (q m) hmW)).trans
          (congrArg (fun x : ℝ => x - ε m * ((B i : ℝ) - (A i : ℝ) / (e : ℝ) * (c : ℝ))) (hbase i))
        calc
          _ = (j.1 i : ℝ) * (Real.log
              (SchemeValuedPoint.eval y.1 V hVy (a i : Γ(X,V)) : ℝ) -
                ε m * ((B i : ℝ) - (A i : ℝ) / (e : ℝ) * (c : ℝ))) :=
            congrArg (fun x : ℝ => (j.1 i : ℝ) * x) hlog
          _ = _ := by ring
      change (∑ i : Fin n, (j.1 i : ℝ) * Real.log
        (SchemeValuedPoint.eval (q m).1 V (hWV (q m) hmW) (a i : Γ(X,V)) : ℝ)) + j.2 =
        (∑ i : Fin n, (j.1 i : ℝ) * Real.log
          (SchemeValuedPoint.eval y.1 V hVy (a i : Γ(X,V)) : ℝ)) + j.2 +
        (-(∑ i : Fin n, (j.1 i : ℝ) * ((B i : ℝ) - (A i : ℝ) / (e : ℝ) * (c : ℝ)))) * ε m
      rw [hsum]
      ring
    rw [hform (q m) hmW]
    apply congrArg (fun x : ℝ => (x : EReal))
    have hfun : (fun j => RelativeSchemeValuedPoint.unitTropAffine a j (q m) (hWV (q m) hmW)) =
        fun j => b j + s j () * ε m := funext hterm
    rw [hfun,hmax () (Finset.mem_singleton_self ()) (ε m)
      (GaussRegularSurfaceConvexProfiles.nativeScale_pos f p π z hπ hz hm ht hπt r hr0 hr1
        (m+1) (Nat.zero_lt_succ m)).le hmδ]
  have hquot : ∀ᶠ m : ℕ in atTop, ((u (q m)).toReal - (u y).toReal) / ε m = D := by
    filter_upwards [hprofile] with m hm'
    rw [hm',h0,EReal.toReal_coe,EReal.toReal_coe,add_sub_cancel_left,
      mul_div_cancel_right₀ _ (GaussRegularSurfaceConvexProfiles.nativeScale_pos f p
        π z hπ hz hm ht hπt r hr0 hr1 (m+1) (Nat.zero_lt_succ m)).ne']
  refine ⟨e,c,A,B,v,he,heorder,horders,h0,?_,?_⟩
  · exact (hunit.and (hprofile.and hquot)).mono fun _ h => ⟨h.1.1,h.2⟩
  · exact tendsto_const_nhds.congr' (hquot.mono fun _ h => h.symm)

private theorem paperRadius_pos : 0 < ProjBerk.gaussRadius := by
  change (0 : ℝ) < Real.exp (-1)
  exact Real.exp_pos _

private theorem paperRadius_lt_one : ProjBerk.gaussRadius < 1 := by
  change Real.exp (-1) < (1 : ℝ)
  exact Real.exp_lt_one_iff.mpr (by norm_num)

/-- The original hu selects ONE family before ANY local point is introduced. -/
theorem exists_common_convex_profiles
    (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) [IsProper f] [IsDominant f]
    {C : Scheme.{u}} [IsIntegral C] (i : C ⟶ X) [IsClosedImmersion i]
    (x₀ : C) [IsNoetherianRing (X.presheaf.stalk (i x₀))]
    (π₀ : X.presheaf.stalk (i x₀)) (hπ₀ : Prime π₀)
    (hker₀ : RingHom.ker (i.stalkMap x₀).hom = Ideal.span {π₀})
    (hη : Polynomial.X ∈ (f (i (genericPoint C))).asIdeal)
    {U : Set (RelativeSchemeValuedPoint
      (gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius) f)}
    {u : RelativeSchemeValuedPoint
      (gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius) f → EReal}
    (hu : RelativeSchemeValuedPoint.IsConvexPLOn U u) :
    ∃ y : RelativeSchemeValuedPoint
        (gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius) f,
      y.1.point = genericPoint X ∧
      RelativeSchemeValuedPoint.center ProjBerk.gaussModelCoefficient_le_one y = i (genericPoint C) ∧
      (y ∈ U → ∃ W : Set (RelativeSchemeValuedPoint
          (gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius) f),
        IsOpen W ∧ ∃ hyW : y ∈ W, W ⊆ U ∧
        ∃ (V : X.Opens) (hWV : ∀ w ∈ W, w.1.point ∈ V)
          (n : ℕ) (a : Fin n → Γ(X,V)ˣ) (I : Finset ((Fin n → ℚ) × ℚ)) (hI : I.Nonempty),
          let hVy := hWV y hyW
          letI : Nonempty V := ⟨⟨y.1.point,hVy⟩⟩
          let b := fun j : (Fin n → ℚ) × ℚ => RelativeSchemeValuedPoint.unitTropAffine a j y hVy
          (FiniteAffineMax.active I hI b).Nonempty ∧
          (∀ w (hw : w ∈ W),
            u w = ((I.sup' hI fun j => RelativeSchemeValuedPoint.unitTropAffine a j w (hWV w hw) : ℝ) : EReal)) ∧
          u y = ((I.sup' hI b : ℝ) : EReal) ∧
          ∀ (x : C) [IsNoetherianRing (X.presheaf.stalk (i x))]
            (π z : X.presheaf.stalk (i x)) (hπ : Prime π)
            (_hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) (hz : ¬ π ∣ z)
            (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)) = Ideal.span {π,z}),
            ∃ (ht : GaussRegularSurfaceConvexProfiles.stalkParameter f (i x) ≠ 0)
              (hπt : π ∣ GaussRegularSurfaceConvexProfiles.stalkParameter f (i x)),
              GaussRegularSurfaceConvexProfiles.nativeVerticalPoint f (i x) π hπ ht hπt
                ProjBerk.gaussRadius paperRadius_pos paperRadius_lt_one = y ∧
              let F := fun j : Fin n => GaussRegularSurfaceConvexProfiles.genericFieldMap (i x)
                (X.germToFunctionField V (a j : Γ(X,V)))
              let q := fun m : ℕ => GaussRegularSurfaceConvexProfiles.nativeWeightedPoint f (i x)
                π z hπ hz hm (m+1) (Nat.zero_lt_succ m) ht hπt
                  ProjBerk.gaussRadius paperRadius_pos paperRadius_lt_one
              let ε := fun m : ℕ => GaussRegularSurfaceConvexProfiles.nativeScale f (i x)
                π z hπ hz hm ProjBerk.gaussRadius (m+1) (Nat.zero_lt_succ m)
              ∃ (e c : ℕ) (A B : Fin n → ℤ)
                (v : Fin n → (GaussRegularSurfaceValuationOrders.verticalRing π hπ)ˣ),
                let s := fun (j : (Fin n → ℚ) × ℚ) (_ : Unit) =>
                  -(∑ l : Fin n, (j.1 l : ℝ) * ((B l : ℝ) - (A l : ℝ) / (e : ℝ) * (c : ℝ)))
                let D := FiniteAffineMax.activeSlope I hI b s ()
                0 < e ∧ e = GaussRegularSurfaceRealNorms.verticalParameterOrder π hπ
                  (GaussRegularSurfaceConvexProfiles.stalkParameter f (i x)) ∧
                (∀ l : Fin n,
                  F l = GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ (v l) *
                    (algebraMap (X.presheaf.stalk (i x)) (FractionRing (X.presheaf.stalk (i x))) π) ^ (A l) ∧
                  GaussRegularSurfaceValuationFractions.verticalOrder π hπ (F l) = WithZero.exp (A l) ∧
                  GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
                    (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm
                      (IsLocalRing.residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ) (v l))) =
                        WithZero.exp (B l)) ∧
                u y = ((I.sup' hI b : ℝ) : EReal) ∧
                (∀ᶠ m : ℕ in atTop,
                  GaussRegularSurfaceRealNorms.weightedParameterOrder π z hπ hz hm (m+1)
                    (Nat.zero_lt_succ m) (GaussRegularSurfaceConvexProfiles.stalkParameter f (i x)) =
                      e * (m+1) + c ∧
                  u (q m) = ((I.sup' hI b + D * ε m : ℝ) : EReal) ∧
                    ((u (q m)).toReal - (u y).toReal) / ε m = D) ∧
                Tendsto (fun m : ℕ => ((u (q m)).toReal - (u y).toReal) / ε m) atTop (𝓝 D)) := by
  obtain ⟨y,hygen,hycenter,Hlocal⟩ :=
    GaussCommonVerticalPoints.exists_commonVerticalPoint (f := f) i x₀ π₀ hπ₀ hker₀ hη
  refine ⟨y,hygen,hycenter,?_⟩
  intro hyU
  obtain ⟨W,hW,hyW,hWU,V,hWV,n,a,I,hI,hform⟩ := hu y hyU
  refine ⟨W,hW,hyW,hWU,V,hWV,n,a,I,hI,FiniteAffineMax.active_nonempty I hI _,hform,?_,?_⟩
  · exact hform y hyW
  · intro x hNoeth π z hπ hker hz hm
    let : IsNoetherianRing (X.presheaf.stalk (i x)) := hNoeth
    obtain ⟨ht,hπt,heq,_hvals⟩ := Hlocal x π hπ hker
    refine ⟨ht,hπt,heq,?_⟩
    exact family_profile f (i x) π z hπ hz hm ht hπt ProjBerk.gaussRadius
      paperRadius_pos paperRadius_lt_one y heq W hW hyW V hWV n a I hI u hform

end EnvelopeProperty.GaussCommonConvexProfiles
