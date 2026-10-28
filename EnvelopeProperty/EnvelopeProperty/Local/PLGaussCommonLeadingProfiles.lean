import EnvelopeProperty.Local.PLGaussLeadingResidueNaturality
import EnvelopeProperty.Local.PLGaussCommonConvexProfiles

/-! # SAME original common profiles and actual global leading functions

Raw integer weighted orders fix BOTH affine coefficients before any normalized
real profile is rewritten. No field/residue/order/norm matching is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Filter Order
open scoped Classical WithZero NNReal Topology

universe u
namespace EnvelopeProperty.GaussCommonLeadingProfiles

variable {Y : Scheme.{u}} [IsIntegral Y]

/-- EVERY original stalk coefficient keeps the literal actual fraction value in old profiles. -/
theorem genericFieldMap_algebraMap (p : Y) (s : Y.presheaf.stalk p) :
    GaussRegularSurfaceConvexProfiles.genericFieldMap p
      (algebraMap (Y.presheaf.stalk p) Y.functionField s) =
      algebraMap (Y.presheaf.stalk p) (FractionRing (Y.presheaf.stalk p)) s :=
  (FractionRing.algEquiv (A := Y.presheaf.stalk p) Y.functionField).symm.commutes s

/-- The actual parameter at ANY original point has the SAME whole-field value before ANY other stalk. -/
theorem genericFieldMap_parameter {k : Type u} [Field k]
    (f : Y ⟶ Spec (CommRingCat.of (Polynomial k))) (p q : Y) :
    GaussRegularSurfaceConvexProfiles.genericFieldMap p
      (algebraMap (Y.presheaf.stalk q) Y.functionField
        (GaussRegularSurfaceConvexProfiles.stalkParameter f q)) =
      algebraMap (Y.presheaf.stalk p) (FractionRing (Y.presheaf.stalk p))
        (GaussRegularSurfaceConvexProfiles.stalkParameter f p) := by
  let : Nonempty (⊤ : Y.Opens) := ⟨⟨p,trivial⟩⟩
  change GaussRegularSurfaceConvexProfiles.genericFieldMap p
    (algebraMap (Y.presheaf.stalk q) Y.functionField
      (Y.presheaf.germ ⊤ q trivial (Berkovich.SchemeValuedPoint.sectionBaseMap f ⊤ Polynomial.X))) = _
  have hq := Y.algebraMap_germ_eq_germToFunctionField
    (show q ∈ (⊤ : Y.Opens) from trivial)
    (Berkovich.SchemeValuedPoint.sectionBaseMap f ⊤ Polynomial.X)
  exact (congrArg (GaussRegularSurfaceConvexProfiles.genericFieldMap p) hq).trans
    (GaussRegularSurfaceConvexProfiles.genericFieldMap_germ p ⊤ trivial _)

section RawOrders
variable {S : Type u} [CommRing S] [IsDomain S] [IsLocalRing S] [IsNoetherianRing S]

/-- The TRUE unnormalized weighted integer order is the exponential of the actual native parameter order. -/
theorem weightedOrder_parameter (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (N : ℕ) (hN : 0 < N)
    (t : S) (ht : t ≠ 0) (hπt : π ∣ t) :
    GaussRegularSurfaceValuationFractions.weightedOrder π z hπ hz hm N hN
      (algebraMap S (FractionRing S) t) =
      WithZero.exp (GaussRegularSurfaceRealNorms.weightedParameterOrder π z hπ hz hm N hN t : ℤ) := by
  let V := GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN
  let : Algebra V (FractionRing S) :=
    (GaussRegularSurfaceValuations.fractionEmbedding π z hπ hz N hm hN).toAlgebra
  let : IsFractionRing V (FractionRing S) :=
    GaussRegularSurfaceValuations.localFractionRing π z hπ hz N hm hN
  change Ring.ordFrac V (algebraMap S (FractionRing S) t) = _
  rw [← GaussRegularSurfaceValuations.fractionEmbedding_coefficient π z hπ hz N hm hN t]
  change Ring.ordFrac V (algebraMap V (FractionRing S)
    (GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN t)) = _
  rw [Ring.ordFrac_eq_valuation_inv,IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal,
    (GaussRegularSurfaceRealNorms.weightedParameterOrder_spec π z hπ hz hm N hN t ht hπt).1,inv_inv]
  rfl

private theorem verticalOrder_of_leading (π : S) (hπ : Prime π) (f : FractionRing S)
    (a : ℤ) (u : (GaussRegularSurfaceValuationOrders.verticalRing π hπ)ˣ)
    (hfactor : f = GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ u *
      (algebraMap S (FractionRing S) π) ^ a) :
    GaussRegularSurfaceValuationFractions.verticalOrder π hπ f = WithZero.exp a := by
  let T := GaussRegularSurfaceValuationOrders.verticalRing π hπ
  let : Algebra T (FractionRing S) :=
    (GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ).toAlgebra
  let : IsFractionRing T (FractionRing S) :=
    GaussRegularSurfaceValuationFractions.verticalFractionRing π hπ
  change Ring.ordFrac T f = _
  have hu : Ring.ordFrac T (GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ u) = 1 :=
    Ring.ordFrac_of_isUnit u.isUnit
  have hp : Ring.ordFrac T (algebraMap S (FractionRing S) π) = WithZero.exp 1 := by
    rw [← GaussRegularSurfaceValuationFractions.verticalFractionEmbedding_coefficient π hπ π]
    exact Ring.ordFrac_irreducible (GaussRegularSurfaceValuationOrders.verticalParameter_irreducible π hπ)
  rw [hfactor,map_mul,map_zpow₀,hu,hp,one_mul,← WithZero.exp_zsmul]
  simp

/-- Genuine factor and residual data force the OLD actual unnormalized affine tail, without any norm ratio. -/
theorem eventual_weightedOrder_of_leading (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (f : FractionRing S) (hf : f ≠ 0) (a b : ℤ)
    (u : (GaussRegularSurfaceValuationOrders.verticalRing π hπ)ˣ)
    (hfactor : f = GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ u *
      (algebraMap S (FractionRing S) π) ^ a)
    (hres : GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
      (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm
        (residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ) u)) = WithZero.exp b) :
    ∃ M : ℕ, ∀ (N : ℕ) (hN : 0 < N), M < N →
      GaussRegularSurfaceValuationFractions.weightedOrder π z hπ hz hm N hN f =
        WithZero.exp (a * (N : ℤ) + b) := by
  obtain ⟨a',b',u',hfactor',horder',hres',M,H⟩ :=
    GaussRegularSurfaceValuationFractions.exists_eventual_fieldOrder π z hπ hz hm f hf
  have haa : a' = a := WithZero.exp_injective <| horder'.symm.trans
    (verticalOrder_of_leading π hπ f a u hfactor)
  subst a'
  have hπK : algebraMap S (FractionRing S) π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr hπ.ne_zero
  have huu : u' = u := by
    apply Units.ext
    apply GaussRegularSurfaceValuationFractions.verticalFractionEmbedding_injective π hπ
    exact mul_right_cancel₀ (zpow_ne_zero a hπK) (hfactor'.symm.trans hfactor)
  subst u'
  have hbb : b' = b := WithZero.exp_injective (hres'.symm.trans hres)
  subst b'
  exact ⟨M,H⟩

end RawOrders

/-- Two adjacent sufficiently large ORIGINAL indices fix both exact integer coefficients. -/
theorem affine_coefficients_eq_of_eventually (a b A B : ℤ)
    (h : ∀ᶠ m : ℕ in atTop,
      WithZero.exp (a * ((m+1 : ℕ) : ℤ) + b) = WithZero.exp (A * ((m+1 : ℕ) : ℤ) + B)) :
    a = A ∧ b = B := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp h
  have h₁ := WithZero.exp_injective (hM M le_rfl)
  have h₂ := WithZero.exp_injective (hM (M+1) (Nat.le_succ M))
  push_cast at h₁ h₂
  have ha : a = A := by nlinarith
  refine ⟨ha,?_⟩
  rw [← ha] at h₁
  linarith

section Comparisons
variable {S : Type u} [CommRing S] [IsDomain S] [IsLocalRing S] [IsNoetherianRing S]

/-- Both coefficients of two genuine original leading tuples agree, by the SAME raw affine orders. -/
theorem profile_orders_eq (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (g : FractionRing S) (hg : g ≠ 0)
    (a b A B : ℤ) (u v : (GaussRegularSurfaceValuationOrders.verticalRing π hπ)ˣ)
    (hu : g = GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ u *
      (algebraMap S (FractionRing S) π) ^ a)
    (hru : GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
      (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm
        (residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ) u)) = WithZero.exp b)
    (hv : g = GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ v *
      (algebraMap S (FractionRing S) π) ^ A)
    (hrv : GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
      (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm
        (residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ) v)) = WithZero.exp B) :
    a = A ∧ b = B := by
  obtain ⟨M,H⟩ := eventual_weightedOrder_of_leading π z hπ hz hm g hg a b u hu hru
  obtain ⟨M',H'⟩ := eventual_weightedOrder_of_leading π z hπ hz hm g hg A B v hv hrv
  apply affine_coefficients_eq_of_eventually
  filter_upwards [eventually_gt_atTop (max M M')] with m hm'
  exact (H (m+1) (Nat.zero_lt_succ m) (by omega)).symm.trans
    (H' (m+1) (Nat.zero_lt_succ m) (by omega))

/-- The SAME actual parameter's raw affine tail fixes the actual natural profile degree and constant. -/
theorem parameter_profile_orders_eq (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (t : S) (ht : t ≠ 0) (hπt : π ∣ t)
    (a b : ℤ) (u : (GaussRegularSurfaceValuationOrders.verticalRing π hπ)ˣ)
    (hfactor : algebraMap S (FractionRing S) t =
      GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ u *
        (algebraMap S (FractionRing S) π) ^ a)
    (hres : GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
      (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm
        (residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ) u)) = WithZero.exp b)
    (E C : ℕ)
    (hprofile : ∀ᶠ m : ℕ in atTop,
      GaussRegularSurfaceRealNorms.weightedParameterOrder π z hπ hz hm (m+1) (Nat.zero_lt_succ m) t =
        E * (m+1) + C) :
    a = (E : ℤ) ∧ b = (C : ℤ) := by
  have htK : algebraMap S (FractionRing S) t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr ht
  obtain ⟨M,H⟩ := eventual_weightedOrder_of_leading π z hπ hz hm _ htK a b u hfactor hres
  apply affine_coefficients_eq_of_eventually
  filter_upwards [eventually_gt_atTop M,hprofile] with m hm' hp
  calc
    WithZero.exp (a * ((m+1 : ℕ) : ℤ) + b) =
      GaussRegularSurfaceValuationFractions.weightedOrder π z hπ hz hm (m+1)
        (Nat.zero_lt_succ m) (algebraMap S (FractionRing S) t) :=
      (H (m+1) (Nat.zero_lt_succ m) (by omega)).symm
    _ = WithZero.exp
        (GaussRegularSurfaceRealNorms.weightedParameterOrder π z hπ hz hm (m+1)
          (Nat.zero_lt_succ m) t : ℤ) :=
      weightedOrder_parameter π z hπ hz hm (m+1) (Nat.zero_lt_succ m) t ht hπt
    _ = WithZero.exp ((E : ℤ) * ((m+1 : ℕ) : ℤ) + (C : ℤ)) := by
      congr 1
      exact_mod_cast hp

end Comparisons

omit [IsIntegral Y] in
private theorem actualCoefficientMap_eq_native {k : Type u} [Field k]
    (f : Y ⟶ Spec (CommRingCat.of (Polynomial k))) (p : Y) :
    GaussRegularSurfaceConvexProfiles.stalkCoefficientMap f p =
      SchemeStalkCoefficients.coefficientMap f p := by
  apply RingHom.ext
  intro a
  change Y.presheaf.germ ⊤ p trivial
    (Y.presheaf.map (homOfLE (le_refl (⊤ : Y.Opens))).op
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv a))) =
    Y.presheaf.germ ⊤ p trivial (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv a))
  simp only [homOfLE_refl,op_id]
  exact congrArg (fun q : Γ(Y,⊤) ⟶ Γ(Y,⊤) =>
    Y.presheaf.germ ⊤ p (show p ∈ (⊤ : Y.Opens) from trivial)
      (q (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv a))))
    (Y.presheaf.map_id (Opposite.op (⊤ : Y.Opens)))

private theorem genericParameter_facts {k : Type u} [Field k]
    (f : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsProper f] [IsDominant f] (η : Y)
    (hη : Polynomial.X ∈ (f η).asIdeal) :
    GaussRegularSurfaceConvexProfiles.stalkParameter f η ≠ 0 ∧
      GaussRegularSurfaceConvexProfiles.stalkParameter f η ∈ maximalIdeal (Y.presheaf.stalk η) := by
  constructor
  · change GaussRegularSurfaceConvexProfiles.stalkCoefficientMap f η Polynomial.X ≠ 0
    rw [actualCoefficientMap_eq_native]
    exact (map_ne_zero_iff _ (SchemeStalkCoefficients.coefficientMap_injective f η)).mpr Polynomial.X_ne_zero
  · change GaussRegularSurfaceConvexProfiles.stalkCoefficientMap f η Polynomial.X ∈ _
    rw [actualCoefficientMap_eq_native]
    change Polynomial.X ∈ (maximalIdeal (Y.presheaf.stalk η)).comap (SchemeStalkCoefficients.coefficientMap f η)
    rw [SchemeStalkCoefficients.maximalIdeal_comap_coefficientMap]
    exact hη

section Main
open Berkovich
variable {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C]
  (i : C ⟶ Y) [IsClosedImmersion i]

local notation "D" => Y.presheaf.stalk (i (genericPoint C))

private theorem paperRadius_pos : 0 < ProjBerk.gaussRadius := by
  change (0 : ℝ) < Real.exp (-1)
  exact Real.exp_pos _

private theorem paperRadius_lt_one : ProjBerk.gaussRadius < 1 := by
  change Real.exp (-1) < (1 : ℝ)
  exact Real.exp_lt_one_iff.mpr (by norm_num)

/-- The OLD actual common profile has exact slopes of ONE original global-leading family,
with BOTH raw affine coefficients internally identified, including the actual c_nat. -/
theorem exists_common_globalLeading_profiles
    (f : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsProper f] [IsDominant f]
    (x₀ : C) [IsNoetherianRing (Y.presheaf.stalk (i x₀))]
    (π₀ : Y.presheaf.stalk (i x₀)) (hπ₀ : Prime π₀)
    (hker₀ : RingHom.ker (i.stalkMap x₀).hom = Ideal.span {π₀})
    (hη : Polynomial.X ∈ (f (i (genericPoint C))).asIdeal)
    (hdim : topologicalKrullDim C ≤ 1)
    {U : Set (RelativeSchemeValuedPoint
      (gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius) f)}
    {u : RelativeSchemeValuedPoint
      (gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius) f → EReal}
    (hu : RelativeSchemeValuedPoint.IsConvexPLOn U u) :
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
                let s := fun (j : (Fin n → ℚ) × ℚ) (_ : Unit) =>
                  -(∑ l : Fin n, (j.1 l : ℝ) * ((C.ord (i.stalkMap (genericPoint C) (UF l)) x : ℝ) -
                    (A l : ℝ) / (e : ℝ) * (C.ord (i.stalkMap (genericPoint C) Ut) x : ℝ)))
                let slope := FiniteAffineMax.activeSlope I hI β s ()
                ∃ c : ℕ,
                  (∀ᶠ m : ℕ in atTop,
                    GaussRegularSurfaceRealNorms.weightedParameterOrder π z hπ hz hm (m+1)
                      (Nat.zero_lt_succ m) (GaussRegularSurfaceConvexProfiles.stalkParameter f (i x)) =
                        e * (m+1) + c) ∧
                  (∀ᶠ m : ℕ in atTop,
                    u (q m) = ((I.sup' hI β + slope * ε m : ℝ) : EReal) ∧
                      ((u (q m)).toReal - (u y).toReal) / ε m = slope) ∧
                  Tendsto (fun m : ℕ => ((u (q m)).toReal - (u y).toReal) / ε m) atTop (𝓝 slope)) := by
  obtain ⟨y,hygen,hycenter,Hcommon⟩ :=
    GaussCommonConvexProfiles.exists_common_convex_profiles f i x₀ π₀ hπ₀ hker₀ hη hu
  refine ⟨y,hygen,hycenter,?_⟩
  intro hyU
  obtain ⟨W,hW,hyW,hWU,V,hWV,n,units,I,hI,hactive,hform,hbase,Hlocal⟩ := Hcommon hyU
  let hVy := hWV y hyW
  let : Nonempty V := ⟨⟨y.1.point,hVy⟩⟩
  let β := fun j : (Fin n → ℚ) × ℚ => RelativeSchemeValuedPoint.unitTropAffine units j y hVy
  obtain ⟨htη,htηm⟩ := genericParameter_facts f (i (genericPoint C)) hη
  obtain ⟨ϖ,e,Ut,hϖ,he,htfac,Hleading⟩ := GaussLeadingResidueNaturality.exists_correctedLeadingOrders
    i x₀ π₀ hπ₀ hker₀ (GaussRegularSurfaceConvexProfiles.stalkParameter f (i (genericPoint C))) htη htηm hdim
  have hF (l : Fin n) : Y.germToFunctionField V (units l : Γ(Y,V)) ≠ 0 :=
    (map_ne_zero_iff _ (Y.germToFunctionField_injective V)).mpr (Units.ne_zero (units l))
  choose A UF hfacF HF using fun l : Fin n => Hleading (Y.germToFunctionField V (units l : Γ(Y,V))) (hF l)
  obtain ⟨_a₁,_U₁,_hfac₁,H₁⟩ := Hleading 1 one_ne_zero
  refine ⟨W,hW,hyW,hWU,V,hWV,n,units,I,hI,ϖ,e,Ut,A,UF,hϖ,he,htfac,hfacF,hactive,hform,hbase,?_⟩
  intro x hNoeth hx π z hπ hker hz hm
  let : IsNoetherianRing (Y.presheaf.stalk (i x)) := hNoeth
  obtain ⟨ht,hπt,hq,E,cOld,Aold,Bold,vOld,_heOld,_heOrder,horders,_hbaseX,htail,hlim⟩ :=
    Hlocal x π z hπ hker hz hm
  have hparam := htail.mono fun _ h => h.1
  have htfield := genericFieldMap_parameter f (i x) (i (genericPoint C))
  change (FractionRing.algEquiv (A := Y.presheaf.stalk (i x)) Y.functionField).symm
      (algebraMap D Y.functionField (GaussRegularSurfaceConvexProfiles.stalkParameter f (i (genericPoint C)))) =
    algebraMap (Y.presheaf.stalk (i x)) (FractionRing (Y.presheaf.stalk (i x)))
      (GaussRegularSurfaceConvexProfiles.stalkParameter f (i x)) at htfield
  obtain ⟨_b₀,c₀,_u₀,w₀,_v₀,_hv₀,_hfu₀,htw₀,_hrf₀,_hrt₀,_hresf₀,hrest₀,_hq₀,_hi₀,_hc₀⟩ :=
    H₁ x hNoeth hx π z hπ hz hm hker
  rw [htfield] at htw₀
  have hEC := parameter_profile_orders_eq π z hπ hz hm _ ht hπt (e : ℤ) c₀ w₀ htw₀ hrest₀ E cOld hparam
  have hE : E = e := by exact_mod_cast hEC.1.symm
  have hgamma (l : Fin n) : (Bold l : ℝ) - (Aold l : ℝ) / (E : ℝ) * (cOld : ℝ) =
      (C.ord (i.stalkMap (genericPoint C) (UF l)) x : ℝ) -
        (A l : ℝ) / (e : ℝ) * (C.ord (i.stalkMap (genericPoint C) Ut) x : ℝ) := by
    obtain ⟨b,c,u',w',_v',_hv',hfu,htw,_hrf,_hrt,hresf,hrest,_hq',_hi',hcorr⟩ :=
      HF l x hNoeth hx π z hπ hz hm hker
    rw [htfield] at htw
    have hF' : GaussRegularSurfaceConvexProfiles.genericFieldMap (i x)
        (Y.germToFunctionField V (units l : Γ(Y,V))) ≠ 0 :=
      (map_ne_zero_iff _ (FractionRing.algEquiv (A := Y.presheaf.stalk (i x)) Y.functionField).symm.injective).mpr (hF l)
    have hAB := profile_orders_eq π z hπ hz hm _ hF' (A l) b (Aold l) (Bold l) u' (vOld l)
      hfu hresf (horders l).1 (horders l).2.2
    have hEC' := parameter_profile_orders_eq π z hπ hz hm _ ht hπt (e : ℤ) c w' htw hrest E cOld hparam
    have hcR : (cOld : ℝ) = (c : ℝ) := by exact_mod_cast hEC'.2.symm
    rw [← hAB.1,← hAB.2,hE,hcR]
    exact hcorr
  let oldS := fun (j : (Fin n → ℚ) × ℚ) (_ : Unit) =>
    -(∑ l : Fin n, (j.1 l : ℝ) * ((Bold l : ℝ) - (Aold l : ℝ) / (E : ℝ) * (cOld : ℝ)))
  let newS := fun (j : (Fin n → ℚ) × ℚ) (_ : Unit) =>
    -(∑ l : Fin n, (j.1 l : ℝ) * ((C.ord (i.stalkMap (genericPoint C) (UF l)) x : ℝ) -
      (A l : ℝ) / (e : ℝ) * (C.ord (i.stalkMap (genericPoint C) Ut) x : ℝ)))
  have hS : oldS = newS := by
    funext j _
    change -(∑ l : Fin n, (j.1 l : ℝ) * _) = -(∑ l : Fin n, (j.1 l : ℝ) * _)
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    rw [hgamma l]
  have hD : FiniteAffineMax.activeSlope I hI β oldS () = FiniteAffineMax.activeSlope I hI β newS () :=
    congrArg (fun s => FiniteAffineMax.activeSlope I hI β s ()) hS
  refine ⟨ht,hπt,hq,cOld,?_,?_,?_⟩
  · exact hparam.mono fun _ h => by simpa only [hE] using h
  · filter_upwards [htail] with m hm'
    have hp := hm'.2.1
    have hq' := hm'.2.2
    change u _ = ((I.sup' hI β + FiniteAffineMax.activeSlope I hI β oldS () * _ : ℝ) : EReal) at hp
    change _ = FiniteAffineMax.activeSlope I hI β oldS () at hq'
    rw [hD] at hp hq'
    exact ⟨hp,hq'⟩
  · change Tendsto _ atTop (𝓝 (FiniteAffineMax.activeSlope I hI β oldS ())) at hlim
    rw [hD] at hlim
    exact hlim

end Main

end EnvelopeProperty.GaussCommonLeadingProfiles
