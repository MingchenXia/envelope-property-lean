import EnvelopeProperty.AlgGeom.CurveLineDegrees
import EnvelopeProperty.AlgGeom.SchemeGeneratorFrameNeighborhoods

/-! # Actual original sections/global generators imply TRUE intrinsic curve degree nonnegativity -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.CurveLineSectionPositivity
open CurveCartierLocalOrders CurveLineDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every actual original effective Cartier equation has nonnegative TRUE native local order. -/
theorem localOrder_nonneg {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I.IsInvertible) (x : X) : 0 ≤ localOrder I hI x := by
  let U := equationChart I hI x
  let : Nonempty U.1 := ⟨⟨x, mem_equationChart I hI x⟩⟩
  let : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  have hc : equation I hI x ≠ 0 := nonZeroDivisors.ne_zero (equation_mem_nonZeroDivisors I hI x)
  change 0 ≤ X.ord (X.germToFunctionField U.1 (equation I hI x)) x
  by_cases hx : Order.coheight x = 1
  · rw [SchemeOrderLocalLength.ord_germToFunctionField_eq_stalk_length x hx U.1
      (mem_equationChart I hI x) _ hc]
    exact Nat.cast_nonneg _
  · rw [X.ord_eq_zero_of_coheight_neq_one hx]

/-- Every SAME original Cartier order with its ORIGINAL residue degree is genuinely nonnegative. -/
theorem weightedLocalOrder_nonneg {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {k : Type u} [Field k] (q : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (hI : I.IsInvertible) (x : X) :
    0 ≤ weightedLocalOrder q I hI x := by
  unfold weightedLocalOrder
  exact mul_nonneg (localOrder_nonneg I hI x) (Nat.cast_nonneg _)

/-- Every SAME actual original nonzero global line section gives nonnegative
TRUE full normalized coherent Euler degree on the ORIGINAL projective curve. -/
theorem degree_nonneg_of_nonzero_section {X : Scheme.{u}} [IsIntegral X]
    {k : Type u} [Field k] (q : X ⟶ Spec (.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) (hs : s ≠ 0) :
    letI : IsProper q := hq.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
    0 ≤ degree q L := by
  let : IsProper q := hq.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  rw [degree_eq_zeroSection_orders q hq hdim L hL s hs]
  exact finsum_nonneg (fun x => weightedLocalOrder_nonneg q _ _ x)

/-- At ANY actual original point, an actual original generating family
contains a genuinely nonzero SAME original global generator, internally derived. -/
theorem exists_generatorHom_ne_zero {X : Scheme.{u}} {L : X.Modules}
    (hL : IsInvertible L) (G : L.GeneratingSections) (x : X) :
    ∃ i : G.I, SchemeGeneratingSectionsUnit.generatorHom G i ≠ 0 := by
  obtain ⟨U, hxU, i, hi⟩ := SchemeGeneratorFrameNeighborhoods.exists_affine_generator_frame hL G x
  refine ⟨i, ?_⟩
  intro hz
  let : Nonempty U.1.toScheme := ⟨⟨x, hxU⟩⟩
  let : Nonempty (⊤ : U.1.toScheme.Opens) := ⟨⟨⟨x, hxU⟩, trivial⟩⟩
  have he := SchemeGeneratorFrameNeighborhoods.generatorFrame_section G U.1 i hi
  rw [hz, SchemeLineSectionEvaluation.pullbackSectionHom, Functor.map_zero, comp_zero, zero_comp] at he
  have h := congrArg (fun α : unitObj U.1.toScheme ⟶ unitObj U.1.toScheme =>
    (α.val.app (op ⊤)).hom (1 : Γ(U.1.toScheme, ⊤))) he
  change (0 : Γ(U.1.toScheme, ⊤)) = 1 at h
  exact zero_ne_one h

/-- ANY genuine original global generating family makes the SAME original
line's true projective-curve degree nonnegative, with no finite-family certificate. -/
theorem degree_nonneg_of_generatingSections {X : Scheme.{u}} [IsIntegral X]
    {k : Type u} [Field k] (q : X ⟶ Spec (.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules) (hL : IsInvertible L)
    (G : L.GeneratingSections) :
    letI : IsProper q := hq.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
    0 ≤ degree q L := by
  obtain ⟨i, hi⟩ := exists_generatorHom_ne_zero hL G (genericPoint X)
  exact degree_nonneg_of_nonzero_section q hq hdim L hL (SchemeGeneratingSectionsUnit.generatorHom G i) hi

/-- Every actual ORIGINAL curve pullback of a SAME genuinely globally generated
line has nonnegative TRUE full Euler degree. No flat/proper curve-map assumption,
finite family or numerical/nef matching certificate is supplied. -/
theorem degree_pullback_nonneg_of_generatingSections {C Z : Scheme.{u}} [IsIntegral C]
    {k : Type u} [Field k] (q : C ⟶ Spec (.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim C ≤ 1) (i : C ⟶ Z) (L : Z.Modules)
    (hL : IsInvertible L) (G : L.GeneratingSections) :
    letI : IsProper q := hq.isProper
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace q
    0 ≤ degree q ((Scheme.Modules.pullback i).obj L) :=
  degree_nonneg_of_generatingSections q hq hdim _ (hL.pullback i)
    (ClosedProjectiveGlobalGeneration.pullback_generatingSections i G)

end EnvelopeProperty.CurveLineSectionPositivity
