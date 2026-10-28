# Errata in the literature found while formalizing FHX

This file lists the mistakes in the **literature** (published papers, preprints, notes and the
Stacks project) that were found, or recorded, while formalizing Fang–Han–Xia, *The envelope
property for unibranch projective varieties* (FHX), and whose formalized consequences are part of
this repository. It is an extract of the errata file of the development workspace; the entry
identifiers (`EP-1.1`, `T23`, `J8`, `TN-S2`, …) are those of the workspace file, so they stay
stable across both. Mistakes in our own blueprints, plans or Lean interfaces are not listed.

**Provenance of this extract.**
- Extracted by `make-errata.py` from the workspace `ERRATA.md` (sha256 `2ab11a7b9723c533…`, last
  modified 2026-10-28 08:59 UTC), workspace revision `322d15868e36b7aec63561aa2fc8cf98f038206c`.
- Included: workspace §5.1–§5.5 (here §1.1–§1.5), §6.1–§6.2 (here §2.1–§2.2), §2.1 and §2.3
  (here §3.1–§3.2), and the matching rows of the summary table. Not included: the workspace
  sections on our own material (§2.4, §5.6, §6.3), on SGPTFormalization (§3; only scheme/germ
  infrastructure of that project is in this repository, not the modules about the cited book
  statements), on BingWangEntropy (§4; no mistake recorded), SixSphereFormalization (§1) and
  DeJongEPBridge (§7).
- The source revisions the entries refer to are stated at the head of each section (FHX
  revision `832e086`, against which the FHX entries were checked; the paper in `paper/` is the
  author's later revision of 2026-10-28).
- Lean names and Lean file paths are those of this repository: paths are relative to the
  package directory (`EnvelopeProperty/`, `DeJongAlterations/`, `TranscendentalNakamaye/`).
  A name or file marked ‡ is not part of this repository (it lives in a module outside the
  import closure of the release roots). An entry identifier marked † refers to an entry of the
  workspace file that is not reproduced here (our own material, or a project not in this
  release). Blueprint labels (`thm:…`, `lem:…`, …) refer to the blueprint; chapter files that
  are part of the curated subset are cited as `blueprint/src/….tex`.
- References to files of the development workspace (working notes, plans, audits,
  transcriptions of the sources) are replaced by neutral phrases such as "our development
  notes" or "our transcription"; lane names (PNN, G13a, …) identify the working groups of
  the formalization that found an entry.

**Status legend.** ☐ open (not fixed in the source, or not yet reported) · ☑ fixed in the source (a later edition or revision has the correction) · — not applicable (a withdrawn report, or an observation that is not an error).

---

## 0. Summary of the most serious items

False statements, false proof steps and counterexamples, across all projects. Details in the entry named in the last
column.

| # | Project | Location | Mistake | Evidence | Status | Entry |
|---|---|---|---|---|---|---|
| 1 | EP | BJ22 (arXiv v4) Lemma 4.6 `lem:PSH` | **Statement false** (and its proof breaks at `−∞` values) | explicit counterexample on `K=[0,1]`; Lean `EnvelopeProperty.not_bj22Lemma46`; recorded by FHX 2026-10-28 (Remark 2.2, a weaker example with limit `≡ −∞`) | ☐ | EP-1.1 |
| 2 | EP | BJ22 Thm 4.5 (PSH2) at psef non-nef classes; FHX Prop 2.1(1) cites it at all classes | **unproved** (rests on the false Lemma 4.6); FHX 832e086 uses it at three places | repaired for FHX's uses (lane PNN, `blueprint/src/nonnef.tex`); FHX 2026-10-28 restricts Prop 2.1(1) to nef or homogeneous nets (unibranch after the main theorem) and no longer uses it at non-nef classes | ☐ BJ22 · ☑ FHX (2026-10-28) | EP-1.1 |
| 3 | EP | BJ22 Thm 6.21 `thm:pshdiv` | proof gap (author's note); FHX §7 gives a `ℙ¹` counterexample to the monotonicity step | recorded by the author/FHX; Lean `EnvelopeProperty.ProjBerk.bj621_counterexample` (PR227, merged into main in 590ac51eff) | ☐ | EP-4.1 |
| 4 | EP | Wu26 Lemma 5.11 | incorrect ideal-theoretic claim (recorded by FHX) | FHX `lem:principal-hull` | ☐ | EP-4.2 |
| 5 | DJA | Temkin 2010, Lemma B.3 proof (T:4476–4478) | **false step** ("some double point joins `Y₁∖Y₂` to `Y₂∖Y₁`") | counterexample with three components `a,b,c` | ☐ | DJA-T23 |
| 6 | DJA | Temkin 2010, Prop 6.2.4 types 2/3 | stated for any critical coset, induction closes only for `a ∈ k` | only special cosets are used later | ☐ | DJA-T26 |
| 7 | DJA | Temkin 2010, Prop 4.4.6 (T:3212–3214) | ~~`H¹(Z,O_Z)=0 ⇒ H¹(O_Y(mΣpᵢ))=0` fails when `\|∂Z\|=2`~~ **withdrawn 2026-10-21**: Temkin's step is correct; the failure concerns only our reconstruction (DJA-O34†) | `H¹(ℙ¹,O(−2)) ≠ 0` (applies to our reconstruction) | — | DJA-T10 |
| 8 | DJA | Temkin 2010, Prop 2.2.1 proof (T:2128–2129) | "`m F̂°_i = F̂°°_i`": `m` undefined; equality fails for ramified `F̂_i/K̂` | — | ☐ | DJA-T27 |
| 9 | DJA | Temkin 2010, Prop 4.3.1 (T:2972–2975) | "x the only closed point of the modification locus" does not make a local blow-up extend by the identity (locus need not be closed in `C`) | `𝔸¹_R`, `R` of height 2 (BL1) | ☐ | DJA-T33 |
| 10 | DJA | Temkin 2010, Lemma 4.4.4 proof (T:3164–3166) | **false step**: components in the closure of an exceptional component need not be exceptional | height-2 counterexample (T44A) | ☐ | DJA-T57 |
| 11 | TN | original TN note, l. 264–266 / 476–478 | per-current identity "non-pluripolar product = CT22 absolutely continuous part" **false** | `P¹`, `φ=max(log\|z\|²,0)−log(1+\|z\|²)` | ☑ (revised) | TN-S2 |
| 12 | TN | original TN note, l. 305–309 `it:monotone` | mass monotonicity written in the wrong direction | Witt Nyström | ☑ (revised) | TN-S1 |

---

## 1. EnvelopeProperty: FHX and the literature it uses

Sources: FHX = Fang–Han–Xia, *The envelope property for unibranch projective varieties*, revision 832e086; BJ22 = Boucksom–Jonsson, *Global pluripotential theory over a trivially valued
field*, arXiv:1801.08229, version of 2022-03-08 (theorem numbers of this arXiv version from
its shared counter, e.g. `defi:psh` = Def 4.1, `thm:psh12` = Thm 4.5, `lem:PSH` = Lemma 4.6, `cor:pshcvx` = Cor 4.10,
`thm:pshdiv` = Thm 6.21; the published version may number differently); BJadd = BJ addendum arXiv:2206.07183v2; Wu26 =
Wu, *On the local theory of non-archimedean psh functions*, arXiv:2609.27610v1; Stacks at commit a04446e5; Roberts–Singh,
Compositio Math. 85 (1993). FHX′ = the revision of FHX supplied by the author on 2026-10-28
(`main.tex`; unified diff against 832e086 in
our copy of the source, 43 hunks, classified and refereed by lane FX in
our development notes). Line numbers `l. N` refer to 832e086 unless marked FHX′.
For an entry whose source is FHX, ☑ (2026-10-28) means fixed in FHX′; for an entry whose source is BJ22, BJadd, Wu26,
Stacks or Roberts–Singh the status refers to that source, which FHX′ does not change, and how FHX′ now avoids the
problem is recorded in the entry.



### 1.1 Errors and proof gaps found in this project

**EP-1.1. BJ22 Lemma 4.6 (`lem:PSH`) is false as stated; its proof breaks when approximants take the value −∞** ☐
(BJ22; FHX's citation ☑ 2026-10-28, see the update below)
- *Statement (BJ22).* `K` compact; for `s ∈ S` a family `𝓕_s` of continuous `K → ℝ ∪ {−∞}` stable under adding
  constants; `ρ : S → T`, `T` metrizable; `𝓕̃_t` = decreasing limits of nets `f_i ∈ 𝓕_{s_i}` with `ρ(s_i) → t`. Claim:
  `𝓕̃̃_t = 𝓕̃_t`.
- *Gap in the proof.* To show that the set `A` of triples `(i,j,ε)`, preordered by (4.4) (`equ:directed`), is directed,
  the proof passes from `g_{i₃} ≤ min{f_{i₁,j₁}, f_{i₂,j₂}}` to the strict (4.5) `g_{i₃}+ε₃ < min{f_{i₁,j₁}+ε₁,
  f_{i₂,j₂}+ε₂}` (`equ:i3i1`), puts `h_j = exp(f_{i₃,j}+ε₃) − exp(min{…})`, claims `lim_j h_j < 0` pointwise, and covers
  `K` by the increasing open sets `{h_j < 0}` to find `j₃`. At every `x` where `min{f_{i₁,j₁}, f_{i₂,j₂}}(x) = −∞` also
  `g_{i₃}(x) = −∞`, so (4.5) reads `−∞ < −∞` and fails; there `h_j(x) = exp(f_{i₃,j}(x)+ε₃) ≥ 0` for every `j` and
  `lim_j h_j(x) = exp(g_{i₃}(x)+ε₃) = 0` — FHX′ Remark 2.2 (l. 183) puts it this way: "(4.5) fails at a common `−∞`
  point; the exponential difference … then has limit zero, rather than a strictly negative limit" — so `x` lies in no
  `{h_j < 0}` (`h_j(x) > 0` if `f_{i₃,j}(x)` is finite, `= 0` if it is `−∞`). Weakening `<` to `≤`, which is all that
  (4.4) needs, does not repair the step, because the failure need not stay at the point: in the counterexample below
  the `−∞` loci are compatible (`f_{n,j}(p₁) = −∞` for all `n, j`, so `h_j(p₁) = 0`), yet for every `j` one has `h_j > 0`
  on a punctured neighbourhood of `p₁`, and `(1,j₁,ε₁)`, `(2,j₂,ε₂)` have no common upper bound (lane CE, `ex:A-ours`).
- *Counterexample to the step.* `K = (ℙ¹)^an`, `𝓕` the Fubini–Study functions, `s` a section with a zero `p`;
  `f_{i₁,j₁} = log|s|` (= `−∞` at the rigid point `p`), `g_{i₃} = log|s|` approximated by `f_{i₃,j} = max{log|s|, −j}`;
  here `h_j(p) = e^{ε₃−j} > 0` for all `j` (note §4, `ex:A-P1`; the conclusion of the lemma holds in this example, only
  the construction of the proof breaks).
- *The statement is false* (lane PNN, 2026-10-15; checked by the orchestrator against `trivval_2022_Mar8.tex`). `S`, `T`
  one point, `K = [0,1]`, `p_i = 2^{−i}`, `r_i = 2^{−i−2}`, `B_i = [p_i−r_i, p_i+r_i]` (pairwise disjoint, avoiding 0 and 1), `ℓ_i = log(|x−p_i|/r_i)` on `B_i` and
  0 elsewhere, `𝓕 = {f_{n,j}+c}`, `f_{n,j} = Σ_{i≤n} max{2ℓ_i, (1+1/n)ℓ_i − j}`. Then `f_{n,j} ↓ g_n = Σ_{i≤n} 2ℓ_i` and
  `g_n ↓ g = Σ_i 2ℓ_i ∈ 𝓕̃̃`; in a decreasing net `f_{n_α,j_α}+c_α → g` the rate `1+1/n` at `p₁` forces `n_α = N`
  eventually, and then `c_α` must tend both to `g(1) = 0` and to `g(p_{N+1}) = −∞`; so `g ∉ 𝓕̃`. Blueprint
  `prop:nn-bj-lemma46-false` (`blueprint/src/nonnef.tex`). **Lean certificate:** `EnvelopeProperty.not_bj22Lemma46 :
  ¬ BJ22Lemma46Statement` (`EnvelopeProperty/Global/Lemma46Counterexample.lean`, lane NN6), a faithful
  universe-polymorphic statement of both of BJ22's formulations (`bj22Lemma46Statement_iff_explicit`), refuted with the
  standard axioms only.
- *Consequences.* BJ22 Thm 4.5 (PSH2) is unproved at psef non-nef limit classes (for Fubini–Study families Lemma 4.6
  is exactly PSH2). Lane PNN (`blueprint/src/nonnef.tex`) proves PSH2 for homogeneous nets, for structured nets covering
  FHX's three uses (Thm 7.2, Prop 7.4, Thm 8.3 char 0), and for all nets on unibranch models; open: arbitrary nets at
  non-nef classes on non-unibranch models. Further affected statements (per PNN, to be confirmed in Lean): Thm 4.7(i)
  (real scaling), Cor 4.25, Thm 4.32, Lemma 5.9 and Lemma 6.23 at non-nef classes; the first step of Thm 4.15(i)
  (repairable by rounding weights, `cor:gl-pshhom`), and through Thm 4.15 also Cor 4.17, Lemma 4.26, Thm 4.22, Cor 12.18(i)
  (conclusions survive; the comparison theorem is proved without Lemma 4.6, `thm:gl-comparison`);
  BJadd Theorem A for real or non-big psef classes, the corollary "V_θ is θ-psh for psef θ" and `cor:contenvcomp` rest on
  PSH2 at psef classes (repair on smooth `X`, char 0 or dim ≤ 2, via `thm:nn-psh2-of-ep`); FHX Prop
  2.1(1) (`prop:BJ-package`) cites BJ22 Thm 4.5 at all classes (its three uses at non-nef classes are repaired without
  changing any FHX statement). Observation: the converse of BJ22 (4.1), `PSH(θ) ≠ ∅ ⇔ θ psef`, is
  proved here on unibranch varieties (`cor:nn-psef`); open on arbitrary varieties with this method.
- *Update 2026-10-27 (lane GR; not formalized).* Every use of PSH2
  in FHX §§1–8 is at a nef class, definitional (Thm 4.2, Lemma 7.1), or one of the three non-nef uses above (on normal or
  unibranch models; covered by `isPSHHom_of_antitone`, `isPSH_of_dominated_homMax`, `isPSH_of_sandwich`): FHX never uses
  PSH2 at a non-nef class on a non-unibranch variety. (a) On every model PSH2 holds for a decreasing limit `u` as soon as
  one homogeneous θ-psh `Ψ` dominates the slope of `u` at infinity ("Prop R"). (b) Example 1 (ℙ² blown up at a point, a
  point of the exceptional curve glued to a point off it): no single `Ψ` works for all `u` (the supremum of homogeneous
  θ-psh functions is not usc), although PSH2 holds there. (c) Example 2 (an abelian surface with an irrational nef
  boundary ray, blown up and glued the same way): a psef class θ with `PSH(X, θ) = ∅`. Hence the converse of BJ22 (4.1)
  **fails** on non-unibranch varieties (answering the observation above negatively), the unibranch hypothesis of
  `cor:nn-psef` is necessary, and the set of classes with nonempty PSH is not closed; PSH2 holds there vacuously. FHX
  Prop 2.1(1) at psef non-nef classes on non-unibranch varieties remains open (no proof, no counterexample). Suggested
  restatement: PSH2 at nef limit classes, homogeneous PSH2 at every class, and PSH2 at every class on unibranch
  varieties — which is all FHX uses.
- *Update 2026-10-28 (lane PR2; PR227, merged into main in 590ac51eff).* Part (a), "Prop R", is formalized on every
  model:
  `EnvelopeProperty.MultiModel.isPSH_of_antitone_of_homMajorant` (`Global/PSH2HomogeneousMajorant.lean`; blueprint
  `thm:hm-psh2-hom-majorant`, `blueprint/src/psh2-homogeneous-majorant.tex`): if `u_i ∈ PSH(θ_i)` decrease to `u ≢ −∞`, `θ_i → θ`,
  and one `Ψ ∈ PSH_hom(θ)` dominates every Legendre slice `û_λ`, `λ < u(⋆)`, then `u ∈ PSH(θ)`. (That this hypothesis
  means "`Ψ` dominates the slope `u_∞` at infinity" is proved on paper only, `rmk:hm-majorant-hypothesis`.) The
  majorant exists under `EP(θ)` (`exists_homMajorant_of_hasEnvelopeProperty`) and when `0 ∈ PSH(θ)`
  (`isPSH_of_antitone_of_isPSH_zero`). This is a conditional reduction, not general PSH2; Examples 1 and 2 are not
  formalized. Compiled sorry-free with the standard axioms (lane report); the file is imported by the root module
  `EnvelopeProperty.lean`‡ (l. 2738) together with the main theorems, so the pending name-clash probe is superseded by
  the merge (not re-checked by lane FX, which ran no Lean).
- *Update 2026-10-28 (FHX′; lane FX).* FHX′ adopts the restatement suggested above. Prop 2.1(1)
  (`prop:BJ-package`, FHX′ l. 163) now asserts PSH2 only for nef `θ` or homogeneous `u_i`, and at all classes on unibranch
  `X` "as proved after the main theorem" (Cor 8.4 `cor:unibranch-decreasing-stability`, l. 1167–1182); "We do not
  assert the unrestricted version of [BJ22, Theorem 4.5] on non-unibranch varieties in non-nef classes" (l. 194).
  The nef case is proved directly (l. 172): promotion into ample classes `θ + δ_iω`, truncation `max(φ, −m)`, and
  BJ22's diagonalization for finite-valued families — the "Fix used in Lean" below. New: Remark 2.2
  `rem:BJ-decreasing-limits` (l. 182–195), Lemma 2.3 `lem:homogeneous-decreasing-stability` (l. 197–216; =
  `thm:nn-psh2-hom`, `MultiModel.isPSHHom_of_antitone`, proved differently: compactness of `{q = −1}`, homogeneity and
  the generic points of the components of the common zero locus, instead of Rees points and a finite comparison),
  Lemma 7.4 `lem:homogeneous-carrier-limit` (l. 1010–1049; on models a special case of Prop R, since every Legendre
  slice of `lim U_n` is `≤ Ψ`), Cor 8.4 (= `cor:nn-psh2-unibranch`; see §1.5 for a shorter proof). The three non-nef
  uses are gone: Thm 7.2 by Lemma 2.3 for a constant net (l. 1003), Prop 7.5 (was 7.4) by Lemma 7.4 (l. 1079), Thm 8.3
  by descending homogeneous functions first (Lemma 2.3, l. 1126) and then slices with Lemma 7.4 (l. 1156–1160); the
  definitional uses now cite Def 4.1 (§3 l. 439, Thm 4.2 l. 510, Thm 6.1 Step 2 l. 972, Lemma 7.1 l. 991). Also avoided:
  BJ22 Thm 4.7 ((4), (5) proved on approximants, incl. real scaling, l. 178), Cor 6.17/Rem 6.18 (homogeneous projection,
  l. 176), Lemma 6.23 (l. 1060), and Thm 5.11 (Prop 2.4, was 2.2, reproved via BJ22 Thm 5.6, l. 229; the old proof's
  (i)⇒(ii) applied PSH2 at the class itself, harmless in 832e086, where that direction was used only at ample classes,
  but needed now that FHX′ uses it at arbitrary classes in Thm 8.3 and Cor 8.4). Real weights are reduced to rational
  ones by rounding (l. 149; = `cor:gl-pshhom`), which repairs the first step of BJ22 Thm 4.15(i) without saying so
  (EP-2.10). All new arguments checked by lane FX: correct.
  FHX′'s counterexample (`K = [0,1]`, `S = ℤ_{>0}`, `T = ℝ`, `ρ(n) = 1/n`, `𝓕_n = {log|x − 1/n| + c}`), checked against
  BJ22's exact statement: correct — BJ22's `𝓕̃_t` admits the limit `≡ −∞` (so `−∞ ∈ 𝓕̃_{1/n}` and `−∞ ∈ 𝓕̃̃_0`), `t = 0 ∉
  ρ(S)` is allowed, and by directedness a decreasing net from the `𝓕_n` lies in a single `𝓕_n` (`f_{i₃} ≤ f_{i₁}` forces
  a pole of `f_{i₃}` at the pole of `f_{i₁}`), also for nets eventually constant in the index; so `𝓕̃_0 = ∅`. It is
  weaker than ours: the iterated limit is `≡ −∞` and families with different `n` are incomparable, so it does not refute
  the restriction of the lemma to limits `≢ −∞`, which is all that BJ22's proof of Thm 4.5 uses and which for FS
  families is equivalent to PSH2 (note, `rmk:equiv`); ours refutes that restriction with `S`, `T` points and `g(1) = 0`
  (EP-2.9). Status: BJ22 unchanged (☐); FHX's citation fixed (☑, 2026-10-28). Still open in FHX′ and here: PSH2 for
  arbitrary nets at psef non-nef classes on non-unibranch varieties (no proof, no counterexample).
- *Fix used in Lean* (`EnvelopeProperty/Projective/PSH2.lean`): `IsDecrNetLimit.of_antitone_of_finite` proves BJ22's
  argument verbatim for real-valued continuous families (the limits `g_i` may still take `−∞`); `IsDecrNetLimit.of_
  antitone` proves the statement for families that avoid `+∞` and are stable under `max(·, c)`, by truncation. (The
  errata file's sentence "whether the statement holds as written is not settled here" predates the counterexample.)
- *Impact.* None at nef (semiample-approximated) classes: there `𝓗^gf_ℝ(L)` can be taken with `L` semiample, contains
  the constants and is stable under `max(·, c)` (covers `ℙⁿ` and everything formalized at the time;
  `ProjBerk.isPSH_of_antitone`, `FSSystem.isPSH_of_antitone`). Load-bearing for psef non-nef classes (lane P68, checked
  against `defi:psh`): Def 4.1 allows `𝓗^gf_ℝ(L_i)` for merely effective `L_i`, whose functions take `−∞` and contain no
  constants unless `L_i` is semiample. FHX uses PSH2 at non-nef classes in the last step of `thm:homogeneous-Siu`, in (U)
  of `prop:homogeneous-slices` and in char 0 of `thm:normalization-reflection` (P68). A fourth citation is harmless: FHX
  Lemma 7.1 (`lem:fixed-coefficient-division`) cites PSH2 for `q_t = lim q_i ∈ PSH_hom(X, η − t[E])`, but the `q_i` are
  homogeneous FS functions of classes `c₁(L_i) − t[E] → η − t[E]`, so the limit is psh by Def 4.1 (lane G10,
  `MultiModel.IsPSHHom.exists_eq_add_of_le_logSecAbs`).
- *Found by.* Lanes BJ1 and BJP (the gap), P68 (the impact), PNN (statement false), NN6 (Lean certificate), GR (the
  list of FHX's uses, Examples 1 and 2), PR2 (Prop R in Lean), FX (FHX′ review); Claude.
  Reporting to Boucksom–Jonsson is left to the author (after PNN).

### 1.2 Imprecisions and attribution issues

**EP-2.1. FHX Lemma 5.11(6) is stronger than the cited Wu26 Lemma 3.26** ☑ (2026-10-28)
- FHX's (6) allows, near every compact set, arbitrary local convex PL charts; Wu26 Lemma 3.26 requires a single
  tropicalization (`TConv ∩ PL` on `int E_r`) and `u ∈ PSH_log`. The extra strength comes from FHX Lemma 5.5 (the
  Chambert-Loir–Ducros positivity criterion in local charts). Suggested fix: cite Lemma 5.5 in the proof of (6) (or
  state (6) with Wu's hypothesis). The trust boundary of `WuRegularization` is recorded as FHX Lemmas 5.5, 5.9, 5.10 with
  BJ22 and CLD12.
- *Fixed in FHX′* (proof of `lem:regularizable-closure`, l. 678): "The positivity of the glued truncations in this
  argument is supplied by `lem:local-PL-positivity`. Thus (6) applies to the local convex PL presentations in its
  statement; [Wu26, Lemma 3.26], which assumes a single tropicalization and logarithmic growth, does not by itself
  give this form." (Lane FX.)

**EP-2.2. BJ22 Cor 4.10 (`cor:pshcvx`): value of `χ` at `−∞` and the approximants** ☐ (minor)
- `χ : (−∞, 0] → ℝ` is applied to `φ − ψ`, which may be `−∞`; the statement needs `χ(−∞) = lim_{t→−∞} χ(t)`. The proof
  asserts without construction that `χ` is a decreasing limit of finite maxima of affine functions with slopes in
  `[0,1]`; Lean uses chords over dyadic intervals of `[−m, 0]` plus the constant `χ(−m)`, raised by `3·2^{−m}`
  (`Projective/PSHConvex.lean`‡, `IsPSH.convexComp`‡).

**EP-2.3. BJadd Lemma 1.3 (`lem:contenv`), proof of (iii)⇒(i): reduction to PL obstacles** ☐ (minor)
- "By density of PL in C⁰ we can in fact assume `p_j ∈ PL`": uniform approximation of the terms of a decreasing net does
  not by itself give a decreasing net. Routine fix: index the net by all rational PL `ψ > h` (directed under `min`, by
  Urysohn and density); `ProjBerk.exists_antitone_isRatPL_net` (`Projective/PLDensity.lean`).
- *FHX′* (proof of Prop 2.5(1), was 2.3(1), l. 252) now gives this reduction explicitly, with the net indexed by all
  rational PL majorants of `f` (stable under finite minima) — the fix above — so FHX no longer depends on BJadd's step.
  BJadd is unchanged (☐). (Lane FX.)

**EP-2.4. Wu26 Lemma 3.24 (`lem:psh_PL_functions_are_pshlogreg`), proof of (3): sign typo** ☐ (minor)
- "`w′_i = ch − C_i` on `Y^an ∖ P_i`" should read "`ch + C_i`" (`w′_i = max{w_i, ch + C_i}` and `w_i ≤ h < ch + C_i` off
  `P_i`). Harmless. Found by lane PW.

**EP-2.5. FHX Lemma 8.2 (`lem:normalization-local-sandwich`): "subintegral extension" not defined** ☑ (2026-10-28)
- The lemma cites Roberts–Singh Thm 4.17, Prop 4.2, Cor 4.3 but FHX never defines the term. Roberts–Singh §4: a union of
  finite towers of elementary steps `A_i[e]` with `e², e³ ∈ A_i`; this is also what Stacks 0CND produces in the proof of
  FHX Thm 8.3 (char 0). With it, the first assertion of Lemma 8.2 is Roberts–Singh Thm 4.17 (ii)⇒(i) (printed p. 267).
  Suggested fix: add the definition. Found by lane REF; adopted as D-H3′.
- *Fixed in FHX′* (l. 1106): "An extension of rings `A ⊆ B` is *subintegral* if it is integral, `Spec B → Spec A` is
  bijective, and the induced residue-field maps are isomorphisms. Equivalently, every finite subset of `B` lies in a
  finite tower … with `e_i², e_i³ ∈ A[e_1, …, e_{i−1}]` [Stacks 0CND]" (Swan's definition, as in Roberts–Singh). Nit:
  0CND's condition (1) is "universal homeomorphism inducing isomorphisms on residue fields"; its equivalence with the
  three conditions is Stacks 04DF and 01S4, which FHX cites in Lemma 8.1. (Lane FX.)

**EP-2.6. Stacks 0CNF and 0CND: an implicit step; 0CN9 without proof** ☐ (minor)
- The proofs of Lemma 29.47.9 (`0CNF`) and Prop 29.47.7 (`0CND`, (1)⇒(2)) apply `0CNC` (resp. `0CNB`) to an intermediate
  `B′ ⊆ B` without checking that `Spec B → Spec B′` is again a universal homeomorphism (it is: integral, surjective by
  lying over, universal injectivity passes to the first factor). `0CN9` has its proof omitted ("clear denominators").
  Formalized at ring level: `Algebra.IsRadicialIntegral.over_subalgebra`, `exists_mul_not_mem_and_mul_pow_mem`. Found by
  lanes REF and G13b.

**EP-2.7. Roberts–Singh 1993, proof of Thm 4.17 (i)⇒(ii): misprint** ☐ (minor)
- p. 267: "If p = 0 then bⁿ ∈ B for n ≫ 0" should read "bⁿ ∈ A" (checked on the scanned page; transcription note in
  `page-0020`). Found by lanes REF and G13a.

**EP-2.8. FHX: two definitions of "unibranch" used interchangeably** ☑ (2026-10-28)
- *Location.* `BJ_envelope_fixed.tex` l. 68 (§1.1): "`X` is unibranch if its normalization is bijective, or
  equivalently, over the algebraically closed field `k`, a universal homeomorphism (`lem:unibranch-universal`)". The
  proof of `lem:unibranch-universal` (l. 1020) derives that `ν` is bijective "since the points of `Y` over `x ∈ X`
  correspond to the branches of `O_{X,x}` [Stacks 0C37, 0C3B], and `X` is unibranch [Stacks 0BQ2]", i.e. from the local
  notion (each local ring has one branch).
- *Problem.* Under the §1.1 definition that step is the hypothesis itself; the proof uses the stalkwise definition, and
  the equivalence of the two is never stated. Harmless: the cited tags supply it.
- *Fix.* State one definition and the equivalence (for integral `X`: normalization bijective ⇔ every local ring
  unibranch, Stacks 0C37/0C3B). Lean, with no hypothesis beyond integrality:
  `EnvelopeProperty.Variety.isUnibranch_iff_isUnibranchLocalRing_stalk` (`EnvelopeProperty/Source/Unibranch.lean`;
  blueprint `lem:var-unibranch-stalks`, `blueprint/src/source-unibranch.tex`; PR227, merged into main in 590ac51eff). Found by lane UB
  (PR227); checked against l. 68 and 1015–1022 by lane ER.
- *Fixed in FHX′* (l. 65): "Here `X` is *unibranch* if every local ring `O_{X,x}` has one branch. This is equivalent to
  bijectivity of the normalization [Stacks 0C37, 0C3B], and, over the algebraically closed field `k`, to its being a
  universal homeomorphism (`lem:unibranch-universal`)." The proof of `lem:unibranch-universal` (FHX′ l. 1103) is
  unchanged and now uses the stated definition. Our Theorem 1.1 assumes the equivalent form "normalization bijective";
  the bridge is the lemma above and Corollary 1.2's TFAE contains the stalk-wise form (lane FX).

**EP-2.9. FHX′ Remark 2.2 (`rem:BJ-decreasing-limits`): the counterexample to BJ22 Lemma 4.6 is degenerate** ☐ (minor)
- *Location.* FHX′ `main.tex` l. 185–190: `K = [0,1]`, `S = ℤ_{>0}`, `T = ℝ`, `ρ(n) = 1/n`,
  `𝓕_n = {log|x − 1/n| + c}`; `−∞ ∈ 𝓕̃_{1/n}`, hence `−∞ ∈ 𝓕̃̃_0`, while `𝓕̃_0 = ∅`.
- *Checked (lane FX).* Correct against BJ22's literal statement (EP-1.1, update of 2026-10-28).
- *Problem.* The example needs the limit `≡ −∞`, which BJ22's `𝓕̃_t` admits but PSH functions exclude, and families that
  are pairwise incomparable. It does not refute the lemma restricted to limits `≢ −∞` (here that restriction holds
  vacuously), which is all that the proof of BJ22 Thm 4.5 uses ("`PSH(θ)` is precisely the set of functions in `𝓕̃_θ`
  that are generically finite") and which, for Fubini–Study families, is equivalent to PSH2. So the example alone does
  not show that the proof of Thm 4.5 is incomplete; the failing step (4.5), which the remark also names, does. The
  remark's conclusion is stated correctly (the example "neither proves nor disproves" Thm 4.5).
- *Suggested fix.* Add that the lemma fails also for limits `≢ −∞`, with `S`, `T` points (EP-1.1; Lean
  `EnvelopeProperty.not_bj22Lemma46`), or say that the example uses only the identically `−∞` limit. Found by lane FX.

**EP-2.10. FHX′ §2.2: the rounding of real weights repairs BJ22 Thm 4.15(i) without saying so** ☐ (minor)
- *Location.* FHX′ l. 149 (real weights, "This gives the same psh class"), l. 174 (Prop 2.1(2): BJ22 Cor 4.17,
  Thm 4.22), l. 176 (Prop 2.1(3): BJ22 Cor 12.18), l. 229 (Prop 2.4: BJ22 Thm 5.6).
- *Problem.* These BJ22 results pass through BJ22 Thm 4.15(i) (Cor 4.17 and Cor 12.18 directly; Thm 4.22 and Thm 5.6
  through Lemma 4.26 `lem:supPL`, which uses Thm 4.15(iii)), whose first step applies the false Lemma 4.6 to the
  families `𝓗^gf_ℝ(L)` with the value `−∞` to pass to rational weights (EP-1.1, *Consequences*). FHX′'s rounding
  paragraph is exactly the repair of that step (our `cor:gl-pshhom`), and the rest of Thm 4.15 applies Lemma 4.6 only
  to finite-valued families, where it holds; but neither l. 149 nor Remark 2.2 mentions Thm 4.15, so a reader cannot
  see that the results cited in Prop 2.1(2), (3) and Prop 2.4 no longer depend on Lemma 4.6.
- *Suggested fix.* One sentence after l. 149: "This replaces the use of [BJ22, Lemma 4.6] in the first step of the
  proof of [BJ22, Theorem 4.15(i)], on which the results of [BJ22] cited in (2) and (3) and in Prop 2.4 rely." Found by
  lane FX (checked against `trivval_2022_Mar8.tex` l. 2950–2955, 3000–3013, 3307–3329, 7168–7198).

### 1.3 Hypotheses that can be dropped (the formalized statements are stronger) — not errors

| Source | Hypothesis | Lean |
|---|---|---|
| FHX Lemma 5.8(2) | injectivity of `φ` | `FSData.exists_eval_le_comap_of_isIntegral` |
| FHX Lemma 5.11(1) | used in §5 only at `v_triv` | `IsRegularizable.triv_ne_bot` |
| FHX Lemma 5.13 | `Y` normal: only integrality is used (the only point over `v_triv` is `v_triv`); lane N3 | `IsRegularizable.flatNormFun` (`IsDomain A` only) |
| FHX Cor 5.26 | `X′` normal: the proof uses it only through Lemma 5.10(1) on `P = X′`, whose proof (BJ22 Cor 12.18(iii), dehomogenization) does not use normality of `P` (only `Y = P_s`, here `≅` an open of the normal `X`), and Lemma 5.4(2) holds on any projective variety; planning lane P26, checked against the source text; also our development notes | confirmed: `ProjSubvariety.isPSH_of_isPSH_comp_proj` (no normality of the blowup `X′`) |
| FHX Lemma 5.10(1) | `P` normal (only `Y = P_s` normal is needed) | not formalized as such; the Lean proof of Cor 5.26 does not use Lemma 5.10(1) |
| FHX Thm 4.2 / Prop 4.1 (finite descent) | `T` normal (lane P68): normality of `X` is used only for the norm coefficients; FHX uses normality of `T` only through Prop 2.2 on `T` (BJ22 Thm 5.6), which the usc-regularization proof avoids; also, the weighted average formula holds at every point with generic support, not only on `X^div` | `MultiModel.FiniteHom.hasEnvelopeProperty` (lane G7; no hypothesis on `𝒯`, every class θ) |
| BJ22 `lem:legendre` (Lemma 6.20) as used in the proof of `thm:homogFS` (and FHX §7) | stated for `x ∈ ℝ^r` but applied with `x_i = log\|s_i\|(v) = −∞`; the one-variable formula holds with `−∞` entries; `max λ_i ≥ 0` is superfluous (P68; lane G4) | `iInf_sup_add_mul_eq_legendreMax` |
| BJ22 `cor:pshhom` | its proof goes through Thm 4.15(i) and hence the false Lemma 4.6; the conclusion holds for every class by rounding weights (lane G4) | `MultiModel.IsPSH.exists_isRatFS_net` |
| FHX Lemma 8.2, second assertion | `n ≥ N − d` and `a_m ∈ A`: `b^{n+2d} ∈ (a_{n+d}, …, a_{n+2d})B` holds for every `n ≥ 0` and arbitrary `c_i` (the interpolation only needs `n + d ≥ d`); the restriction only ensures `a_m ∈ A` when the lemma is applied (lane G13a) | `pow_mem_span_addPow` |
| FHX Lemma 5.15 (Rossi) | `x ∉ K` follows from the other hypotheses | `mem_hull_frontier_inter_hull` |
| FHX Lemma 5.17 | `K ⊆ Y_f` | `le_iSup_of_mem_hull_awayExtend` |
| FHX Prop 5.20(1) | `k` countable | `gluing_hullIneq` |
| FHX Prop 5.24 | weak plurisubharmonicity enters only through usc and stability under adding / taking maxima with regularizable functions | `projection_hullIneq`, `IsPshClass` |
| FHX Thm 5.25, proof | making `W ∩ Y₁` irreducible, and the dimension argument that `E = closure(Z′) ∩ W_U` is a proper closed subset, are not needed: incomparability for the finite `π` (every minimal prime of `I A_a` is minimal over `π⁻¹(I A_a) A_a`) gives `g` and the partition `f₁ + f₂ = 1` directly; only smoothness at `z` is needed | `exists_separation`, `ProjectionExistence.toProjectionPackage` |
| FHX §3 (test ideals) | subadditivity `B_{mℓ} ⊆ B_m^ℓ` needs no diagonal argument: `(IJ)^{[1/q]} ⊆ I^{[1/q]} J^{[1/q]}` by adjunction with Frobenius powers | `frobRoot_mul_le`, `asymptoticTestIdeal_mul_le` |

Adopted in FHX′ (2026-10-28; lane FX): the rows Thm 4.2 / Prop 4.1 (`T` integral, FHX′ l. 452, 506), Lemma 5.15
(`x ∈ K̂`, l. 742), Lemma 5.17 (any compact `K ⊆ Y^an`, conclusion `sup_{K∩Y_f^an}`, proof repaired, l. 762–772),
Cor 5.26 (`X′` integral, via its normalization, l. 938, 942), Lemma 8.2 second assertion (every `n ≥ 0`, l. 1114),
BJ22 `lem:legendre` (vanishing factors handled on faces in the homogeneous projection, l. 176) and BJ22 `cor:pshhom`
(rounding of weights, l. 149, 176). The other rows are unchanged in FHX′.

### 1.4 Known issues recorded by the sources or the author (not found here)

**EP-4.1. BJ22 Thm 6.21 (`thm:pshdiv`, homogeneous Siu decomposition): proof gap** ☐
- Author's note (2026-10-14); FHX §7 gives the counterexample on `ℙ¹` to the monotonicity
  step (FHX `REVIEW.md` §7.1: "Retained and checked the supplied `P¹` counterexample to varying-coefficient
  monotonicity"). Nothing in EP uses it or its consequences (BJ22 Cor 6.22, 6.41, Thm 6.31, 6.35, 6.40).
- *Lean certificate of FHX's example (lane PR2, PR227; merged into main in 590ac51eff).* FHX Remark 7.3 (`rem:BJ-6-21`,
  l. 963–965) checked: for `ℓ = e_E`, `ψ_n = (1 − 1/(2n))ℓ` and `t_n = 1 − 1/n` one has `ψ_n ↓ ℓ`, `ψ_n ≤ t_nℓ` and
  `ψ_n − t_nℓ = ℓ/(2n)`, strictly increasing where `ℓ` is finite and negative; no error in the remark.
  `EnvelopeProperty.ProjBerk.bj621_counterexample` (`EnvelopeProperty/Projective/Remark73ProjectiveLine.lean`, indices
  shifted by one, any field with the trivial absolute value; blueprint `prop:r73-p1-example`,
  `blueprint/src/remark-7-3-projective-line.tex`) proves it on `ℙ¹` at the points `s·ord_{x₀}`, `s > 0`. It refutes the monotonicity
  step of the published proof, not the statement of BJ22 Thm 6.21. FHX′ Remark 7.3 (l. 1006–1008) is unchanged except
  for notation.

**EP-4.2. Wu26 Lemma 5.11: incorrect ideal-theoretic claim** ☐
- FHX gives a direct proof of Wu26 Prop 5.10 (`lem:principal-hull`).

**EP-4.3. Wu26 minor corrections recorded in FHX's footnotes** ☐ (in Wu26; recorded by the authors)

| Wu26 location | Correction (FHX footnote) | FHX `BJ_envelope_fixed.tex` |
|---|---|---|
| Def 3.1(3) | the supporting affine function must touch the graph: `u(x) = l(x)` and `u ≥ l` near `x` | l. 498 |
| Def 3.15(2) | growth condition should read `u ≤ g + O(1)` with `g ∈ FS(Y)` | l. 582 |
| Lemma 3.16, proof | use `log\|f\| ≤ max_α log\|a_α z^α\|`; monic-root bound `log\|f\| ≤ max_{i<m} (m−i)^{−1} log\|b_i\|` | l. 592 |
| Prop 3.17(2), proof | displayed sections are a generating family, not necessarily a basis | l. 602 |
| Cor 3.18 / Prop 3.17(1) | the limit is `g + φ`; replace the constant 0 in the maximum by `−C_j`; add dominated generator terms | l. 616 |
| Lemma 3.25(1) | continuity of the limit (Dini) is unnecessary; compactness of the collar suffices | l. 618 |
| Prop 3.30, proof | read `u_ε` as `g_ε = max{g, −ε log\|f\|}`, `ε = c/3`; keep the constant in `u_j ≤ 2g_ε + C_j` (approximation-index-dependent) | l. 645 |
| §5 (Prop 5.4 ff.) | use strict polynomial inequalities; `int{g ≤ t} ≠ {g < t}` in general | l. 677 |
| Prop 5.7 / Lemma 5.8 | fibre-radius formula `−log d_{W_j} = max{−j, M_j}` | l. 713 |
| Lemma 6.8 / Cor 6.9 | assume `u\|_{U_α} ∈ 𝓡(U_α)` (local hypothesis); regularizability of `u + cρ` alone does not justify the auxiliary function `u + cρ′ + εv`; barrier convention `v = max_i log\|f_i\|` for generators of the ideal of `Z`, `ε` rational | l. 775 |
| Lemma 6.16, proof | take `U = r^{−1}(S)` rather than `r^{−1}(W)` (inverse-image typo); local projection; generic étaleness in char p | l. 849 |

The footnotes are unchanged in FHX′ (`main.tex` l. 541, 625, 635, 645, 659, 661, 688, 720, 756, 818, 892, i.e. the old
line numbers shifted by 43); Wu26 itself is unchanged (☐).

**EP-4.4. Corrections in FHX's own revisions (author's revisions of 2026-10-13 and 2026-10-28)** ☑ (fixed in 832e086,
resp. FHX′)
- Recorded in `CHANGELOG.md` (base `8c0445d`, revision `d64981e`, then
  follow-up) and `REVIEW.md`; a proofreading of the earlier manuscript, not found by the formalization. §2.1 trivial
  valuation defined as the zero additive valuation (was "trivial absolute value"); §2.2 the blanket promise to record the
  value at every use of PSH2 did not match the proofs; §2.3 normality of `X` made explicit for normal test configurations
  (a normal total space cannot be `X × G_m` off the central fibre if `X` is non-normal); Lemma 3.2 (3.7) parenthesization
  of the Frobenius pushforward; Prop 4.1 independence of the FS presentation proved; §5 conventions / Thm 5.25 reduced
  structure needed for generic smoothness; Lemma 5.5 undefined `K_{i₀}` replaced by `Q_{i₀}`, one common rational weight;
  Lemma 5.10(2) Dini's theorem replaced by a compactness argument (the decreasing limit need not be continuous); Lemma
  5.11(3) sign ambiguity in real translations; Lemma 5.18 binomial identity applied to the real `|f|` (avoids `0·(−∞)`);
  Thm 6.1 cites de Jong Thm 4.1 directly; Lemma 7.1 the case `E = 0`; Thm 8.3 the step needs the kernel statement, not
  surjectivity of global sections.
- *Revision of 2026-10-28 (FHX′, supplied by the author; no changelog file).* `cgeometry.sty` is identical, the `.bib`
  differs only cosmetically (Fornæss accent, de Jong shorthand DJ96, LiChi21 published). The 43 hunks of `main.tex`
  (lane FX): 22 notation only (macros `\Hgf`, `\Hhom`, `\Rcal` expanded; labels
  `positive_intersection_formula_na_functionals` → `prop:positive-intersection-na-functionals`, `appendix_preliminaries`
  → `subsec:appendix-preliminaries`; label `rem:big-model-stability` on the unchanged Remark A.3; misprint `𝐇_v` →
  `𝐇^NA_v` in the proof of `prop:entropy_approximation`, l. 1297); 8 corrections adopting entries of this file (EP-1.1,
  EP-2.1, EP-2.3, EP-2.8, the §1.5 observation on `lem:finite-class-promotion`, definitional uses of PSH2); 6 changing
  statements (§4 and Thm 4.2, Lemmas 5.15, 5.17, Cor 5.26, Lemma 8.2 with the new definition of subintegral, EP-2.5: all
  adopt §1.3 rows and make the statements stronger); 7 of new mathematics (real weights, Prop 2.1 restated and reproved,
  Remark 2.2, Lemma 2.3, Prop 2.4 via BJ22 Thm 5.6, Lemma 7.4, new routes in Thms 7.2 and 8.3, Cor 8.4). Theorem A and
  Corollary 1.1 (workspace: Theorem 1.1 and Corollary 1.2) are verbatim unchanged (FHX′ l. 69–90); only "unibranch" is
  now defined stalk-wise (l. 65). Numbering: §2 gains Remark 2.2 and Lemma 2.3, so `prop:EP-criterion` = 2.4,
  `prop:ample-envelopes` = 2.5, `lem:finite-class-promotion` = 2.6; §7 gains Lemma 7.4, so `prop:homogeneous-slices` =
  7.5, `cor:normal-EP` = 7.6; §8 gains Cor 8.4. Every new argument was checked (lane FX): correct; minor imprecisions
  EP-2.9, EP-2.10; a shorter proof of Cor 8.4 in §1.5. Formalization impact: no required change.

### 1.5 Route simplifications (not errors; may simplify the paper)

Found by planning lanes P31G and P68 (2026-10-14/15); "to be confirmed when formalized" unless a Lean name is given.
- FHX Cor 5.26 (`cor:normal-weak-global`), proof: Lemma 5.10(1) on `X′` (hence BJ22 Cor 12.18(iii), fixed-class regularization on `X′`)
  is not needed; regularizability of `u_i` on `(Y_i)_g` follows from the Lemma 5.4(2)-type argument in the blowup chart
  `A_i[𝔞_i/g] ⊆ (A_i)_g` with Lemma 5.11(4); only the dyadic regularization on `X′` is used. Formalized (lane PG8,
  `ProjSubvariety.BlowupCenter.isRegularizable_descentChartFun_awayComap`). (our development notes add: Cor 5.26
  needs no positivity input beyond 5.11; for countable `k` a decreasing sequence in the fixed class follows from Def 4.1,
  Lindelöf and class monotonicity, without energy theory.)
- FHX Lemma 3.2 (`lem:smooth-uniform-twist`): its cohomological inputs can be replaced by an elementary degree count on
  the punctured cone with a non-canonical twist; §3 needs only some twist independent of `m`. Lemma 3.3 is used only
  through the existence of a constant independent of `m`, `q`, `J_•`.
- FHX Prop 2.2, (i)⇒(iii) (rests on BJ22 Thm 5.6, Cor 4.17, Prop 1.28) is never needed: its uses in FHX Thm 4.2, Thm 6.1
  Step 1, Thm 7.2, Prop 7.4, Cor 7.5 and BJ22 Thm 5.12 go through with usc regularizations and the comparison theorem;
  BJ22 Cor 12.18 is not needed outside §5; FHX Thm 6.1 Step 2 needs neither test configurations nor flat base change of
  base ideals (formalized, lane G6, `ProjSubvariety.hasEnvelopeProperty_one_of_countable`: the obstacle descends as a
  continuous function, so neither PL-ness nor base point freeness needs to descend); BJ22 Thm 5.12 ((3)⇒(1) of
  FHX Cor 1.2) has a short proof by conductor descent; the fibre-constancy claim in FHX Thm 6.1 Step 1 holds for every
  proper birational map onto a normal variety.
  FHX′ (Prop 2.4, was 2.2, l. 229) reproves (i)⇒(iii) directly from BJ22 Thm 5.6 and uses it also at arbitrary classes
  (Thm 8.3, Cor 8.4); the observation that our route does not need it stands (lane FX).
- Roberts–Singh (4.2)–(4.5), (4.13) as used for FHX Lemma 8.2 (first assertion) need neither Roberts–Singh Thm 3.8 nor
  Lemma 2.8: multiply the `m`-th relation by `π(m)`, `π(X) = ∏_{j<R}(1 − X/j)`; sums, products and the square-and-cube
  step follow by exponential generating functions and Lagrange interpolation. Formalized (lane G13a,
  `Algebra/AdditivePowersBasic.lean`, about 900 lines).
- FHX′ Cor 8.4 (`cor:unibranch-decreasing-stability`, l. 1167–1182; lane FX): after the pointwise identity
  `u = sup_{λ<0}(q_λ + λ)` with `q_λ ∈ PSH_hom(X, θ)`, Theorem A applied to the family `{q_λ + λ}` (bounded above by `0`)
  gives `u^* ∈ PSH(X, θ)`, and `u^* = u` since `u` is a decreasing limit of usc functions; the envelope `Ψ`, the dyadic
  `U_n` and Lemma 7.4 in the last paragraph are not needed. Formalized on models: `thm:nn-psh2-of-ep`,
  `MultiModel.isPSH_of_antitone_of_hasEnvelopeProperty` (`Global/EPDecreasingLimits.lean`). (In Thm 8.3 the same
  shortcut is not available, `EP_X` being what is proved there.)
- FHX Lemma 5.5 (`lem:local-PL-positivity`; lane ER2's suggestion, checked briefly by lane FX from the docstrings and
  the blueprint, dependency cone not traced): FHX prove the nonnegativity of `𝓛` on the curves of the central fibre with
  the Chambert-Loir–Ducros criterion (CLD12 Cor 18.8.9, after base change to `k((ϖ))` and a formal model; FHX′
  l. 596–598). Our instance `LocalPositivity.instOfIsAlgClosed` (`Local/LocalPositivityInstance.lean`) uses no CLD12:
  central nefness of the PL model is proved algebraically (`thm:central-nef-tc-given-model`,
  `blueprint/src/intrinsic-psh-resume-numerical-original-central-nef-tc.tex`: canonical gauges of generic sections, nonnegative
  degree on normal SNC central curves, then on all central curves via a regular paired surface and de Jong
  alterations, and the nef-cone criterion), followed by an auxiliary polarization and an approximation argument
  (`ProjSubvariety.isPSH_of_potential_family`; these two steps are ours, not FHX's, see EP-O11†). An alternative route
  avoiding non-Archimedean analytic geometry over `k((ϖ))`, at the price of de Jong alterations (which FHX use in
  Thm 6.1 anyway) and a much longer argument; not a shortening.

Other observations in the plans, explicitly "not errors": BJ22's char-0 proof of Thm 5.20 uses relative uniform global
generation of multiplier ideals on the non-proper total space without a reference; "can rely on resolution of singularities" also needs Kawamata–Viehweg-type vanishing; FHX states only that its line weights do not depend on `u` (independence of the line follows
from `lem:nf-line-weights`) and states Prop 5.22 for all weakly psh functions while its only consumer supplies
chart-regularizable ones; FHX's "closed by usc and open by the local maximum principle" needs the
fibre connected as an analytic space, which FHX also cites. Lane FA (PR227 report): FHX
`lem:finite-class-promotion` (l. 216–237) uses a norm on `N¹(T)_ℝ` ("`c₁(M_i) − h^*θ = o(ε_i)`") and "openness of the
ample cone" for `h^*L_i − M_i`, i.e. finite-dimensionality of `N¹` (Néron–Severi) and Kleiman's criterion, without
saying so — standard for projective varieties; the formalization needs neither finite-dimensionality (order convergence
in the ample cone, `Variety.AmpleTendsto`, `def:var-ample-convergence`) nor Kleiman as an input (it is derived from
nef + ample ⇒ ample, `NativeNumericalFubiniStudy.numericalAmplenessCriterion`), and the displayed normalization
`(rm)⁻¹ max{log|s_j^{⊗r} ⊗ t_a^{⊗m}| + rλ_j}` is correct (`FSData.exists_promotion`, `lem:var-class-promotion`). FHX′
(Lemma 2.6, l. 269) now states both inputs: "The space `N¹(T)_ℝ` is finite dimensional, and the ample cone is open by
Kleiman's criterion", with `ε_i⁻¹c₁(P_i) → h^*c₁(A)`.

---

## 2. DeJongAlterations: Temkin 2010 and de Jong 1996

Sources: Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3 (TeX line numbers `T:<line>`); de Jong, *Smoothness, semi-stability and alterations*, IHÉS 83 (1996)
(pages `page-NNNN`, printed page = PDF page + 49). None of these invalidates a main theorem. Unverified plan-stage findings are marked (plan). All
source entries are ☐ (published sources; not reported).

### 2.1 Temkin 2010 (Claude)

| # | Location | Issue | Fix used | Found by |
|---|---|---|---|---|
| T1 | Prop 3.2.1 (`quacomprop`), converse, T:2330–2334 | "by the same argument" needs the open `U` qcqs, i.e. quasi-separatedness of `S`, which is what is being proved | apply the argument to a finite affine cover of `U` | RZ0 |
| T2 | Lemma 3.2.9 (end of §3.2) | stated without proof | continuity of the center map for separated quasi-compact `S` by a patch-compactness argument (`prop:sm-rz-affine-open`) | RZ0 |
| T3 | Lemma 2.1.2 (`Abhlem`), T:1936 | `B_E ⊂ \|l^×\|` should be lifts `b ∈ l^×` of a ℚ-basis | choose lifts | VAL0 |
| T4 | Lemma 2.1.2, T:1938 | orthogonality of monomials "easy to see", not proved | residue part (max-coefficient formula) + value part (distinct values) | VAL0 |
| T5 | Cor 2.1.3(i), T:1949–1951 | omits height ≤ rational rank and rat. rank of `v(F^×)` ≤ 1 for the prime field | `lem:sm-height-le-ratrank`, `lem:sm-prime-field-value-group` | VAL0 |
| T6 | T:2210–2212 | silently assumes `k₁K₁^p ≠ K₁` and the valuation nontrivial on `k₁` (both true in his setting) | explicit hypotheses | VB |
| T7 | T:2797–2799 | "by decompletion and induction on height": finite height is superfluous for divisibility, separably/algebraically closed residue fields | direct proofs for any separably closed valued field | VB |
| T8 | Lemma 6.1.2, T:3449–3451 | "valuation not discrete" is superfluous for part (i) in characteristic `p` | `isCriticalCoset_iff_isGLB` without it | T34 |
| T9 | Lemma 6.2.9(ii), proof T:3913–3919 | reducing the `w^{pi}` terms cannot remove the constant term (the step `c = b̄₀^{1/p}` does not lower index `i = 0`), yet `B` is written without constant term | the constant lies in `℘₁(l)` since `l` is algebraically closed; the formal proof avoids `B` (Hasse–Cauchy route) | T34 |
| T10 | Prop 4.4.6, T:3212–3214 | `H¹(Z,O_Z)=0 ⇒ H¹(O_Y(mΣpᵢ))=0` fails as stated when `\|∂Z\| = 2` (`H¹(P¹,O(−2)) ≠ 0`); needs surjectivity `H⁰(Y′,O(mΣpᵢ)) → k^{∂Z}/k` for `m ≫ 0` | use the sequence `0 → O_Z(−∂Z) → O_Y(mΣpᵢ) → O_{Y′}(mΣpᵢ) → 0` with a section separating the two points of `∂Z`; confirmed in Lean (`h¹(ℙ¹, O(−2)) = 1`, `CurvesField.finrank_cohomology_one_twist_projectiveLine`) and the fixed step formalized (`CurvesField.isZero_cohomology_one_temkin`‡) | PA (plan); COH4. **Withdrawn 2026-10-21 (lane T44F): not a source error.** Temkin's "using `h¹(Z, O_Z) = 0` it follows easily" is correct for every `\|∂Z\| ≤ 2` via `0 → I_Z → O_{Y∖D} → O_Z → 0` (`I_Z` supported on the affine `Y′∖D`, so `H¹(Y∖D, O) = 0`, then Serre vanishing; `BlowDown.VanishingCore.exists_sub_eq_res`, `BlowDown/VanishingTwist.lean`); the counterexample applies only to our blueprint's reconstruction through `O_Z(−∂Z)` (DJA-O34†) |
| T11 | Lemma 4.4.2, T:3115–3118 (also 4.4.6, T:3198–3201) | "since V is closed in C̄" needs `R` strictly henselian (closures of non-closed points finite over `R/𝔭`, hence local); some henselianity is necessary: over `ℤ₍₅₎` the closure of `(x² + 1)` in `ℙ¹` meets the closed fibre at `x = ±2` | proved when every `Frac(V/𝔭)` is separably closed (`BlowDown.isClosed_of_forall_specializes`, `specializes_of_specializes_of_isAlgebraicAt`) | PA (plan); T44A |
| T12 | Prop 4.3.3, T:3065 | "by flattening theorem" over non-Noetherian `Spec Ā` needs Raynaud–Gruson 5.2.2 | route S7 (descent of étale algebras) | PA (plan) |
| T13 | Lemma 4.4.4 / Prop 4.4.6, T:3162, T:3196 | "replace C with its normalization" silently needs the reduced fibre theorem (Grauert–Remmert) | smooth-generic-fibre case: Stein finiteness suffices (S8); "not an error" (PLAN-SM-GEOM L4) | PA (plan) |
| T14 | Prop 4.3.1 stage 2, T:3000 | `f(T) ∈ L∖R` should range over `K(T)^×` (typo) | — | PA (plan) |
| T15 | Lemma 3.5.1 cites Raynaud–Gruson I 3.4.7 | correct; replaced by a self-contained proof (homogenization + graded Nakayama) | `thm:sm-nagata-fp` | NAG |
| T16 | T:1920–1923 | valuation rings over `k°` = localizations of the integral closure at maximal ideals, stated without proof | proved (`isLocalization_integralClosure`, `exists_valuationSubring_of_isMaximal`) | UR |
| T17 | T:2178–2186 | the reduction to absolutely finitely generated fields loses the separably closed hypothesis | equal-characteristic route keeps `K = k₀(S)^s` (PLAN-SM-VAL LI-1 fix: reduce to `(L·lˢ)/lˢ`) | PB (plan) |
| T18 | Lemma 6.2.6 proof, T:3775–3778 | filtration of `F/F^p` written as balls of radius `< n`, but `U_n` has elements of norm `n`; must be `≤ n` | `{ν ≤ n}` | FF |
| T19 | Lemma 6.2.6 proof, T:3782–3783 | the element lying in `F^{p^i}` and constant is the remainder `f − f₀ − … − f_{i−1}`, not `f_i` (slip) | step (d) of the blueprint | FF |
| T20 | Thm 6.3.1 proof, T:4080–4083 | appeal to Lemma 6.2.6 for `c̃` with `c̃^p − c̃ + z̃ ∉ L̃^p` superfluous: `c̃ = 0` or any `c̃ ∉ L̃^p` | — | FF |
| T21 | Prop 3.2.6 proof, T:2400–2402 | reduction to affine pieces omits that the morphisms from the opens glue to a proper morphism | same centre argument as the covering statement | RZ1 |
| T22 | T:2308–2310 | `K^s`-modifications are generically étale alterations needs generic freeness (EGA IV 6.9.2) for non-Noetherian `S` | assume `S` locally Noetherian (our case) | RZ1 |
| T23 | Lemma B.3 proof, T:4476–4478 | **false step**: "if neither of two meeting exceptional trees contains the other, some double point joins `Y₁∖Y₂` to `Y₂∖Y₁`"; counterexample: components `a,b,c` with double points `a∩b`, `a∩c`, `Y₁ = a∪b`, `Y₂ = a∪c`. The derived bound `\|∂(Y₁∪Y₂)\| ≤ \|∂Y₁\|+\|∂Y₂\|−2` still holds | identity `\|∂(A∪B)\|+\|∂(A∩B)\|+2·#cross = \|∂A\|+\|∂B\|` and `\|∂(A∩B)\| ≥ 2(\|A∩B\| − #inner(A∩B))` | CRV1 |
| T24 | Lemma B.3 | the union of meeting exceptional trees is a tree only if `C′` is connected and `f` maps onto a curve (counterexample otherwise: two exceptional paths covering a contracted 4-cycle); covered by Temkin's standing assumptions | explicit `IsAnchored` hypothesis | CRV1 |
| T25 | T:4482–4484 | "hence the stable blow down factors through `C̄′`" needs that a maximal exceptional tree is contracted by any blow-down without exceptional components | counting lemma `sum_star_le` (handshake identity) | CRV1 |
| T26 | Prop 6.2.4, types 2/3 (statement T:3724–3726, proof T:3956–3958) | stated for any critical coset, but the reduction subtracts `a_{ij}u^{p^i} − a·a_{ij}^{1/p}u^{p^{i−1}}`, which stays in `Span(B)` only for `a ∈ k`; for `a ∈ L∖k` the induction does not close. Only special cosets (`a ∈ {0,1}`) are used later (Thm 6.3.1, T:4062–4070) | state and prove it for special cosets | TYPE2 (also T34 for type 3) |
| T27 | Prop 2.2.1 proof, T:2128–2129 | "`f_i` has a root in `m F̂°_i = F̂°°_i`": `m` undefined; if `K°°` the equality fails for ramified `F̂_i/K̂`; "all roots small" silently uses equal absolute values of conjugates over `K̂` | no decomposition: roots of `f/g` in `K̂^a` are small (`isometric-root`, `small-roots`) | DEC |
| T28 | Prop 2.2.1 proof, T:2121–2123 | choosing `z ∈ K°°` with `x = x₀+zy` primitive and `zy ∈ m₁⋯mₙ` needs `y` integral over `K°`, but `y` is any primitive element | use `c·y`, `0 ≠ c ∈ K°` | DEC |
| T29 | T:2115–2119 | semi-local `F°` and `K̂ ⊗_K F ≅ ∏ F̂_i` used without proof (standard) | avoided: only valuation rings induced by embeddings into `K̂^a` | DEC |
| T30 | T:2204–2206 | "`{x}` is a separable transcendence basis iff `x ∉ kK^p`" stated as well known | proved both directions; the converse needed `isSeparable_of_adjoin_pow_eq_top` (a Mathlib TODO) | DEC |
| T31 | T:4091–4093 | "admits only immediate algebraic extensions; in particular any finite extension splits into a tower of p-extensions" asserted without argument | `e = f = 1 ⇒ G = T = V`, a p-group by the trace lemma; then p-group and purely inseparable tower lemmas | RAMIF |
| T32 | T:4057–4061; Prop 6.1.4 (T:3589) | cites Gabber–Ramero (`Gal(K^s/K^mr)` pro-p) and Ostrowski via `K^mr` (not errors) | finite-level lemmas on `T`, `V`; explicit coset construction | RAMIF |
| T33 | Prop 4.3.1, T:2972–2975 | "we will build these blow ups so that `x` is the only closed point of the modification locus; this allows to work locally at `x` since each such blow up extends trivially": extending a blow-up of a neighbourhood `U` by the identity needs its locus closed in `C`, which does not follow. Counterexample (reading "closed" as closed in `C`): `R` with primes `0 ⊊ 𝔭 ⊊ 𝔪`, `0 ≠ c ∈ 𝔭`, `π ∈ 𝔪∖𝔭`, `C = 𝔸¹_R`, `y` = point `T=0` of the closed fibre, `U = C∖{y}`; the blow-up of `U` along `(T,c)(T−1,π)` has locus `{z, x}` (`z`: `T=0` over `𝔭`; `x`: `T=1` over `𝔪`), closed in `U`, `x` its only point closed in `C`, but `y ∈ cl{z}`, so it does not extend by the identity. Related to T11. Also T:2988 "semi-stable": the charts give strictly semi-stable | `R` strictly henselian: the étale-pulled-back locus splits as `Z₀ ⊔ Z₁` with `Z₀ ≅ Spec R/(π)`; shrink `U` to `U∖Z₁`; `Z₀` is closed in `C` (proper over `R`, `C` separated; `Blowups.isClosed_range_of_isProper_comp`); blueprint `rem:sm-blowup-use` | BL1 |
| T34 | Prop 4.2.3 (`schmodprop`) proof, T:2935 | "Lemma 4.2.2 implies `Γ(C′) ⊆ Γ(C″)`" needs `Γ(C′) = gen(Γ₀(C′)) ∪ Γ(C)` for `C′`, but Lemma 4.2.2 (T:2909–2912) assumes `C′` normal (its bijection `Γ(C′) ≅ (C′/S)⁰` uses normality) and Prop 4.2.3 does not | `ValCurves.gammaSet_eq_union` holds for every modification (composite valuation, Lemma 2.1.4, and a contraction lemma); blueprint `rem:sm-vm-literature` | T42 |
| T35 | Lemma 4.2.2 proof, T:2915 | "obviously the sets `Γ(C′)` and `Γ₀(C′)` are finite" needs the strict inequality of fibre transcendence degrees under proper specialization within a fibre (Abhyankar), besides the standing finite-height assumption (T:2796) | `ValCurves.one_add_fiberTrdeg_le_of_specializes`, `finite_gammaSet` | T42 |
| T36 | Thm 2.1.10(iii) (`fieldunif1`), T:2084 | the hypothesis `K̃ ≠ k̃` is superfluous: transcendence of `x̃` over `k̃` implies it (not an error) | dropped; `Analytic.isUnramified_closureAdjoin_of_transcendental` | ONEDIM |
| T37 | Lemma 6.3.3 (`fin`), T:4015–4017 | the hypothesis `\|α(x) − β(x)\| < ε\|x\|` for any `x ∈ K` fails at `x = 0`; completeness of the images is used implicitly | `≤` (or `x ≠ 0`) with complete `K`, `E`: `Analytic.finrank_le_of_forall_exists_norm_sub_le` | ONEDIM |
| T38 | Lemma 6.3.2, T:4001–4011 | the proofs at T:4103–4109 and T:4150 use that the image of the embedding is `cl k(z′)`, which the lemma does not state and which needs `L` complete | stated and proved under `CompleteSpace L` (`Analytic.exists_algHom_closureAdjoin`) | ONEDIM |
| T39 | Cor 6.3.4, T:4033–4039 | finiteness of `l` over `cl k(x′)` is used without justification | transcendence exchange (`Analytic.isAlgebraic_adjoin_of_isAlgebraic_adjoin`, `finiteDimensional_closureAdjoin`) | ONEDIM |
| T40 | Thm 6.3.1 proof, T:4065–4067 | "no immediate extensions of degree `p`, hence stable" silently uses that a non-immediate degree-`p` step is Cartesian (defect theory) | `e, f ∈ {1, p}` for the steps that occur and non-immediate steps are Cartesian (blueprint `lem:sm-an-step-degrees`) | ONEDIM |
| T41 | Prop 4.3.1 (`cofinprop`) proof, T:2961–2966 | the reduction applies the claim to the finite set `Γ₀(C′)` and then Prop 4.2.3, but `Γ₀(C′)` is known finite only for normal `C′` (Lemma 4.2.2); Lemma 4.3.2 (T:3030) applies `cofinprop` to a possibly non-normal blow-up | cofinality stated for modifications with finite `Γ₀` (in particular normal ones): `LocalUniformization.exists_dominates_of_isNormalScheme`; blueprint `rem:sm-lu-literature` | T43M |
| T42 | Prop 4.3.1 stage 2, T:3005–3011 | "we can find `a ∈ K` and `π_a ∈ R`" with transcendental residue of `(T − a)/π_a`: `a ∈ R` is derived only afterwards and the case `\|a\| > 1` is not excluded explicitly (minor) | for `\|a\| > 1` the residue is that of `−a/π_a ∈ K`, algebraic (`LocalUniformization.exists_transcendental_residue_sub`) | T43M |
| T43 | Prop 4.3.1 stage 2, T:3001–3004 | the perturbation `f + ωT` needs `\|T\| ≤ 1` and some `0 ≠ ω` with `\|ω\| < \|π\|` (nontrivial `v_K`); `f + ωT` is separable but may be reducible and must be factored again (imprecise wording, no counterexample) | `LocalUniformization.residue_mem_linearResidueField` (induction on degree) | T43M |
| T44 | Prop 4.3.1, T:2972–2975, with T:1674 ("`C` is not assumed `S`-proper or even `S`-separated") | extends T33: even with the strict-henselian shrinking, a local blow-up need not extend when `C` is not separated. Counterexample: `A` with primes `0 ⊊ 𝔭 ⊊ 𝔪`, `0 ≠ π ∈ 𝔭`; `C` = two copies of `𝔸¹_A` glued off the closed origin, `x` = origin of copy 1, `Bl_{(π,T)}`: the locus `{z, x}` with `z = (T, 𝔭)` has `cl{z}` containing the origin of copy 2, and every neighbourhood of `x` contains `z` | assume `C` separated (true for all curves of the de Jong route): `Blowups.exists_transport`, blueprint `rem:sm-transport-separated` | BND |
| T45 | Lemma 5.1(i) (`openloclem`) proof, T:3290–3291 | "the semi-stable locus of `C′ → S` is open (e.g. use the local description from [dJ, 2.23])": de Jong 2.23 (`page-0012`) describes only completed local rings `Ô_{X,x} ≅ A′[[u,v]]/(Q − h)`, which gives no Zariski neighbourhood with nodal fibres (gap in the justification, not a false claim) | present the curve near a node as a quotient of a standard étale `R[X₀,X₁]`-algebra, show the kernel is principal `(g)` with invertible Hessian, classify nearby geometric points by Taylor expansion (`Curves.SemistableOpen.exists_isNodalCurve_nbhd`, `nodalLocus`); blueprint `rem:sm-semistable-open-sources` | SS2 |
| T46 | Thm 2.1.8 proof, T:2205–2208 ("`k₁` and `K₁` … the induced valuations of height one"), and Prop 4.3.3, T:3061 (Lemma 2.1.1 needs `O ∩ K(T)` of finite height) | finiteness of the height of the valuation of `L` (resp. `K(T)`) is used but not justified when only `O ∩ K` has finite height (in Temkin it would come from the flawed reduction T17). The height of `O` can exceed that of `O ∩ K`: `v(K^×) = ℤ × {0}`, `L = K(t)`, `v(t) = (0,1)` in lexicographic `ℤ²` gives `ht O = 2`, `ht(O ∩ K) = 1` | for `trdeg ≤ 1` no three overrings have the same trace on `K` (Abhyankar on residue fields), so `ht V ≤ 2·ht(V ∩ K) + 1` (`Valuation.MainUniformization.finite_primeSpectrum_of_trdeg_le_one`); induct on the height of the base | MAIN-VAL |
| T47 | Prop 4.4.6 proof, T:3215–3219 | imprecision, not an error: the Noetherian approximation is unnecessary (valuation rings are coherent), and Grauert's theorem (Hartshorne III.12.9) needs `h⁰` constant on an integral neighbourhood of the closed point, which holds (`h¹ = 0` nearby by semicontinuity, then `h⁰ = χ`) but is not what is stated (only `h⁰(L_η) = h⁰(L_s)`) | surjectivity of `H⁰(L) → H⁰(L_s)` needs only `h¹(L_s) = 0`, by top-degree base change for the two-term complex (`Cohomology.ProjectiveCoordinates.epi_cechPullbackMap_of_residue_valuation`); blueprint `rem:sm-val-temkin-onto` | COH3A |
| T48 | Prop 4.3.1, T:2972–2975 ("we can replace `R` with its localization beneath `x`" and "extends trivially") | extends T33 to a global base: a closed point of `C` can lie over a non-closed prime `𝔭` (e.g. `(πT − 1)` in `𝔸¹` over a DVR, residue field `Frac R`), so the blow-up lives over `R_𝔭` and its locus, closed in `C_𝔭`, need not be closed in `C`; counterexample for a point not closed in `C`: `R` with primes `0 ⊊ 𝔭 ⊊ 𝔪`, `z = 𝔭R[T] + (T)`: `{z}` is closed in `𝔸¹_{R_𝔭}` but its closure in `𝔸¹_R` contains `𝔪R[T] + (T)` | closedness from `x` closed in `C`, finiteness of the locus and a coarsening of the valuation at `O ∖ 𝔭` (`LocalUniformization.isClosed_of_finite_of_unique`, blueprint `lem:sm-cofinal-closed`, `rem:sm-cofinal-literature`) | T43A |
| T49 | Prop 4.3.1 stage 2, T:2997–3000 ("we can actually assume that `C = Spec(A)`") | the reduction replaces `L` by `K(T)`; keeping a residue transcendental over `K̃` needs `L/K(T)` algebraic and Abhyankar for `L/K(T)`, and "centred at the generic point of `Z`" must be checked on `C` through the étale map (imprecision); also the smooth-generic-fibre hypothesis of 4.3.1 is not needed for the cofinality, and normality of strictly semistable curves (used at T:2966 via Prop 3.5.2) is elementary over any normal base | `LocalUniformization.exists_transcendental_residue_comap`, `exists_smoothStep` step (f), `isNormalScheme_of_isStrictlySemistable` | T43A |
| T50 | App. B, T:4375–4377 | "`g(x)` is the geometric genus `h¹(𝒪)` of its irreducible component": it is `h¹` of the structure sheaf of the normalization of the component, not of the component (wording); Lemma B.1's `p_a = h¹` (T:4411) uses `h⁰(𝒪_C) = 1`, covered by the standing hypotheses | `p_a := 1 − χ`; `CurvesField.Genus.arithmeticGenus_eq_normalization`; blueprint `rem:sm-genus-literature` | CRV2 |
| T51 | Prop 4.3.1 proof, T:2966–2967 (also Prop 3.5.2) | "normality of semi-stable `S`-curves with smooth generic fiber" is used without proof or reference here (gap; the claim is true). Smooth generic fibre is necessary: `R[u,v]/(uv)` over a DVR is nodal with non-domain local ring at the origin | étale-local form `uv − c` of a node (Stacks 0CBY with a Morse lemma in families, no Artin approximation) plus normality of `O[u,v]/(uv − c)` for `c ≠ 0` and faithfully flat descent, over any integral normal base (no Noetherian hypothesis): `Curves.SemistableNormal.isNormalScheme_of_isNodalCurve`, blueprint `thm:sm-nodal-normal` | SS3 |
| T52 | Thm 2.1.8 proof, T:2190–2192 | "for any uniformizer `x` at `z`, … `x` induces an étale morphism from a neighborhood of `z` to `𝔸¹_k`" is false at smooth closed points with inseparable residue field (possible when `k` is separably closed but imperfect). Counterexample: `𝔸¹_k` at the point `T^p − c`, `c ∉ k^p`: smooth, residue field `k(c^{1/p}) ≠ k`, uniformizer `x = T^p − c` with `dx = 0`. An étale coordinate (`T`) exists but is not a uniformizer | with an étale coordinate the argument goes through; our interface (`UniformizationHypotheses`) asks for residue field `K`, and T43B adds `AllPlacesRational K L` (automatic for `K` algebraically closed) | T43B |
| T53 | Prop 4.3.3 proof, T:3062 | "`Ā = k[T]`": the base ring is meant (`R′[T]`), not the field `k` (typo) | — | T43B |
| T54 | Lemma 4.4.2 proof, T:3125–3129 | Zariski connectedness over a non-Noetherian `S` justified by "`C′` comes from a curve defined over a noetherian base": the hypothesis of EGA III 4.3.2 (`π_*O = O`, or geometric connectedness of the generic fibre) must hold on the Noetherian model, and normality does not descend (gap; the statement is true) | direct proof over a finite-height valuation ring by induction along the chain of primes, bounded torsion of `Ȟ¹` and lifting of idempotents from thickenings (`Cohomology.Connected.isConnected_fiber_of_isProjectiveOver`, blueprint `thm:sm-zariski-connected`); the birational form (T:3133) is proved directly over `V` for height one (`Cohomology.ConnectedBirational.isConnected_preimage_singleton_of_heightOne`) and for finite height when no generization of `x` lies in the modification locus (`isConnected_preimage_singleton_of_generizations`); height ≥ 2 with such generizations is proved when `B` is projective over `V`, every `Frac(V/𝔭)` is separably closed and the residue field of `V` is infinite (`Cohomology.ConnectedBirationalHeight.isConnected_preimage_singleton_of_isProjectiveOver`, induction along specialization in the modification locus); the case of `Y` only separated of finite type in height ≥ 2 is still open | COH3C, COH3D, COH3E |
| T55 | Cor B.2 proof, T:4442–4444 | uses without saying so that the normalization of `C` is the normalization of `C′` with the components of `Z` removed | replace `C̃` by `N`, the normalization of `C′` in its generic points outside `Z`, finite over `C` by Zariski's main theorem (`CurvesField.Genus.isFinite_outerNormalization`); `N ≅ C̃` still open | CRV3 |
| T56 | Lemma B.1 / Cor B.2, App. B | the argument needs `x` not a generic point of `C` (if `Z` is a whole connected component of `C′`, `x` is isolated in `C`); implicit, `C` being pure one-dimensional at `x` (minor). Same for CRV2's sketch of `lem:sm-stabdown-count` (`|C′⁰| = |C⁰| + |Y|`) | explicit hypothesis `x ∉ genericPoints C` (`CurvesField.Genus.deltaInvariant_contraction`) | CRV3 |
| T57 | Lemma 4.4.4 (`emptylem`) proof, T:3164–3166 | **false step**: "if `t` is a specialization of `s` then any irreducible component `Z′ ⊂ C′_t` lying in the Zariski closure of `Z` is exceptional". Counterexample: `V` of height 2, `0 ⊊ 𝔭 ⊊ 𝔪`, `s = 𝔭`, `t = 𝔪`, `C = C_k ×_k V`, `a ∈ 𝔭 ∖ 0`, `b ∈ 𝔪 ∖ 𝔭`; blow up `(u, a)` at a `k`-point (rational tails `E_s`, `E_t`, `E_t` in the closure of `E_s`), then `(v − c_j, b)` at three points of `E_t`: `C′` is semistable, `E_s` is exceptional, but `E_t ≅ ℙ¹` in its closure is contracted with 4 double points, not exceptional. The lemma itself is not refuted | the closure meets `C′_t` in an exceptional tree, which contains an exceptional component (CRV1 `IsExceptionalTree.exists_isExceptional`); blueprint `lem:sm-bd-exc-specialize`, `rem:sm-bd-literature` | T44A |
| T58 | §1, property (b) of `ω_{C/S}`, T:1704–1706 | Rosenlicht's condition is written `Res_{x_i}(ν) = Res_{y_i}(ν)`; it should be `Res_{x_i}(ν) + Res_{y_i}(ν) = 0` (at `uv = 0` the generator `du/u = −dv/v` has residues `1` and `−1`). Sign error; the degree computation is unaffected | blueprint `rem:sm-omega-degree-literature`; confirmed in Lean by `Omega.Rosenlicht.rosenlicht_one`‡, `isRosenlicht_iff`‡ (`Omega/RosenlichtAlgebra.lean`‡) | OM2, OM1C |
| T59 | Thm 1.1 proof, T:1731–1737 | "`V` not exceptional for all `V`, thus `(Z̄, D̄ ⊔ Ē)` is stable": classical stability also needs `2g − 2 + n > 0` on each connected component; a connected `Z̄` with `Ē = D̄ = ∅` of arithmetic genus one (a smooth genus-one curve, or a rational curve with one self-node) has no exceptional components but `ω|_Z̄ ≅ O` is not ample. Such `Z̄` would be a whole connected component of `C′_s̄` contracted to `x`; this must be excluded separately (implicit step) | excluded since `Z̄` meets the strict transforms of the components of `C_s` through `x` (the modification locus is finite over `S` and `C_s` is pure one-dimensional), so `Ē ≠ ∅`; lane OM2B suggests Stein factorization plus upper semicontinuity, but that needs coherence of `β_*O` for a proper `β` (unavailable); planned fix (PO3, our development notes G3, corrected by OM3D, DJA-O35†; connectedness of geometric fibres formalized as `Projectivity.exists_geometricPoint_connected` from `ValuationProjectivity`): geometric connectedness of the fibres of `C′ → S′` (COH3C over valuation rings of `K(S′)^a`, invariance of `h⁰` under field extension) plus surjectivity of `β` onto the pure one-dimensional fibres of `C ×_S S′`. Unformalized; blueprint `rem:sm-omega-degree-scheme-literature` | OM2B (orchestrator note) |
| T60 | Cor B.2 proof, T:4461–4466 | "`Z` is a connected curve" is used to get `|x̃| = |∂Z|` and the genus count, but only "`Z` is a curve" is needed; connectedness is a superfluous hypothesis (same remark as CRV3's (c)). Implicit facts used without comment: the local genus `g_x` is `1` at double points and `0` at smooth points, and `g ≥ 0` (via `h⁰ = 1`, `H² = 0`) | formalized without connectedness; `g ≥ 0` kept as the explicit hypothesis `hg` of the interface, now proved in general for reduced projective curves over `k = k̄` (`BlowDown.ExcSpecialize.componentGenus_nonneg`, lane T44A3); `CurvesField.stabdown_scheme_normalization_iff`, `stabdown_scheme_of_isP1Tree` (`CurvesField/StableDownGeometric*.lean`), the DeJongAlterations blueprint | CRV4 |
| T61 | Lemma 4.4.2 proof, T:3123–3124 | "any finite, connected and dominant `S`-scheme maps bijectively onto `S`" is false unless the scheme is integral. Counterexample: `c ∈ 𝔪∖0`, `A = {(a,b) ∈ K°×K° : a ≡ b mod c}`: finite (generated by `(1,1)`, `(0,c)`), local, dominant, but `A[1/c] = K×K` has two points over `η` | harmless in Temkin's use: the Stein factorization of the integral `C′` is integral; blueprint `rem:sm-connbirh-literature` | COH3E |
| T62 | Prop 4.5.1 proof, T:3250–3252 | "Applying to them first Proposition [cofinprop]": the modifications `C′_i → C_i` from Prop 3.2.6 are not normal in general, while the proof of Prop 4.3.1 needs `Γ₀(C′_i)` finite, which Lemma 4.2.2 gives only for normal `C′` (extends T41 to §4.5; gap, not a false statement) | planned: `Γ₀` is finite for every projective modification `C′ ⊂ ℙⁿ_C` (a valuation centred at a fibre-generic point restricts to a Gauss valuation in some chart coordinate; finitely many extensions to the finite extension), and the refinement pieces are projective over the `C_i` (node A3). Formalized in a stronger form: `Γ` and `Γ₀` are finite for every modification of a flat, quasi-compact, locally-of-finite-type relative curve over a finite-height valuation ring, without normality or projectivity (`Gluing.finite_gammaZeroSet_of_flat`, `Gluing/GammaFinite.lean`); so Prop 4.3.1 holds for all modifications (`exists_dominates_isStrictlySemistable_of_isModification`), closing T41 and T62 | PT5, T45A |
| T63 | Cor 4.4.3 proof, T:3145–3147 ("Lemmas [stabcritlem] and [stabblowdown] imply …") | Applying Lemma B.3 (uniqueness of the stable blow-down over a field) needs two unstated facts: the fibres of `h′` and `h` must be read in one incidence graph, which must be anchored (true since `C_s` is a curve of pure dimension one), and stability of `C_st` must make the fibres of `h` a stable family, i.e. the description of the components of `(C_st)_s` by stars (T:4463–4467, stated there without proof). Gap, not an error | the needed direction proved: `BlowDown.Domination.fibresStable_of_fibreStable`, `dominates_of_fibreStable` (`BlowDown/Domination*.lean`) | T44D |
| T64 | Lemma 4.4.5 proof, T:3180–3186 | The proof uses the openness of the semi-stable locus (Lemma 5.1(i)), which assumes geometric fibres of pure dimension one; this property of the blow-down `C″` is not established at that point (gap) | `lem:sm-bdg-pure-dimension`: fibres of the source have dimension ≤ 1, closed surjections preserve this, and the lower bound on component dimension (`BlowDown.pureOneDimensionalFibres_of_isNodalCurve_comp`, `BlowDown/ContractionDimension.lean`) | T44B |
| T65 | Lemma 4.4.5 proof, T:3180–3186 (and our blueprint `lem:sm-stability-criterion`, marks paragraph) | The stability criterion gives "at most one mark on `Z`, and `x` smooth if there is one", but not that `D″` is étale at `x` (that `D′ → C″` is a closed immersion there) (gap) | with `V` henselian the component of `D′` through the mark is a section, whose image is a section of the separated `C″ → S` (`lem:sm-bdg-marks`, `BlowDown.isSemistablePair_blowDown`, `BlowDown/ContractionMarks.lean`) | T44B |
| T66 | Thm 1.5 proof, T:3384–3394 ("by Lemma 5.1(ii) and Remark (ii) we can achieve …") | Lemma 5.1(ii) (T:3282–3311) proves only that the stable locus is constructible; the proof of Thm 1.5 silently needs an open neighbourhood, i.e. approximation of the constructible locus (EGA IV §8) (gap) | the open form at a single geometric point over any variety is the named input `Global.StableOpenNbhd k` (`Global/Statements.lean`); to be proved via `ω` (PLAN-T5 G4) | T5G |
| T67 | Lemma 4.3.2 (`divlem`), T:3036–3046 | "a semi-stable blow up whose center is contained in `D`" via `Bl_{(π,u)}`: the centre `V(u, π)` is a curve, not contained in `D`; the ideal `(u, π)` is invertible but not trivial off the node (it is `(π)` on `D(v)`), so the trivial extension is a modification but not visibly a blow-up of `C` (same phenomenon as DJA-O33† in Prop 4.3.1) | take `π` of minimal valuation among all coordinates of the sections through the node, swap `u, v` so that `a = π²b`, and blow up `(u, v, π)` (cosupported on the node); all lifts land in the `π`-chart (`Gluing.SeparationProjective.exists_node_step_projective`, `exists_separation_marks_projective`) | T45D |
| T68 | Lemma 5.1(ii) proof, T:3292–3311 | The proof uses the incidence graph with genera of the contracted locus `Z_s̄`, which records neither where contracted components meet non-contracted ones nor the marks; both are needed to recognise an exceptional component (at most two special points) (minor gap) | use the data of `(C′_s̄, D′_s̄)` with the contracted vertices marked (constructible by the same EGA IV 9.7 arguments); our route avoids constructibility (`rem:sm-gso-literature`) | T51B |

Plan-stage items of lane PB not carried into our development notes ("gaps in exposition", none a
counterexample):

| # | Location | Issue | Fix | Found by |
|---|---|---|---|---|
| T-LI2 | T:2224–2229 | "the extension `K̃₁/k̃₁` satisfies the conditions of the Theorem" silently uses that `K̃₁/k̃₁` is finitely generated; the centre condition for the residue extension is also unproved there (automatic since `k̃₁` is algebraically closed) | V4c: `[K̃₁ : k̃₁(x̃)] ≤ [K₁ : k₁(x)]` | PB (plan) |
| T-LI3 | T:2196 (unbounded case) | "applying Prop 2.2.2" requires `L/K(x)` unramified for the DVR valuation (a standard étale presentation); in ring terms also `L/K(x)` separable for a uniformizer `x` | M1 (via `K((x))`) | PB (plan) |

(PLAN-SM-VAL LI-5, Lemma 6.3.3's `r`-orthogonal basis, and LI-7, a degenerate case of Thm 2.1.10, are recorded there as
fine or harmless.)

### 2.2 de Jong 1996 (Claude; Codex transcription notes)

| # | Location | Issue | Fix | Found by |
|---|---|---|---|---|
| J1 | 2.20 (`page-0012`) | "`U ⊂ X`" for `U ⊂ S` (misprint) | — | PC, IF |
| J2 | 2.20 (`page-0012`) | "equivalent to dim S = dim S′" stated without proof; true for finite type over a field (proved: `topologicalKrullDim_eq_of_isAlteration`), needs universal catenarity in general | — | IF |
| J3 | 4.18 e) (`page-0023`) | `sm(X/Y)` for `sm(X/S)` | — | PC |
| J4 | 4.20 (`page-0025`) | "`t_α ∈ Z`" for `t_α ∈ T` | — | PC |
| J5 | 4.22 (end of `page-0025`; our development notes says `page-0026`) | "on `Y`" for `Y′` (`ψ^{−1}(D)` lies on `Y′`) | — | PC |
| J6 | 4.27 (`page-0027`) | chart `t₁ ≠ 0`: boundary `t′₂t₃⋯t_s t₁ = 0` should end in `t_r` | — | PC |
| J7 | 2.18 (`page-0011`) | strict transform by dividing out torsion = scheme-theoretic closure of the generic fibre for integral `S′` (consistency remark, not an error) | — | IF |
| J8 | 3.3 (printed p. 63, `page-0014`) | "`t₁,…,t_r` form a regular system of parameters of `O_{S,s}`": only part of one (all of one only if `s` is generic in `D₁∩⋯∩D_r`) | only `tᵢ ∈ 𝔪∖𝔪²` used | END-LOC |
| J9 | 3.3 | `V(h) ⊆ V(∏tᵢ) ⇒ h = ε∏tᵢ^{nᵢ}` stated without argument | Krull's principal ideal theorem + well-founded divisibility (no factoriality) | END-LOC |
| J10 | 3.4 (ii) (`page-0014`) | "smooth over `X∖D`" should read `S∖D` | — | END-LOC |
| J11 | 4.4 (`page-0017`) | "restaints" (spelling) | — | Codex (transcription note) |
| J12 | 6.13 (`page-0036`) | incidence formula printed `S ×_S P_S^{d−1}` and "X-variety" (should be `X ×_S P_S^{d−1}` / S-variety); preserved as printed; "the intended geometric assertion still needs a correctly typed formal construction" | — | Codex |
| J13 | 7.11 (`page-0040`) | displayed formula printed `#sm(Y) ∪ C ∪ Z ≥ 3`, typographically malformed; intended claim fixed by the invocation of 4.13 | — | Codex |
| J14 | 3.4 (`page-0014`, l. 50) | "This integer is independent of the choice of `x ∈ T`" (constancy of `n_T`) is stated without proof | not needed: the centres are global colon ideals `(N : E_α^L) : (N : E_α^{L+1})` with pointwise traces, and a uniform bound comes from stabilization of `(N : E^L)` on a finite affine cover (`Resolution.Global.exists_colonIter_stable`) | END-GLOB |
| J15 | 3.4 (`page-0015`, l. 13) | "completion and blowing up commute in a suitable manner" is not justified | a blow-up stalk is a localization of a chart, with explicit generators of the maximal ideal of its completion (`Resolution.Global.exists_chart_maximalIdeal`) | END-GLOB |
| J16 | 3.4 (`page-0014`, l. 40–42) | "`T → D₁` finite unramified, `D₁` regular ⇒ `T` regular" is only sketched (correct for varieties via the strict henselization; minor) | not needed in our route | END-GLOB |

J1, J3, J4, J5, J6 are also preserved with transcription notes in our transcription and listed in
our development notes and our audit notes ("Known typographical issues"). Superfluous hypothesis (not an
error): 2.17 assumes the integral base Noetherian; the definition and the composition/alteration arguments need no such
hypothesis (Codex). Reading caution (not an error): in 2.23 "lies over" the norm
zero-locus means factorization, not equality of ideals, and the parameter-quotient map need not be flat or étale
(`A = ℝ[[t]]`, `A′ = ℂ[[t]]`, `h = t`: the norm is `t²`) (Codex).

---

## 3. TranscendentalNakamaye: the TN note and the analytic literature

Sources: the author's TN note in four versions, Xia's SGPT notes (earlier PDF), and the analytic and
Hironaka literature.

### 3.1 Source: the author's TN note (historical versions)

Recorded in our development notes (human mathematical review of 2026-08-31,
aligned with Copy-3 and Copy-4 on 2026-09-11). Items 1–3 are handled in the revised versions; the complex-geometric
counterexample of item 2 is not formalized in Lean.

**TN-S1. Original note l. 305–309 (`it:monotone`): direction of mass monotonicity** ☑ (corrected in the revisions)
- `φ ≼ ψ` is defined as "φ more singular", but the text writes mass(φ) ≥ mass(ψ); it should be ≤. `eq:dom-mass` and
  `lem:positive-rooftop` use the correct direction; the Witt Nyström abstract states that mass decreases as singularity
  increases. The blueprint uses the correct direction.

**TN-S2. Original note l. 264–266 and 476–478: bridge between the two numerical restricted volumes** ☑ (revised
definition)
- The note allows the remainder of an analytic singularity to be merely bounded, and claims (l. 476–478) that the
  non-pluripolar product of such a current equals the absolutely continuous part used by CT22. This per-current
  identity is false.
- *Counterexample.* On `P¹` with normalized Fubini–Study `ω`, `φ = max(log|z|², 0) − log(1+|z|²)` is continuous with
  `−log 2 ≤ φ ≤ 0`, so it has `(1, O)` analytic singularities in the note's sense; `ω+ddᶜφ = ddᶜ max(log|z|²,0)` is a
  positive measure of mass 1 on the unit circle; its non-pluripolar measure is that measure (mass 1), but its
  absolutely continuous part with respect to a smooth area form is 0.
- This shows the note's reason is insufficient; it does not refute the main theorem or the final equality of the two
  suprema. The revised versions use CT22's smooth-remainder definition directly; the old comparison is kept as an open
  appendix result, not as a Lean axiom or main-line premise.

**TN-S3. `lem:relative-principalization` and `prop:gluing`: the submanifold must be closed** ☑
- `prop:gluing` uses compactness of `W` (original l. 2010, 2031, 2048). The strict transform built in the main theorem
  is closed; the blueprint states the condition.

**TN-S4. Extended-real operations (convention, not an error)** —
- "ψ_D+χ−φ bounded on K" is read as `∃ C∈ℝ, ∀ x∈K, ψ_D(x)+χ(x) ≤ φ(x)+C`, consistent with the note's own l. 1945–1947;
  no `−∞−(−∞)` is formed. Recorded with the items above.

### 3.2 Other sources used by TN

**TN-S5. Włodarczyk 2009 (analytic resolution), printed pp. 49–57: misprints** ☐ (minor, typographical)
- Kept and marked `[sic]` in the transcriptions `page-0019`
  (plain `J` in an ideal product; `μ_I` for `μ_j`), `page-0020` (`T^i(I)^i` and `T(D(I))` without exponent, Lemma
  5.5.1 (4) proof), `page-0021` (unbalanced parenthesis `HI)_i`, Lemma 5.5.3 (5); italic `I`), `page-0022`
  (`u_1''` for `u_i''`), `page-0025` ("algorthm"; subscript `a` for `α`), `page-0027` ("a finite open covers",
  "compact ,"; plain `J`). Found by TN23 (run 0195 r2) and TN3; listed in
  our reference list ("Misprints are kept and marked [sic]").

**TN-S6. Demailly–Xia DX24 (trace operator), Thm 3.16, following paragraph: variable mismatch** ☐ (minor)
- The display uses `φ` whereas the theorem introduces `u`; the original is preserved.

**TN-S7. Błocki, lecture notes on the complex Monge–Ampère operator: printing oddities** ☐ (minor)
- page-0035 (last display of the proof of Prop 2.1.3: integrand `ddᶜ(u∗ρ_{1/j})` with no `−u_ε` term, domain changes
  `Ω → Ω′`); page-0039 (proof of Thm 2.1.7: `v` and `ddᶜ(u_k−ψ)` swapped); page-0045 ("`u_0^j S^j ≤ u_0 S_j`",
  presumably `S^j`). Recorded in our reference list (blocki-ma-operator) and `page-0045`.

**TN-S8. Remmert 1957, Satz 23 line 2 (printed p. 356): punctuation** ☐ (trivial)
- The mark after "lokal-analytische" prints as a period-like dot where the transcription has a comma (the phrase has a
  comma in Satz 22′ and Satz 24); meaning unaffected (TN3; same lane and model, not
  an independent reader).

Not source errors (recorded so they are not re-reported): Włodarczyk's and Bierstone–Milman's centre selector `ρ` is not
the decreasing quantity (the sources separate selector `(inv, ρ)` and decreasing `(inv, ν)`); a counterexample to
transcribing `ρ` as the decreasing quantity is in our development notes. The
standing assumption that manifolds are connected in Boucksom/Demailly–Păun (TN-O5†) and Hiep 2014 Remark 1.3 (TN-O16†)
are correct sources that exposed our own mistakes.

---

## 4. Number of entries

| Section | Numbered entries |
|---|---|
| 1. EnvelopeProperty sources (plus the tables of §1.3–§1.5) | 15 |
| 2. Temkin 2010 / de Jong 1996 (table rows) | 86 |
| 3. TranscendentalNakamaye sources | 8 |
