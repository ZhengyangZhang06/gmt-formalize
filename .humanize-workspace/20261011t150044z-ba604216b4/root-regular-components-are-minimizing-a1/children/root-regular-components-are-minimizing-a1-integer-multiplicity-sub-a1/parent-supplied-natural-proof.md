# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.integer_multiplicity_sub-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, Remark 3.2(1) (chapter-06.txt lines 755–756, stated without proof), used in the parent proof step 5 ('S + T₂ is integer multiplicity (Ch. 6, 3.2(1))'). Uses the sibling approx_tangent_locality and uniqueness of approximate tangent spaces (Simon Ch. 3, 1.5(1); SimonGMT HasApproximateTangentSpaceAt.unique). Notation: ev_τ(α) := α(τ_1, …, τ_n); a unit orientation of a subspace Q is ±ev_τ with τ an orthonormal basis of Q (IsUnitOrientationOf); for such ξ', |ξ'(α)| ≤ ‖α‖ ∏_i ‖τ_i‖ = ‖α‖ (operator norm), and ξ' ≠ 0 since ξ'(±β_τ) = 1 for β_τ(v) := det(⟨τ_i, v_j⟩).

1. (Data.) Let R_S = (C_S, θ_S, ξ_S) represent S and R_T = (C_T, θ_T, ξ_T) represent T. Then C := C_S ∪ C_T is Borel, ⊆ U, countably n-rectifiable (SimonGMT countablyRectifiable_iUnion), and for compact K ⊆ U, H^n(C ∩ K) ≤ ∫_{C_S∩K} θ_S dH^n + ∫_{C_T∩K} θ_T dH^n < ∞, as θ_S, θ_T ≥ 1 on their carriers.

2. (Common tangent planes on the overlap.) By approx_tangent_locality applied to C_S ⊆ C and to C_T ⊆ C: for H^n-a.e. x ∈ C_S, HasApproximateTangentSpaceAt n C x Q ⟺ HasApproximateTangentSpaceAt n C_S x Q for all Q, and likewise for C_T. Together with the orientation conditions of R_S and R_T and uniqueness of approximate tangent spaces, for H^n-a.e. x ∈ C_S ∩ C_T the approximate tangent space Q_x of C at x exists and ξ_S(x), ξ_T(x) are both unit orientations of Q_x.

3. (Sign lemma.) If τ and τ' are orthonormal bases of the same n-dimensional subspace Q, then α(τ') = det(B) α(τ) for all α ∈ Λ^n, where B_{ij} := ⟨τ_i, τ'_j⟩, and det B = ±1. Indeed τ'_j = Σ_i B_{ij} τ_i; expanding multilinearly and using that α is alternating, α(τ') = Σ_{σ∈Sym(n)} sgn(σ) ∏_j B_{σ(j) j} · α(τ) = det(B) α(τ); and BᵀB = (⟨τ'_i, τ'_j⟩) = I, so det(B)² = 1. Consequently, by step 2, ξ_T(x) = ±ξ_S(x) for H^n-a.e. x ∈ C_S ∩ C_T.

4. (Measurable bookkeeping.) Let ξ̃_S, ξ̃_T be Borel functions with ξ̃_S = ξ_S H^n-a.e. on C_S and ξ̃_T = ξ_T H^n-a.e. on C_T. Let σ(x) := 1 if ξ̃_T(x) = ξ̃_S(x) and σ(x) := −1 otherwise (Borel). Then ξ_T = σ ξ_S H^n-a.e. on C_S ∩ C_T: at a.e. such x, ξ̃_S(x) = ξ_S(x), ξ̃_T(x) = ξ_T(x) and ξ_T(x) = ±ξ_S(x) (step 3); if ξ_T(x) = ξ_S(x) then σ(x) = 1, and otherwise ξ_T(x) = −ξ_S(x) and σ(x) = −1. For x ∈ C_S ∩ C_T let d(x) := θ_S(x) − σ(x) θ_T(x) ∈ ℤ. Define
 C' := (C_S ∖ C_T) ∪ (C_T ∖ C_S) ∪ {x ∈ C_S ∩ C_T : d(x) ≠ 0} (Borel);
 θ'(x) := θ_S(x) on C_S ∖ C_T, θ_T(x) on C_T ∖ C_S, |d(x)| on C_S ∩ C_T, and 0 elsewhere (Borel, ℕ-valued, ≥ 1 on C');
 ξ'(x) := ξ_S(x) on C_S ∖ C_T, −ξ_T(x) on C_T ∖ C_S, sign(d(x)) ξ_S(x) on C_S ∩ C_T (a.e. strongly measurable for H^n⌞C').

5. (R' := (C', θ', ξ') is an IMRep in U.) C' ⊆ C ⊆ U is Borel and countably n-rectifiable (subset of C). θ' ≤ θ_S + θ_T on C', so ∫_{C'∩K} θ' dH^n < ∞ for compact K ⊆ U. Orientation: C' is the union of the Borel pieces P₁ := C_S ∖ C_T ⊆ C_S, P₂ := C_T ∖ C_S ⊆ C_T and P₃ := C' ∩ C_S ∩ C_T ⊆ C_S. For P₁, apply approx_tangent_locality to P₁ ⊆ C_S and to P₁ ⊆ C' (H^n(C' ∩ K) ≤ H^n(C ∩ K) < ∞): for H^n-a.e. x ∈ P₁ the approximate tangent spaces of C_S, P₁ and C' at x coincide, and ξ'(x) = ξ_S(x) is a unit orientation of the one of C_S. Similarly for P₂ (with C_T and −ξ_T; −ev_τ is again a unit orientation, the definition allowing either sign) and for P₃ (with C_S and sign(d) ξ_S). Hence for H^n-a.e. x ∈ C' there is Q with HasApproximateTangentSpaceAt n C' x Q and ξ'(x) a unit orientation of Q.

6. (R' represents S − T.) Let ω ∈ 𝒟^n(U). The functions θ_S ξ_S(ω) and θ_T ξ_T(ω) are bounded by θ_S ‖ω‖_∞ 1_{tsupport ω}, resp. θ_T ‖ω‖_∞ 1_{tsupport ω}, a.e. on their carriers, hence integrable, and (S − T)(ω) = ∫_{C_S} θ_S ξ_S(ω) dH^n − ∫_{C_T} θ_T ξ_T(ω) dH^n. Split both integrals over C_S ∖ C_T, C_T ∖ C_S and C_S ∩ C_T. On C_S ∩ C_T the combined integrand is a.e. θ_S ξ_S(ω) − θ_T σ ξ_S(ω) = d ξ_S(ω) = |d| sign(d) ξ_S(ω), which vanishes where d = 0. Therefore (S − T)(ω) = ∫_{C'} θ' ξ'(ω) dH^n = R'.action ω for every ω, so R' represents S − T and S − T is integer multiplicity.

## Key steps

1. On C_S ∩ C_T both orientations orient the common approximate tangent plane of C_S ∪ C_T (locality), so ξ_T = ±ξ_S there (an orthonormal change of frame has determinant ±1).
2. Carrier C' = (C_S △ C_T) ∪ {d ≠ 0}, multiplicity |θ_S − σθ_T| on the overlap, orientation sign(d)ξ_S; locality transfers the orientation condition to C'.
3. Splitting the integrals over the three pieces shows that R' represents S − T.

## Reference use

### local-project

Queries:
- `cmp .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `python3 summary of lean_name fields in dag.json; grep -rl regcomp_ in the run directory (no match)`
- `grep -n 'def GeometricCurrentOn.massOn|massAdmissibleOn|covectorEuclideanNorm' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `grep -n 'GeometricCurrentOn.support|zeroRegion|restrictDomain' simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique, CountablyRectifiable.mono, countablyRectifiable_iUnion, aemeasurable_starProjection_of_approximateTangentField)`
- `grep -rn 'simon_theorem_3_6|simon_remark_3_7' simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `grep -n 'wedgeCovectors_apply_det' simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean (exp_normalizedBallMass_monotoneOn and the sign-convention remark)`
- `read simongmt/Poincare/SimonGMT/Chapter07/Basic.lean (minimizing_summands, minimizing_summands_source)`
- `grep -rln 'Cauchy-Binet|CauchyBinet|cauchyBinet|cauchy_binet' Mathlib (no match)`
- `grep -rn 'IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero|nullSingletonClass_hausdorff|hausdorffMeasure_zero_singleton|Set.Finite.measure_zero|exists_isSubordinate|hausdorffMeasure_image_le|integral_pos_iff_support_of_nonneg_ae|norm_integral_le_lintegral_norm|norm_alternatizeUncurryFin_le|withDensity_apply|setLIntegral_mono|ae_tendsto_measure_inter_div' Mathlib`
- `grep -n 'μHE\[|euclideanHausdorffMeasure' Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `lake build GMT.Ch07.Submission in scratch copy /tmp/regcomp-proj; lake env lean /tmp/regcomp-proj/Check.lean (nine child types + conditional parent assembly + #print axioms)`
- `lake env lean /tmp/regcomp-proj/Axioms.lean (#print axioms of reused SimonGMT lemmas)`
- `lake env lean /tmp/regcomp-proj/Inst.lean (#synth Norm (Covector (Euclid 3) 2); #synth Sub (GeometricCurrentOn univ 2))`
- `grep -n for book line ranges: chapter-07.txt (1.4, 4.1, 5.1–5.2, 5.11), chapter-06.txt (3.1, 3.2), chapter-04.txt (3.1–3.17), chapter-03.txt (1.5, 1.6), chapter-01.txt (3.6, 3.7)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter07/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-07-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/regcomp-proj/Check.lean`
- `/tmp/regcomp-proj/Axioms.lean`
- `/tmp/regcomp-proj/Inst.lean`

The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Submission.lean, and the DAG reserves no regcomp_ names. The children cite these library facts, all using only propext, Classical.choice and Quot.sound: SimonGMT Chapter01.simon_theorem_3_6 and simon_remark_3_7_of_openSigmaFinite (Upper Density Theorem, for approx_tangent_locality); Chapter06.wedgeCovectors_apply_det (determinant covectors, used for the normalisations); Chapter03.HasApproximateTangentSpaceAt.unique, CountablyRectifiable.mono and countablyRectifiable_iUnion; and Chapter07.minimizing_summands_source (the 1.4 chain over abstract groups). That chain cannot be instantiated directly, because the contract gives GeometricCurrentOn no AddCommGroup instance, so minimizing_summand restates it. SimonGMT's monotonicity (Chapter04 RectifiableVarifold.HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn) is stated for its own varifold structure, which assumes a measurable tangent projection. monotonicity_mass_bound therefore proves the bound for IMRep directly, including measurability of the tangential divergence. From Mathlib the children use: IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (needs only LocallyIntegrableOn), SmoothPartitionOfUnity.exists_isSubordinate, nullSingletonClass_hausdorff, hausdorffMeasure_zero_singleton, μHE[0] = μH[0], LipschitzWith.hausdorffMeasure_image_le and norm_alternatizeUncurryFin_le. The search found no Cauchy–Binet theorem in Mathlib, so the multilinear arguments use slotwise Parseval and determinant covectors instead. All nine child types elaborate after import GMT.Ch07.Submission. The conditional assembly of RegularComponentsAreMinimizing from them, MinimizingImpliesStationary and CodimensionOneRegularity compiles, using the standard axioms plus sorryAx from the child stubs only.
