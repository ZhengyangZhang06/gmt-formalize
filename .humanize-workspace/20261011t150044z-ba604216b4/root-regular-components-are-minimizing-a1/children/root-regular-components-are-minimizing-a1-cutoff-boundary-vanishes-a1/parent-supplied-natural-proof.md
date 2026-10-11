# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.cutoff_boundary_vanishes-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: proof of Simon 7.5.11, (1)–(2) and the cut-off argument (chapter-07.txt lines 990–1016), parent proof step 4, with the parent's corrections: [D1] the cut-off is ζ = ∏_j (1 − φ_j), which vanishes near the singular points (printed: ζ = ∏ φ_j); [D2] the printed pointwise bound |d(ζω) − ζ dω| ≤ c|ω| Σ σ_j^{n−1} is replaced by an integrated estimate using the density bound (h6); [D3] the separation of M₁ from the rest of spt T (book: 'ζ ≡ 0 in a neighbourhood of spt T ∖ spt T₁') is done by a partition of unity subordinate to the neighbourhoods of (h4). Notation: for a k-form F, dF(x) is the alternation of DF(x), so ‖dF(x)‖ ≤ (k + 1) ‖DF(x)‖ and tsupport dF ⊆ tsupport F; 𝒟^k(U) are the smooth k-forms with compact support in U.
Fix ω ∈ 𝒟^m(U); we show ∂T₁(ω) = T₁(dω) = 0.

1. (Constants.) Let K := tsupport ω, a compact subset of U. By (h5) choose Z; replacing Z by Z ∩ K we may assume Z ⊆ K (Z ∩ K is compact, μH[m]-null, and closure(M₁) ∩ K ⊆ M₁ ∪ (Z ∩ K)). By (h6) for K choose C and r₁ > 0; we may assume C ≥ 0. Let δ₀ := min(1, r₁/2). Fix φ₀ ∈ C_c^∞(ℝ^P) with 0 ≤ φ₀ ≤ 1, φ₀ = 1 on closedBall(0, 1) and tsupport φ₀ ⊆ ball(0, 2) (e.g. a smooth bump with inner radius 1 and outer radius 3/2), and let c₀ := sup ‖Dφ₀‖ < ∞. Let a := sup_z ‖ω(z)‖ and b := sup_z ‖Dω(z)‖ (finite, ω being smooth with compact support), and C' := (m + 1) C 2^{m+1} (b + c₀ a).

2. (Covering; uses μH[m](Z) = 0.) Let ε ∈ (0, 1). There are J ∈ ℕ, points p_1, …, p_J ∈ Z and radii σ_j ∈ (0, δ₀) with Z ⊆ ⋃_j B(p_j, σ_j) and Σ_j σ_j^m < ε. If m = 0: μH[0] is counting measure (μH[0]({x}) = 1), so Z = ∅ and J = 0 works. If m ≥ 1: let η' := min(ε 2^{−m−1}, (δ₀/2)^m). By the definition of the Hausdorff measure, μH[m](Z) = sup_{δ>0} inf {Σ_i diam(E_i)^m : Z ⊆ ⋃_i E_i countable, diam E_i ≤ δ}; since it is 0, there is a countable cover (E_i)_{i ≥ 1} of Z with diam E_i ≤ δ₀/2 and Σ_i diam(E_i)^m < η'. Discard the E_i not meeting Z, pick p_i ∈ E_i ∩ Z and set σ_i := diam(E_i) + (η' 2^{−i})^{1/m} > 0 (indices i ≥ 1, so (η' 2^{−i})^{1/m} ≤ 2^{−1/m} δ₀/2 < δ₀/2). Then E_i ⊆ B(p_i, σ_i), σ_i < δ₀, and Σ_i σ_i^m ≤ 2^{m−1} Σ_i (diam(E_i)^m + η' 2^{−i}) ≤ 2^m η' < ε. The open balls B(p_i, σ_i) cover the compact set Z; keep a finite subcover.

3. (Cut-off ζ, [D1].) Let φ_j(z) := φ₀((z − p_j)/σ_j): smooth, 0 ≤ φ_j ≤ 1, φ_j = 1 on B(p_j, σ_j), tsupport φ_j ⊆ B(p_j, 2σ_j), ‖Dφ_j‖ ≤ c₀/σ_j. Let ζ := ∏_{j=1}^J (1 − φ_j). Then ζ is smooth, 0 ≤ ζ ≤ 1; ζ = 0 on the open set O_Z := ⋃_j B(p_j, σ_j) ⊇ Z; ζ = 1 on the open set ℝ^P ∖ ⋃_j tsupport φ_j; by the product rule and 0 ≤ 1 − φ_i ≤ 1, ‖Dζ‖ ≤ Σ_j ‖Dφ_j‖ ≤ Σ_j (c₀/σ_j) 1_{B(p_j, 2σ_j)}; and 1 − ζ ≤ Σ_j φ_j ≤ Σ_j 1_{B(p_j, 2σ_j)}. The forms ζω and (1 − ζ)ω belong to 𝒟^m(U) (smooth, tsupport ⊆ K) and ω = ζω + (1 − ζ)ω, so by linearity of d and of T₁: T₁(dω) = T₁(d(ζω)) + T₁(d((1 − ζ)ω)).

4. (T₁(d(ζω)) = 0; [D3] and book (2).) Let K₁ := closure(M₁) ∩ tsupport(ζω). Since ζω vanishes on the open set O_Z, tsupport(ζω) ⊆ K ∖ O_Z ⊆ K ∖ Z; hence K₁ ⊆ (closure(M₁) ∩ K) ∖ Z ⊆ M₁ by (h5), and K₁ is compact. By (h4) every z ∈ K₁ has G_z and c_z; choose z_1, …, z_L with K₁ ⊆ G_{z_1} ∪ … ∪ G_{z_L}. Choose an open O₁ with K₁ ⊆ O₁ ⊆ closure(O₁) ⊆ G_{z_1} ∪ … ∪ G_{z_L} and closure(O₁) compact, and a smooth partition of unity (ψ_l)_{l ≤ L} on the closed set closure(O₁) subordinate to (G_{z_l}) (Mathlib SmoothPartitionOfUnity.exists_isSubordinate): each ψ_l is smooth with tsupport ψ_l ⊆ G_{z_l}, and Σ_l ψ_l = 1 on closure(O₁). Put χ := Σ_l ψ_l.
 (a) The form (1 − χ)ζω vanishes on the open set O₁ ∪ (ℝ^P ∖ tsupport(ζω)), which contains M₁ (points of M₁ ∩ tsupport(ζω) lie in K₁ ⊆ O₁). Hence d((1 − χ)ζω) = 0 at every point of M₁ and, by (h2), T₁(d((1 − χ)ζω)) = 0.
 (b) For each l, ψ_l ζω ∈ 𝒟^m(U) and tsupport d(ψ_l ζω) ⊆ tsupport(ψ_l ζω) ⊆ tsupport ψ_l ⊆ G_{z_l}; by (h4) and (h1), T₁(d(ψ_l ζω)) = c_{z_l} T(d(ψ_l ζω)) = c_{z_l} ∂T(ψ_l ζω) = 0.
 Since ζω = (1 − χ)ζω + Σ_l ψ_l ζω, linearity gives T₁(d(ζω)) = 0.

5. (Error term; [D2].) Let F := (1 − ζ)ω. F vanishes on the open set ℝ^P ∖ ⋃_j tsupport φ_j, so dF(x) = 0 unless x ∈ ⋃_j B(p_j, 2σ_j). Since DF(x) = (1 − ζ(x)) Dω(x) − Dζ(x) ⊗ ω(x), ‖dF(x)‖ ≤ (m + 1) ‖DF(x)‖ ≤ (m + 1)((1 − ζ(x)) b + ‖Dζ(x)‖ a) ≤ s(x) := (m + 1) Σ_j (b + c₀ a/σ_j) 1_{B(p_j, 2σ_j)}(x). By (h2), |T₁(dF)| = |∫_{M₁} ξ(x)(dF(x)) dH^n| ≤ (∫⁻_{M₁} |ξ(x)(dF(x))| dH^n).toReal (this bound of a Bochner integral by the lower integral of its absolute value needs no integrability), and by (h3), |ξ(x)(dF(x))| ≤ ‖dF(x)‖ ≤ s(x) for H^n-a.e. x ∈ M₁. By (h6) at the points p_j ∈ Z ⊆ K with radii 2σ_j < r₁ (σ_j < δ₀ ≤ r₁/2):
 ∫⁻_{M₁} s dH^n = (m + 1) Σ_j (b + c₀ a/σ_j) H^n(M₁ ∩ B(p_j, 2σ_j)) ≤ (m + 1) Σ_j (b + c₀ a/σ_j) C (2σ_j)^{m+1} ≤ (m + 1) C 2^{m+1} (b + c₀ a) Σ_j σ_j^m ≤ C' ε,
 using σ_j ≤ 1 (so σ_j^{m+1} ≤ σ_j^m). Hence |T₁(dF)| ≤ C' ε.

6. By steps 3–5, |T₁(dω)| ≤ C' ε for every ε ∈ (0, 1), with C' independent of ε. Hence ∂T₁(ω) = T₁(dω) = 0. As ω ∈ 𝒟^m(U) was arbitrary, T₁.boundary = 0.

## Key steps

1. Cover the compact μH[n−1]-null set Z ⊇ (closure(M₁) ∩ spt ω) ∖ M₁ by finitely many balls B(p_j, σ_j) with Σ σ_j^{n−1} < ε and set ζ = ∏(1 − φ_j).
2. closure(M₁) ∩ spt(ζω) is a compact subset of M₁; a partition of unity subordinate to the proportionality neighbourhoods gives T₁(d(ζω)) = Σ_l c_l ∂T(ψ_l ζω) = 0.
3. The remainder T₁(d((1 − ζ)ω)) is at most n C 2^n (b + c₀a) Σ σ_j^{n−1} by the density bound.
4. Let ε → 0.

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
