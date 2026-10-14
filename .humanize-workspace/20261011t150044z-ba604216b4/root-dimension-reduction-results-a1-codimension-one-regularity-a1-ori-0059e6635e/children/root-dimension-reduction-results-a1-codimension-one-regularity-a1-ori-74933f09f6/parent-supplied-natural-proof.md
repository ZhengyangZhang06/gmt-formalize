# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.oriented_piece_mass-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.oriented_piece_mass-a1.oriented_mass_lower-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon Ch. 6, 2.5 (the mass M_W(T), chapter-06.txt lines 224–240) and 3.2(3) (M_W(T) = ∫_{M∩W} θ dH^n, chapter-06.txt lines 755–770). This is the lower half of the parent proof: its step 1 and step 3. Steps (3a)–(3b) of the parent (the measure ν = θ'·H^k⌞M', finite on W, and Lusin's theorem) are carried out with the accepted lemma lusin_covector. Steps (3c)–(3e) (Tietze extension, normalization to |·| ≤ 1, mollification, smooth cut-off) are exactly what the accepted lemma smooth_unit_approximation packages: for each δ > 0 it gives one admissible form that is δ-close to L∘ξ' on the Lusin set K. Because that form is δ-close on K, rather than a member of a pointwise convergent sequence, the parent's dominated-convergence passage (3f) is not needed. The parent's estimate (3g) is applied directly to T(ω), with the one extra error term δ·ν(K) (step 8). Measurability of M' (a hypothesis of the parent) is not needed and not assumed: every restriction below is to one of the Borel sets W, Z, A, K, and (H^k⌞M')⌞B = H^k⌞(B ∩ M') for Borel B and an arbitrary set M'.

Sibling children used (accepted declarations, reused with their identical frozen types):
- unit_orientation_dual (Submission.dor_ims_unitOrientation_dual): there is a continuous linear map L : Λ_k(ℝ^P) → Λ^k(ℝ^P) such that whenever IsUnitOrientationOf ξ Q: (a) |ξ(α)| ≤ |α| for every k-covector α; (b) |L(ξ)| ≤ 1; (c) ξ(L(ξ)) = 1.
- lusin_covector (Submission.dor_ims_lusin_continuousOn): for a measure ν on ℝ^P, a measurable A ⊆ ℝ^P with ν(A) < ∞, a ν-a.e. strongly measurable f : ℝ^P → Λ^k(ℝ^P) and a real η > 0, there is a compact K ⊆ A with ν(A ∖ K) < η such that f is continuous on K.
- smooth_unit_approximation (Submission.dor_ims_smooth_unit_approx): for K ⊆ G ⊆ ℝ^P with K compact and G open, β : ℝ^P → Λ^k(ℝ^P) continuous on K with |β(x)| ≤ 1 for x ∈ K, and δ > 0, there is a smooth compactly supported k-form ω₀ (IsTestForm ω₀) with tsupport ω₀ ⊆ G, |ω₀(x)| ≤ 1 for every x and |ω₀(x) − β(x)| ≤ δ for every x ∈ K.

Notation.
- H^k := μHE[k]; μ := H^k⌞M'; Λ^k := Covector (Euclid P) k with |α| := covectorEuclideanNorm α; Λ_k := MultiVector P k.
- ν := μ with density ofReal∘θ', i.e. ν(B) = ∫⁻_B ofReal(θ') dμ = ∫⁻_{M'∩B} ofReal(θ') dH^k for Borel B (the second equality because (H^k⌞M')⌞B = H^k⌞(B ∩ M') for Borel B).
- I := I(W) = ∫⁻_{M'∩W} ofReal(θ') dH^k, assumed finite.
- ω ∈ 𝒟^k(U) is admissible for M_W(T) if tsupport ω ⊆ W and |ω(x)| ≤ 1 for every x; by definition of the supremum, ofReal(T(ω)) ≤ M_W(T) for each admissible ω.

Proof. Fix the data and hypotheses of the statement and an open W ⊆ V with I < ∞.

1. (Good points.) Let L be the map of unit_orientation_dual for (P, k). Call x good if (a) |ξ'(x)(α)| ≤ |α| for every α ∈ Λ^k, (b) |L(ξ'(x))| ≤ 1 and (c) ξ'(x)(L(ξ'(x))) = 1. By the orientation hypothesis and unit_orientation_dual, μ-a.e. x is good. So the set of points that are not good is μ-null, and it is contained in a Borel set Z with μ(Z) = 0 (every null set has a measurable null superset).

2. (The measure ν.) ν ≪ μ, since ν(B) = ∫⁻_B ofReal(θ') dμ = 0 whenever μ(B) = 0. Hence ν(Z) = 0, and ν-a.e. x is good. W is open, hence Borel, so ν(W) = ∫⁻_W ofReal(θ') d(H^k⌞M') = ∫⁻_{M'∩W} ofReal(θ') dH^k = I < ∞, and ν(B) ≤ I for every Borel B ⊆ W. Write m := I, a real number ≥ 0.
 Density formula: ofReal∘θ' is measurable (θ' is) and finite everywhere, so every ν-integrable g : ℝ^P → ℝ satisfies ∫ g dν = ∫ (ofReal θ'(x)).toReal·g(x) dμ(x) = ∫ θ'·g dμ, because (ofReal θ'(x)).toReal = θ'(x) when θ'(x) ≥ 0 (Mathlib: integral_withDensity_eq_integral_toReal_smul).

3. (Reduction.) It suffices to prove r ≤ M_W(T) for every real r ≥ 0 with r < I; then I ≤ M_W(T) in [0, ∞]. Fix such an r, choose ε > 0 with r + ε < I, and put η := ε/4 > 0, so that r + 4η < m.

4. (Lusin.) h := L∘ξ' : ℝ^P → Λ^k is ν-a.e. strongly measurable: ξ' is μ-a.e. strongly measurable by hypothesis, hence ν-a.e. strongly measurable because ν ≪ μ, and L is continuous. The set A := W ∖ Z is Borel with ν(A) ≤ ν(W) < ∞. By lusin_covector, applied to ν, A, h and η, there is a compact K ⊆ A with ν(A ∖ K) < η such that h is continuous on K.
 (4a) K ⊆ W and K ∩ Z = ∅, so every x ∈ K is good; in particular |h(x)| ≤ 1 for x ∈ K, by (b).
 (4b) W ∖ K ⊆ (A ∖ K) ∪ Z, so ν(W ∖ K) ≤ ν(A ∖ K) + ν(Z) < η.
 (4c) K is compact, hence Borel, and K ⊆ W, so ν(K) + ν(W ∖ K) = ν(W) = m, all terms finite. With (4b), ν(K) > m − η; also ν(K) ≤ m.

5. (An admissible form.) Put δ := η/(m + 1) > 0. Apply smooth_unit_approximation to the compact set K, the open set G := W ⊇ K, β := h (continuous on K, with |β| ≤ 1 on K by (4a)) and δ. It gives a smooth compactly supported k-form ω₀ with tsupport ω₀ ⊆ W, |ω₀(x)| ≤ 1 for every x, and |ω₀(x) − h(x)| ≤ δ for every x ∈ K. Since tsupport ω₀ ⊆ W ⊆ V ⊆ U, ω₀ is an element ω of 𝒟^k(U), and ω is admissible for M_W(T). Hence ofReal(T(ω)) ≤ M_W(T).

6. (Integrability and the value of T(ω).) Let f(x) := ξ'(x)(ω₀(x)).
 - f is ν-a.e. strongly measurable: it is the composite of x ↦ (ξ'(x), ω₀(x)), which is ν-a.e. strongly measurable (ξ' by step 4, ω₀ continuous), with the evaluation pairing Λ_k × Λ^k → ℝ, (ζ, α) ↦ ζ(α), which is continuous (a bounded bilinear map).
 - For every good x, |f(x)| ≤ 1_W(x): if x ∉ W then x ∉ tsupport ω₀, so ω₀(x) = 0 and f(x) = 0; if x ∈ W then |f(x)| ≤ |ω₀(x)| ≤ 1 by (a).
 - 1_W is ν-integrable because ν(W) < ∞. Hence f is ν-integrable, and, by the representation hypothesis (tsupport ω ⊆ W ⊆ V) and the density formula of step 2,
 T(ω) = ∫_{M'} θ'(x)·ξ'(x)(ω₀(x)) dH^k(x) = ∫ θ'·f dμ = ∫ f dν.

7. (Pointwise lower bound.) For every good x,
 f(x) ≥ (1 − δ)·1_K(x) − 1_{W∖K}(x).
 - x ∈ K: by linearity of ξ'(x) and (c), f(x) = ξ'(x)(h(x)) + ξ'(x)(ω₀(x) − h(x)) = 1 + ξ'(x)(ω₀(x) − h(x)) ≥ 1 − |ω₀(x) − h(x)| ≥ 1 − δ, using (a).
 - x ∈ W ∖ K: f(x) ≥ −|ξ'(x)(ω₀(x))| ≥ −|ω₀(x)| ≥ −1, by (a).
 - x ∉ W: ω₀(x) = 0, so f(x) = 0, which is the value of the right side.
 Since ν-a.e. x is good, the inequality holds ν-a.e.

8. (Integration and arithmetic.) The right side of step 7 is ν-integrable (ν(K) and ν(W ∖ K) are finite), so monotonicity of the integral gives
 T(ω) = ∫ f dν ≥ (1 − δ)·ν(K) − ν(W ∖ K) = ν(K) − δ·ν(K) − ν(W ∖ K).
 Now δ·ν(K) ≤ δ·m = η·m/(m + 1) < η, ν(W ∖ K) < η by (4b), and ν(K) > m − η by (4c). Therefore
 T(ω) > (m − η) − η − η = m − 3η > (r + 4η) − 3η = r + η > r.

9. (Conclusion.) By steps 5 and 8, r = ofReal(r) ≤ ofReal(T(ω)) ≤ M_W(T). Since r ∈ [0, I) was arbitrary, I ≤ M_W(T). ∎

## Key steps

1. unit_orientation_dual gives L with |ξ'(α)| ≤ |α|, |L(ξ')| ≤ 1 and ξ'(L(ξ')) = 1 off a Borel H^k⌞M'-null set Z; ν := θ'·H^k⌞M' satisfies ν ≪ H^k⌞M' and ν(W) = I < ∞.
2. Reduce to r < I; with η = ε/4 and r + 4η < I, lusin_covector on A = W ∖ Z gives a compact K ⊆ A with ν(A ∖ K) < η on which L∘ξ' is continuous; since ν(Z) = 0, ν(W ∖ K) < η.
3. smooth_unit_approximation gives an admissible ω with tsupport ω ⊆ W, |ω| ≤ 1 and |ω − L∘ξ'| ≤ δ := η/(I + 1) on K.
4. T(ω) = ∫ ξ'(ω) dν ≥ (1 − δ)ν(K) − ν(W ∖ K) > I − 3η > r, so r ≤ M_W(T); hence I ≤ M_W(T).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C lake-packages-25730c7c/mathlib rev-parse HEAD; git -C lake-packages-25730c7c/simongmt rev-parse HEAD; python3 read of snapshot project/lake-manifest.json (mathlib and simongmt revs)`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem .*[Ll]usin' mathlib/Mathlib; rg -ln Lusin mathlib/Mathlib; rg -n Lusin mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean (snapshot)`
- `rg -n 'theorem enorm_integral_le_lintegral_enorm|theorem integral_withDensity_eq_integral_toReal_smul |theorem lintegral_indicator |theorem restrict_restrict |theorem exists_measurable_superset_of_null|theorem isBoundedBilinearMap_apply|theorem le_of_forall_nnreal_lt|theorem withDensity_apply |theorem withDensity_absolutelyContinuous|image_eq_zero_of_notMem_tsupport' mathlib/Mathlib (snapshot)`
- `rg -n 'instance.*InnerRegular' mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `rg -n 'def covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|theorem GeometricCurrentOn.le_massOn' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; read Chapter06/Currents.lean and Forms.lean (TestFormOn, IsTestForm, DifferentialForm, Covector)`
- `python3 scan of dag.json: subtree root.density_one_implies_regular-a1.imrep_mass_and_support-a1 (statuses, candidate commits, exact lean_statement of unit_orientation_duality, lusin_covector, smooth_unit_approximation, mass_upper_bound, mass_lower_bound) and their parent-child-handoff.json proofs`
- `git show 57cebee2fbae5e013e3b0e4191cd38bc03b89473:GMT/Ch07/Submission.lean (accepted Lean proofs of dor_ims_measure_le_massOn and of the three reused declarations)`
- `grep -c codim1_oriented_rep dag.json; grep -rn 'codim1_oriented_rep|oriented_rep_massOn|oriented_rep_lintegral' GMT/ simongmt/Poincare and the snapshot; git grep -l codim1_oriented_rep over all 1193 distinct ref commits -- 'GMT/*.lean'`
- `lean -DautoImplicit=false /tmp/opm-decomp-check/Check.lean and /tmp/opm-decomp-check/CheckAx.lean with #print axioms (LEAN_PATH from .lake/build/lib/lean/GMT/Ch07/Submission.trace)`
- `sed -n 220,242p and 750,772p book/chapter-06.txt (Simon 6.2.5 and 6.3.2(3))`
- `runtime.py: _solve_children, _existing_lean_name_problem, _accepted_checkpoint, _install_parent_supplied_child_handoff`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-ori-0059e6635e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-ori-0059e6635e/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-unit-or-24edf309fb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-lusin-covector-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-smooth-49478a38c9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1/decomposition-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/opm-decomp-check/Check.lean`
- `/tmp/opm-decomp-check/CheckAx.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`

Pins match.
- The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to the workspace HEAD and lake-packages mathlib.
- The snapshot lake-manifest pins simongmt 2b366308, equal to the installed package.
- Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Library.
- The snapshot Mathlib has no Lusin continuity theorem: only Lusin separation and Lusin–Souslin in Constructions/Polish/Basic.lean. Hence the reuse of the accepted dor_ims_lusin_continuousOn.
- It provides everything the new children use: enorm_integral_le_lintegral_enorm (Integral/Bochner/Basic.lean:333), integral_withDensity_eq_integral_toReal_smul (Bochner/ContinuousLinearMap.lean:318), lintegral_indicator (Lebesgue/Basic.lean:510), Measure.restrict_restrict (Restrict.lean:205), exists_measurable_superset_of_null (MeasureSpaceDef.lean:219), withDensity_apply / withDensity_absolutelyContinuous (WithDensity.lean:44/146), isBoundedBilinearMap_apply (BoundedLinearMaps.lean:391), Real.enorm_eq_ofReal_abs (Group/Real.lean:110), ENNReal.le_of_forall_nnreal_lt (ENNReal/Inv.lean:487) and image_eq_zero_of_notMem_tsupport.
- SimonGMT Chapter06/Mass.lean supplies massAdmissibleOn, massOn (sSup of ofReal T ω), le_massOn and covectorEuclideanNorm.

DAG.
- dor_ims_unitOrientation_dual, dor_ims_lusin_continuousOn and dor_ims_smooth_unit_approx are status accepted with candidate commits 9c8432cb0101, 83274ea8a2c7 and 89e4c45cd3c1. Their lean_statement strings are copied byte-for-byte. Their reviewed handoff proofs are copied verbatim; the accepted Lean proofs are in 57cebee2fbae:GMT/Ch07/Submission.lean.
- The accepted IMRep mass lemmas (dor_ims_massOn_le_measure, dor_ims_measure_le_massOn) do not apply to a real weight with a representation only on V.
- The new names codim1_oriented_rep_massOn_le_lintegral and codim1_oriented_rep_lintegral_le_massOn are free in dag.json (578 nodes), GMT/, SimonGMT, the snapshot and all 1193 distinct ref commits.
- runtime.py allows reuse of accepted checkpoints with identical types, and _install_parent_supplied_child_handoff returns early for them.

Lean.
- Check.lean elaborates all 5 child types after import GMT.Ch07.Submission. It fully proves both new children and the selected frozen theorem from them, exiting 0 with only the 3 reused stand-in sorries.
- CheckAx.lean shows the axioms are propext, Classical.choice, Quot.sound and the reused declarations only.

Book. chapter-06.txt lines 224–240 (6.2.5) and 755–770 (6.3.2(3)) are the cited sources.
