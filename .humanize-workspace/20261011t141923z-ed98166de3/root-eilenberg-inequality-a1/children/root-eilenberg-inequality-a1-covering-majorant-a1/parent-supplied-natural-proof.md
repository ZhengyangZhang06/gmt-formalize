# Parent-supplied natural-language proof

- Parent DAG node: `root.eilenberg_inequality-a1`
- Child DAG node: `root.eilenberg_inequality-a1.covering_majorant-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the covering half of the printed proof of Simon, Introduction to GMT, Ch. 2, Theorem 1.9 (pp. 45-46), in the completed form of the parent proof (Part II, Step 1, items 1-6). Printed text (cleaned transcription): 'For each i = 1, 2, ... pick closed subsets C_{i1}, C_{i2}, ... with diam C_{ij} < 1/i, A ⊆ ∪_j C_{ij} and (1) Σ_j ω_{m+k}(diam C_{ij}/2)^{m+k} ≤ H^{m+k}_{1/i}(A) + 1/i, and let g_i = Σ_j ω_k (diam C_{ij}/2)^k χ_{f(C_{ij})} ... (2) g_i(y) = Σ_{j : f⁻¹y ∩ C_{ij} ≠ ∅} ω_k(diam C_{ij}/2)^k ≥ H^k_{1/i}(A ∩ f⁻¹y), and hence ... ∫* H^k_{1/i}(A ∩ f⁻¹y) dLᵐ(y) ≤ ∫ g_i dLᵐ = Σ_j ω_k (diam C_{ij}/2)^k Lᵐ(f(C_{ij})) ≤ Σ_j ω_k ω_m (Lip f)^m (diam C_{ij}/2)^{m+k} ≤ (ω_mω_k/ω_{m+k})(Lip f)^m (H^{m+k}_{1/i}(A) + 1/i), where we used Lᵐ(f(C_{ij})) ≤ ω_m(diam f(C_{ij})/2)^m (isodiametric inequality 2.10) ≤ ω_m (Lip f)^m (diam C_{ij}/2)^m. Letting i → ∞ we conclude ...'. Documented corrections carried over from the parent proof: (a) f(C_{ij}) need not be Borel, so the indicator of the closed set closure f(C_{ij} ∩ E), which has the same diameter, is used instead; (b) instead of the upper integral ∫* of Remark 1.10, an explicit Borel majorant G := liminf_i g_i is built and Fatou's lemma is applied. The isodiametric inequality 2.10 is the kernel-checked SimonGMT theorem `Poincare.SimonGMT.Chapter01.simon_theorem_2_10 (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) : volume A ≤ realUnitBallVolume (n : ℝ) * (ediam A / 2) ^ (n : ℝ)` (valid for every n, including n = 0, and every set A); it lives in `Poincare.SimonGMT.Chapter01.EuclideanNormalization`, which must be imported (it is not imported by the frozen contract). No other erratum.

Conventions used below. (C1) All diameters are extended diameters ediam (Mathlib `Metric.ediam`, `ediam ∅ = 0`); `LipschitzOnWith K f E` means edist (f x) (f x') ≤ K·edist x x' for all x, x' ∈ E. (C2) For d ∈ ℝ, r ∈ (0,∞] and F ⊆ X put pre^d_r(F) := inf { Σ_{n∈ℕ} [t_n ≠ ∅](ediam t_n)^d : t : ℕ → Set X, F ⊆ ⋃_n t_n, ediam t_n ≤ r for all n }, where [t ≠ ∅]x := ⨆ (_ : t.Nonempty), x (that is, x if t ≠ ∅ and 0 if t = ∅). Mathlib's `MeasureTheory.Measure.hausdorffMeasure_apply` states exactly μH[d](F) = ⨆_{r>0} pre^d_r(F) for every F ⊆ X (no measurability needed). If 0 < r ≤ r' then pre^d_{r'}(F) ≤ pre^d_r(F), because every cover admissible at scale r is admissible at scale r'; in particular pre^d_r(F) ≤ μH[d](F) for every r > 0. (C3) For d ≥ 0 put c_d := ω_d/2^d, where ω_d = Chapter01.realUnitBallVolume d. Since 0 < ω_d < ∞ (`Chapter01.realUnitBallVolume_pos`, `Chapter01.realUnitBallVolume_ne_top`) and 0 < 2^d < ∞, we have 0 < c_d < ∞, and 𝓗^d(F) = c_d·μH[d](F) for every F ⊆ X (unfold `Chapter01.simonHausdorffMeasureReal d = (ω_d / 2^d) • μH[d]` and use `Measure.smul_apply`, `smul_eq_mul`). (C4) Fix the data of the statement and put s := m + k > 0, M := μH[s](E), c := ω_m ω_k/ω_s and a := ω_m ω_k K^m / 2^s. All of ω_m, ω_k, ω_s, K^m, 2^s are finite and ω_s, 2^s are nonzero, so c < ∞ and a < ∞.

Proof.
1. (Constant identity.) c·K^m·𝓗^s(E) = a·M. Indeed 𝓗^s(E) = (ω_s/2^s)·M by (C3), and (ω_mω_k/ω_s)·K^m·(ω_s/2^s) = ω_mω_kK^m/2^s = a because the factor ω_s ∈ (0,∞) cancels (ENNReal: `ENNReal.div_mul_cancel`/`ENNReal.mul_div_cancel` with ω_s ≠ 0, ω_s ≠ ⊤, plus commutativity and associativity).
2. (Finiteness.) 𝓗^s(E) = c_s·M < ∞ and c_s ≠ 0 give M < ∞. Hence pre^s_r(E) ≤ M < ∞ for every r > 0 by (C2).
3. (Near-optimal covers.) For i ∈ ℕ put δ_i := ε_i := 1/(i+1) ∈ (0,1] (as elements of ℝ≥0∞, (i+1)⁻¹). Because pre^s_{δ_i}(E) < ∞ and ε_i > 0, pre^s_{δ_i}(E) < pre^s_{δ_i}(E) + ε_i, so by the definition of the infimum (`iInf_lt_iff`) there is a sequence (C_{i,l})_{l∈ℕ} of subsets of X with E ⊆ ⋃_l C_{i,l}, ediam C_{i,l} ≤ δ_i for all l, and Σ_l [C_{i,l} ≠ ∅](ediam C_{i,l})^s ≤ pre^s_{δ_i}(E) + ε_i ≤ M + ε_i. Choose such a sequence for every i.
4. (Trimmed pieces.) Put D_{i,l} := C_{i,l} ∩ E and d_{i,l} := ediam D_{i,l}. Then d_{i,l} ≤ ediam C_{i,l} ≤ δ_i ≤ 1, so d_{i,l} < ∞. Because s > 0 we have d_{i,l}^s ≤ [C_{i,l} ≠ ∅](ediam C_{i,l})^s: if D_{i,l} = ∅ the left side is 0^s = 0; otherwise C_{i,l} ≠ ∅ and t ↦ t^s is monotone. Summing over l and using step 3: (★) Σ_l d_{i,l}^s ≤ M + ε_i.
5. (Image closures.) Put T_{i,l} := closure (f '' D_{i,l}) ⊆ ℝᵐ, a closed and therefore Borel set. For x, x' ∈ D_{i,l} ⊆ E, edist (f x) (f x') ≤ K·edist x x' ≤ K·d_{i,l}; hence ediam (f '' D_{i,l}) ≤ K·d_{i,l} (`Metric.ediam_le`), and since a closure has the same diameter (`Metric.ediam_closure`), ediam T_{i,l} ≤ K·d_{i,l}.
6. (Borel functions g_i.) Define g_i : ℝᵐ → [0,∞] by g_i(y) := Σ_{l∈ℕ} 1_{T_{i,l}}(y)·c_k·d_{i,l}^k (a tsum of `Set.indicator (T_{i,l}) (fun _ ↦ c_k * d_{i,l} ^ k)`). Each summand is a constant times the indicator of a closed set, hence Borel, and a countable sum of Borel [0,∞]-valued functions is Borel (`Measurable.ennreal_tsum`, deprecated but available; or `Measurable.tsum` from `Mathlib.MeasureTheory.Constructions.Polish.Basic`). So every g_i is measurable.
7. (Pointwise bound at scale δ_i.) Fix y ∈ ℝᵐ and put F_y := E ∩ f⁻¹{y}. The sets t_l := D_{i,l} ∩ f⁻¹{y} (l ∈ ℕ) cover F_y (a point x ∈ F_y lies in E ⊆ ⋃_l C_{i,l}), satisfy ediam t_l ≤ d_{i,l} ≤ δ_i, and if t_l ≠ ∅ then y = f(x) for some x ∈ D_{i,l}, so y ∈ f '' D_{i,l} ⊆ T_{i,l}. Therefore [t_l ≠ ∅](ediam t_l)^k ≤ 1_{T_{i,l}}(y)·d_{i,l}^k for every l (k > 0, monotonicity of t ↦ t^k), and by (C2) pre^k_{δ_i}(F_y) ≤ Σ_l 1_{T_{i,l}}(y)·d_{i,l}^k. Multiplying by c_k (`ENNReal.tsum_mul_left`): c_k·pre^k_{δ_i}(F_y) ≤ g_i(y).
8. (Integral of g_i.) By the monotone convergence theorem for series (`lintegral_tsum`) and ∫⁻ 1_T·b dLᵐ = b·Lᵐ(T) for Borel T (`lintegral_indicator_const`), ∫⁻ g_i dLᵐ = Σ_l c_k·d_{i,l}^k·Lᵐ(T_{i,l}). By `simon_theorem_2_10` with n = m (rewrite the real exponent (m:ℝ) as the natural power m by `ENNReal.rpow_natCast`) and step 5, Lᵐ(T_{i,l}) ≤ ω_m·(ediam T_{i,l}/2)^m ≤ ω_m·(K·d_{i,l}/2)^m = ω_m·K^m·d_{i,l}^m/2^m (monotonicity of x ↦ (x/2)^m, `mul_pow`, `ENNReal.inv_pow`). Hence, writing d := d_{i,l} (finite), c_k·d^k·Lᵐ(T_{i,l}) ≤ (ω_k/2^k)·d^k·ω_m·K^m·d^m/2^m = (ω_mω_kK^m/2^{k+m})·d^{k+m} = a·d^s, using d^k·d^m = d^{k+m} (first rewrite the natural powers d^m and 2^m as real powers d^(m:ℝ), 2^(m:ℝ) with `ENNReal.rpow_natCast`; then `ENNReal.rpow_add_of_nonneg`, valid also for d = 0 since k ≥ 0 and (m:ℝ) ≥ 0), 2^k·2^(m:ℝ) = 2^{k+m} (`ENNReal.rpow_add`, as 2 ≠ 0, 2 ≠ ⊤) and k + m = m + k = s. (All factors are finite, so these identities may also be checked after passing to ℝ≥0.) Summing over l and using (★): (★★) ∫⁻ g_i dLᵐ ≤ a·Σ_l d_{i,l}^s ≤ a·(M + ε_i).
9. (The majorant.) Define G(y) := liminf_{i→∞} g_i(y) (`Filter.liminf (fun i ↦ g_i y) atTop`). G is Borel (`Measurable.liminf`).
10. (G dominates the fibre measures.) Fix y ∈ ℝᵐ and r ∈ (0,∞]. Choose i₀ with δ_{i₀} ≤ r (`ENNReal.exists_inv_nat_lt`). For every i ≥ i₀ we have δ_i ≤ δ_{i₀} ≤ r, so by (C2) and step 7, c_k·pre^k_r(F_y) ≤ c_k·pre^k_{δ_i}(F_y) ≤ g_i(y). Hence c_k·pre^k_r(F_y) ≤ ⨅_{i≥i₀} g_i(y) ≤ liminf_i g_i(y) = G(y). Taking the supremum over r > 0 and using (C3), (C2) and `ENNReal.mul_iSup`: 𝓗^k(E ∩ f⁻¹{y}) = c_k·⨆_{r>0} pre^k_r(F_y) = ⨆_{r>0} c_k·pre^k_r(F_y) ≤ G(y).
11. (Integral bound.) By Fatou's lemma (`lintegral_liminf_le`, all g_i measurable) and (★★), ∫⁻ G dLᵐ ≤ liminf_i ∫⁻ g_i dLᵐ ≤ liminf_i a·(M + ε_i). Since a < ∞, M < ∞ and ε_i = (i+1)⁻¹ → 0 (`ENNReal.tendsto_inv_nat_nhds_zero` composed with the shift i ↦ i + 1, e.g. via `tendsto_add_atTop_iff_nat 1`), a·(M + ε_i) → a·M (`ENNReal.Tendsto.const_mul`, `Tendsto.const_add`), so this liminf equals a·M (`Tendsto.liminf_eq`), which equals c·K^m·𝓗^s(E) by step 1. Hence ∫⁻ G dLᵐ ≤ (ω_mω_k/ω_{m+k})·K^m·𝓗^{m+k}(E).
12. (Conclusion.) G is measurable (step 9), dominates y ↦ 𝓗^k(E ∩ f⁻¹{y}) everywhere (step 10) and satisfies the integral bound (step 11). The argument is uniform in K ≥ 0 and m ∈ ℕ (K = 0 and m = 0 included), because simon_theorem_2_10 holds in every dimension and every identity used above holds for these values. ∎

## Key steps

1. Constant identity c·K^m·𝓗^{m+k}(E) = (ω_mω_kK^m/2^{m+k})·μH[m+k](E) and finiteness of μH[m+k](E).
2. For δ_i = ε_i = 1/(i+1) choose near-optimal covers C_{i,l} of E from hausdorffMeasure_apply; trimmed diameters d_{i,l} = ediam(C_{i,l} ∩ E) satisfy Σ_l d_{i,l}^{m+k} ≤ μH[m+k](E) + ε_i.
3. Borel functions g_i = Σ_l c_k d_{i,l}^k 1_{closure f(C_{i,l} ∩ E)} satisfy c_k·pre^k_{δ_i}(E ∩ f⁻¹{y}) ≤ g_i(y) for every y.
4. Isodiametric inequality (simon_theorem_2_10) and the Lipschitz diameter bound give ∫⁻ g_i ≤ (ω_mω_kK^m/2^{m+k})(μH[m+k](E) + ε_i).
5. G := liminf g_i is Borel, dominates 𝓗^k(E ∩ f⁻¹{y}) pointwise (sup over scales), and Fatou's lemma gives ∫⁻ G ≤ (ω_mω_k/ω_{m+k})K^m𝓗^{m+k}(E).

## Reference use

### local-project

Queries:
- `cat local-references/ff09f3909baeeae7/manifest.json (project 1b1689a8, mathlib 25730c7c)`
- `rg -n 'EilenbergInequality|Eilenberg' project`
- `rg -n -i 'eilenberg' mathlib/Mathlib`
- `rg -n -i 'coarea' mathlib/Mathlib`
- `rg -n 'hausdorffMeasure.*preimage|preimage.*hausdorffMeasure' mathlib/Mathlib`
- `grep -n '^end|^section|^noncomputable section|^namespace|^local notation|^theorem main_theorem' project/GMT/Ch02/Contract.lean`
- `rg -n 'theorem hausdorffMeasure_apply|theorem hausdorffMeasure_le_liminf_sum' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'theorem lintegral_liminf_le|theorem lintegral_tsum|theorem lintegral_indicator_const|theorem lintegral_eq_zero_iff' mathlib/Mathlib/MeasureTheory/Integral/Lebesgue`
- `rg -n 'theorem UpperSemicontinuous.measurable|theorem measurable_of_Iio|theorem Measurable.liminf|protected theorem Measurable.iSup|theorem Measurable.ennreal_tsum' mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace`
- `rg -n 'exists_isCompact_sdiff_lt|Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure|instance.*InnerRegularCompactLTTop' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n 'Monotone.measure_iUnion|measure_iUnion_eq_iSup' mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `rg -n 'ediam_image_le|ediam_closure|ediam_thickening_le' mathlib/Mathlib/Topology`
- `rg -n 'rpow_add_of_nonneg|div_rpow_of_nonneg' mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `rg -n 'theorem IsCompact.elim_finite_subcover|theorem IsCompact.diff|theorem IsCompact.image_of_continuousOn|theorem ContinuousOn.preimage_isClosed_of_isClosed' mathlib/Mathlib/Topology`
- `grep -n 'theorem|lemma' mathlib/Mathlib/Order/SetAccumulate.lean`
- `grep -rn 'simon_theorem_2_10|exists_isOpen_superset_ediam_rpow_lt|def simonHausdorffMeasureReal|def realUnitBallVolume|realUnitBallVolume_pos|realUnitBallVolume_ne_top' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01`
- `read lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/LipschitzMeasurability.lean and Chapter01/RegularityCompletion.lean (compact-approximation pattern)`
- `python3 -I gen_checks.py (imports verifier gmt-compare.py contract_scope/child_modules and lean_contract.validate_lean_statement) then lean NodeChallenge_00..02.lean, AssemblyCheck.lean, ExhaustionCheck.lean, Probe.lean against a scratch olean of GMT.Ch02.Submission built with plain `lean -o` (no lake build)`
- `#print axioms assembly_check / exhaustion_check; #print EilenbergInequality; #check child targets`
- `python3 -I: collect all lean_name values in dag.json and nodes/*/*.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Order/SetAccumulate.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/AlgebraicTopology/EilenbergSteenrod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/EuclideanNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffOpenCovers.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RegularityCompletion.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/LipschitzMeasurability.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/UpperIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/eilenberg-decomp-NyRDhV/checks/AssemblyCheck.lean`
- `/tmp/eilenberg-decomp-NyRDhV/checks/ExhaustionCheck.lean`
- `/tmp/eilenberg-decomp-NyRDhV/final/NodeChallenge_00.lean`

**No existing result.** No ready-made result exists in the snapshot:
- The 'eilenberg' matches in Mathlib are only the Eilenberg–Steenrod and Eilenberg–Schützenberger files.
- 'coarea' has no match.
- Hausdorff-measure preimage lemmas exist only for antilipschitz maps and isometries, with no fibre-measurability theorem.
- The project has only the frozen definition (Contract.lean:232) and README row 6.

**Contract scope.** In Contract.lean, a bare `end` at line 374 closes the noncomputable section holding the local notations 𝓗[·]/ω[·] (lines 51, 54) before main_theorem (line 377). The comparator replays that `end`, and the first draft statements were misparsed as GetElem on an auto-bound 𝓗. The final statements therefore spell out Chapter01.simonHausdorffMeasureReal and Chapter01.realUnitBallVolume; `open Poincare.SimonGMT` (line 43) is still in scope.

**Mathlib tools.**
- Hausdorff measure: hausdorffMeasure_apply (Hausdorff.lean:546; covers with ediam ≤ r and Nonempty-weighted cost) and hausdorffMeasure_le_liminf_sum (:563).
- Lebesgue integral: lintegral_liminf_le (Lebesgue/Add.lean:233), lintegral_tsum (Add.lean:362), lintegral_indicator_const (Basic.lean:541), lintegral_eq_zero_iff (Basic.lean:349).
- Measurability: UpperSemicontinuous.measurable (BorelSpace/Order.lean:649), Measurable.iSup (Order.lean:909), Measurable.liminf (Order.lean:1058), Measurable.ennreal_tsum (deprecated, BorelSpace/Real.lean:354).
- Regularity and continuity: MeasurableSet.exists_isCompact_sdiff_lt (Regular.lean:843), Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (Regular.lean:1183), Monotone.measure_iUnion (Continuity.lean:71; arbitrary sets).
- Metric and topology: ediam_thickening_le (Thickening.lean:354), Metric.ediam_closure (ENNReal/Lemmas.lean:649), LipschitzWith.ediam_image_le (Lipschitz.lean:171), IsCompact.elim_finite_subcover/diff/image_of_continuousOn (Compact.lean:208/101/110), ContinuousOn.preimage_isClosed_of_isClosed (ContinuousOn.lean:197).
- ENNReal powers and accumulate: ENNReal.rpow_add_of_nonneg (Pow/NNReal.lean:633), ENNReal.div_rpow_of_nonneg (NNReal.lean:769), plus the accumulate lemmas (SetAccumulate.lean).
- There is no LipschitzOnWith.ediam_image_le, so child 1 bounds diameters directly with Metric.ediam_le.

**SimonGMT (pinned package).**
- simonHausdorffMeasureReal s = (realUnitBallVolume s / 2^s) • μH[s] (Hausdorff.lean:283).
- realUnitBallVolume_pos and realUnitBallVolume_ne_top (Hausdorff.lean:499, 506).
- simon_theorem_2_10, the isodiametric inequality for every n and every set (EuclideanNormalization.lean:24). It is not imported by the contract, so the child must add the import; I verified the import works alongside GMT.Ch02.Submission.
- exists_isOpen_superset_ediam_rpow_lt (HausdorffOpenCovers.lean:29; optional, needs an import).
- LipschitzMeasurability.lean shows the same restrict/Regular compact-approximation pattern that child 3 uses.
- The UpperIntegral.lean tools are not needed.

**Lean verification.**
- All three child lean_statements elaborate in the replayed comparator scope.
- AssemblyCheck.lean derives `EilenbergInequality` from the three child types using only propext, Classical.choice and Quot.sound.
- ExhaustionCheck.lean proves child 3 outright with standard axioms only.

**Name collisions.** dag.json reserves only the 12 depth-1 names and GMT.Ch02.main_theorem, so the eilenberg_-prefixed names do not collide.
