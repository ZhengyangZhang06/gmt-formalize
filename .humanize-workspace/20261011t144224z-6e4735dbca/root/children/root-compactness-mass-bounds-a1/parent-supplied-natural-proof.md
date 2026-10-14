# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.compactness_mass_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, Lemma 2.15 (p. 137) together with the paragraph printed immediately before it (“We also observe that if sup_q M_W(T_q) < ∞ for each open W ⊂⊂ U then by 2.7 the distribution convergence 2.13 is equivalent to weak convergence with respect to continuous forms with compact support ..., and hence by applying the standard Banach–Alaoglu theorem (in the Banach spaces M_n(W) = {T ∈ D_n(W) : M_W(T) < ∞}, W ⊂⊂ U) we deduce 2.15”). The printed argument is: uniform local mass bounds + separability give a weakly convergent subsequence (Banach–Alaoglu / diagonal argument), and the integral representation (2.7) turns convergence on smooth forms into convergence on continuous compactly supported forms. Below the printed argument is written out in numbered steps for the exact Lean statement (in which the conclusion about continuous forms is required for every measure representation in the sense of `IsMeasureRepresentation`). No erratum applies.

Conventions. ℝ^P = `Eucl P`, e_1,…,e_P the standard basis. D^n(U) = `TestFormOn U n` (smooth n-forms on ℝ^P with compact tsupport ⊆ U), D_n(U) = `GeometricCurrentOn U n`. For an n-covector α let |α| := `covectorEuclideanNorm α` = (Σ_{β∈I(n,P)} α(e_β)²)^{1/2} (I(n,P) = strictly increasing multi-indices, e_β = (e_{β_1},…,e_{β_n})), and for a form ω let ‖ω‖ := sup_x |ω(x)|. For an n-vector w ∈ `NVector (Eucl P) n` (a continuous linear functional on n-covectors) put w^β := w(dx^β), where dx^β = dx^{β_1}∧⋯∧dx^{β_n}, and |w| := (Σ_β (w^β)²)^{1/2}.
Fact A (coordinates). Every n-covector satisfies α = Σ_β α(e_β) dx^β (an alternating n-linear map is determined by its values on increasing tuples of basis vectors, and dx^β(e_γ) = δ_{βγ}). Hence w(α) = Σ_β α(e_β) w^β and, by Cauchy–Schwarz, |w(α)| ≤ |α|·|w|.

Proof.

1. (Exhaustion.) For i ≥ 1 let W_i := {x ∈ U : |x| < i and B̄_{1/i}(x) ⊆ U} (this avoids any convention for dist(x, ∅); if U = ℝ^P it is just the open ball of radius i). Each W_i is open; if x ∈ closure(W_i) then |x| ≤ i and B_{1/i}(x) ⊆ U (every y with |y−x| < 1/i satisfies |y − x_k| < 1/i for points x_k ∈ W_i close to x), so closure(W_i) is closed and bounded, hence compact, and closure(W_i) ⊆ W_{i+1} ⊆ U (B̄_{1/(i+1)}(x) ⊆ B_{1/i}(x)). Thus `CompactlyContainedOpen W_i U`; the W_i increase and ⋃_i W_i = U (U is open). Every compact K ⊆ U is contained in some W_i (open cover of K by an increasing sequence). Put C_i := sup_q M_{W_i}(T_q) < ∞ (hypothesis).

2. (Basic mass estimate.) If T ∈ D_n(U), W is any set and ω ∈ D^n(U) with tsupport ω ⊆ W, then |T(ω)| ≤ M_W(T)·‖ω‖. Indeed ‖ω‖ < ∞ (ω continuous with compact support). If ‖ω‖ = 0 then ω = 0 and T(ω) = 0. Otherwise ±ω/‖ω‖ lies in `massAdmissibleOn U n W`, so ENNReal.ofReal(±T(ω)/‖ω‖) ≤ M_W(T) by `GeometricCurrentOn.le_massOn`, which gives the claim (trivial if M_W(T) = ∞).

3. (Countable dense families.) Fix i. The set D_i := {ω ∈ D^n(U) : tsupport ω ⊆ W_i} is a subset of the separable metric space C(closure W_i ; Λ^n(ℝ^P)) with the sup norm built from |·| (continuous functions on a compact metric space with values in a finite-dimensional space form a separable Banach space), hence D_i is separable for ‖·‖. Choose a countable E_i ⊆ D_i which is ‖·‖-dense in D_i and put E := ⋃_i E_i, enumerated as η_1, η_2, … .

4. (Diagonal subsequence; Banach–Alaoglu step.) For η ∈ E_i, Step 2 gives |T_q(η)| ≤ C_i‖η‖ for all q, so (T_q(η_k))_q is a bounded real sequence for every k. By Bolzano–Weierstrass and Cantor's diagonal procedure there is a strictly increasing φ : ℕ → ℕ such that lim_q T_{φ(q)}(η_k) exists for every k.

5. (Convergence on every test form.) Let ω ∈ D^n(U). tsupport ω is compact and ⊆ U, so ω ∈ D_i for some i. Given ε > 0 pick η ∈ E_i with ‖ω − η‖ < ε; ω − η ∈ D_i. For all q, q′, by Step 2,
|T_{φ(q)}(ω) − T_{φ(q′)}(ω)| ≤ |T_{φ(q)}(ω−η)| + |T_{φ(q)}(η) − T_{φ(q′)}(η)| + |T_{φ(q′)}(η−ω)| ≤ 2C_iε + |T_{φ(q)}(η) − T_{φ(q′)}(η)|.
Hence (T_{φ(q)}(ω))_q is Cauchy; define T₀(ω) := lim_q T_{φ(q)}(ω).

6. (T₀ ∈ D_n(U) and T_{φ(q)} ⇀ T₀.) T₀ is linear as a pointwise limit of linear maps. Continuity: let ω_j → 0 in the sense of `TestFormOnConverges` (tsupports in one compact K ⊆ U, every iterated derivative → 0 uniformly on K). Choose i with K ⊆ W_i. By Step 2, |T_{φ(q)}(ω_j)| ≤ C_i‖ω_j‖ for all q, hence |T₀(ω_j)| ≤ C_i‖ω_j‖. Since ω_j → 0 uniformly on K and vanishes off K, and |α| ≤ (#I(n,P))^{1/2}·max_β|α(e_β)| ≤ (#I(n,P))^{1/2}·‖α‖_op, we get ‖ω_j‖ → 0, so T₀(ω_j) → 0. Thus T₀ is a `GeometricCurrentOn U n`, and `WeaklyConvergesOn (fun q => T (φ q)) T₀` holds by construction. By lower semicontinuity of mass (Simon 2.14; `WeaklyConvergesOn.massOn_le_liminf`), for every W ⊂⊂ U: M_W(T₀) ≤ liminf_q M_W(T_{φ(q)}) ≤ sup_q M_W(T_q) < ∞; in particular M_{W_i}(T₀) ≤ C_i.

7. (Representation lemma; this is the content of “by 2.7” in the printed text.) Let T ∈ D_n(U) with M_W(T) < ∞ for every W ⊂⊂ U and let (μ, v) satisfy `IsMeasureRepresentation T μ v`, i.e. for every ω ∈ D^n(U) the function x ↦ v(x)(ω(x)) is μ-integrable and T(ω) = ∫ v(x)(ω(x)) dμ(x).
 (a) For every compact K ⊆ U, x ↦ |v(x)| is μ-integrable on K and each v^β is a.e.-strongly measurable on K. Proof: take χ ∈ C_c^∞(ℝ^P) with 0 ≤ χ ≤ 1, χ = 1 on K, tsupport χ ⊆ U. For each β the form ω_β := χ·dx^β (constant covector times χ) lies in D^n(U) and v(x)(ω_β(x)) = χ(x)v^β(x) (Fact A). By hypothesis χv^β is μ-integrable, hence v^β is μ-integrable on K, and |v| ≤ Σ_β|v^β| is μ-integrable on K.
 (b) Let ω be a continuous n-form with compact support, tsupport ω ⊆ W where W is open with closure(W) compact ⊆ U. Then x ↦ v(x)(ω(x)) is μ-integrable and |∫ v(ω) dμ| ≤ M_W(T)‖ω‖. Proof: measurability and integrability follow from v(x)(ω(x)) = Σ_β ω(x)(e_β)v^β(x) and |v(ω)| ≤ ‖ω‖|v|1_{tsupport ω} with (a). Choose δ > 0 such that the closed δ-neighbourhood K′ of tsupport ω lies in W. Let ϕ be a smooth mollifier (ϕ ≥ 0, ∫ϕ = 1, spt ϕ ⊆ B_1(0)), ϕ_ε(x) = ε^{−P}ϕ(x/ε), and for 0 < ε < δ let ω_ε := ϕ_ε * ω (convolution of each coefficient function x ↦ ω(x)(e_β), equivalently of the covector-valued function). Then ω_ε is smooth, tsupport ω_ε ⊆ K′ ⊆ W (so ω_ε ∈ D^n(U)), |ω_ε(x)| ≤ ∫|ω(x−y)|ϕ_ε(y)dy ≤ ‖ω‖ (convexity of the Euclidean norm on coefficient vectors), and ω_ε → ω uniformly as ε ↓ 0 (uniform continuity of ω). By Step 2, |∫ v(ω_ε)dμ| = |T(ω_ε)| ≤ M_W(T)‖ω‖. By dominated convergence (dominating function ‖ω‖·|v|·1_{K′}, integrable by (a)), ∫v(ω_ε)dμ → ∫v(ω)dμ. Hence |∫ v(ω)dμ| ≤ M_W(T)‖ω‖.
 The same mollification shows: every such ω is a uniform limit of test forms ω_ε ∈ D^n(U) with tsupport ω_ε ⊆ W.

8. (Convergence on continuous compactly supported forms.) Let ω : ℝ^P → Λ^n(ℝ^P) be continuous with compact support and tsupport ω ⊆ U, and let (μ_q, v_q), (μ₀, v₀) be representations of T_{φ(q)} and T₀. Choose i with tsupport ω ⊆ W_i and put W := W_{i+1} (so closure(W_i) ⊆ W ⊂⊂ U). Let ε > 0. By Step 7 there is a test form η ∈ D^n(U) with tsupport η ⊆ W and ‖ω − η‖ ≤ ε; ω − η is continuous with compact tsupport ⊆ W. Since all integrands are integrable (Step 7(b)) the integrals are linear, and by Step 7(b) together with T_{φ(q)}(η) = ∫v_q(η)dμ_q and T₀(η) = ∫v₀(η)dμ₀:
|∫v_q(ω)dμ_q − ∫v₀(ω)dμ₀| ≤ |∫v_q(ω−η)dμ_q| + |T_{φ(q)}(η) − T₀(η)| + |∫v₀(η−ω)dμ₀| ≤ C_{i+1}ε + |T_{φ(q)}(η) − T₀(η)| + M_W(T₀)ε.
Here M_W(T_{φ(q)}) ≤ C_{i+1} and M_W(T₀) ≤ C_{i+1} (Step 6). Since T_{φ(q)}(η) → T₀(η), limsup_q |∫v_q(ω)dμ_q − ∫v₀(ω)dμ₀| ≤ 2C_{i+1}ε; ε being arbitrary, ∫ v_q(ω) dμ_q → ∫ v₀(ω) dμ₀.

9. (Degenerate cases.) If U = ∅ every test form and every ω with tsupport ω ⊆ ∅ is 0; then any strictly increasing φ and T₀ := 0 satisfy all conclusions (all integrals vanish). Steps 1–8 also cover this case formally. This proves `CompactnessUnderMassBounds`.

## Key steps

1. Exhaust U by open W_i ⊂⊂ U with closure W_i ⊆ W_{i+1}; C_i := sup_q M_{W_i}(T_q) < ∞.
2. Mass estimate |T(ω)| ≤ M_W(T)‖ω‖ for tsupport ω ⊆ W (±ω/‖ω‖ is mass-admissible).
3. Choose countable sup-norm-dense families E_i of test forms supported in W_i (separability).
4. Diagonal (Bolzano–Weierstrass / Banach–Alaoglu) subsequence converging on all of E = ⋃E_i.
5. Cauchy argument extends convergence to every test form; define T₀ as the limit.
6. T₀ is linear and sequentially continuous (|T₀(ω)| ≤ C_i‖ω‖), and M_W(T₀) ≤ sup_q M_W(T_q) by 2.14.
7. Any IsMeasureRepresentation (μ,v) has |v| locally μ-integrable and |∫v(ω)dμ| ≤ M_W(T)‖ω‖ for continuous ω (mollification + dominated convergence).
8. Approximate continuous ω uniformly by test forms supported in W_{i+1} to get convergence of ∫v_q(ω)dμ_q to ∫v₀(ω)dμ₀.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n '^def |^structure |^theorem main_theorem' project/GMT/Ch06/Contract.lean`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean against GMT/Ch06/Submission.lean and against snapshot project/GMT/Ch06/Contract.lean (all byte-identical)`
- `python3 listing of dag.json nodes (only 'root'; no reserved child lean_name)`
- `python3 audit of nodes/root/decomposition-audit-v2.json and decomposition-v2.json (only deformation A3 rejected; search of all 12 proofs for 'θ′ ≥ 1', 'σ-finite', 'Radon–Nikodym', 'IsLipschitzPushforward', 'LipschitzPushforwardIntegerMultiplicity', 'as in the conventions')`
- `rg -n 'theorem sigmaFinite_of_countable' mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `rg -n 'theorem mul_meas_ge_le_lintegral₀' mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/`
- `rg -n 'theorem ae_eq_of_forall_setIntegral_eq_of_sigmaFinite|theorem Integrable.ae_eq_of_forall_setIntegral_eq' mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`
- `rg -n 'theorem hausdorffMeasure_image_le (h : LipschitzWith' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'theorem restrict_congr_set|theorem restrict_restrict [(]|theorem ae_restrict_iff.₀|theorem ae_restrict_mem₀' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -il 'coarea|co-area' mathlib/Mathlib/MeasureTheory (no match)`
- `rg -il 'Besicovitch.Federer|purely unrectifiable' mathlib/Mathlib/MeasureTheory (no match)`
- `rg -n 'def HasWeightedApproximateTangentSpaceAt|def blowUpMap|theorem HasWeightedApproximateTangentSpaceAt.unique|def CountablyRectifiable' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n 'abbrev NVector|def simpleNVector|def nVectorPushforward|theorem nVectorPushforward_simple|def covectorEuclideanNorm' simongmt/Poincare/SimonGMT/Chapter06/`
- `#print MeasureTheory.Measure.euclideanHausdorffMeasure (μHE[d] = volume.addHaarScalarFactor μH[d] • μH[d])`
- `grep -n '1.12|1.15|Borel-regular|3.19|3.24' book/chapter-01.txt`
- `lake build GMT.Ch06.Submission (scratch /tmp/gmt_ch06_v3_check, frozen commit d8d46c9, pinned packages)`
- `lake env lean Scratch/V3_Stmts.lean (12 child statements in gmt-compare.py contract_scope; 0 errors)`
- `lake env lean Scratch/V3_Assembly.lean (exact Submission.<name>; 12-way assembly vs type_of% GMT.Ch06.main_theorem; ff_from_siblings; parent_from_children; #print axioms)`
- `lake env lean Scratch/V3_SigmaFinite.lean (v3_sigmaFinite_restrict; #print axioms)`
- `lake env lean Scratch/V3_Tangent.lean (v3_weightedTangent_congr; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_Stmts.lean`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_Assembly.lean`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_SigmaFinite.lean`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_Tangent.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract, a byte-identical Submission with no Submission.* declarations, and the README. The DAG contains only root, so the 12 bare child names are unreserved. All 12 conjuncts are `def … : Prop` in namespace GMT.Ch06. In a scratch build of the frozen project, every child statement elaborates in the comparator's child scope, `exact Submission.<name>` resolves for all 12 children, and the 12-way assembly typechecks against `type_of% GMT.Ch06.main_theorem`. FedererFlemingCompactness follows from its three declared siblings and the parent from the other 11 children, with axioms [propext, Classical.choice, Quot.sound]. The contract's `IsLipschitzPushforward` supplies only an `IsRectifiableTriple` representation (θ′ > 0 real, integrable on compacts), confirming the v2 defect. The repaired deformation A3 uses only that. Its σ-finiteness step is kernel-checked as `v3_sigmaFinite_restrict` (via Mathlib `Measure.sigmaFinite_of_countable`, `mul_meas_ge_le_lintegral₀`, `Measure.restrict_restrict`, `ae_restrict_mem₀`), and its tangent-space step as `v3_weightedTangent_congr`, against the actual SimonGMT `HasWeightedApproximateTangentSpaceAt`/`blowUpMap` definitions (via `LipschitzWith.hausdorffMeasure_image_le`, `Measure.restrict_congr_set`, `ae_restrict_iff'₀`; μHE[d] is a scalar multiple of μH[d]), both with standard axioms only. Mathlib provides Radon–Nikodym-type uniqueness (`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`, `Integrable.ae_eq_of_forall_setIntegral_eq`). SimonGMT provides `nVectorPushforward_simple`, `covectorEuclideanNorm` and `HasWeightedApproximateTangentSpaceAt.unique`. Simon Ch. 1 gives 1.12 (μ⌞Y is Borel regular for measurable Y of finite measure), 1.15(2) (inner regularity) and 2.6 (H^m is Borel regular), as cited. There is no Mathlib match for co-area or for Besicovitch–Federer/purely unrectifiable; these are cited from Simon Ch. 3, as SimonGMT omits them. These checks do not certify the analytic proofs.
