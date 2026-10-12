# Parent-supplied natural-language proof

- Parent DAG node: `root.gauss_green-a1.riesz_on_open-a1`
- Child DAG node: `root.gauss_green-a1.riesz_on_open-a1.zero_extension_functional-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1-4 of the supplied proof of gaussGreenRep_riesz_on_open. These steps pass from ℝ^N to the locally compact space U, as needed to apply Simon Ch. 1, Theorem 4.14 in Simon Ch. 2, (2.1)-(2.2), chapter-02.txt lines 485-496. Let ι : U → ℝ^N be the inclusion; U carries the subspace topology. A field g : ℝ^N → ℝ^N is admissible if it is continuous, has compact support and tsupport g ⊆ U.

1. Topology. U is open, so ι is an open embedding. U and ℝ^N are Hausdorff. A set A ⊆ U is compact in U iff ι(A) is compact in ℝ^N (Subtype.isCompact_iff). For S ⊆ ℝ^N, ι(ι⁻¹(S)) = U ∩ S (Subtype.image_preimage_coe).

2. Zero extension. For f ∈ C_c(U; ℝ^N) let f̃ : ℝ^N → ℝ^N be its extension by zero: f̃(ι y) = f(y) for y ∈ U, and f̃(x) = 0 for x ∉ U. In Lean f̃ = Function.extend Subtype.val f 0; the two identities are Subtype.val_injective.extend_apply and Function.extend_apply', the latter because x ∉ U is not in the range of ι.
(a) Support. T := ι(tsupport f) is compact (continuous image of a compact set), hence closed in the Hausdorff space ℝ^N, and T ⊆ U. Since f̃ vanishes outside ι(support f) ⊆ T, we get tsupport f̃ ⊆ T ⊆ U (HasCompactSupport.tsupport_extend_zero_subset). In particular f̃ has compact support (HasCompactSupport.extend_zero).
(b) Continuity (HasCompactSupport.continuous_extend_zero, which uses that U is open). A function is continuous if it is continuous at each point of its topological support. Let x ∈ tsupport f̃ ⊆ T ⊆ U, say x = ι(y). On the open set U, f̃ agrees with f ∘ ι⁻¹, and f is continuous at y. Since ι is an open embedding, f̃ is continuous at x.
Hence f̃ is admissible.
(c) Linearity of the extension. For f, f' ∈ C_c(U; ℝ^N) and c ∈ ℝ: (f + f')~ = f̃ + f̃' and (c f)~ = c f̃. Pointwise check: at x = ι(y) both sides equal f(y) + f'(y), resp. c f(y); at x ∉ U both sides are 0.
(d) If |f(y)| ≤ 1 for all y ∈ U, then |f̃(x)| ≤ 1 for all x ∈ ℝ^N. On U the value is |f(y)|; off U it is 0.
(e) If tsupport f ⊆ K ⊆ U, then tsupport f̃ ⊆ ι(tsupport f) ⊆ ι(K), by (a).

3. Definition and linearity of L (Step 4). Put L(f) := Λ(f̃).
- Additivity: for f, f' ∈ C_c(U; ℝ^N), f̃ and f̃' are admissible (step 2). The additivity hypothesis and 2(c) give L(f + f') = Λ(f̃ + f̃') = Λ(f̃) + Λ(f̃') = L(f) + L(f').
- Homogeneity: for c ∈ ℝ, the homogeneity hypothesis and 2(c) give L(c f) = Λ(c f̃) = c Λ(f̃) = c L(f).
So L is ℝ-linear.

4. The local bound (i) (Step 4). Let K ⊆ U be compact in U. Then ι(K) is compact in ℝ^N (continuous image) and ι(K) ⊆ U. The bound hypothesis gives C ∈ ℝ with Λ(g) ≤ C for every continuous g with tsupport g ⊆ ι(K) and |g| ≤ 1 everywhere. Let f ∈ C_c(U; ℝ^N) with |f| ≤ 1 on U and tsupport f ⊆ K. Then g := f̃ is continuous (2(b)), tsupport f̃ ⊆ ι(K) (2(e)) and |f̃| ≤ 1 (2(d)). Hence L(f) = Λ(f̃) ≤ C.

5. Restriction (Step 3). Let g be admissible and put f₀ := g ∘ ι : U → ℝ^N, which is continuous.
- K₀ := ι⁻¹(tsupport g) is compact in U by step 1: ι(K₀) = U ∩ tsupport g = tsupport g, which is compact because tsupport g ⊆ U.
- If y ∉ K₀ then ι(y) ∉ tsupport g, so f₀(y) = g(ι y) = 0 (image_eq_zero_of_notMem_tsupport).
- So f₀ vanishes outside the compact K₀ and has compact support (HasCompactSupport.intro; U is Hausdorff).
Thus f := f₀ ∈ C_c(U; ℝ^N) and f(y) = g(ι y) for all y ∈ U.

6. f̃ = g. For x = ι(y) ∈ U: f̃(x) = f(y) = g(x). For x ∉ U: f̃(x) = 0, and x ∉ tsupport g (as tsupport g ⊆ U), so g(x) = 0. Hence f̃ = g and L(f) = Λ(f̃) = Λ(g).

7. Conclusion. L is ℝ-linear (step 3) and satisfies the local bound (i) (step 4). For every admissible g, the f of step 5 satisfies f(y) = g(y) for all y ∈ U and L(f) = Λ(g) (step 6). This is (ii).

## Key steps

1. For f ∈ C_c(U; ℝ^N) the zero extension f̃ = extend ι f 0 is continuous because U is open. It satisfies tsupport f̃ ⊆ ι(tsupport f) ⊆ U, so it is admissible; it is linear in f and preserves |·| ≤ 1.
2. L(f) := Λ(f̃) is ℝ-linear by the additivity and homogeneity of Λ on admissible fields.
3. For compact K ⊆ U, ι(K) is a compact subset of ℝ^N inside U. The bound for Λ on unit fields supported in ι(K) bounds L on unit fields supported in K.
4. For admissible g, the restriction g ∘ ι vanishes off the compact set ι⁻¹(tsupport g), so it lies in C_c(U; ℝ^N). Its zero extension is g, hence L(g ∘ ι) = Λ(g).

## Reference use

### local-project

Queries:
- `diff local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean workspaces/gmt-ch03/GMT/Ch03/Contract.lean (identical); grep -n -i 'unfaithful|Riesz|4.14|### 11' project/GMT/Ch03/README.md`
- `python3 transitive import scan of Poincare.SimonGMT.Chapter02.BV + Chapter03.Rectifiable (Submission imports): only Chapter01.{Basic,Hausdorff,MetricCriterion}; ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter01 (RadonPolarRepresentation.olean present)`
- `grep -n 'theorem simon_theorem_4_14' -A 60 Poincare/SimonGMT/Chapter01/*.lean`
- `sed -n 1,135p RadonPolarRepresentation.lean; sed -n 1,120p,200,280p VectorFunctionalEnvelope.lean; cat RadonCaratheodoryIntegral.lean`
- `grep -rn 'exists_borel_subset_mod_null|isOpenSigmaFinite_of_finite_compacts|measure_toOuterMeasure_isBorelRegular|def IsOpenSigmaFinite|def IsBorelRegularOuterMeasure|structure IsRadonOuterMeasure|toCaratheodoryMeasure_apply_all' Poincare/SimonGMT; grep -n 'IsCaratheodoryMeasurable' Chapter01/Basic.lean`
- `rg -n 'NullMeasurable.aemeasurable|theorem integral_map|aestronglyMeasurable_map_iff|ae_map_iff|subtype_coe|measurable_extend|map_apply' mathlib/Mathlib/MeasureTheory/{Measure/AEMeasurable,Integral/Bochner/Basic,Function/StronglyMeasurable/AEStronglyMeasurable,MeasurableSpace/Embedding,Measure/Map}.lean`
- `rg -n 'continuous_extend_one|continuous_extend_zero|extend_zero|extendByZero|continuous_of_mulTSupport' mathlib/Mathlib/Topology; sed -n 280,365p Mathlib/Topology/Algebra/Support.lean`
- `rg -n 'theorem IsOpen.locallyCompactSpace|sigmaCompactSpace_of_locallyCompact_secondCountable|instance Subtype.borelSpace|theorem Subtype.isCompact_iff' mathlib/Mathlib`
- `sed -n 1640,1760p book/chapter-01.txt (Thm 4.14 at line 1654); sed -n 480,500p book/chapter-02.txt`
- `sed -n 1,80p,520,570p verifier/gmt-compare.py; cat verifier/lean_contract.py (child_modules, contract_scope, validate_lean_statement)`
- `python3: lean_contract.validate_lean_statement on the 4 statements; grep -rl candidate lean_names over the run directory; dag.json lean_name scan`
- `lake env lean /tmp/riesz_decomp/gen/ChallengeCheck.lean (exact NodeChallenge forms, pp.explicit #check, assembly from A2,B,C, #print axioms)`
- `lake env lean /tmp/riesz_decomp/gen/ProofCheck.lean (Submission-style proofs of the 4 children and the parent, exact Submission.X checks, #print axioms)`
- `WebSearch: Evans Gariepy vector-valued Riesz representation §1.8; Folland Proposition 2.12 completion-measurable functions a.e. equal measurable`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonCaratheodoryIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonOuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RegularityCompletion.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-riesz-on-open-a1/parent-child-handoff.json`

Snapshot state: project d09bc8a with Contract.lean identical to the workspace contract, Mathlib 25730c7c, pinned simongmt. No declaration proves the selected statement or any of the four child statements.

SimonGMT supplies the following:
- Simon 4.14 only in Carathéodory form: simon_theorem_4_14_caratheodory, with vectorFunctionalEnvelopeMeasure (Regular), IsLocallyBoundedCcFunctional, radonCaratheodoryMeasure_apply, ae_radonCaratheodoryMeasure_iff and integral_radonCaratheodoryMeasure (used by child riesz_sigma_compact).
- The Borel-regularity tools measure_toOuterMeasure_isBorelRegular, isOpenSigmaFinite_of_finite_compacts and IsBorelRegularOuterMeasure.exists_borel_subset_mod_null (child caratheodory_borel_version). IsCaratheodoryMeasurable is an abbrev for Mathlib's OuterMeasure.IsCaratheodory.
- These modules are not imported by GMT.Ch03.Submission, but their oleans are built. A child proof may add `import Poincare.SimonGMT.Chapter01.RadonPolarRepresentation`, as earlier proved nodes added SimonGMT imports. The frozen statements use only Mathlib notions, so they elaborate with or without that import.
- README section 11 flags only Chapter03.FinitePerimeterRepresentation (not used). No SimonGMT Chapter01 Riesz definition is marked unfaithful.

Mathlib supplies the following:
- Zero extension from an open set: HasCompactSupport.continuous_extend_zero, tsupport_extend_zero_subset, extend_zero and HasCompactSupport.intro (child zero_extension_functional).
- Push-forward: MeasurableEmbedding.subtype_coe, map_apply (valid on all sets), ae_map_iff, aestronglyMeasurable_map_iff and integral_map (child pushforward_from_subset).
- NullMeasurable.aemeasurable (child caratheodory_borel_version).
- For the parent assembly: IsOpen.locallyCompactSpace, the instance sigmaCompactSpace_of_locallyCompact_secondCountable, and Subtype.borelSpace.

No match: Mathlib and SimonGMT have no Riesz theorem with a Borel unit field on σ-compact spaces and no ambient push-forward of a Riesz pair from an open subset. These are therefore supplied as children.

Checks run:
- All four frozen statements pass validate_lean_statement and elaborate in the exact NodeChallenge form.
- The assembly A2 + B + C ⇒ parent compiles.
- Complete Submission-style proofs of all four children and the parent compile with only propext, Classical.choice and Quot.sound.
- Public references: Simon Ch. 1 Thm 4.14 (chapter-01.txt 1654-1663) and Ch. 2 (2.1)-(2.2) (chapter-02.txt 485-496); Evans–Gariepy §1.8; Folland Prop. 2.12.
