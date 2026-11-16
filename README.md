# Lean-in-Lean: Complete 9-Layer Formal Verification of Lean 4 in Lean 4

**100% Machine-Checked in Lean 4 (v4.35.0) — 3,907 Lines • 78 Formal Theorems • 0 `sorry`s • 0 Custom Axioms • 0 `ofReduceBool` Circularity**

This repository contains a self-contained, dependency-free formalization and soundness/memory-safety audit of **both the Lean 4 C++ Core Kernel (`src/kernel/`) and the 8 surrounding Full-Stack Subsystems** of Lean 4.35.0:

1. **Layer 1 — Pratt Parser & Operator Precedence** ([`LeanInLean/FrontendAndMeta.lean`](LeanInLean/FrontendAndMeta.lean#L18-L203) ↔ [`Parser_Basic.lean`](audited_sources/full_stack/Parser_Basic.lean#L160-L210)): `checkPrec` / `checkLhsPrec` monotonicity, right-associativity of `→` vs. left-associativity of `+`, and constructive proof of the **Operator Spoofing Paradox** (`(False → (False → False)) ↔ True` vs. `((False → False) → False) ↔ False`).
2. **Layer 2 — Beyond-Notations Hygienic Macro Expansion** ([`LeanInLean/FrontendAndMeta.lean`](LeanInLean/FrontendAndMeta.lean#L206-L382) ↔ [`Hygiene.lean`](audited_sources/full_stack/Hygiene.lean#L41-L114)): monotonic `MacroScope` freshness, `eraseMacroScopes` stem recovery, **zero accidental variable capture** for arbitrary surface antiquotations, and 0-axiom unhygienic capture refutation.
3. **Layer 3 — `MetaM` Metavariables, Scoping, Depth & Unification** ([`LeanInLean/FrontendAndMeta.lean`](LeanInLean/FrontendAndMeta.lean#L385-L658) ↔ [`MetavarContext.lean`](audited_sources/full_stack/MetavarContext.lean#L95-L152), [`ExprDefEq.lean`](audited_sources/full_stack/ExprDefEq.lean#L1015-L1071)): enforces all four `CheckAssignment` barriers (transitive occurs check, `lctx` free-variable scope check, `mctx.depth` read-only isolation, `syntheticOpaque` subgoal protection), proves exact lowering to `KExpr`, and proves `?0 := ?0` diverges for every `fuel : Nat`.
4. **Layer 4 — Tabled Typeclass Synthesis & Coherence** ([`LeanInLean/FrontendAndMeta.lean`](LeanInLean/FrontendAndMeta.lean#L661-L900) ↔ [`SynthInstance.lean`](audited_sources/full_stack/SynthInstance.lean#L30-L140)): full inductive soundness of memoized tabled resolution, clean termination on `Coe A B`/`Coe B A` 2-cycles, diamond subgoal sharing, and 0-axiom coherence of `Prop` and `[Subsingleton C]` instances.
5. **Layer 5 — Core Calculus of Inductive Constructions Kernel** ([`LeanInLean/CoreKernel.lean`](LeanInLean/CoreKernel.lean#L1-L953) ↔ [`audited_sources/kernel/`](audited_sources/kernel/)): exact `mk_imax` universe laws, bidirectional `kernelInferType Γ e = some T ↔ HasType Γ e T`, type uniqueness, $\beta$-subject reduction, Boolean inhabitance consistency (`∀ p, kernelInferType [] p ≠ some False`), **Gödel-stratified bounded self-verification** (`Lean_u` verified in `Lean_{u+1}`), `checkPositivity`, `elimOnlyAtUniverseZero`, `DefEq` conversion consistency, and `Quot.lift` coherence—plus **5 constructive derivations of `False`** if any kernel guard is omitted.
6. **Layer 6 — `.olean` Compacted Regions, Flat DAGs & `LeanChecker` Replay** ([`LeanInLean/RuntimeAndOlean.lean`](LeanInLean/RuntimeAndOlean.lean#L385-L1150) ↔ [`CompactedRegion.lean`](audited_sources/full_stack/CompactedRegion.lean#L27-L50), [`Replay.lean`](audited_sources/full_stack/Replay.lean#L46-L191), [`LeanChecker.lean`](audited_sources/full_stack/LeanChecker.lean#L17-L91)): pointer relocation bijection, exact `KExpr` flat-region serialize/deserialize round-trip, global consistency of `runFreshReplay`, deterministic cycle rejection (`A := A`, `A ↔ B`) via `Replay.lean`'s `remaining`/`pending` split, and necessity of `checkPostponedRecursors`.
7. **Layer 7 — LCNF Phase 1: Proof, Type & Quotient Erasure (`ToMono`)** ([`LeanInLean/CompilerAndRC.lean`](LeanInLean/CompilerAndRC.lean#L16-L416) ↔ [`ToMono.lean`](audited_sources/full_stack/ToMono.lean#L30-L110)): zero-cost erasure of `Type`, `Prop`, `Quot.mk`, and 1-field structures; full forward simulation `evalMono (toMono e) = eraseVal (evalFull e)`; and 0-axiom **Kernel-to-Compiler Bridge** proving `Or : Prop → Bool` large elimination breaks compiler erasure.
8. **Layer 8 — LCNF Phase 2: Perceus Reference Counting, Borrows & `Reset`/`Reuse`** ([`LeanInLean/CompilerAndRC.lean`](LeanInLean/CompilerAndRC.lean#L419-L735) ↔ [`ResetReuse.lean`](audited_sources/full_stack/ResetReuse.lean#L70-L126), [`ExpandResetReuse.lean`](audited_sources/full_stack/ExpandResetReuse.lean#L20-L109), [`InferBorrow.lean`](audited_sources/full_stack/InferBorrow.lean#L20-L49)): `mayReuse` memory-footprint safety, `rc = 1` **zero-allocation in-place mutation** (hot path), `rc ≥ 2` **copy-on-write alias preservation** (cold path), `ExpandResetReuse.lean:93` duplicate-projection `mask[i]` double-free prevention, and `@&` borrow lifetime safety.
9. **Layer 9 — 64-Bit Tagged `lean.h` C Runtime, 32-Bit Sticky RC Band & `native_decide`** ([`LeanInLean/RuntimeAndOlean.lean`](LeanInLean/RuntimeAndOlean.lean#L24-L382) ↔ [`lean.h`](audited_sources/full_stack/lean.h#L348-L727), [`Native.lean`](audited_sources/full_stack/Native.lean#L37-L87)): **zero-circularity pure kernel `BitVec 64` & `BitVec 32` proofs** (no `bv_decide` / `Lean.ofReduceBool` axioms!) certifying 63-bit `lean_box`/`lean_unbox` round-trip, 8-byte aligned pointer disjointness, 1-instruction unsigned `lean_is_unstuck_mt` classification across all $2^{32}$ states, `INT_MAX` RC overflow freeze into `LEAN_RC_STICKY` without Use-After-Free, PAP closure currying, and `nativeEqTrue` (`native_decide`) TCB soundness.

---

## PDF Reports & Technical Guides

- 📄 [**Lean 4 Core Kernel Correctness & Gödel Stratification (PDF)**](docs/Lean4_Kernel_Correctness_and_Formal_Proof.pdf) • [Markdown Guide](docs/KERNEL_VERIFICATION_GUIDE.md)
- 📄 [**Proving All of Lean 4 — Complete 9-Layer Full-Stack Report (PDF)**](docs/Lean4_Full_Stack_Formal_Proof.pdf) • [Markdown Guide](docs/FULL_STACK_VERIFICATION_GUIDE.md)

---

## Architecture Overview

```mermaid
flowchart LR
    subgraph Frontend["I. Frontend & Elaboration (FrontendAndMeta.lean)"]
        P["1. Pratt Parser<br/>Parser_Basic.lean:160-210"] --> H["2. Macro Hygiene<br/>Hygiene.lean:41-114"]
        H --> M["3. MetaM Unifier<br/>ExprDefEq.lean:1015-1071"]
        M <--> TC["4. Tabled Typeclasses<br/>SynthInstance.lean:30-140"]
    end
    subgraph KernelImport["II. Kernel & .olean Replay"]
        M -->|"instantiateMVars"| K["5. Core CIC Kernel<br/>CoreKernel.lean (src/kernel/)"]
        K <--> O["6. .olean DAG & Replay<br/>RuntimeAndOlean.lean"]
    end
    subgraph Backend["III. Compiler, Perceus RC & C Runtime"]
        K --> E["7. LCNF ToMono Erasure<br/>CompilerAndRC.lean"]
        E --> RC["8. Perceus RC & Reset/Reuse<br/>CompilerAndRC.lean"]
        RC --> RT["9. C Runtime & Sticky RC<br/>lean.h + Native.lean"]
    end
    RT -.->|"native_decide (e = Bool.true)"| K
```

---

## Quick Start & Reproducible Verification

Requires Lean `v4.35.0` (automatically selected via [`lean-toolchain`](lean-toolchain) if [`elan`](https://github.com/leanprover/elan) is installed):

```bash
# 1. Machine-check all 78 theorems across all 5 modules (0 errors, 0 warnings, 0 sorrys)
lake build

# 2. Run the native compiled 9-layer self-verification showcase
lake exe lean_in_lean

# 3. Audit #print axioms on every single theorem (verifies 0 sorryAx, 0 custom/native axioms)
python3 scripts/audit_axioms.py
```

Expected output of `lake exe lean_in_lean`:
```text
==================================================================================
  Lean-in-Lean: Complete 9-Layer Formal Verification of Lean 4 (v4.35.0)
  3,907 Lines • 78 Machine-Checked Theorems • 0 sorrys • 0 Custom/Native Axioms
==================================================================================
✓ Layer 1 (Pratt Parser)        : 'False → False → False' right-assoc truth = (some true)
✓ Layer 2 (Macro Hygiene)       : Hygienic eval = true (capture-free) vs Unhygienic = false
✓ Layer 3 (MetaM Unifier)       : Self-cycle ?0:=?0 allowed = false, escaped FVar allowed = false
✓ Layer 4 (Tabled Typeclasses)  : Coe 2-cycle = none, Diamond dict = (some 100)
✓ Layer 5 (Core CIC Kernel)     : (λ h:False => h) : some (...), Gödel Sort 0 @ u=1: none, @ u=2: some (Sort 1)
✓ Layer 6 (.olean & Replay)     : Region round-trip = true, Forged mutual cycle A↔B replay = none
✓ Layer 7 (LCNF ToMono Erasure) : Full CIC = some (vNat 42), Erased LCNF = some (mNat 42)
✓ Layer 8 (Perceus Reset/Reuse) : Hot-path (rc=1) new allocs = 0, Cold-path (rc=2) alias intact = true
✓ Layer 9 (lean.h & Sticky RC)  : isScalar(box 42) = true, unbox = 42, INT_MAX+5 neverFreed = true
==================================================================================
```

---

## Repository Structure

| Path | Lines / Files | Description |
| :--- | :--- | :--- |
| [`LeanInLean/CoreKernel.lean`](LeanInLean/CoreKernel.lean) | `953` lines (`26` thms) | Core C++ Kernel (`mk_imax`, `HasType ⇔ kernelInferType`, consistency, Russell/Girard, Gödel stratification, strict positivity, large elimination, `DefEq`, `Quot.lift`) |
| [`LeanInLean/FrontendAndMeta.lean`](LeanInLean/FrontendAndMeta.lean) | `900` lines (`16` thms) | Pratt parser anti-spoofing, `Hygiene.lean` macro scopes, `MetaM` `checkAssignment` & `instantiateMVars`, tabled typeclass synthesis & coherence |
| [`LeanInLean/CompilerAndRC.lean`](LeanInLean/CompilerAndRC.lean) | `735` lines (`11` thms) | LCNF `ToMono` erasure simulation, kernel-to-compiler large-elim bridge, Perceus RC, `@&` borrows & `Reset`/`Reuse` hot/cold heap safety |
| [`LeanInLean/RuntimeAndOlean.lean`](LeanInLean/RuntimeAndOlean.lean) | `1,150` lines (`22` thms) | 64-bit `lean_box`/`lean_unbox`, 32-bit `LEAN_RC_STICKY` overflow freeze ($\forall 2^{32}$), PAP closures, `native_decide` TCB, `.olean` relocation, DAG round-trip & `LeanChecker` `Replay.lean` |
| [`LeanInLean/FullStack.lean`](LeanInLean/FullStack.lean) | `169` lines (`3` thms) | Master end-to-end 9-layer soundness & memory-safety composition certificates |
| [`audited_sources/kernel/`](audited_sources/kernel/) | `7` C++17 files | Audited Lean 4 `src/kernel/` files (`level`, `expr`, `type_checker`, `inductive`, `quot`) |
| [`audited_sources/full_stack/`](audited_sources/full_stack/) | `15` C11/Lean files | Audited Lean 4.35.0 parser, hygiene, `MetaM`, typeclass, LCNF, Perceus RC, `lean.h`, `Native`, `CompactedRegion`, `Replay`, and `LeanChecker` sources |
| [`scripts/audit_axioms.py`](scripts/audit_axioms.py) | Python 3 | Automated `#print axioms` auditor across all `78` theorems (`17` purely 0-axiom CIC proofs + `61` standard CIC proofs, `0` native/custom axioms) |

---

## Summary of All 17 Machine-Checked Paradox & Bug Tightness Proofs

For every critical guard across the kernel, frontend, elaborator, `.olean` replayer, compiler, and runtime, we prove **both sufficiency and necessity**—demonstrating constructively what fails if the guard is omitted:

| # | Subsystem | Omitted Guard | Upstream Source | Formal Tightness Theorem | Consequence Certified |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 1 | Kernel Universes | `Sort u : Sort (u+1)` | `type_checker.cpp:340` | `russell_paradox_if_type_in_type` [0 ax] | Retracting `(U → Prop) ↪ U` derives `False` |
| 2 | Kernel Inductives | `check_positivity` | `inductive.cpp:429` | `negative_inductive_occurrence_derives_false` [0 ax] | `(Bad → False) → Bad` derives `False` in `Prop` |
| 3 | Kernel Large Elim | `num_intros > 1` | `inductive.cpp:523` | `multi_constructor_large_elim_plus_proof_irrel_derives_false` [0 ax] | `OrProp → Bool` + Proof Irrel. equates `true = false` |
| 4 | Kernel Singleton | `to_check ⊆ indices` | `inductive.cpp:546` | `hidden_witness_large_elim_plus_proof_irrel_derives_false` [0 ax] | `ExProp → Bool` + Proof Irrel. equates `true = false` |
| 5 | Kernel Quotients | Coherence `r a b → f a = f b` | `quot.cpp:87` | `unverified_quot_lift_derives_false` | Unchecked `Quot.lift` on total relation derives `False` |
| 6 | Pratt Parser | `→` Right-Assoc `rbp = 24` | `Parser_Basic.lean:208` | `arrow_associativity_spoofing_paradox` | `rbp = 26` flips `False → False → False` from `True` to `False` |
| 7 | Macro Hygiene | Fresh `MacroScope` stamp | `Hygiene.lean:42` | `unhygienic_macro_suffers_capture` [0 ax] | Macro `let x := false` captures user's `"x"` |
| 8 | `MetaM` Unifier | Transitive occurs check | `ExprDefEq.lean:1047` | `omitting_occurs_check_diverges_for_all_fuel` | `?0 := ?0` loops forever for all `fuel : Nat` |
| 9 | `MetaM` Scoping | `lctx.containsFVar` | `ExprDefEq.lean:1018` | `omitting_fvar_scope_check_escapes_hypothesis` | Local `x : False` escapes binder into root `?0` |
| 10 | Typeclasses | Active `visiting` cycle guard | `SynthInstance.lean:78` | `synthGoal_cycle_termination_and_diamond_memo` [0 ax] | `Coe A B` + `Coe B A` terminates cleanly as `none` |
| 11 | LCNF `ToMono` | `Prop` large-elim restriction | `ToMono.lean:32` | `large_elim_impossible_after_toMono_erasure` [0 ax] | `Or.inl`/`inr` both erase to `.mErased`; `true = false` |
| 12 | Perceus `Reset` | `lean_is_exclusive` (`rc = 1`) | `lean.h:759` | `omitting_exclusivity_check_corrupts_alias` | In-place mutation at `rc = 2` corrupts live shared alias |
| 13 | Perceus `Reset` | Duplicate-proj `mask[i]` | `ExpandResetReuse.lean:93` | `duplicate_proj_mask_prevents_double_free` | Stripping two `inc`s on `proj[0]` causes double-free |
| 14 | Perceus Borrows | Escaping `@&` borrow `inc` | `InferBorrow.lean:42` | `borrowed_convention_safety_and_escape_uaf` | Freeing container drops caller's borrowed cell to `rc = 0` |
| 15 | `native_decide` | `!hasFVar && !hasMVar` + Sound Compiler | `Native.lean:39, 41, 67` | `nativeEqTrue_three_tightness_paradoxes` [0 ax] | Asserting `x = true`, `?m = true`, or miscompiled `false` derives `False` |
| 16 | `.olean` Replay | `remaining` / `pending` split | `Replay.lean:46-80` | `replay_accepts_out_of_order_dag_and_rejects_cycles_and_duplicates` | Rejects forged `A := A`, `A ↔ B`, and duplicate shadowing |
| 17 | `.olean` Replay | `checkPostponedRecursors` | `Replay.lean:159-165` | `forged_postponed_recursor_derives_false` [0 ax] | Unchecked `.olean` `recInfo` (`True → False`) derives `False` |

---

## License

Released under the [Apache 2.0 License](LICENSE) (matching upstream Lean 4).
