# Weak-Head Normalizability of λpenv and its Characterization by Intersection Types

Isabelle/HOL formalization of weak-head (call-by-name) termination for the calculus
λpenv and of its characterization by intersection types.

λpenv extends the calculus λenv of first-class environments with *quoted names* `⌜x⌝`,
so that functions and environments can be used interchangeably:

- looking up a variable `x` in a function `λy.M` applies the function to the quoted
  name: `x∘(λy.M) → M∘(⌜x⌝/y·id)`;
- applying an environment to a quoted name looks the name up:
  `E ⌜x⌝ → x∘E`.

Authors: Shin-ya Nishizaki and Shogo Murasaki.

## Main result

For every term `M` of λpenv (theory `Main_Results`):

```
theorem main_characterization:    "Typ M ⟷ CFWHN M"
theorem main_characterization_SN: "Typ M ⟷ CFWHSN M"
```

- `Typ M`: `M` has an essential type in the intersection type system with ω,
  environment types and name types `QN x`, in an environment-type context that
  contains no name types (predicate `qfree`).
- `CFWHN M`: `M` weak-head reduces to a clash-free weak-head normal form.
- `CFWHSN M`: every weak-head reduction sequence from `M` is finite, and every
  weak-head normal form reachable from `M` is clash-free.

### Conservativity

- On sorted λenv terms (terms and environments kept apart, no quoted names), the
  weak-head reduction of λpenv coincides with that of λenv (`sorted_wh_iff`), and
  typability coincides with λenv weak-head normalizability (`conservative_Typ`).
  The λenv reduction is defined verbatim inside the session as `sig0`, `beta0`, `wh0`.
- For pure λ-terms, typability coincides with weak-head normalizability of the
  λ-calculus (`E1`, `pure_characterization`).

## The calculus

Terms: `x | λx.M | M N | id | M/x·N | M∘N | ⌜x⌝` (constructor `Nm x` for `⌜x⌝`).

- **σ-reduction** (all positions) has nine rules:
  - the seven λenv rules: Ass, IdL, IdR, DExtn, VarRef, VarSkip, DApp
  - `AppConst`: `M ⌜x⌝ → x∘M`
  - `ConstComp`: `⌜x⌝∘L → ⌜x⌝`
- **Head β-reduction** has four root rules:
  - `Beta1`: `((λx.M)∘L) N → M∘(N/x·L)`
  - `Beta2`: `(λx.M) N → M∘(N/x·id)`
  - `VarClos`: `x∘((λy.M)∘L) → M∘(⌜x⌝/y·L)`
  - `VarLam`: `x∘(λy.M) → M∘(⌜x⌝/y·id)`

  These rules are closed under two kinds of evaluation contexts:
  - `C ::= [] | C N | C∘L | x∘C` (relation `beta_c`)
  - `E ::= C | E N | x∘E | V E`, where `V` is `id` or an extension (relation
    `beta_h`). The argument of an environment is evaluated until it becomes a name,
    but not below a pending composition.
- **Weak-head reduction**: `→wh = →σ ∪ →β`.

With all congruences, `σ ∪ β` is exactly the reduction of λpenv, so λpenv_wh is a
reduction strategy of λpenv.

## Theories

The session `LambdaPEnvWeakHead` (directory `isabelle/`) has 15 theories.

| Theory | Contents | Main results |
| --- | --- | --- |
| `ARS`, `Syntax` | abstract rewriting, terms | |
| `Reduction` | σ, head β (`beta_c`, `beta_h`), weak-head reduction | `sig_SN`, `beta_h_det` |
| `Sig_Confluence` | critical pairs, Newman's lemma, confluence of σ | `sig_confluent` |
| `WHNF_Classes` | neutral terms, values, clashes | `WHNF_iff_classes` |
| `Uniform` | commutation of β and σ, uniform normalization | `CFWHN_imp_CFWHSN`, `WHNF_unique`, `CFWHN_fwd` |
| `Typing` | types (incl. name types), subtyping, typing, generation | `narrowing`, `gen_*` |
| `Completeness` | subject expansion | `subject_expansion`, `completeness` |
| `Soundness` | realizability interpretation | `soundness` |
| `Main_Results` | main theorems | `main_characterization`, `main_characterization_SN`, `clash_not_Typ` |
| `Examples` | examples | |
| `Sorted`, `Conservative` | sorted terms, the λenv fragment | `sorted_wh_iff`, `conservative_Typ` |
| `Lambda`, `Readback` | de Bruijn λ-terms, readback into the λ-calculus | `E1`, `pure_characterization` |

The theories contain no `sorry`, `oops`, `axiomatization` or `consts`. The session is
built with `quick_and_dirty` and `skip_proofs` disabled. ML blocks in `Main_Results`
and `Readback` fail the build if the main theorems depend on any oracle. The only use
of choice is Hilbert's ε (`SOME`), to name the σ-normal form.

## Building

Requires [Isabelle2025-2](https://isabelle.in.tum.de/).

```bash
isabelle build -d isabelle LambdaPEnvWeakHead
```

To also produce the theory documents (requires LaTeX):

```bash
isabelle build -o document=pdf -d isabelle LambdaPEnvWeakHead
```

The output is written to `isabelle/output/`.

## Files

```
isabelle/ROOT              session LambdaPEnvWeakHead
isabelle/*.thy             the 15 theories
isabelle/document/root.tex LaTeX root of the theory document
docs/document.pdf          theory document: all theories with proofs
docs/outline.pdf           theory document: all theories with proofs omitted
```

## Related repositories

- Lean 4 port of this development (one file per theory, same definitions and theorem
  names, no `sorry`, only Lean's standard axioms):
  [lambda-penv-weak-head-normalizability-intersection-types-lean](https://github.com/nisizaki/lambda-penv-weak-head-normalizability-intersection-types-lean)
- λpenv and the confluence of its weak reduction:
  [lambda-penv-confluence-public](https://github.com/nisizaki/lambda-penv-confluence-public)
- The λenv development that this one extends:
  [lambda-env-weak-head-normalizability-intersection-types](https://github.com/nisizaki/lambda-env-weak-head-normalizability-intersection-types)
  ([Lean 4](https://github.com/nisizaki/lambda-env-weak-head-normalizability-intersection-types-lean))
- Call-by-value λpenv:
  [lambda-penv-call-by-value-termination-intersection-types](https://github.com/nisizaki/lambda-penv-call-by-value-termination-intersection-types)
  ([Lean 4](https://github.com/nisizaki/lambda-penv-call-by-value-termination-intersection-types-lean))
- Call-by-value λenv:
  [lambda-env-call-by-value-termination-intersection-types](https://github.com/nisizaki/lambda-env-call-by-value-termination-intersection-types)

## How to cite

Shin-ya Nishizaki and Shogo Murasaki.
*Mixing Functions and Environments: Weak-Head Normalizability of λpenv and its
Characterization by Intersection Types, Formalized in Isabelle/HOL.*
