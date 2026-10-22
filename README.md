# Barbier's theorem for the Reuleaux triangle in Lean 4

A Lean 4 + Mathlib formalisation of **Barbier's theorem** — every plane curve of constant width `w`
has perimeter `π·w` — for curves given by their **support function**, together with the **Reuleaux
triangle** as the non-smooth instance, the bridge from the support-function model to an actual convex
body, and a proof that the Reuleaux curve's Mathlib length is `π·w`.

> Let `h : ℝ → ℝ` be `C¹` and `2π`-periodic with `h θ + h (θ+π) = w` and `h + h'' ≥ 0` outside a
> countable set. Then the curve `γ_h(θ) = (h θ + i·h' θ)·e^{iθ}` has perimeter `∫₀^{2π} ‖γ_h'‖ = π·w`.

Both the smooth case (`h` twice differentiable) and the piecewise case (corners allowed, as in the
Reuleaux triangle) are proved. The Reuleaux support function is defined explicitly and shown to be
`C¹` but **not** `C²`, so the smooth theorem does not reach it; it is handled by the piecewise theorem.
The support function is also proved to be the support function of an explicit convex set of constant
width `w`, packaged as a Mathlib `ConvexBody`.

**Status:** all statements proved, with no `sorry`. `gate.sh` checks **96** named declarations.

## Main statements

| Lean name | File:line | Statement |
|---|---|---|
| `Barbier.ConstWidthSupport` | `Barbier/Basic.lean:21` | a smooth constant-width support function: `C²`, `2π`-periodic, `h θ + h (θ+π) = w`, `h + h'' ≥ 0` |
| `Barbier.barbier` | `Barbier/Basic.lean:110` | **Barbier, smooth:** such an `h` has perimeter `π·w` |
| `Barbier.ConstWidthSupport.toPiecewise` | `Barbier/Piecewise.lean:57` | every smooth constant-width support function is a piecewise one |
| `Barbier.barbier_piecewise` | `Barbier/Piecewise.lean:72` | **Barbier, with corners:** `C¹`, `2π`-periodic, `h θ + h (θ+π) = w`, `h + h'' ≥ 0` off a countable set ⇒ perimeter `π·w` |
| `Barbier.reuleaux` | `Barbier/Reuleaux.lean:16` | the Reuleaux support function of width `w` |
| `Barbier.reuleaux_constWidth` | `Barbier/Reuleaux.lean:1074` | it is a piecewise constant-width support function of width `w` |
| `Barbier.reuleaux_perimeter` | `Barbier/Reuleaux.lean:1083` | its perimeter is `π·w` |
| `Barbier.reuleaux_not_smooth` | `Barbier/Reuleaux.lean:1086` | it is **not** `C²` (so `barbier` does not apply) |
| `Barbier.reuleaux_vertices` | `Barbier/Reuleaux.lean:1133` | the three corner points are pairwise at distance `w` |
| `Barbier.reuleaux_arc` | `Barbier/Reuleaux.lean:1368` | one side is an arc of radius `w` about the opposite corner |
| `Barbier.reuleaux_length` | `Barbier/ReuleauxLength.lean:248` | the Reuleaux curve's **Mathlib length** (`eVariationOn`) on `[0,2π]` is `π·w` |
| `Barbier.reuleaux_length_ne_top` | `Barbier/ReuleauxLength.lean:296` | that total variation is finite |
| `Barbier.reuleaux_perimeter_eq_eVariationOn` | `Barbier/ReuleauxLength.lean:300` | our perimeter equals that total variation |
| `Barbier.length_eq_integral_norm_deriv` | `Barbier/ArclenFinite.lean:50` | a `C¹` curve's Mathlib length on `[a,b]` is finite and equals `∫_a^b ‖γ'‖` |
| `Barbier.perimeter_eq_eVariationOn` | `Barbier/Bridge.lean:165` | for `C²` support functions, our perimeter is Mathlib's length |
| `Barbier.body` | `Barbier/Bridge.lean:172` | the body `K_h = ⋂_θ {z : Re(z e^{-iθ}) ≤ h θ}` |
| `Barbier.convex_body` | `Barbier/Bridge.lean:175` | `K_h` is convex |
| `Barbier.support_body_piecewise` | `Barbier/BridgePiecewise.lean:177` | the support values of `K_h` are `h` |
| `Barbier.width_body_piecewise` | `Barbier/BridgePiecewise.lean:184` | the widths of `K_h` are `w` in every direction |
| `Barbier.exists_convexBody_piecewise` | `Barbier/ConvexBodyBridge.lean:64` | `K_h` is a Mathlib `ConvexBody` with support function `h` and constant width `w` |
| `Barbier.reuleaux_convexBody` | `Barbier/ConvexBodyBridge.lean:75` | the Reuleaux triangle is a Mathlib convex body of constant width `w` |

The curve is `Barbier.curve` (`Barbier/Basic.lean:28`), `γ_h(θ) = (h θ + i·h' θ)·e^{iθ}`; the
perimeter is `Barbier.perimeter` (`Barbier/Basic.lean:31`), `∫₀^{2π} ‖γ_h'‖`. Other examples:
`Barbier.circle_perimeter` (the circle of diameter `w`) and `Barbier.trefoil_perimeter` (the smooth
family `a + b·cos 3θ`, `0 ≤ 8b ≤ a`).

## Verification

`./gate.sh` builds the library and generates its own `#print axioms` queries for 96 named
declarations. The gate fails if any source file contains `sorry`, `admit`, `native_decide`, `axiom`,
`#eval`, `run_cmd`, `initialize`, `IO`, `set_option` or a syntax extension; if the build fails; if a
named declaration is missing or has an extra report; or if a named declaration depends on anything
other than `propext`, `Classical.choice` and `Quot.sound`.

Output: `PASS (96 declarations, standard axioms only)`. Verified on two machines of different
architecture (x86-64 Linux and arm64 macOS) at the pinned Mathlib revision.

`tests/tamper.sh` plants six kinds of fake proof in scratch copies and checks that the gate rejects
each one:

| Test | What it plants |
|---|---|
| sorry | a `sorry` |
| ax2line | an `axiom` split across two lines |
| evalfake | an `#eval` that prints a fake axiom report |
| macro | a custom macro that rewrites `#print axioms` |
| falsehyp | a hypothesis dropped from a theorem (false) |
| wrap | a genuine extra axiom with a long name, so the report wraps |

## Layers 14 and 15

`Barbier/L14.lean` (20 declarations) restates the main results so that the statements use only Mathlib notions. The curve, perimeter, body and Reuleaux support function are written out in full, with bridge lemmas (`l14b_*`) and explicit witnesses (`l14w_*`). `Barbier/L15Classical.lean` reproduces verbatim, in namespace `Barbier.Classical`, 34 definitions and statements (17 `classical_*` statements and 2 well-formedness obligations) written independently from textbook statements by an AI model that did not see this code. It adds 14 gated theorems (`cov_*` and new-proof lemmas) proving these statements, or parts of them, from this development. No writer statement was shown false.

## Prior art

We found no formal proof of Barbier's theorem, and no formalisation of the Reuleaux triangle, in any
proof assistant: Mathlib (pinned and current), the Archive of Formal Proofs, Coq/GeoCoq/MathComp, HOL
Light, HOL4, Mizar, Metamath (`set.mm`/`iset.mm`), the "1000+ theorems" list, GitHub code search, the
Lean Zulip archive and several autoformalisation benchmarks. Mathlib has convex bodies but no support
function (its convex-body file lists support sets as future work); the nearest external Lean work,
`deancureton/MovingSofa`, defines support values and directional width but states neither Barbier nor
the four-vertex theorem. The four-vertex companion development is
[`fourvertex`](https://github.com/jpbald93/fourvertex).

## Build

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh   # if Lean is not installed
lake exe cache get
lake build
./gate.sh
bash tests/tamper.sh
```

Toolchain: Lean `v4.33.1`, Mathlib `v4.33.1` (revision pinned in `lake-manifest.json`). `gate.sh`
never fetches: run `lake exe cache get` first so the pinned Mathlib checkout is present in
`.lake/packages`.

## Note on how this was produced

The formal proofs and documentation were developed with the help of a large-language-model AI
assistant. The author directed the work, reviewed the statements, and is responsible for the result.
The Lean kernel checks every proof.

## Citation

This repository accompanies the paper *Barbier's theorem for the Reuleaux triangle and the convex
four-vertex theorem in Lean 4, through support functions* (J. Bald, 2026).

```bibtex
@misc{bald2026barbier,
  author       = {Josh Bald},
  title        = {Barbier's theorem for the Reuleaux triangle in Lean 4},
  year         = {2026},
  howpublished = {\url{https://github.com/jpbald93/barbier}},
  note         = {Lean 4 + Mathlib v4.33.1}
}
```

## License

Apache 2.0.
