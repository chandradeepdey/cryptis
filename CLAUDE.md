# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**Cryptis** is a formal verification framework for cryptographic protocols, built on top of [Iris](https://iris-project.org/) (a separation logic framework) and [HeapLang](https://plv.mpi-sws.org/iris/). It provides tools for proving security properties of cryptographic protocol implementations in the [Rocq](https://rocq-prover.org/) (formerly Coq) proof assistant.

The framework allows reasoning about protocols using a Dolev-Yao–style symbolic attacker model within a separation logic setting.

## Keeping documentation in sync

When you change code, check in the **same pass** whether the change invalidates any documentation, and update it. Docs that drift from the code are worse than no docs — a wrong `term` datatype or stale version misleads both human maintainers and future agent sessions. In particular:

- **This file (`CLAUDE.md`)** — the `term` datatype and smart-constructor list, the encryption-predicate and primitive names, the dependency versions, the module dependency order, and the case-study list.
- **`README.md`** — the case-study list and dependency versions. Keep both files consistent with `rocq-cryptis.opam`, which is the single source of truth for versions.
- **File header comments** that state a module's purpose, invariants, or dependency position.

Cheap check: after renaming or removing an identifier, `grep` it across `*.md` (and file headers) before considering the change done. Adding a case study / primitive, or changing the term representation, requires updating `CLAUDE.md` and `README.md`.

## Build Commands

Rocq and its dependencies are not on the default PATH. Always wrap build/check commands in the project's `ai` dev shell, which provides `coq-lsp` plus `rocq-mcp`:

```bash
nix develop .#ai --command make                                # build everything
nix develop .#ai --command make cryptis/core/public.vo         # build one file
nix develop .#ai --command make clean                          # clean artifacts
```

Other useful commands inside the shell: `make builddep` (install build deps via opam, only needed outside Nix), `rocq compile <file.v>` (compile a single `.v` file directly).

Building is slow (Iris typechecking dominates). Foundational files — the `core/term/` layer (especially `base.v` and `algebra.v`), `core/public.v`, `cryptis.v` — cascade a rebuild through much of the tree, so an edit there costs minutes, not seconds. Prefer targeted builds (`make path/to/file.vo`) while iterating, and run the full `make` only to verify everything compiles. `make -k -j<N>` keeps going past the first error and surfaces every root failure at once (dependents of a failed file are silently skipped, so re-run after each fix).

## Interactive Proof Tooling (rocq-mcp)

The project ships an MCP server in `.mcp.json` (`rocq`, launched via `nix develop .#ai --command rocq-mcp`). It exposes `mcp__rocq__*` tools for interactive proof work. The schemas are surfaced as **deferred tools** — load them on demand with `ToolSearch query="select:mcp__rocq__rocq_start,mcp__rocq__rocq_check,..."` before calling.

When to use which:

- **Interactive proof development** (stepping through tactics, inspecting goals, exploring lemmas): prefer the MCP tools. `rocq_start` opens a file/theorem and returns a state id + current goals; `rocq_check` advances by running tactics (imports are cached, so iteration is fast); `rocq_step_multi` tries several tactics at once without committing; `rocq_query` runs `Search`/`Check`/`Print`/`About` without touching proof state; `rocq_toc` outlines a file; `rocq_assumptions` checks what a finished theorem depends on.
- **"Does the file still build?"** (after edits, or to confirm a full proof closes): prefer `nix develop .#ai --command make path/to/file.vo` via Bash. It exercises the real build, respects `_CoqProject`, and avoids loading large schemas into context.

Caveat: a `rocq_start` session reads the file at start time and does not track later edits. After modifying a `.v` file, restart the session (`rocq_start` again) before continuing — otherwise tactic results may be stale.

A second caveat, with a much worse symptom: the coq-lsp process behind the MCP caches loaded `.vo` libraries for its whole lifetime and does **not** invalidate them when you recompile underneath it. After a `make` mid-session, a later `Require` of anything that was rebuilt fails with `Compiled library X ... makes inconsistent assumptions over library Y` — and `rocq_start`/`rocq_query` swallow that into a bare "The reference … was not found in the current environment", which looks like a load-path problem and is not. Fix: `rocq_start` with `force_restart: true`. Rule of thumb: **any `make` invalidates every open MCP session** — restart after rebuilding, not just after editing. (Editor clients drive the same `coq-lsp` binary, so the same rebuild-then-everything-is-"not found" symptom appears there; restarting the LSP server clears it.)

## Setup

**Via Nix (preferred):** Use the provided `flake.nix`. Two dev shells are exposed:

- `nix develop` (or `.#default`) — `coq-lsp` and the cryptis build inputs.
- `nix develop .#ai` — everything in the default shell plus `rocq-mcp`. **Use this shell for any work that compiles Rocq files or invokes proof tooling.**

**Via opam:**
```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install . # or: make builddep && make
```

Key dependencies (authoritative pins live in `rocq-cryptis.opam` — treat it as the single source of truth): rocq-core 9.1.1, rocq-mathcomp-ssreflect 2.5.0, rocq-iris 4.5.0, rocq-iris-heap-lang 4.5.0, coq-deriving 0.2.3. `README.md` and this file must agree with the opam file.

## Code Architecture

### Directory Structure

- **`cryptis/`** — Core library (Rocq namespace `cryptis`)
  - `lib/` — Utilities: session management, adequacy, Diffie-Hellman helpers, ghost state helpers
  - `core/` — Foundation: term definitions, public predicate, term metadata
  - `primitives/` — HeapLang implementations of cryptographic operations
  - `tactics.v` — Ltac2 automation for symbolic execution of HeapLang programs
  - `cryptis.v` — Top-level integration; defines `cryptisGpreS`/`cryptisGS` typeclasses
  - `adequacy.v` — Soundness/adequacy theorems
  - Relational layer (ReLoC-based; files suffixed `_spec.v` or prefixed `rel`): `core/rel.v`, `core/rel_inv_updates.v`, `primitives/*_spec.v`, `primitives/attacker_spec.v`, `rel_adequacy.v`. See **Relational layer** under Core Concepts.

- **`examples/`** — Case studies (Rocq namespace `cryptis.examples`)

### Core Concepts

**Cryptographic Terms** (`core/term/base.v`): The main inductive type `term` is:
- `TInt (n : Z)` — integers/constants
- `TPair t1 t2` — pairs (n-ary tuples are nested pairs; see `Spec.of_list`)
- `TNonce (a : nonce)` — nonces
- `TKey (kt : key_type) t` — keys, where `key_type = AEnc | ADec | Sign | Verify | SEnc`
- `TSeal k t` — a single sealing constructor covering asymmetric encryption, signatures, and symmetric encryption (disambiguated by the key's `key_type`)
- `THash t` — hashes
- `TNonFree pt of PreTerm.wf pt & is_non_free pt` — the Diffie–Hellman fragment (inverse / exponentiation / product), represented indirectly by a well-formed `PreTerm.pre_term`

`TInv`, `TExp`, `TExpN`, `TMul`, `TMulN` are **smart constructors** (locked `Definition`s over `TNonFree`), *not* real constructors — so `case`/`elim` on them is not structural; use the custom induction principles (`term_ind`/`term_rect` in `core/term/base.v`, `term_lt_ind` in `core/term/tsize.v`). Typed key wrappers `aenc_key`/`sign_key`/`senc_key` sit on top of `TKey`, and the surface API lives in `Module Spec` (`core/term/spec.v`: `Spec.tag`, `Spec.of_list`, `Spec.pkey`, `Spec.to_list`, …).

The term layer is split across `core/term/` and aggregated by `core/term.v`: `base.v` (the `term` inductive, the `unfold`/`fold` ↔ `pre_term` conjugation, smart constructors, instances, destructor defs, the `count` API (`count`, `count_inj`, `count_TMulN`, `count_TInv`, …), and the structural `term_rect`/`term_ind` eliminators), `algebra.v` (multiplicative-group + DH-exponentiation laws), `tsize.v` (the `tsize` measure, its termination lemmas, and the well-founded `term_lt_rect`/`term_lt_ind`), `repr.v` (`val_of_term`/`repr`), `nonces.v`, `subterms.v`, `spec.v`. Downstream imports `cryptis.core.term`, so the split is transparent — but **module-qualified references (`base.foo`) break when a lemma moves file**; prefer unqualified names. Each split file must re-declare the file-local `Implicit Types (t k : term) (ts : list term).` and `Set Implicit Arguments.` block (those do not cross a `Require` boundary).

**The Public Predicate** (`core/public.v`): Central to the framework. `public t` (an Iris proposition) holds when term `t` is known to the attacker. Protocol proofs establish invariants about which terms are and are not public.

**Encryption Predicates** (`core/public.v`): Per-protocol invariants attached to a namespace `N`, one per key usage:
- `aenc_pred N (Φ : aenc_key → term → iProp)` — asymmetric-encryption invariant
- `sign_pred N (Φ : sign_key → term → iProp)` — signing invariant
- `senc_pred N (Φ : senc_key → term → iProp)` — symmetric-encryption invariant

These are thin wrappers over the generic `seal_pred F N Φ` (with `F : functionality = AENC | SIGN | SENC`); predicates are allocated against a `seal_pred_token F E`.

**HeapLang Primitives** (`primitives/`): Concrete implementations with associated Hoare-triple specs — sealing (`aenc`/`adec`, `sign`/`verify`, `senc`/`sdec`), `hash`, key handling (`pkey`, `mk_nonce`, `mk_aenc_key`, `mk_sign_key`, `derive_senc_key`, `is_aenc_key`), Diffie–Hellman (`tint`, `texp`), the generic `open`, and channel I/O (`send`, `recv`).

**Tactics** (`tactics.v`): Custom tactics (`tac_wp_hash`, `tac_wp_list_match`, etc.) for stepping through HeapLang programs that manipulate cryptographic terms.

**Relational layer** (ReLoC-based). `PUB⟨t, t'⟩` (`core/rel.v`) relates a term of the left run to a term of the right run: the attacker's view of both. Structural cases relate constructors pointwise; the `publicly_linked` cases record *honest links* made by protocol proofs, where the two runs may carry different payloads (a ciphertext of `m` against one of `m'`, or a nonce against a ciphertext in a real-or-random step). `rel.v` also holds the invariant, the partial-bijection lemmas (`publicly_related_part_bij'`) and the `Spec.open` agreement lemmas; `core/rel_inv_updates.v` holds the ghost-state updates (`public_rel_extend`, `linked_extend`, `public_rel_flow_*`, `public_rel_secret_*`, …).

- *Seal and hash predicates.* The counterpart of `seal_pred`/`hash_pred`: `seal_pred_rel F N Φ` and `hash_pred_rel N Ψ`, allocated from `seal_pred_rel_token F E` / `hash_pred_rel_token E`. A predicate takes one input per side of a link: `seal_pred_input = option (term * term)` is `Some (sk, payload)` (secret key, untagged payload) for a ciphertext side and `None` for a side that is not a ciphertext; `hash_pred_input = option term` likewise for hashes. Every honest link of a seal or hash carries `wf_seal_rel`/`wf_hash_rel`, i.e. `□ ▷ Φ` for the registered predicate of its tag. The linker proves `Φ` inside the `publicly_linked t t' -∗ PUB⟨t, t'⟩` wand it hands to `public_rel_extend`; a decryptor recovers it with `wf_seal_rel_elim` under a later (a left-side program step supplies the credit, as in the unary `wp_adec`), or rules honest links out with `seal_pred_rel_token_seal_pred_rel` for tags whose token it still holds. Predicates are keyed by tag, not key, so they are allocated at setup before keys exist and components sharing a key own separate tags.
- *Primitives and attacker.* `primitives/*_spec.v` are the relational primitive specs (`with_cryptis_spec.v` has `channel_rel`); `primitives/attacker_spec.v` models the attacker as an arbitrary program self-related at `attacker_rel`, exports `attacker_prims`, and defines `run_network_rel`.
- *Adequacy* (`rel_adequacy.v`). `cryptis_rel_adequacy` turns a refinement into a statement about executions; `cryptis_ctx_refinement` into a contextual refinement of `λ: "adv", run_network_rel "adv" f` at type `attacker_ty → τ`; `attacker_rel_typed` discharges self-relatedness for syntactically typed attackers. The protocol obligation is `cryptis_rel_ctx -∗ tokens ={⊤}=∗ □ ∀ c c', channel_rel c c' -∗ REL f c << f' c' : A`, where the tokens are `seal_pred_rel_token F ⊤` for each `F` and `hash_pred_rel_token ⊤`: the update lets the proof register its seal and hash predicates before the refinement is established, and the `□` makes the refinement hold for every run of the game. See the two theorems at the end of `examples/ind_cpa.v` for the template.

### Module Dependency Order

```
examples/*
  → cryptis + primitives + tactics
    → cryptis.v (integration)
      → core/public.v, core/term_meta.v, core/minted.v
        → core/term/, core/pre_term/
          → lib/
            → mathcomp, iris, iris.heap_lang
```

The `_CoqProject` file specifies the exact file ordering for compilation.

**mathcomp ↔ stdpp boundary:** `core/pre_term/base.v` is implemented in mathcomp (`seq`, `%O` order, `~~`, `sort <=%O`, bigops, `deriving`); `core/pre_term/normalize.v` (normal forms + the `wf`/`normalize` machinery) is already stdpp-only. `core/pre_term/with_stdpp.v` is *the* bridge, and is where any new mathcomp→stdpp translation belongs: it packages the deriving-generated order both as `pt_order` (a stdpp `relation` with `RelDecision`/`Transitive`/`Total`/`AntiSymm`) and as a global `Lexico PreTerm.pre_term` instance (with `StrictOrder`/`TrichotomyT`, which is what makes `bool_decide (x = y ∨ lexico x y)` decidable), and proves `pt_order_lexico`, `pt_order_mul` (the derived order on `PTMul ts` *is* stdpp's `lexico` on `ts`) and `pt_orderE` (the structural comparison equation, stated with `bool_decide` and `op0_le`/`op1_le`/`op2_le` instead of `<=%O`). Because of that bridge, `primitives/pre_term.v` — which implements the `normalize.v` operations in HeapLang — needs no mathcomp beyond `ssreflect`. Everything from `core/term/` upward is stdpp (`Forall`, `≡ₚ`, `∈`, `merge_sort`). The active boolean→Prop coercion above `pre_term` is stdpp's `Is_true`, **not** ssreflect's `is_true` (bridged by `is_trueP` in `lib/mathcomp_compat.v`); mixing the two silently breaks `rewrite`/`apply`.

### Case Studies

Directory-structured protocols use some of: `impl.v` (HeapLang implementation), a `proofs.v` / `proofs/` tree (Iris security proofs), and `game.v` (security game + final `*_secure` theorem via `cryptis_adequacy`). **The layout is not uniform** — proof decomposition and the name/location of the final theorem vary per protocol, so inspect a protocol's files rather than assuming the pattern.

- `nsl/` — Needham–Schroeder–Lowe public-key protocol (with game); `nsl_secr.v` / `nsl_auth.v` are standalone single-file variants (secrecy / agreement).
- `nsl_dh/` — NSL with Diffie–Hellman key exchange (with game).
- `iso_dh/` — ISO protocol with DH key exchange + digital signatures (game in `iso_dh/game.v`).
- `gen_conn/`, `conn/` — generic and authenticated secure-connection layers (building blocks).
- `rpc/` — remote procedure calls over `conn`.
- `store/` — authenticated key-value store over `rpc` (game in `store/game.v`); `alist/` is a supporting association-list module.
- `opaque/` — OPAQUE-style password-authenticated key exchange (partial: `impl.v`, `shared.v`, `client_proofs.v`, `server_proofs.v`, `game.v`; `game.v` stops at `wp_game`, no closed theorem yet).
- `tls13/` — TLS 1.3 handshake (partial; `impl.v` executable layer + per-component `proofs/` (base, meth, cshare, sshare, cparams, sparams) + `proofs/protocol.v`, no closed theorem yet).
- `challenge_response.v` — signature-based mutual authentication; `composite_game.v` runs several protocols together under one adequacy game.
- `permanent.v`, `counter.v` — small digital-signature demos (immutable state / monotone counter).
- `ind_cpa.v` — relational IND-CPA game. `alice b` encrypts message `b` and returns the attacker's guess; `rel_alice` relates `alice b` and `alice b'` in ReLoC (under the trivial seal predicate `cpa_pred`, registered for Alice's tag at game setup), `ind_cpa_ctx_equiv` closes the game as a contextual equivalence at `attacker_ty → TBool` via `cryptis_ctx_refinement`, and `ind_cpa_secure` is the adequacy form for the nondeterministic-bit wrapper `alice_guess_wrapped`.

The `gen_conn → conn → rpc → store` chain is a real abstraction stack (reuse it), and the `nsl` / `iso_dh` / `store` `game.v` files share a consistent template worth following.
