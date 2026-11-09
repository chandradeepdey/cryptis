# Cryptis: Cryptographic Reasoning in Separation Logic

The material covered in the paper can be found in the following files:

## Core Library

In the `cryptis` directory you will find:

- `lib/*, lib`: General additions to Iris, MathComp, and stdpp; Diffie–Hellman and HMQV
  key-exchange and ghost-state helpers; list-manipulation programs and AVL maps
  (`lib/avl`) for HeapLang.
- `core/*`, `cryptis`: Core Cryptis components: cryptographic terms, the
  `public` predicate, encryption predicates, and term metadata.
- `primitives/*`, `primitives`: HeapLang functions for manipulating
  cryptographic terms, including randomized public-key encryption
  (`random_aenc`), which pairs a fresh nonce with the plaintext so that equal
  plaintexts give different ciphertexts.  Definition of the attacker.
- `tactics`: Ltac tactics for symbolically executing the main HeapLang functions
  on terms.

## Case studies

In the `examples` directory you will find our case studies:

- `nsl`: Needham–Schroeder–Lowe public-key protocol, including game (`nsl_secr.v`
  and `nsl_auth.v` are standalone single-file variants for secrecy / agreement).
- `nsl_dh`: NSL with Diffie–Hellman key exchange, including game.
- `iso_dh`: ISO protocol with DH key exchange and digital signatures (game is in
  its own file).
- `gen_conn`, `conn`: Generic and authenticated secure-connection layers.
- `rpc`: Remote procedure calls (built on `conn`).
- `store`: Authenticated key-value store built on `rpc` (game is in its own file);
  `alist` is a supporting association-list module.
- `opaque`: OPAQUE-style password-authenticated key exchange with HMQV,
  including game (password leak, theft of the server's file, OPRF
  precomputation).
- `hmqv`: standalone HMQV authenticated key exchange (three-message variant
  with authenticators, built on `lib/hmqv.v`); its games (secrecy,
  key-compromise impersonation, injective agreement, key independence) are in
  `hmqv/games`.
- `tls13`: TLS 1.3 handshake (partial; `impl.v` + per-component `proofs/`).
- `challenge_response`, `composite_game`, `permanent`, `counter`: smaller
  single-file examples plus a composite security game.

## Session types

In the `session` directory (Rocq namespace `cryptis.sess`) you will find
Actris-style session types for authenticated channels built on `iso_dh` and
`gen_conn`: `impl`, `proofs`, `proofs/base` (aggregated by `sess`), the
tagged-message layer `tag`, the `trusted` wrapper for honest parties, and
`proofmode` tactics.  Its case studies live in `session/examples`:

- `basic`: small protocols (send-42, vote, key-value database).
- `store`: authenticated key-value store over session types (game is in its
  own file).

## HyperCryptis: Indistinguishability in the Dolev-Yao model

In the `relational` directory (Rocq namespace `cryptis.hyper`) you will find a
relational version of Cryptis, built on [ReLoC](https://iris-project.org/reloc),
for proving that two runs of a protocol are indistinguishable to the attacker:

- `lib/*`, `lib_spec`: Relational specifications of the list-manipulation
  programs and AVL maps.
- `core/*`: The relation `PUB⟨t, t'⟩`, which says that the attacker cannot tell
  apart a term of one run from a term of the other, and its invariant.
- `primitives/*`: Relational specifications of the primitives.  Definition of
  a valid attacker.
- `rel_adequacy`: Adequacy: a relational proof gives a contextual refinement
  between games run against any valid attacker.
- `proofmode/*`, `proofmode`: Ghost-state updates and tactics for relational
  proofs.

Its case studies live in `relational_examples`:

- `ind_cpa`, `ind_cca2`: IND-CPA and IND-CCA2 for randomized public-key
  encryption.
- `nsl`: Real-or-random secrecy of the Needham–Schroeder–Lowe session key, for
  the programs of `examples/nsl`.
- `vote`: Vote privacy for an election with any number of voters and
  candidates.
- `store_nsl`: Key-value store over an NSL session; the attacker cannot tell
  in which order the client writes to distinct keys.

## Building

Cryptis is known to compile with the following dependencies:

- rocq-core v9.2.0
- rocq-stdlib
- rocq-hierarchy-builder
- rocq-elpi
- rocq-mathcomp-ssreflect v2.6.0
- coq-deriving v0.2.3
- rocq-stdpp
- rocq-iris v4.5.0
- rocq-iris-heap-lang v4.5.0
- rocq-actris v4.5.0
- coq-reloc b80d3bc

### Nix

If you use Nix, the accompanying flake file should be enough to install all the
required dependencies.  To compile and check all proofs, simply type `make`.

### opam

Make sure to add the Rocq opam repository to your switch:

```opam repo add rocq-released https://rocq-prover.org/opam/released```

Afterwards, Cryptis can be installed with:

```opam install .```

Alternatively, run `make builddep` to produce and install a dummy package that
installs the correct dependencies and run `make`.
