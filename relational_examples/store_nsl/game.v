(** The store game: the attacker sees the stores [ops], made in order, and
    the value of the final load, and then guesses.  Permuting stores to
    distinct keys does not change its guess. *)

From reloc Require Import reloc.
From cryptis.hyper.core Require Import public.
From cryptis.hyper.primitives Require Import with_cryptis attacker.
From cryptis.hyper Require Import adequacy.
From cryptis.hyper.examples.store_nsl Require Import impl.
From cryptis.hyper.examples.store_nsl.proofs Require Import conn.
From cryptis.hyper.examples.store_nsl Require Import proofs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem store_nsl_game_ctx_equiv ops ops' k :
  NoDup ops.*1 → ops ≡ₚ ops' →
  ∅ ⊨ hypercryptis_game (game ops k) =ctx= hypercryptis_game (game ops' k) :
      hypercryptis_game_ty TUnit.
Proof.
move=> Hnd Hp.
have Hnd' : NoDup ops'.*1 by rewrite -Hp.
split;
  apply: (hypercryptis_ctx_refinement (Σ:=#[relocΣ; publicΣ; connΣ])) => ? ? Δ;
  iIntros "#Hctx".
- by iApply (store_game_refinement k Hnd Hp with "Hctx").
- by iApply (store_game_refinement k Hnd' (symmetry Hp) with "Hctx").
Qed.
