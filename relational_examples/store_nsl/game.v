(** The store game: the attacker sees the stores [ops], made in order, and
    the value of the final load, and then guesses.  Permuting stores to
    distinct keys does not change its guess. *)

From cryptis Require Import lib cryptis primitives.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.core Require Import rel.
From cryptis.hyper.primitives Require Import with_cryptis_spec attacker_spec.
From cryptis.hyper Require Import proofmode rel_adequacy.
From cryptis.hyper.examples.nsl Require Import game.
From cryptis.hyper.examples.store_nsl Require Import impl.
From cryptis.hyper.examples.store_nsl.proofs Require Import conn.
From cryptis.hyper.examples.store_nsl Require Import proofs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition store_game (ops : list (Z * Z)) (k : Z) (adv : expr) : expr :=
  (run_network adv (guess (game ops k)))%E.

Theorem store_nsl_ctx_equiv ops ops' k adv :
  attacker_valid adv → NoDup ops.*1 → ops ≡ₚ ops' →
  ∅ ⊨ store_game ops k adv =ctx= store_game ops' k adv : TBool.
Proof.
move=> Hadv Hnd Hp.
have Hnd' : NoDup ops'.*1 by rewrite -Hp.
split;
  apply: (cryptis_ctx_refinement (Σ:=#[relocΣ; public_relΣ; connΣ])) => // ? ? Δ c c';
  iIntros "#Hctx #Hc"; iApply (guess_refinement with "Hctx Hc").
- by iApply (store_game_refinement k Hnd Hp with "Hctx Hc").
- by iApply (store_game_refinement k Hnd' (symmetry Hp) with "Hctx Hc").
Qed.
