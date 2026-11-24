(** The store game: the attacker sees the stores [ops], made in order, and
    the value of the final load, and then guesses.  Permuting stores to
    distinct keys does not change its guess. *)

From reloc Require Import reloc.
From cryptis.hyper.core Require Import public.
From cryptis.hyper.primitives Require Import with_cryptis attacker.
From cryptis.hyper Require Import adequacy.
From cryptis.hyper.examples.nsl Require Import game.
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

Theorem store_nsl_secure ops ops' k adv adv' σ :
  NoDup ops.*1 → ops ≡ₚ ops' →
  attacker_valid adv adv' →
  adequate NotStuck (guess (game ops k) adv)%E σ
    (λ v _, ∃ thp' h v',
       rtc erased_step ([(guess (game ops' k) adv')%E], σ) (of_val v' :: thp', h) ∧
       v = v').
Proof.
move=> Hnd Hp ?.
apply: (hypercryptis_adequacy (Σ:=#[relocΣ; publicΣ; connΣ])) => // ? ?.
iIntros "#Hctx". rel_values. iIntros "!> !> %a %a' #Ha".
iApply (refines_wand with "[]").
{ iApply (guess_refinement with "Hctx Ha").
  iApply (refines_app _ _ _ _ lrel_attacker); last by rel_values.
  by iApply (store_game_refinement k Hnd Hp). }
by iIntros (v v') "(%g & -> & ->) !>".
Qed.
