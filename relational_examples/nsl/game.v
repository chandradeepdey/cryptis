(** The real-or-random games: an attacker that sees one of the two tests
    guesses whether the key revealed to it is the session key or a fresh
    one. *)

From cryptis Require Import cryptis primitives.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib.
From cryptis.hyper.core Require Import public.
From cryptis.hyper.primitives Require Import with_cryptis attacker.
From cryptis.hyper Require Import proofmode adequacy.
From cryptis.hyper.examples.nsl Require Import impl proofs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition guess (test : val) : val := λ: "sys",
  let: "chan_guess" := new_channel "sys" in
  test "sys";;
  let: "guess" := recv "chan_guess" in
  eq_term (TInt 1) "guess".

Section Game.

Context `{!relocG Σ, !publicGS Σ}.

Lemma guess_refinement (test test' : val) adv adv' :
  hypercryptis_ctx -∗
  lrel_attacker adv adv' -∗
  (REL test adv << test' adv' : ()) -∗
  REL guess test adv << guess test' adv' : lrel_bool.
Proof.
iIntros "#Hctx #Hadv Htest". rewrite /guess. rel_pures.
rel_apply (refines_new_channel with "Hadv").
iIntros (chan_guess chan_guess') "#Hchan_guess". rel_pures.
rel_bind_l (test adv). rel_bind_r (test' adv').
iApply (refines_bind with "Htest").
iIntros (? ?) "_" => /=. rel_pures.
rel_apply (refines_recv with "Hchan_guess").
iIntros (g g') "#Hg" => /=.
rel_prims. rel_values.
iMod (public_part_bij' (E:=⊤) (TInt 1) (TInt 1) g g'
        ltac:(solve_ndisj) with "Hctx [] Hg") as %H.
{ by rewrite public_TInt. }
iModIntro. iExists (bool_decide (TInt 1 = g)). iPureIntro.
split; first done. do 2 f_equal. by apply bool_decide_ext.
Qed.

End Game.

(** Real-or-random secrecy of the responder's session key as a contextual
    equivalence: when R's peer is I, no well-typed context can tell the
    session key from a fresh key. *)
Theorem nsl_resp_ror_game_ctx_equiv :
  ∅ ⊨ hypercryptis_game (resp_test true) =ctx= hypercryptis_game (resp_test false) :
      hypercryptis_game_ty TUnit.
Proof.
by split;
  apply: (hypercryptis_ctx_refinement (Σ:=#[relocΣ; publicΣ])) => ? ? Δ;
  iIntros "#Hctx";
  [iApply (resp_test_refinement true) | iApply (resp_test_refinement false)].
Qed.

(** The same fact for the initiator's session key, when I's peer is R. *)
Theorem nsl_init_ror_game_ctx_equiv :
  ∅ ⊨ hypercryptis_game (init_test true) =ctx= hypercryptis_game (init_test false) :
      hypercryptis_game_ty TUnit.
Proof.
by split;
  apply: (hypercryptis_ctx_refinement (Σ:=#[relocΣ; publicΣ])) => ? ? Δ;
  iIntros "#Hctx";
  [iApply (init_test_refinement true) | iApply (init_test_refinement false)].
Qed.

Theorem nsl_resp_ror_secure b adv adv' σ :
  attacker_valid adv adv' →
  adequate NotStuck (guess (resp_test b) adv)%E σ
    (λ v _, ∃ thp' h v',
       rtc erased_step ([(guess (resp_test (negb b)) adv')%E], σ) (of_val v' :: thp', h) ∧
       v = v').
Proof.
move=> ?; apply: (hypercryptis_adequacy (Σ:=#[relocΣ; publicΣ])) => // ? ?.
iIntros "#Hctx". rel_values. iIntros "!> !> %a %a' #Ha".
iApply (refines_wand with "[]").
{ iApply (guess_refinement with "Hctx Ha").
  iApply (refines_app _ _ _ _ lrel_attacker); last by rel_values.
  by iApply resp_test_refinement. }
by iIntros (v v') "(%g & -> & ->) !>".
Qed.

Theorem nsl_init_ror_secure b adv adv' σ :
  attacker_valid adv adv' →
  adequate NotStuck (guess (init_test b) adv)%E σ
    (λ v _, ∃ thp' h v',
       rtc erased_step ([(guess (init_test (negb b)) adv')%E], σ) (of_val v' :: thp', h) ∧
       v = v').
Proof.
move=> ?; apply: (hypercryptis_adequacy (Σ:=#[relocΣ; publicΣ])) => // ? ?.
iIntros "#Hctx". rel_values. iIntros "!> !> %a %a' #Ha".
iApply (refines_wand with "[]").
{ iApply (guess_refinement with "Hctx Ha").
  iApply (refines_app _ _ _ _ lrel_attacker); last by rel_values.
  by iApply init_test_refinement. }
by iIntros (v v') "(%g & -> & ->) !>".
Qed.
