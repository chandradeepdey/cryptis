(** The real-or-random games: an attacker that sees one of the two tests
    guesses whether the key revealed to it is the session key or a fresh
    one. *)

From iris.heap_lang.lib Require Import nondet_bool.
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

Definition guess_wrapped (test : bool → val) : val := λ: "sys",
  let: "b" := nondet_bool #() in
  ("b", if: "b" then guess (test true) "sys" else guess (test false) "sys").

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

Lemma guess_wrapped_refinement (test : bool → val) adv adv' :
  hypercryptis_ctx -∗
  lrel_attacker adv adv' -∗
  (∀ b, REL test b adv << test (negb b) adv' : ()) -∗
  REL guess_wrapped test adv << guess_wrapped test adv' : λ p1 p2,
    ⌜∃ b g b' g' : bool,
    p1 = (#b, #g)%V ∧ p2 = (#b', #g')%V ∧ b' = negb b ∧ g = g'⌝.
Proof.
iIntros "#Hctx #Hadv Htest". rewrite /guess_wrapped.
rel_pures.
rel_apply_l refines_nondet_bool_l. iIntros (choice).
rel_apply_r (refines_nondet_bool_r _ _ (negb choice)).
case: choice; rel_pures.
- rel_apply (guess_refinement with "Hctx Hadv Htest").
  iIntros (v v') "(%g & %e & %e')"; subst v v' => /=.
  rel_pures. rel_values.
  iPureIntro. by exists true, g, false, g.
- rel_apply (guess_refinement with "Hctx Hadv Htest").
  iIntros (v v') "(%g & %e & %e')"; subst v v' => /=.
  rel_pures. rel_values.
  iPureIntro. by exists false, g, true, g.
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

Theorem nsl_resp_ror_secure :
  hypercryptis_secure (guess_wrapped resp_test) (λ v v',
    ∃ b g b' g' : bool,
      v = (#b, #g)%V ∧ v' = (#b', #g')%V ∧ b' = negb b ∧ g = g').
Proof.
move=> ? ? ? ?.
apply: (hypercryptis_adequacy (Σ:=#[relocΣ; publicΣ])) => // ? ?.
iIntros "#Hctx". rel_arrow_val. iIntros (adv adv') "#Hadv".
iApply (guess_wrapped_refinement with "Hctx Hadv").
iIntros (b). iApply (refines_app _ _ _ _ lrel_attacker); last by rel_values.
by iApply resp_test_refinement.
Qed.

Theorem nsl_init_ror_secure :
  hypercryptis_secure (guess_wrapped init_test) (λ v v',
    ∃ b g b' g' : bool,
      v = (#b, #g)%V ∧ v' = (#b', #g')%V ∧ b' = negb b ∧ g = g').
Proof.
move=> ? ? ? ?.
apply: (hypercryptis_adequacy (Σ:=#[relocΣ; publicΣ])) => // ? ?.
iIntros "#Hctx". rel_arrow_val. iIntros (adv adv') "#Hadv".
iApply (guess_wrapped_refinement with "Hctx Hadv").
iIntros (b). iApply (refines_app _ _ _ _ lrel_attacker); last by rel_values.
by iApply init_test_refinement.
Qed.
