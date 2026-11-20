(** The privacy game: an attacker that sees two elections with the same
    count per candidate guesses which assignment of votes it watched. *)

From iris.heap_lang.lib Require Import nondet_bool.
From cryptis Require Import cryptis primitives.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib.
From cryptis.hyper.core Require Import public.
From cryptis.hyper.primitives Require Import comp with_cryptis attacker.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples.vote Require Import impl proofs.
From cryptis.hyper Require Import adequacy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!relocG Σ, !publicGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (skT : aenc_key) (skV : sign_key).
Implicit Types (votes cands : list Z) (ks : list sign_key).
Implicit Types (st : list (option (term * term))).

Definition election_guess cands votes : val := λ: "network",
  let: "chan_guess" := "network" #() in
  election_of cands votes "network";;
  let: "guess" := recv "chan_guess" in
  eq_term (TInt 1) "guess".

Definition election_guess_wrapped cands votes0 votes1 : val := λ: "network",
  let: "b" := nondet_bool #() in
  ("b", if: "b" then election_guess cands votes1 "network"
        else election_guess cands votes0 "network").

Lemma election_guess_refinement cands votes votes' :
  votes ≡ₚ votes' →
  hypercryptis_ctx -∗
  REL election_guess cands votes << election_guess cands votes' :
    lrel_attacker → lrel_bool.
Proof.
iIntros (Hperm) "#Hctx". rewrite /election_guess.
rel_arrow_val. iIntros (adv adv') "#Hadv". rel_pures.
rel_apply (refines_new_channel with "Hadv").
iIntros (chan_guess chan_guess') "#Hchan_guess". rel_pures.
rel_bind_l (election_of _ _ _). rel_bind_r (election_of _ _ _).
iApply refines_bind.
{ iApply (refines_app _ _ _ _ lrel_attacker); last by rel_values.
  by iApply election_of_refinement. }
iIntros (? ?) "[-> ->]"=> /=.
rel_pures.
rel_bind_l (recv _). rel_bind_r (recv _).
iApply refines_bind'. iApply refines_recv=> //.
iIntros (guess guess') "#Hguess"=> /=.
rel_pures.
rel_apply_l refines_eq_term_l. rel_apply_r refines_eq_term_r.
rel_values.
iMod (public_part_bij' (E:=⊤) (TInt 1) (TInt 1) guess guess'
        ltac:(solve_ndisj)
        with "Hctx [] Hguess") as %H.
{ by rewrite public_TInt. }
iModIntro. iExists (bool_decide (TInt 1 = guess)). iPureIntro.
split; first done. do 2 f_equal. by apply bool_decide_ext.
Qed.

Lemma election_guess_wrapped_refinement cands votes0 votes1 :
  votes0 ≡ₚ votes1 →
  hypercryptis_ctx -∗
  REL election_guess_wrapped cands votes0 votes1
   << election_guess_wrapped cands votes0 votes1 : lrel_attacker → LRel (λ p1 p2,
    ⌜∃ b g b' g' : bool,
    p1 = (#b, #g)%V ∧ p2 = (#b', #g')%V ∧ b' = negb b ∧ g = g'⌝).
Proof.
iIntros (Hperm) "#Hctx". rewrite /election_guess_wrapped.
rel_arrow_val. iIntros (adv adv') "#Hadv". rel_pures.
rel_apply_l refines_nondet_bool_l. iIntros (choice).
rel_apply_r (refines_nondet_bool_r _ _ (negb choice)).
case: choice; rel_pures.
- rel_bind_l (election_guess _ votes1 _). rel_bind_r (election_guess _ votes0 _).
  iApply refines_bind.
  { iApply (refines_app _ _ _ _ lrel_attacker); last by rel_values.
    by iApply (election_guess_refinement _ (Permutation_sym Hperm) with "Hctx"). }
  iIntros (v v') "(%g & %e & %e')"; subst v v' => /=.
  rel_pures. rel_values.
  iPureIntro. by exists true, g, false, g.
- rel_bind_l (election_guess _ votes0 _). rel_bind_r (election_guess _ votes1 _).
  iApply refines_bind.
  { iApply (refines_app _ _ _ _ lrel_attacker); last by rel_values.
    by iApply (election_guess_refinement _ Hperm with "Hctx"). }
  iIntros (v v') "(%g & %e & %e')"; subst v v' => /=.
  rel_pures. rel_values.
  iPureIntro. by exists false, g, true, g.
Qed.

End Game.

(** Vote privacy as a contextual equivalence: two assignments of votes to
    voters with the same number of votes for every candidate yield
    contextually equivalent elections. *)
Theorem election_game_ctx_equiv cands votes votes' :
  votes ≡ₚ votes' →
  ∅ ⊨ network_game (election_of cands votes)
      =ctx= network_game (election_of cands votes') :
      network_game_ty TUnit.
Proof.
move=> Hperm.
by split;
  apply: (hypercryptis_ctx_refinement (Σ:=#[relocΣ; publicΣ])) => ? ? Δ;
  iIntros "#Hctx"; iApply (election_of_refinement with "Hctx").
Qed.

Theorem election_secure Σ `{!relocPreG Σ, !publicGpreS Σ} cands votes0 votes1
    (adv adv' : expr) σ :
  votes0 ≡ₚ votes1 →
  attacker_valid adv adv' →
  adequate NotStuck (run_network adv (election_guess_wrapped cands votes0 votes1)) σ
    (λ v _, ∃ thp' h v',
       rtc erased_step
         ([run_network adv' (election_guess_wrapped cands votes0 votes1)], σ)
         (of_val v' :: thp', h) ∧
       ∃ b g b' g' : bool,
         v = (#b, #g)%V ∧ v' = (#b', #g')%V ∧ b' = negb b ∧ g = g').
Proof.
move=> Hperm Hadv. apply: hypercryptis_adequacy => // ? ?.
iIntros "#Hctx". by iApply election_guess_wrapped_refinement.
Qed.
