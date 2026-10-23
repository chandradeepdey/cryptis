(** The privacy game: an attacker that sees two elections with the same
    count per candidate guesses which assignment of votes it watched. *)

From iris.heap_lang.lib Require Import nondet_bool.
From cryptis Require Import lib cryptis primitives.
From cryptis.lib Require Import avl.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.core Require Import minted_spec term_meta_spec rel rel_inv_updates.
From cryptis.hyper.primitives Require Import simple_spec comp_spec with_cryptis_spec attacker_spec.
From cryptis.hyper.lib Require Import avl_spec.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples.vote Require Import impl proofs.
From cryptis.hyper Require Import rel_adequacy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!relocG Σ, !public_relGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (skT : aenc_key) (skV : sign_key).
Implicit Types (votes cands : list Z) (ks : list sign_key).
Implicit Types (st : list (option (term * term))).

Definition election_guess cands votes : val := λ: "c",
  election_of cands votes "c";;
  let: "guess" := recv "c" in
  eq_term (TInt 1) "guess".

Definition election_guess_wrapped cands votes0 votes1 : val := λ: "c",
  let: "b" := nondet_bool #() in
  ("b", if: "b" then election_guess cands votes1 "c"
        else election_guess cands votes0 "c").

Lemma rel_election_guess c c' cands votes votes' :
  votes ≡ₚ votes' →
  cryptis_rel_ctx -∗
  channel_rel c c' -∗
  REL election_guess cands votes c << election_guess cands votes' c' : lrel_bool.
Proof.
iIntros (Hperm) "#Hctx #Hc". rewrite /election_guess.
rel_pures.
rel_bind_l (election_of _ _ _). rel_bind_r (election_of _ _ _).
iApply refines_bind; first by iApply rel_election_of.
iIntros (? ?) "[-> ->]"=> /=.
rel_pures.
rel_bind_l (recv _). rel_bind_r (recv _).
iApply refines_bind'. iApply rel_recv=> //.
iIntros (guess guess') "#Hguess"=> /=.
rel_pures.
rel_apply_l rel_eq_term_l. rel_apply_r rel_eq_term_r.
rel_values.
iMod (publicly_related_part_bij' (E:=⊤) (TInt 1) (TInt 1) guess guess'
        ltac:(solve_ndisj)
        with "Hctx [] Hguess") as %H.
{ by rewrite publicly_related_TInt. }
iModIntro. iExists (bool_decide (TInt 1 = guess)). iPureIntro.
split; first done. do 2 f_equal. by apply bool_decide_ext.
Qed.

Lemma rel_election_guess_wrapped c c' cands votes0 votes1 :
  votes0 ≡ₚ votes1 →
  cryptis_rel_ctx -∗
  channel_rel c c' -∗
  REL election_guess_wrapped cands votes0 votes1 c
   << election_guess_wrapped cands votes0 votes1 c' : λ p1 p2,
    ⌜∃ b g b' g' : bool,
    p1 = (#b, #g)%V ∧ p2 = (#b', #g')%V ∧ b' = negb b ∧ g = g'⌝.
Proof.
iIntros (Hperm) "#Hctx #Hc". rewrite /election_guess_wrapped.
rel_pures.
rel_apply_l rel_nondet_bool_l. iIntros (choice).
rel_apply_r (rel_nondet_bool_r _ _ (negb choice)).
case: choice; rel_pures.
- rel_bind_l (election_guess _ votes1 _). rel_bind_r (election_guess _ votes0 _).
  iApply refines_bind;
    first by iApply (rel_election_guess _ _ _ (Permutation_sym Hperm) with "Hctx Hc").
  iIntros (v v') "(%g & %e & %e')"; subst v v' => /=.
  rel_pures. rel_values.
  iPureIntro. by exists true, g, false, g.
- rel_bind_l (election_guess _ votes0 _). rel_bind_r (election_guess _ votes1 _).
  iApply refines_bind; first by iApply (rel_election_guess _ _ _ Hperm with "Hctx Hc").
  iIntros (v v') "(%g & %e & %e')"; subst v v' => /=.
  rel_pures. rel_values.
  iPureIntro. by exists false, g, true, g.
Qed.

End Game.

Definition election_game (cands votes : list Z) : expr :=
  (λ: "adv", run_network_rel "adv" (election_of cands votes))%E.

(** Vote privacy as a contextual equivalence: two assignments of votes to
    voters with the same number of votes for every candidate yield
    contextually equivalent elections. *)
Theorem election_ctx_equiv cands votes votes' :
  votes ≡ₚ votes' →
  ∅ ⊨ election_game cands votes =ctx= election_game cands votes' :
      (attacker_ty → ())%ty.
Proof.
move=> Hperm.
by split; apply: (cryptis_ctx_refinement (Σ:=#[relocΣ; public_relΣ])) => ? ? Δ c c';
  iApply rel_election_of.
Qed.

(** The same fact as an adequacy statement for the nondeterministic game:
    whenever a run terminates with a bit [b] and a guess [g], the run with the
    other assignment can terminate with the same guess. *)
Theorem election_secure Σ `{!relocPreG Σ, !public_relGpreS Σ} cands votes0 votes1
    (adv : val) σ :
  votes0 ≡ₚ votes1 →
  (∀ `{!relocG Σ}, ⊢ REL adv << adv : attacker_rel) →
  adequate NotStuck (run_network_rel adv (election_guess_wrapped cands votes0 votes1)) σ
    (λ v _, ∃ thp' h v',
       rtc erased_step
         ([run_network_rel adv (election_guess_wrapped cands votes0 votes1)], σ)
         (of_val v' :: thp', h) ∧
       ∃ b g b' g' : bool,
         v = (#b, #g)%V ∧ v' = (#b', #g')%V ∧ b' = negb b ∧ g = g').
Proof.
move=> Hperm Hadv. apply: cryptis_rel_adequacy => // ? ? c c'.
by iApply rel_election_guess_wrapped.
Qed.
