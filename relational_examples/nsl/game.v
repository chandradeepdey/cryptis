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

Definition guess (test : val) : val := λ: "c",
  test "c";;
  let: "guess" := recv "c" in
  eq_term (TInt 1) "guess".

Definition guess_wrapped (test : bool → val) : val := λ: "c",
  let: "b" := nondet_bool #() in
  ("b", if: "b" then guess (test true) "c" else guess (test false) "c").

Section Game.

Context `{!relocG Σ, !publicGS Σ}.

Lemma guess_refinement (test test' : val) c c' :
  hypercryptis_ctx -∗
  lrel_channel c c' -∗
  (REL test c << test' c' : ()) -∗
  REL guess test c << guess test' c' : lrel_bool.
Proof.
iIntros "#Hctx #Hc Htest". rewrite /guess. rel_pures.
rel_bind_l (test c). rel_bind_r (test' c').
iApply (refines_bind with "Htest").
iIntros (? ?) "_" => /=. rel_pures.
rel_apply (refines_recv with "Hc").
iIntros (g g') "#Hg" => /=.
rel_prims. rel_values.
iMod (public_part_bij' (E:=⊤) (TInt 1) (TInt 1) g g'
        ltac:(solve_ndisj) with "Hctx [] Hg") as %H.
{ by rewrite public_TInt. }
iModIntro. iExists (bool_decide (TInt 1 = g)). iPureIntro.
split; first done. do 2 f_equal. by apply bool_decide_ext.
Qed.

Lemma guess_wrapped_refinement (test : bool → val) c c' :
  hypercryptis_ctx -∗
  lrel_channel c c' -∗
  (∀ b, REL test b c << test (negb b) c' : ()) -∗
  REL guess_wrapped test c << guess_wrapped test c' : λ p1 p2,
    ⌜∃ b g b' g' : bool,
    p1 = (#b, #g)%V ∧ p2 = (#b', #g')%V ∧ b' = negb b ∧ g = g'⌝.
Proof.
iIntros "#Hctx #Hc Htest". rewrite /guess_wrapped.
rel_pures.
rel_apply_l refines_nondet_bool_l. iIntros (choice).
rel_apply_r (refines_nondet_bool_r _ _ (negb choice)).
case: choice; rel_pures.
- rel_apply (guess_refinement with "Hctx Hc Htest").
  iIntros (v v') "(%g & %e & %e')"; subst v v' => /=.
  rel_pures. rel_values.
  iPureIntro. by exists true, g, false, g.
- rel_apply (guess_refinement with "Hctx Hc Htest").
  iIntros (v v') "(%g & %e & %e')"; subst v v' => /=.
  rel_pures. rel_values.
  iPureIntro. by exists false, g, true, g.
Qed.

End Game.

Definition ror_game (test : bool → val) (b : bool) (adv : expr) : expr :=
  (run_network adv (guess (test b)))%E.

(** Real-or-random secrecy of the responder's session key as a contextual
    equivalence: against any pair of valid attackers, when R's peer is I,
    no well-typed context can tell the session key from a fresh key. *)
Theorem nsl_resp_ror_ctx_equiv adv adv' :
  attacker_valid adv adv' → attacker_valid adv' adv →
  ∅ ⊨ ror_game resp_test true adv =ctx= ror_game resp_test false adv' : TBool.
Proof.
move=> Hadv Hadv'; split;
  apply: (hypercryptis_ctx_refinement (Σ:=#[relocΣ; publicΣ])) => // ? ? Δ;
  iIntros "#Hctx"; rel_arrow_val; iIntros (c c') "#Hc";
  iApply (guess_refinement with "Hctx Hc");
  [iApply (resp_test_refinement true) | iApply (resp_test_refinement false)]; by iFrame "#".
Qed.

(** The same fact for the initiator's session key, when I's peer is R. *)
Theorem nsl_init_ror_ctx_equiv adv adv' :
  attacker_valid adv adv' → attacker_valid adv' adv →
  ∅ ⊨ ror_game init_test true adv =ctx= ror_game init_test false adv' : TBool.
Proof.
move=> Hadv Hadv'; split;
  apply: (hypercryptis_ctx_refinement (Σ:=#[relocΣ; publicΣ])) => // ? ? Δ;
  iIntros "#Hctx"; rel_arrow_val; iIntros (c c') "#Hc";
  iApply (guess_refinement with "Hctx Hc");
  [iApply (init_test_refinement true) | iApply (init_test_refinement false)]; by iFrame "#".
Qed.

Theorem nsl_resp_ror_secure Σ `{!relocPreG Σ, !publicGpreS Σ} (adv adv' : expr) σ :
  attacker_valid adv adv' →
  adequate NotStuck (run_network adv (guess_wrapped resp_test)) σ
    (λ v _, ∃ thp' h v',
       rtc erased_step ([run_network adv' (guess_wrapped resp_test)], σ)
         (of_val v' :: thp', h) ∧
       ∃ b g b' g' : bool,
         v = (#b, #g)%V ∧ v' = (#b', #g')%V ∧ b' = negb b ∧ g = g').
Proof.
move=> Hadv. apply: hypercryptis_adequacy => // ? ?.
iIntros "#Hctx". rel_arrow_val. iIntros (c c') "#Hc".
iApply (guess_wrapped_refinement with "Hctx Hc").
iIntros (b). by iApply resp_test_refinement.
Qed.

Theorem nsl_init_ror_secure Σ `{!relocPreG Σ, !publicGpreS Σ} (adv adv' : expr) σ :
  attacker_valid adv adv' →
  adequate NotStuck (run_network adv (guess_wrapped init_test)) σ
    (λ v _, ∃ thp' h v',
       rtc erased_step ([run_network adv' (guess_wrapped init_test)], σ)
         (of_val v' :: thp', h) ∧
       ∃ b g b' g' : bool,
         v = (#b, #g)%V ∧ v' = (#b', #g')%V ∧ b' = negb b ∧ g = g').
Proof.
move=> Hadv. apply: hypercryptis_adequacy => // ? ?.
iIntros "#Hctx". rel_arrow_val. iIntros (c c') "#Hc".
iApply (guess_wrapped_refinement with "Hctx Hc").
iIntros (b). by iApply init_test_refinement.
Qed.
