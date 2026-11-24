(** * Proofs of the NSL case study

Each role has its own file.  A test creates the honest keys, runs both roles,
and lets R record its session on I's seed.  It then takes the tokens of the
tested session key out of the test's invariant, and reveals the key or a
fresh key.

- [Claim]: the test's invariant, which R fills when it records its session.
- [Tests]: the setup, the reveal, and the two tests. *)

From cryptis.hyper.examples.nsl.proofs Require Export base init resp.
From cryptis Require Import cryptis primitives.
From reloc Require Import reloc.
From cryptis.hyper.core Require Import minted_spec term_meta_spec public.
From cryptis.hyper.primitives Require Import with_cryptis attacker.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples.nsl Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Proofs.

Context `{!relocG Σ, !publicGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (t s : term).

Abbreviation rorN := (nslN.@"ror").
Abbreviation sessN := (nslN.@"sess").
Abbreviation sess2N := (nslN.@"sess_alloc").

Section Claim.

(** The right to take the tokens of the hash out of the test's invariant,
    once. *)
Definition claim skI : iProp := term_token (seed_of_aenc_key skI) (↑claimN).

(** The session that the test may claim: R records it on I's seed. *)
Definition ror_sess skI s s' : iProp :=
  term_meta (seed_of_aenc_key skI) sessN (s, s') ∗ secret_in_l s ∗ secret_in_r s'.

Definition sess_tokens s s' : iProp :=
  term_token (sess_key s) ⊤ ∗ term_token_spec (sess_key s') ⊤.

#[global] Instance ror_sess_persistent skI s s' : Persistent (ror_sess skI s s').
Proof. apply _. Qed.

#[global] Instance ror_sess_timeless skI s s' : Timeless (ror_sess skI s s').
Proof. apply _. Qed.

(** Before R records its session, the invariant holds the token that does
    it; afterwards, the tokens of the session key until the test claims
    them. *)
Definition ror_inv skI : iProp :=
  term_token (seed_of_aenc_key skI) (↑sessN) ∨
  ∃ s s', ror_sess skI s s' ∗ term_token (seed_of_aenc_key skI) (↑sess2N) ∗
    (sess_tokens s s' ∨ claim skI).

Lemma ror_alloc skI :
  hypercryptis_ctx -∗
  inv rorN (ror_inv skI) -∗
  term_token (seed_of_aenc_key skI) (↑sess2N) -∗
  ∀ s s', key_tokens s s' -∗ secret_in_l s -∗ secret_in_r s' ={⊤}=∗ ror_sess skI s s'.
Proof.
iIntros "#Hctx #Hinv tok2" (s s') "(tt_k & tts_k) #sec #sec'".
iInv "Hinv" as "[>tok|(%s0 & %s0' & _ & >tok2' & _)]"; last first.
{ iDestruct (term_token_disj with "tok2 tok2'") as %dis.
  pose proof (nclose_non_empty sess2N). set_solver. }
iMod (term_meta_set sessN (s, s') with "tok") as "#Hm"; first done.
iAssert (ror_sess skI s s') as "#Hs"; first by iFrame "#".
iModIntro. iSplitL; last done.
iNext. iRight. iExists s, s'. iFrame "Hs tok2". iLeft. iFrame.
Qed.

Lemma claim_key E skI skI' skR skR' s s' :
  ↑sealsIN ⊆ E → ↑cryptisN ⊆ E ∖ ↑sealsIN → ↑rorN ⊆ E →
  hypercryptis_ctx -∗
  nsl_ctx skI skI' skR skR' (ror_sess skI) -∗
  inv rorN (ror_inv skI) -∗
  session skI skI' skR skR' s s' -∗ claim skI ={E}=∗
  sess_tokens s s' ∗ secret_in_l s ∗ secret_in_r s'.
Proof.
iIntros (HN HE HE') "#Hctx #Hnsl #Hinv #Hs claim".
iMod (session_sess with "Hctx Hnsl Hs") as (nI nI' nR nR' [Hs1 Hs2]) "(_ & _ & _ & _ & #Hss)";
  [done..|].
rewrite -Hs1 -Hs2. iPoseProof "Hss" as "(Hm & sec & sec')".
iInv "Hinv" as "[>tok|(%s0 & %s0' & >#[Hm0 _] & >tok2 & >slot)]".
{ by iDestruct (term_meta_token with "tok Hm") as "[]". }
iDestruct (term_meta_agree with "Hm Hm0") as %[= <- <-].
iDestruct "slot" as "[toks|claim']"; last first.
{ iDestruct (term_token_disj with "claim claim'") as %dis.
  pose proof (nclose_non_empty claimN). set_solver. }
iModIntro. iSplitR "toks"; last by iFrame "toks sec sec'".
iNext. iRight. iExists s, s'. iFrame "Hss tok2". by iRight.
Qed.

End Claim.

Section Tests.

Lemma setup_refinement adv adv' :
  hypercryptis_ctx -∗
  lrel_attacker adv adv' -∗
  REL setup adv << setup adv' : λ v v',
    (∃ (chan_init chan_init' chan_resp chan_resp' : val)
       (skI skI' skR skR' : aenc_key) (pkX pkX' : term),
      ⌜v = ((chan_init, chan_resp), (skI : term, skR : term, pkX))%V⌝ ∗
      ⌜v' = ((chan_init', chan_resp'), (skI' : term, skR' : term, pkX'))%V⌝ ∗
      lrel_channel chan_init chan_init' ∗ lrel_channel chan_resp chan_resp' ∗
      nsl_ctx skI skI' skR skR' (ror_sess skI) ∗ inv rorN (ror_inv skI) ∗
      claim skI ∗ term_token (seed_of_aenc_key skI) (↑sess2N) ∗ PUB⟨pkX, pkX'⟩)%I.
Proof.
iIntros "#Hctx #Hadv". rewrite /setup. rel_pures.
rel_apply (refines_new_channel with "Hadv").
iIntros (chan_init chan_init') "#Hchan_init". rel_pures.
rel_apply (refines_new_channel with "Hadv").
iIntros (chan_resp chan_resp') "#Hchan_resp". rel_pures.
rel_bind_l (mk_aenc_key #()). rel_bind_r (mk_aenc_key #()).
iApply (mk_honest_key_refinement with "Hctx").
iIntros (skI skI') "#HI sealsI tokI" => /=. rel_pures.
rel_bind_l (mk_aenc_key #()). rel_bind_r (mk_aenc_key #()).
iApply (mk_honest_key_refinement with "Hctx").
iIntros (skR skR') "#HR sealsR _" => /=. rel_pures.
iMod (inv_alloc sealsIN _ (seals_inv skI skI' (seals_I_info skI skI' skR skR' (ror_sess skI)))
        with "[sealsI]") as "#HinvI".
{ iNext. iExists ∅, _, _. iFrame "sealsI".
  iSplit; first by iPureIntro => ?; left; apply nclose_subseteq.
  iSplit; first by iPureIntro => ?; left; apply nclose_subseteq.
  by rewrite !big_sepS_empty. }
iMod (inv_alloc sealsRN _ (seals_inv skR skR' (seals_R_info skI skI'))
        with "[sealsR]") as "#HinvR".
{ iNext. iExists ∅, _, _. iFrame "sealsR".
  iSplit; first by iPureIntro => ?; left; apply nclose_subseteq.
  iSplit; first by iPureIntro => ?; left; apply nclose_subseteq.
  by rewrite !big_sepS_empty. }
rewrite (term_token_difference (seed_of_aenc_key skI) (↑claimN)
           (⊤ ∖ ↑hypercryptisN)); last solve_ndisj.
iDestruct "tokI" as "[claim tokI]".
rewrite (term_token_difference (seed_of_aenc_key skI) (↑sessN)
           (⊤ ∖ ↑hypercryptisN ∖ ↑claimN)); last solve_ndisj.
iDestruct "tokI" as "[tok_sess tokI]".
rewrite (term_token_difference (seed_of_aenc_key skI) (↑sess2N)
           (⊤ ∖ ↑hypercryptisN ∖ ↑claimN ∖ ↑sessN)); last solve_ndisj.
iDestruct "tokI" as "[tok_sess2 _]".
iMod (inv_alloc rorN _ (ror_inv skI) with "[tok_sess]") as "#Hror".
{ iNext. by iLeft. }
rel_prims.
rel_apply (refines_send with "Hchan_init []").
{ iNext. by iDestruct "HI" as "(_ & _ & _ & _ & ? & _)". }
iIntros (? ?) "[-> ->]" => /=. rel_prims.
rel_apply (refines_send with "Hchan_resp []").
{ iNext. by iDestruct "HR" as "(_ & _ & _ & _ & ? & _)". }
iIntros (? ?) "[-> ->]" => /=. rel_pures.
rel_apply (refines_recv with "Hchan_init").
iIntros (pkX pkX') "#HpkX" => /=. rel_pures. rel_values. iModIntro.
iExists chan_init, chan_init', chan_resp, chan_resp'.
iExists skI, skI', skR, skR', pkX, pkX'. do 2 (iSplit; first done).
iFrame "claim tok_sess2 HpkX". by iFrame "#".
Qed.

Lemma reveal_refinement b c c' s s' :
  hypercryptis_ctx -∗
  lrel_channel c c' -∗
  sess_tokens s s' -∗ secret_in_l s -∗ secret_in_r s' -∗
  REL reveal b c (sess_key s) << reveal (negb b) c' (sess_key s') : ().
Proof.
have Hdisj : ∀ k : senc_key, seed_of_senc_key k ∉ ({[k : term]} : gset term).
{ case=> t. rewrite [term_of_senc_key]unlock /= elem_of_singleton => H.
  have := f_equal tsize H. rewrite (tsize_eq (TKey SEnc t)). lia. }
iIntros "#Hctx #Hc (tok & tok') #sec #sec'". rewrite /reveal.
iPoseProof (term_token_minted with "tok") as "#mint".
iPoseProof (term_token_spec_minted_spec with "tok'") as "#mint'".
iEval (rewrite /sess_key minted_senc) in "mint".
iEval (rewrite /sess_key minted_spec_senc) in "mint'".
case: b; rel_pures.
- rel_apply_r (refines_mk_senc_key_r _ _ (λ k, {[k]}) _ Hdisj with "Hctx []").
  { iIntros (?). rewrite big_sepS_singleton. iModIntro. by iSplit; iIntros "?". }
  iIntros ([a']) "%Ha' #mint_k' tok_a' tok_k'". rewrite big_sepS_singleton.
  iEval (rewrite minted_spec_senc) in "mint_k'".
  iMod (public_secret_nonce_r (E:=⊤) Ha' ltac:(solve_ndisj) with "Hctx tok_a'")
    as "[#sec_a' _]".
  iDestruct (term_token_public_token_l with "tok") as "(tok & _ & rel & _)";
    first (rewrite /sess_key; solve_not_TSeal).
  iDestruct (term_token_public_token_r with "tok_k'") as "(tok_k' & _ & rel' & _)";
    first solve_not_TSeal.
  iMod (public_publish (E:=⊤) ltac:(solve_ndisj) with "Hctx [] [rel] [rel'] tok tok_k'")
    as "[_ #Hk]"; [|by rewrite /sess_key [term_of_senc_key]unlock..|].
  { iIntros "!> #link". rewrite /sess_key [term_of_senc_key]unlock public_TKey.
    iSplit; first done. iRight. do 3 (iSplit; first done). iSplit; last done.
    by iApply secret_in_linked. }
  by rel_apply (refines_send with "Hc Hk").
- rel_apply_l (refines_mk_senc_key_l _ _ (λ k, {[k]}) _ Hdisj with "Hctx []").
  { iIntros (?). rewrite big_sepS_singleton. iModIntro. by iSplit; iIntros "?". }
  iIntros ([a]) "%Ha #mint_k tok_a tok_k". rewrite big_sepS_singleton.
  iEval (rewrite minted_senc) in "mint_k".
  iMod (public_secret_nonce_l (E:=⊤) Ha ltac:(solve_ndisj) with "Hctx tok_a")
    as "[#sec_a _]".
  iDestruct (term_token_public_token_l with "tok_k") as "(tok_k & _ & rel & _)";
    first solve_not_TSeal.
  iDestruct (term_token_public_token_r with "tok'") as "(tok' & _ & rel' & _)";
    first (rewrite /sess_key; solve_not_TSeal).
  iMod (public_publish (E:=⊤) ltac:(solve_ndisj) with "Hctx [] [rel] [rel'] tok_k tok'")
    as "[_ #Hk]"; [|by rewrite /sess_key [term_of_senc_key]unlock..|].
  { iIntros "!> #link". rewrite /sess_key [term_of_senc_key]unlock public_TKey.
    iSplit; first done. iRight. do 3 (iSplit; first done). iSplit; last done.
    by iApply secret_in_linked. }
  by rel_apply (refines_send with "Hc Hk").
Qed.

Lemma resp_test_refinement b :
  hypercryptis_ctx -∗
  REL resp_test b << resp_test (negb b) : lrel_attacker → ().
Proof.
iIntros "#Hctx". rewrite /resp_test.
rel_arrow_val. iIntros (adv adv') "#Hadv". rel_pures.
rel_apply (setup_refinement with "Hctx Hadv").
iIntros (? ?) "(%chan_init & %chan_init' & %chan_resp & %chan_resp' &
                %skI & %skI' & %skR & %skR' & %pkX & %pkX' & -> & -> &
                #Hchan_init & #Hchan_resp &
                #Hnsl & #Hror & claim & tok2 & #HpkX)" => /=.
rel_pures.
rel_bind_l (spawn _ _). rel_bind_r (spawn _ _).
iApply (refines_bind with "[]").
{ iApply (refines_spawn with "Hadv"). rel_pures.
  rel_apply (init_refinement with "Hctx Hchan_init Hnsl HpkX").
  iIntros (? ?) "_" => /=. rel_pures. by rel_values. }
iIntros (? ?) "_" => /=. rel_pures.
rel_apply (resp_refinement with "Hctx Hchan_resp Hnsl [tok2]").
{ by iApply (ror_alloc with "Hctx Hror tok2"). }
iIntros (? ?) "[[-> ->]|(%pkI & %pkI' & %k & %k' & [-> ->] & #HpkI & Hsess)]" => /=.
{ rel_pures. by rel_values. }
rel_prims.
iPoseProof "Hnsl" as "((_ & _ & _ & _ & #pub_pkI & _) & _)".
iMod (public_part_bij' (E:=⊤) with "Hctx HpkI pub_pkI") as %HX;
  first solve_ndisj.
case: (decide (pkI = Spec.pkey skI)) => [eX|neX]; last first.
{ rewrite bool_decide_eq_false_2 // bool_decide_eq_false_2; last by rewrite -HX.
  rel_pures. by rel_values. }
rewrite bool_decide_eq_true_2 // bool_decide_eq_true_2; last by apply HX.
rel_pures.
iDestruct ("Hsess" with "[//]") as (s s' [-> ->]) "Hs".
iMod (claim_key with "Hctx Hnsl Hror Hs claim") as "(toks & #sec & #sec')"; [solve_ndisj..|].
by iApply (reveal_refinement with "Hctx Hchan_resp toks sec sec'").
Qed.

Lemma init_test_refinement b :
  hypercryptis_ctx -∗
  REL init_test b << init_test (negb b) : lrel_attacker → ().
Proof.
iIntros "#Hctx". rewrite /init_test.
rel_arrow_val. iIntros (adv adv') "#Hadv". rel_pures.
rel_apply (setup_refinement with "Hctx Hadv").
iIntros (? ?) "(%chan_init & %chan_init' & %chan_resp & %chan_resp' &
                %skI & %skI' & %skR & %skR' & %pkX & %pkX' & -> & -> &
                #Hchan_init & #Hchan_resp &
                #Hnsl & #Hror & claim & tok2 & #HpkX)" => /=.
rel_pures. rel_prims.
rel_bind_l (spawn _ _). rel_bind_r (spawn _ _).
iApply (refines_bind with "[tok2]").
{ iApply (refines_spawn with "Hadv"). rel_pures.
  rel_apply (resp_refinement with "Hctx Hchan_resp Hnsl [tok2]").
  { by iApply (ror_alloc with "Hctx Hror tok2"). }
  iIntros (? ?) "_" => /=. rel_pures. by rel_values. }
iIntros (? ?) "_" => /=. rel_pures.
rel_apply (init_refinement with "Hctx Hchan_init Hnsl HpkX").
iIntros (? ?) "[[-> ->]|(%k & %k' & [-> ->] & Hsess)]" => /=.
{ rel_pures. by rel_values. }
rel_prims.
iPoseProof "Hnsl" as "(_ & (_ & _ & _ & _ & #pub_pkR & _) & _)".
iMod (public_part_bij' (E:=⊤) with "Hctx HpkX pub_pkR") as %HX;
  first solve_ndisj.
case: (decide (pkX = Spec.pkey skR)) => [eX|neX]; last first.
{ rewrite bool_decide_eq_false_2 // bool_decide_eq_false_2; last by rewrite -HX.
  rel_pures. by rel_values. }
rewrite bool_decide_eq_true_2 // bool_decide_eq_true_2; last by apply HX.
rel_pures.
iDestruct ("Hsess" with "[//]") as (s s' [-> ->]) "Hs".
iMod (claim_key with "Hctx Hnsl Hror Hs claim") as "(toks & #sec & #sec')"; [solve_ndisj..|].
by iApply (reveal_refinement with "Hctx Hchan_init toks sec sec'").
Qed.

End Tests.

End Proofs.
