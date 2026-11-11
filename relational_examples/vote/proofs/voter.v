(** Voters: the ballot, the voter thread, and the loops that generate the
    voters' keys and fork the voters. *)

From cryptis Require Import lib cryptis primitives.
From reloc Require Import reloc.
From cryptis.hyper.core Require Import minted_spec term_meta_spec public.
From cryptis.hyper.primitives Require Import with_cryptis.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples.vote Require Import impl.
From cryptis.hyper.examples.vote.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Voter.

Context `{!relocG Σ, !publicGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (skT : aenc_key) (skV : sign_key).
Implicit Types (votes cands : list Z) (ks : list sign_key).
Implicit Types (st : list (option (term * term))).

Lemma ballot_refinement skT skT' skV skV' v v' :
  hypercryptis_ctx -∗
  arb_key skT skT' -∗
  voter_key skV skV' skT skT' v v' -∗
  minted v -∗ minted_spec v' -∗
  term_token (seed_of_sign_key skV) (↑signedN) -∗
  REL ballot skV (Spec.pkey skT) v << ballot skV' (Spec.pkey skT') v' : lrel_term.
Proof.
iIntros "#Hctx (%HnonceT & %HnonceT' & #mint_T & #mint_T' & #pub_pkT & #elem_pkT &
               #secret_T & #secret_T' & #Hurn)".
iIntros "(%HnonceV & %HnonceV' & #mint_V & #mint_V' & #pub_pkV & _ & _ &
          #secret_V & #secret_V' & #Hballot) #mint_v #mint_v' token".
iAssert (minted (Spec.pkey skT)) as "#mint_pkT"; first by rewrite minted_pkey.
iAssert (minted_spec (Spec.pkey skT')) as "#mint_pkT'"; first by rewrite minted_spec_pkey.
rewrite /ballot. rel_pures.
rel_apply (refines_random_aenc (λ _, ∅) (λ _, ∅) skT skT'
  with "Hctx mint_T mint_T' elem_pkT [] mint_v mint_v' [] [] [] []").
{ iIntros "!> %n %n' _ _ #Hs". iExFalso.
  iDestruct (public_nonce_term _ HnonceT with "Hs") as "[Hl _]".
  by iDestruct (secret_in_l_publicly_linked_in_l with "secret_T Hl") as "[]". }
{ iPureIntro. set_solver. }
{ iPureIntro. set_solver. }
{ by iIntros (?); rewrite big_sepS_empty. }
{ by iIntros (?); rewrite big_sepS_empty. }
iIntros (n n') "%Hn %Hn' #mint_n #mint_n' _ _ tc tc' upd".
(* The urn records the ballot, which relates the ciphertexts. *)
iMod (urn_inv_seal (E:=⊤) skT skT' _ _ (PUB⟨ballot_ct skT n v, ballot_ct skT' n' v'⟩)
        ltac:(solve_ndisj) with "Hurn [tc] [tc'] [upd]") as "#pub_c".
{ iApply (term_token_drop with "tc"). solve_ndisj. }
{ iApply (term_token_spec_drop with "tc'"). solve_ndisj. }
{ iIntros (Ek Ek') "%sub %sub' ns".
  by iMod ("upd" $! (⊤ ∖ ↑urnN) Ek Ek' with "[] [//] [//] ns") as "($ & _ & $)";
    first (iPureIntro; solve_ndisj). }
iAssert (PUB⟨ballot_body skT n v, ballot_body skT' n' v'⟩) as "#pub_tgc".
{ rewrite /ballot_body public_tag. by iSplit. }
iMod (ballot_inv_sign _ _ _ _ _ _ n n' with "Hctx Hballot token []") as "#pub_sig";
  [solve_ndisj..| |].
{ iIntros "!> #Hsu".
  by iApply (pub_sign with "mint_V mint_V' secret_V secret_V' pub_pkV pub_tgc Hsu"). }
iModIntro. rel_prims. rel_values. iModIntro. by iApply lrel_term_intro.
Qed.

Lemma voter_refinement c c' skT skT' skV skV' (v v' : Z) :
  hypercryptis_ctx -∗
  lrel_channel c c' -∗
  arb_key skT skT' -∗
  voter_key skV skV' skT skT' (TInt v) (TInt v') -∗
  term_token (seed_of_sign_key skV) (↑signedN) -∗
  REL voter c skV (Spec.pkey skT) #v << voter c' skV' (Spec.pkey skT') #v' : ().
Proof.
iIntros "#Hctx #Hc #HT #HV token".
rewrite /voter. rel_prims.
rel_bind_l (ballot _ _ _). rel_bind_r (ballot _ _ _).
iApply (refines_bind with "[token]").
{ iApply (ballot_refinement with "Hctx HT HV [] [] token"); by rewrite ?minted_TInt ?minted_spec_TInt. }
iIntros (? ?) "(%s & %s' & -> & -> & #Hs)" => /=.
by iApply refines_send.
Qed.


Lemma mk_voters_refinement skT skT' votes votes' :
  length votes = length votes' →
  hypercryptis_ctx -∗
  REL mk_voters (repr votes) << mk_voters (repr votes') : λ v v',
    (∃ ks ks', ⌜v = repr (zip ks votes)⌝ ∗ ⌜v' = repr (zip ks' votes')⌝ ∗
      ⌜length ks = length votes⌝ ∗ ⌜length ks' = length votes'⌝ ∗
      voter_keys skT skT' ks ks' votes votes' ∗ voter_tokens ks)%I.
Proof.
rewrite /= ![@repr_list]unlock.
elim: votes votes' => [|v votes IH] [|v' votes'] //= Hlen; iIntros "#Hctx".
- rel_rec_l. rel_rec_r. rel_pures. rel_values. iModIntro.
  iExists [], []. rewrite /voter_keys /voter_tokens /=. by eauto.
- rel_rec_l. rel_rec_r. rel_pures.
  rel_bind_l (mk_sign_key #()). rel_bind_r (mk_sign_key #()).
  iApply (mk_voter_key_refinement _ _ skT skT' (TInt v) (TInt v') with "Hctx").
  iIntros (sk sk') "#HV tok" => /=.
  rel_pures.
  rel_bind_l (mk_voters _). rel_bind_r (mk_voters _).
  iApply (refines_bind with "[]"); first by iApply IH; first lia.
  iIntros (? ?) "(%ks & %ks' & -> & -> & %Hk & %Hk' & #Hkeys & toks)" => /=.
  rel_pures. rel_values. iModIntro.
  iExists (sk :: ks), (sk' :: ks'). rewrite /voter_keys /voter_tokens /=.
  iFrame "#∗". iPureIntro. by split; last split; last lia.
Qed.

Lemma fork_voters_refinement c c' skT skT' ks ks' votes votes' :
  length votes = length ks → length votes' = length ks' →
  hypercryptis_ctx -∗ lrel_channel c c' -∗ arb_key skT skT' -∗
  voter_keys skT skT' ks ks' votes votes' -∗ voter_tokens ks -∗
  REL fork_voters c (Spec.pkey skT) (repr (zip ks votes))
   << fork_voters c' (Spec.pkey skT') (repr (zip ks' votes')) : ().
Proof.
rewrite /= ![@repr_list]unlock /voter_keys /voter_tokens.
elim: ks ks' votes votes' => [|sk ks IH] ks' votes votes' Hl Hl';
  iIntros "#Hctx #Hc #HT #Hkeys toks".
- iDestruct (big_sepL2_nil_inv_l with "Hkeys") as %->.
  case: votes votes' Hl Hl' => [|??] [|??] //= _ _.
  rel_rec_l. rel_rec_r. rel_pures. by rel_values.
- iDestruct (big_sepL2_cons_inv_l with "Hkeys") as (sk' ks'' ->) "[#HV #Hkeys']".
  case: votes votes' Hl Hl' => [|v votes] [|v' votes'] //= [Hl] [Hl'].
  iDestruct "toks" as "[tok toks]".
  rel_rec_l. rel_rec_r. rel_pures.
  rel_bind_l (Fork _). rel_bind_r (Fork _).
  iApply (refines_bind with "[tok]").
  { iApply refines_fork. rel_pures.
    by iApply (voter_refinement with "Hctx Hc HT HV tok"). }
  iIntros (? ?) "_" => /=. rel_pures.
  by iApply (IH _ votes votes' Hl Hl' with "Hctx Hc HT Hkeys' toks").
Qed.

End Voter.
