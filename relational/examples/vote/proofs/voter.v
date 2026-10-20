(** Voters: the ballot, the voter thread, and the loops that generate the
    voters' keys and fork the voters. *)

From cryptis Require Import lib cryptis primitives.
From cryptis.lib Require Import avl.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.core Require Import minted_spec term_meta_spec rel rel_inv_updates.
From cryptis.hyper.primitives Require Import simple_spec comp_spec with_cryptis_spec attacker_spec.
From cryptis.hyper.lib Require Import avl_spec.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples.vote Require Import impl.
From cryptis.hyper.examples.vote.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Voter.

Context `{!relocG Σ, !public_relGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (skT : aenc_key) (skV : sign_key).
Implicit Types (votes cands : list Z) (ks : list sign_key).
Implicit Types (st : list (option (term * term))).

Lemma rel_ballot skT skT' skV skV' v v' :
  cryptis_rel_ctx -∗
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
(* The ciphertext is randomized; its tagging and signature are fresh on top. *)
rel_apply (rel_random_aenc
  (λ n, {[ Spec.tag (Tag (voteN.@"ballot")) (ballot_ct skT n v);
           Spec.enc skV (Tag (voteN.@"ballot")) (ballot_ct skT n v) ]})
  (λ n', {[ Spec.tag (Tag (voteN.@"ballot")) (ballot_ct skT' n' v');
            Spec.enc skV' (Tag (voteN.@"ballot")) (ballot_ct skT' n' v') ]})
  skT skT' with "Hctx [//] mint_T mint_T' elem_pkT secret_T mint_v mint_v' [] [] [] []").
{ iPureIntro. move=> n Hn. rewrite /random_terms /ballot_ct. solve_term_disj. }
{ iPureIntro. move=> n' Hn'. rewrite /random_terms /ballot_ct. solve_term_disj. }
{ rewrite /ballot_ct. solve_minted_iff. }
{ rewrite /ballot_ct. solve_minted_iff. }
iIntros (n n') "%Hn %Hn' #mint_n #mint_n' tok tok' upd".
split_term_tokens.
iDestruct "tok" as "[tt_tgc tt_sig]". iDestruct "tok'" as "[tts_tgc tts_sig]".
(* The urn records the ballot, which links the ciphertexts. *)
iMod (urn_inv_insert (E:=⊤) _ _ (random_seal skT skT' (voteN.@"vote") n n' v v')
        (PUB⟨ballot_ct skT n v, ballot_ct skT' n' v'⟩) ltac:(solve_ndisj)
        with "Hurn [upd]") as "#pub_c".
{ iIntros (S S') "seals seals'". iApply ("upd" with "[] seals seals'").
  iPureIntro. solve_ndisj. }
(* The tagged ciphertexts are publicly related. *)
iMod (public_rel_publish (E:=⊤) ltac:(solve_ndisj) with "Hctx [] tt_tgc tts_tgc")
  as "[#elem_tgc #pub_tgc]".
{ iIntros "!> _". rewrite publicly_related_tag. by iSplit. }
(* The signatures are publicly related. *)
iMod (ballot_inv_sign _ _ _ _ _ _ n n' with "Hballot token") as "[#Hsl #Hsr]";
  first solve_ndisj.
iMod (public_rel_publish (E:=⊤) ltac:(solve_ndisj) with "Hctx [] tt_sig tts_sig")
  as "[_ #pub_sig]".
{ iIntros "!> #elem_sig".
  by iApply (pub_sign with "mint_V mint_V' secret_V secret_V' pub_pkV pub_tgc elem_tgc Hsl Hsr elem_sig"). }
(* Run the program. *)
iModIntro. rel_prims. rel_values. iModIntro. by iApply lrel_term_intro.
Qed.

Lemma rel_voter c c' skT skT' skV skV' (v v' : Z) :
  cryptis_rel_ctx -∗
  channel_rel c c' -∗
  arb_key skT skT' -∗
  voter_key skV skV' skT skT' (TInt v) (TInt v') -∗
  term_token (seed_of_sign_key skV) (↑signedN) -∗
  REL voter c skV (Spec.pkey skT) #v << voter c' skV' (Spec.pkey skT') #v' : ().
Proof.
iIntros "#Hctx #Hc #HT #HV token".
rewrite /voter. rel_prims.
rel_bind_l (ballot _ _ _). rel_bind_r (ballot _ _ _).
iApply (refines_bind with "[token]").
{ iApply (rel_ballot with "Hctx HT HV [] [] token"); by rewrite ?minted_TInt ?minted_spec_TInt. }
iIntros (? ?) "(%s & %s' & -> & -> & #Hs)" => /=.
by iApply rel_send.
Qed.


Lemma rel_mk_voters skT skT' votes votes' :
  length votes = length votes' →
  cryptis_rel_ctx -∗
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
  iApply (rel_mk_voter_key _ _ skT skT' (TInt v) (TInt v') with "Hctx").
  iIntros (sk sk') "#HV tok" => /=.
  rel_pures.
  rel_bind_l (mk_voters _). rel_bind_r (mk_voters _).
  iApply (refines_bind with "[]"); first by iApply IH; first lia.
  iIntros (? ?) "(%ks & %ks' & -> & -> & %Hk & %Hk' & #Hkeys & toks)" => /=.
  rel_pures. rel_values. iModIntro.
  iExists (sk :: ks), (sk' :: ks'). rewrite /voter_keys /voter_tokens /=.
  iFrame "#∗". iPureIntro. by split; last split; last lia.
Qed.

Lemma rel_fork_voters c c' skT skT' ks ks' votes votes' :
  length votes = length ks → length votes' = length ks' →
  cryptis_rel_ctx -∗ channel_rel c c' -∗ arb_key skT skT' -∗
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
    by iApply (rel_voter with "Hctx Hc HT HV tok"). }
  iIntros (? ?) "_" => /=. rel_pures.
  by iApply (IH _ votes votes' Hl Hl' with "Hctx Hc HT Hkeys' toks").
Qed.

End Voter.
