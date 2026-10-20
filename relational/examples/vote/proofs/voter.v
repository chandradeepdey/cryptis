(** Voters: the ballot, the voter thread, and the loops that generate the
    voters' keys and fork the voters. *)

From cryptis Require Import lib cryptis primitives.
From cryptis.lib Require Import avl.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.core Require Import minted_spec term_meta_spec rel rel_inv_updates.
From cryptis.hyper.primitives Require Import simple_spec comp_spec with_cryptis_spec attacker_spec.
From cryptis.hyper.lib Require Import avl_spec.
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
rewrite /ballot. rel_pures_l. rel_pures_r.
rel_apply_l (rel_mk_nonce_l _ _
  (λ n, {[ n;
           TPair n v;
           Spec.tag (Tag (voteN.@"vote")) (TPair n v);
           ballot_ct skT n v;
           Spec.tag (Tag (voteN.@"ballot")) (ballot_ct skT n v);
           Spec.enc skV (Tag (voteN.@"ballot")) (ballot_ct skT n v) ]})
  with "[//]").
{ iIntros "%t". rewrite big_sepS_forall. iIntros (t' Ht').
  rewrite !elem_of_union !elem_of_singleton in Ht'.
  case: Ht' => [[[[[->|->]|->]|->]|->]|->]; iModIntro.
  - by iSplit; iIntros "?".
  - rewrite minted_TPair.
    iSplit; iIntros "#H"; [by iFrame "#" | by iDestruct "H" as "[? _]"].
  - rewrite minted_tag minted_TPair.
    iSplit; iIntros "#H"; [by iFrame "#" | by iDestruct "H" as "[? _]"].
  - rewrite /ballot_ct /Spec.enc !(minted_TSeal, minted_tag) minted_TPair.
    iSplit; iIntros "#H"; [by iFrame "#" | by iDestruct "H" as "[_ [? _]]"].
  - rewrite /ballot_ct /Spec.enc !(minted_TSeal, minted_tag) minted_TPair.
    iSplit; iIntros "#H"; [by iFrame "#" | by iDestruct "H" as "[_ [? _]]"].
  - rewrite /ballot_ct /Spec.enc !(minted_TSeal, minted_tag) minted_TPair.
    iSplit; iIntros "#H"; [by iFrame "#" | by iDestruct "H" as "[_ [_ [? _]]]"]. }
iIntros (n) "%Hn #mint_n Htt".
rel_apply_r (rel_mk_nonce_r _ _
  (λ n, {[ n;
           TPair n v';
           Spec.tag (Tag (voteN.@"vote")) (TPair n v');
           ballot_ct skT' n v';
           Spec.tag (Tag (voteN.@"ballot")) (ballot_ct skT' n v');
           Spec.enc skV' (Tag (voteN.@"ballot")) (ballot_ct skT' n v') ]})
  with "[//]").
{ iIntros "%t". rewrite big_sepS_forall. iIntros (t' Ht').
  rewrite !elem_of_union !elem_of_singleton in Ht'.
  case: Ht' => [[[[[->|->]|->]|->]|->]|->]; iModIntro.
  - by iSplit; iIntros "?".
  - rewrite minted_spec_TPair.
    iSplit; iIntros "#H"; [by iFrame "#" | by iDestruct "H" as "[? _]"].
  - rewrite minted_spec_tag minted_spec_TPair.
    iSplit; iIntros "#H"; [by iFrame "#" | by iDestruct "H" as "[? _]"].
  - rewrite /ballot_ct /Spec.enc !(minted_spec_TSeal, minted_spec_tag) minted_spec_TPair.
    iSplit; iIntros "#H"; [by iFrame "#" | by iDestruct "H" as "[_ [? _]]"].
  - rewrite /ballot_ct /Spec.enc !(minted_spec_TSeal, minted_spec_tag) minted_spec_TPair.
    iSplit; iIntros "#H"; [by iFrame "#" | by iDestruct "H" as "[_ [? _]]"].
  - rewrite /ballot_ct /Spec.enc !(minted_spec_TSeal, minted_spec_tag) minted_spec_TPair.
    iSplit; iIntros "#H"; [by iFrame "#" | by iDestruct "H" as "[_ [_ [? _]]]"]. }
iIntros (n') "%Hn' #mint_spec_n' Htts".
set pl := TPair n v.
set tg := Spec.tag (Tag (voteN.@"vote")) pl.
set c := ballot_ct skT n v.
set tgc := Spec.tag (Tag (voteN.@"ballot")) c.
set sig := Spec.enc skV (Tag (voteN.@"ballot")) c.
set pl' := TPair n' v'.
set tg' := Spec.tag (Tag (voteN.@"vote")) pl'.
set c' := ballot_ct skT' n' v'.
set tgc' := Spec.tag (Tag (voteN.@"ballot")) c'.
set sig' := Spec.enc skV' (Tag (voteN.@"ballot")) c'.
case/is_nonceP: (Hn) => [an En]. case/is_nonceP: (Hn') => [an' En'].
(* Split the tokens. *)
have Hd_pl : ({[n]} : gset term) ## {[pl]}.
{ rewrite /pl En /=. set_solver. }
have Hd_tg : ({[n]} ∪ {[pl]} : gset term) ## {[tg]}.
{ rewrite /tg /pl [Spec.tag]unlock [Tag]unlock En /=. set_solver. }
have Hd_c : ({[n]} ∪ {[pl]} ∪ {[tg]} : gset term) ## {[c]}.
{ rewrite /c /tg /pl /ballot_ct /Spec.enc [Spec.tag]unlock [Tag]unlock En /=. set_solver. }
have Hd_tgc : ({[n]} ∪ {[pl]} ∪ {[tg]} ∪ {[c]} : gset term) ## {[tgc]}.
{ rewrite /tgc /c /tg /pl /ballot_ct /Spec.enc [Spec.tag]unlock [Tag]unlock En /=. set_solver. }
have Hd_sig : ({[n]} ∪ {[pl]} ∪ {[tg]} ∪ {[c]} ∪ {[tgc]} : gset term) ## {[sig]}.
{ rewrite /sig /tgc /c /tg /pl /ballot_ct /Spec.enc [Spec.tag]unlock [Tag]unlock En /=.
  set_solver. }
have Hd_pl' : ({[n']} : gset term) ## {[pl']}.
{ rewrite /pl' En' /=. set_solver. }
have Hd_tg' : ({[n']} ∪ {[pl']} : gset term) ## {[tg']}.
{ rewrite /tg' /pl' [Spec.tag]unlock [Tag]unlock En' /=. set_solver. }
have Hd_c' : ({[n']} ∪ {[pl']} ∪ {[tg']} : gset term) ## {[c']}.
{ rewrite /c' /tg' /pl' /ballot_ct /Spec.enc [Spec.tag]unlock [Tag]unlock En' /=. set_solver. }
have Hd_tgc' : ({[n']} ∪ {[pl']} ∪ {[tg']} ∪ {[c']} : gset term) ## {[tgc']}.
{ rewrite /tgc' /c' /tg' /pl' /ballot_ct /Spec.enc [Spec.tag]unlock [Tag]unlock En' /=.
  set_solver. }
have Hd_sig' : ({[n']} ∪ {[pl']} ∪ {[tg']} ∪ {[c']} ∪ {[tgc']} : gset term) ## {[sig']}.
{ rewrite /sig' /tgc' /c' /tg' /pl' /ballot_ct /Spec.enc [Spec.tag]unlock [Tag]unlock En' /=.
  set_solver. }
rewrite !big_sepS_union // !big_sepS_singleton.
iDestruct "Htt" as "(((((tt_n & tt_pl) & tt_tg) & tt_c) & tt_tgc) & tt_sig)".
iDestruct "Htts" as "(((((tts_n & tts_pl) & tts_tg) & tts_c) & tts_tgc) & tts_sig)".
iDestruct (token_flow_map with "tt_n") as "(tt_n_flow & tt_n_map & _)".
iDestruct (token_flow_map with "tt_pl") as "(tt_pl_flow & tt_pl_map & _)".
iDestruct (token_flow_map with "tt_tg") as "(_ & tt_tg_map & _)".
iDestruct (token_flow_map with "tt_c") as "(tt_c_flow & tt_c_map & _)".
iDestruct (token_flow_map with "tt_tgc") as "(tt_tgc_flow & tt_tgc_map & _)".
iDestruct (token_flow_map with "tt_sig") as "(tt_sig_flow & tt_sig_map & _)".
iDestruct (token_spec_flow_map with "tts_n") as "(tts_n_flow & tts_n_map & _)".
iDestruct (token_spec_flow_map with "tts_pl") as "(tts_pl_flow & tts_pl_map & _)".
iDestruct (token_spec_flow_map with "tts_tg") as "(_ & tts_tg_map & _)".
iDestruct (token_spec_flow_map with "tts_c") as "(tts_c_flow & tts_c_map & _)".
iDestruct (token_spec_flow_map with "tts_tgc") as "(tts_tgc_flow & tts_tgc_map & _)".
iDestruct (token_spec_flow_map with "tts_sig") as "(tts_sig_flow & tts_sig_map & _)".
(* The tagged payload is protected by the chain nonce → payload → tagged payload. *)
have Hsub_pl : is_immediate_subterm n pl by exact: SubtermPairL.
have Hsub_tg : is_immediate_subterm pl tg.
{ rewrite /tg [Spec.tag]unlock. exact: SubtermPairR. }
have Hsub_pl' : is_immediate_subterm n' pl' by exact: SubtermPairL.
have Hsub_tg' : is_immediate_subterm pl' tg'.
{ rewrite /tg' [Spec.tag]unlock. exact: SubtermPairR. }
iMod (public_rel_flow_l_extend (E:=⊤) n ltac:(solve_ndisj)
        with "Hctx tt_n_flow") as "prot_n".
iMod (public_rel_flow_l_grow_5 (E:=⊤) Hn ltac:(solve_ndisj) Hsub_pl
        with "Hctx prot_n tt_n_map") as "(prot_n & protby_pl & tt_n_map)".
iMod (public_rel_flow_l_extend (E:=⊤) pl ltac:(solve_ndisj)
        with "Hctx tt_pl_flow") as "prot_pl".
iMod (public_rel_flow_l_grow_3 (E:=⊤) n ltac:(solve_ndisj) Hsub_tg
        with "Hctx protby_pl prot_pl tt_pl_map") as "(prot_pl & protby_tg & protby_pl & tt_pl_map)".
iMod (public_rel_flow_r_extend (E:=⊤) n' ltac:(solve_ndisj)
        with "Hctx tts_n_flow") as "prot_n'".
iMod (public_rel_flow_r_grow_5 (E:=⊤) Hn' ltac:(solve_ndisj) Hsub_pl'
        with "Hctx prot_n' tts_n_map") as "(prot_n' & protby_pl' & tts_n_map)".
iMod (public_rel_flow_r_extend (E:=⊤) pl' ltac:(solve_ndisj)
        with "Hctx tts_pl_flow") as "prot_pl'".
iMod (public_rel_flow_r_grow_3 (E:=⊤) n' ltac:(solve_ndisj) Hsub_tg'
        with "Hctx protby_pl' prot_pl' tts_pl_map") as "(prot_pl' & protby_tg' & protby_pl' & tts_pl_map)".
iMod (linked_extend (E:=⊤) tg tg' pl pl' ltac:(solve_ndisj)
        with "Hctx protby_tg protby_tg' tt_tg_map tts_tg_map") as "(_ & _ & #priv_tg & _ & _)".
(* The arbitrator's secret key can never become publicly related. *)
iAssert (□ (PUB⟨skT, skT'⟩ → PUB⟨pl, pl'⟩))%I as "#Hbox".
{ iIntros "!> #Hsk". iExFalso.
  rewrite publicly_related_adec_key'.
  iDestruct (publicly_related_nonce_term _ HnonceT with "Hsk") as "[Hl _]".
  by iDestruct (secret_in_l_publicly_linked_in_l with "secret_T Hl") as "[]". }
(* The ciphertexts are publicly related. *)
iAssert (minted pl) as "#mint_pl".
{ rewrite /pl minted_TPair. by iFrame "#". }
iAssert (minted_spec pl') as "#mint_spec_pl'".
{ rewrite /pl' minted_spec_TPair. by iFrame "#". }
iMod (urn_inv_insert _ _ (Some (skT : term, tg), Some (skT' : term, tg'))
        with "Hurn") as "[#Hin_l #Hin_r]"; first solve_ndisj.
iAssert (□ (publicly_linked c c' -∗ PUB⟨c, c'⟩))%I as "#Hwand_c".
{ iIntros "!> #elem_c". rewrite /c /c' /ballot_ct publicly_related_aenc. iRight.
  do 5 (iSplit; first done).
  iSplit; first by iApply publicly_linked_linked.
  iSplit; first done. iSplit; first done.
  by iApply (wf_seal_rel_aenc_intro with "Hin_l Hin_r"). }
iMod (public_rel_flow_l_extend (E:=⊤) c ltac:(solve_ndisj)
        with "Hctx tt_c_flow") as "prot_c".
iMod (public_rel_flow_r_extend (E:=⊤) c' ltac:(solve_ndisj)
        with "Hctx tts_c_flow") as "prot_c'".
iMod (public_rel_extend (E:=⊤) c c' ltac:(solve_ndisj)
        with "Hctx Hwand_c prot_c prot_c' tt_c_map tts_c_map") as "#elem_c".
iPoseProof ("Hwand_c" with "elem_c") as "#pub_c".
(* The tagged ciphertexts are publicly related. *)
iMod (public_rel_flow_l_extend (E:=⊤) tgc ltac:(solve_ndisj)
        with "Hctx tt_tgc_flow") as "prot_tgc".
iMod (public_rel_flow_r_extend (E:=⊤) tgc' ltac:(solve_ndisj)
        with "Hctx tts_tgc_flow") as "prot_tgc'".
iMod (public_rel_extend (E:=⊤) tgc tgc' ltac:(solve_ndisj)
        with "Hctx [] prot_tgc prot_tgc' tt_tgc_map tts_tgc_map") as "#elem_tgc".
{ iIntros "_". rewrite /tgc /tgc' publicly_related_tag. by iSplit. }
iAssert (PUB⟨tgc, tgc'⟩) as "#pub_tgc".
{ rewrite /tgc /tgc' publicly_related_tag. by iSplit. }
(* The signatures are publicly related. *)
iMod (ballot_inv_sign _ _ _ _ _ _ n n' with "Hballot token") as "[#Hsl #Hsr]";
  first solve_ndisj.
iMod (public_rel_flow_l_extend (E:=⊤) sig ltac:(solve_ndisj)
        with "Hctx tt_sig_flow") as "prot_sig".
iMod (public_rel_flow_r_extend (E:=⊤) sig' ltac:(solve_ndisj)
        with "Hctx tts_sig_flow") as "prot_sig'".
iMod (public_rel_extend (E:=⊤) sig sig' ltac:(solve_ndisj)
        with "Hctx [] prot_sig prot_sig' tt_sig_map tts_sig_map") as "#elem_sig".
{ iIntros "#elem_sig".
  by iApply (pub_sign with "mint_V mint_V' secret_V secret_V' pub_pkV pub_tgc elem_tgc Hsl Hsr elem_sig"). }
iPoseProof (pub_sign with "mint_V mint_V' secret_V secret_V' pub_pkV pub_tgc elem_tgc Hsl Hsr elem_sig")
  as "#pub_sig".
(* Run the program. *)
rel_pures_l. rel_pures_r.
rel_apply_l rel_tuple_l. rel_apply_r rel_tuple_r.
rel_apply_l rel_aenc'_l. iModIntro.
rel_apply_r rel_aenc'_r.
rel_apply_l rel_sign'_l. iModIntro.
rel_apply_r rel_sign'_r.
rel_values. iModIntro. by iApply lrel_term_intro.
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
rewrite /voter. rel_pures_l. rel_pures_r.
rel_apply_l rel_tint_l. rel_apply_r rel_tint_r.
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
- rel_rec_l. rel_rec_r. rel_pures_l. rel_pures_r. rel_values. iModIntro.
  iExists [], []. rewrite /voter_keys /voter_tokens /=. by eauto.
- rel_rec_l. rel_rec_r. rel_pures_l. rel_pures_r.
  rel_bind_l (mk_sign_key #()). rel_bind_r (mk_sign_key #()).
  iApply (rel_mk_voter_key _ _ skT skT' (TInt v) (TInt v') with "Hctx").
  iIntros (sk sk') "#HV tok" => /=.
  rel_pures_l. rel_pures_r.
  rel_bind_l (mk_voters _). rel_bind_r (mk_voters _).
  iApply (refines_bind with "[]"); first by iApply IH; first lia.
  iIntros (? ?) "(%ks & %ks' & -> & -> & %Hk & %Hk' & #Hkeys & toks)" => /=.
  rel_pures_l. rel_pures_r. rel_values. iModIntro.
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
  rel_rec_l. rel_rec_r. rel_pures_l. rel_pures_r. by rel_values.
- iDestruct (big_sepL2_cons_inv_l with "Hkeys") as (sk' ks'' ->) "[#HV #Hkeys']".
  case: votes votes' Hl Hl' => [|v votes] [|v' votes'] //= [Hl] [Hl'].
  iDestruct "toks" as "[tok toks]".
  rel_rec_l. rel_rec_r. rel_pures_l. rel_pures_r.
  rel_bind_l (Fork _). rel_bind_r (Fork _).
  iApply (refines_bind with "[tok]").
  { iApply refines_fork. rel_pures_l. rel_pures_r.
    by iApply (rel_voter with "Hctx Hc HT HV tok"). }
  iIntros (? ?) "_" => /=. rel_pures_l. rel_pures_r.
  by iApply (IH _ votes votes' Hl Hl' with "Hctx Hc HT Hkeys' toks").
Qed.

End Voter.
