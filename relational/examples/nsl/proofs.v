(** Proofs of the NSL case study, one file per role, and of the tests.  A
    test creates the honest keys, runs both roles, takes the tested session
    key out of the seal set of I's key, and reveals it or a fresh key. *)

From cryptis.hyper.examples.nsl.proofs Require Export base init resp.
From cryptis Require Import lib cryptis primitives.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.core Require Import minted_spec term_meta_spec rel rel_inv_updates.
From cryptis.hyper.primitives Require Import simple_spec comp_spec with_cryptis_spec.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples.nsl Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Proofs.

Context `{!relocG Σ, !public_relGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (t s : term).

Lemma rel_setup c c' :
  cryptis_rel_ctx -∗
  channel_rel c c' -∗
  REL setup c << setup c' : λ v v',
    (∃ (skI skI' skR skR' : aenc_key) (pkX pkX' : term),
      ⌜v = (skI : term, skR : term, pkX)%V⌝ ∗
      ⌜v' = (skI' : term, skR' : term, pkX')%V⌝ ∗
      nsl_ctx skI skI' skR skR' ∗ claim skI ∗ PUB⟨pkX, pkX'⟩)%I.
Proof.
iIntros "#Hctx #Hc". rewrite /setup. rel_pures.
rel_bind_l (mk_aenc_key #()). rel_bind_r (mk_aenc_key #()).
iApply (rel_mk_honest_key with "Hctx").
iIntros (skI skI') "#HI sealsI sealsI' tokI" => /=. rel_pures.
rel_bind_l (mk_aenc_key #()). rel_bind_r (mk_aenc_key #()).
iApply (rel_mk_honest_key with "Hctx").
iIntros (skR skR') "#HR sealsR sealsR' _" => /=. rel_pures.
iMod (inv_alloc sealsIN _ (seals_inv skI skI' (seals_I_info skI skI' skR skR'))
        with "[sealsI sealsI']") as "#HinvI".
{ iNext. iExists ∅. iFrame. iSplit; last by rewrite big_sepS_empty.
  iPureIntro. exact: set_Forall_empty. }
iMod (inv_alloc sealsRN _ (seals_inv skR skR' (seals_R_info skI skI' skR skR'))
        with "[sealsR sealsR']") as "#HinvR".
{ iNext. iExists ∅. iFrame. iSplit; last by rewrite big_sepS_empty.
  iPureIntro. exact: set_Forall_empty. }
rewrite (term_token_difference (seed_of_aenc_key skI) (↑claimN)
           (⊤ ∖ ↑cryptisN.@"public_rel")); last solve_ndisj.
iDestruct "tokI" as "[claim _]".
rel_prims.
rel_apply (rel_send with "Hc []").
{ iNext. by iDestruct "HI" as "(_ & _ & _ & _ & ? & _)". }
iIntros (? ?) "[-> ->]" => /=. rel_prims.
rel_apply (rel_send with "Hc []").
{ iNext. by iDestruct "HR" as "(_ & _ & _ & _ & ? & _)". }
iIntros (? ?) "[-> ->]" => /=. rel_pures.
rel_apply (rel_recv with "Hc").
iIntros (pkX pkX') "#HpkX" => /=. rel_pures. rel_values. iModIntro.
iExists skI, skI', skR, skR', pkX, pkX'. do 2 (iSplit; first done).
iFrame "claim HpkX". by iFrame "#".
Qed.

Lemma rel_reveal b c c' s s' :
  cryptis_rel_ctx -∗
  channel_rel c c' -∗
  key_tokens s s' -∗ secret_in_l s -∗ secret_in_r s' -∗
  REL reveal b c (sess_key s) << reveal (negb b) c' (sess_key s') : ().
Proof.
iIntros "#Hctx #Hc [tok tok'] #sec #sec'". rewrite /reveal.
iPoseProof (term_token_minted with "tok") as "#mint".
iPoseProof (term_token_spec_minted_spec with "tok'") as "#mint'".
case: b; rel_pures.
- rel_apply_r (rel_mk_senc_key_r _ _ (λ _, ∅) _ (λ _, not_elem_of_empty _) with "Hctx []").
  { by iIntros (?); rewrite big_sepS_empty. }
  iIntros (k') "%Hk' #mint_k' tok_k' _".
  destruct k' as [n']. simpl in Hk'. case/is_nonceP: Hk' => a' e. subst n'.
  iEval (rewrite minted_spec_senc) in "mint_k'".
  iMod (public_rel_publish (E:=⊤) ltac:(solve_ndisj) with "Hctx [] tok tok_k'")
    as "[_ #Hpub]".
  { iIntros "!> #link". rewrite /=. iSplit; first done. iSplit; first done. by iSplit. }
  iAssert (PUB⟨sess_key s, SEncKey (TNonce a')⟩) as "#Hk".
  { rewrite /sess_key [term_of_senc_key]unlock publicly_related_TKey. by iSplit. }
  by rel_apply (rel_send with "Hc Hk").
- rel_apply_l (rel_mk_senc_key_l _ _ (λ _, ∅) _ (λ _, not_elem_of_empty _) with "Hctx []").
  { by iIntros (?); rewrite big_sepS_empty. }
  iIntros (k) "%Hk #mint_k tok_k _".
  destruct k as [n]. simpl in Hk. case/is_nonceP: Hk => a e. subst n.
  iEval (rewrite minted_senc) in "mint_k".
  iMod (public_rel_publish (E:=⊤) ltac:(solve_ndisj) with "Hctx [] tok_k tok'")
    as "[_ #Hpub]".
  { iIntros "!> #link". rewrite /=. iSplit; first done. iSplit; first done. by iSplit. }
  iAssert (PUB⟨SEncKey (TNonce a), sess_key s'⟩) as "#Hk".
  { rewrite /sess_key [term_of_senc_key]unlock publicly_related_TKey. by iSplit. }
  by rel_apply (rel_send with "Hc Hk").
Qed.

Lemma rel_resp_test b c c' :
  cryptis_rel_ctx -∗
  channel_rel c c' -∗
  REL resp_test b c << resp_test (negb b) c' : ().
Proof.
iIntros "#Hctx #Hc". rewrite /resp_test. rel_pures.
rel_apply (rel_setup with "Hctx Hc").
iIntros (? ?) "(%skI & %skI' & %skR & %skR' & %pkX & %pkX' & -> & -> &
                #Hnsl & claim & #HpkX)" => /=.
rel_pures.
rel_bind_l (Fork _). rel_bind_r (Fork _).
iApply (refines_bind with "[]").
{ iApply refines_fork. rel_pures.
  rel_apply (rel_init with "Hctx Hc Hnsl HpkX").
  iIntros (? ?) "_" => /=. rel_pures. by rel_values. }
iIntros (? ?) "_" => /=. rel_pures.
rel_apply (rel_resp with "Hctx Hc Hnsl").
iIntros (? ?) "[[-> ->]|(%pkI & %pkI' & %k & %k' & [-> ->] & #HpkI & Hsess)]" => /=.
{ rel_pures. by rel_values. }
rel_prims.
iPoseProof "Hnsl" as "((_ & _ & _ & _ & #pub_pkI & _) & _)".
iMod (publicly_related_part_bij' (E:=⊤) with "Hctx HpkI pub_pkI") as %HX;
  first solve_ndisj.
case: (decide (pkI = Spec.pkey skI)) => [eX|neX]; last first.
{ rewrite bool_decide_eq_false_2 // bool_decide_eq_false_2; last by rewrite -HX.
  rel_pures. by rel_values. }
rewrite bool_decide_eq_true_2 // bool_decide_eq_true_2; last by apply HX.
rel_pures.
iDestruct ("Hsess" with "[//]") as (s s' [-> ->]) "Hs".
iMod (claim_key with "Hnsl Hs claim") as "(toks & #sec & #sec')"; first solve_ndisj.
by iApply (rel_reveal with "Hctx Hc toks sec sec'").
Qed.

Lemma rel_init_test b c c' :
  cryptis_rel_ctx -∗
  channel_rel c c' -∗
  REL init_test b c << init_test (negb b) c' : ().
Proof.
iIntros "#Hctx #Hc". rewrite /init_test. rel_pures.
rel_apply (rel_setup with "Hctx Hc").
iIntros (? ?) "(%skI & %skI' & %skR & %skR' & %pkX & %pkX' & -> & -> &
                #Hnsl & claim & #HpkX)" => /=.
rel_pures.
rel_bind_l (Fork _). rel_bind_r (Fork _).
iApply (refines_bind with "[]").
{ iApply refines_fork. rel_pures.
  rel_apply (rel_resp with "Hctx Hc Hnsl").
  iIntros (? ?) "_" => /=. rel_pures. by rel_values. }
iIntros (? ?) "_" => /=. rel_pures.
rel_apply (rel_init with "Hctx Hc Hnsl HpkX").
iIntros (? ?) "[[-> ->]|(%k & %k' & [-> ->] & Hsess)]" => /=.
{ rel_pures. by rel_values. }
rel_prims.
iPoseProof "Hnsl" as "(_ & (_ & _ & _ & _ & #pub_pkR & _) & _)".
iMod (publicly_related_part_bij' (E:=⊤) with "Hctx HpkX pub_pkR") as %HX;
  first solve_ndisj.
case: (decide (pkX = Spec.pkey skR)) => [eX|neX]; last first.
{ rewrite bool_decide_eq_false_2 // bool_decide_eq_false_2; last by rewrite -HX.
  rel_pures. by rel_values. }
rewrite bool_decide_eq_true_2 // bool_decide_eq_true_2; last by apply HX.
rel_pures.
iDestruct ("Hsess" with "[//]") as (s s' [-> ->]) "Hs".
iMod (claim_key with "Hnsl Hs claim") as "(toks & #sec & #sec')"; first solve_ndisj.
by iApply (rel_reveal with "Hctx Hc toks sec sec'").
Qed.

End Proofs.
