(** * Nondeterministic public-key encryption

[nondet_aenc] encrypts a fresh nonce together with the plaintext, so that
equal plaintexts give different ciphertexts.  Callers never see the nonce.

- [Programs]: encryption, decryption, and what they compute on terms.
- [Receipts]: what encrypting leaves to the caller for each pair of
  ciphertexts: what hides the nonce, and the release tokens of the
  ciphertexts.
- [Specs]: encrypting takes, from whoever owns the public key, the tokens
  of the fresh ciphertexts, and returns a receipt.  Once the plaintexts are
  public, the receipt makes the nonces public and gives back the part of
  the key that the ciphertexts hold, which the owners of the key need to
  publish the decryption key.
- [Decryption]: decryption is pure. *)

From cryptis Require Import lib cryptis primitives.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib.
From cryptis.hyper.core Require Import minted_spec term_meta_spec public.
From cryptis.hyper.primitives Require Import simple with_cryptis.
From cryptis.hyper Require Import proofmode.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Programs.

Definition nondet_aenc : val := λ: "pk" "N" "t",
  aenc "pk" "N" (tuple (mk_nonce #()) "t").

Definition nondet_adec : val := λ: "sk" "N" "c",
  match: adec "sk" "N" "c" with
    SOME "pl" =>
    match: untuple "pl" with
      SOME "p" => SOME (Snd "p")
    | NONE => NONE
    end
  | NONE => NONE
  end.

Definition nondet_open k N c : option term :=
  match Spec.dec k N c with
  | Some pl => match Spec.untuple pl with Some p => Some p.2 | None => None end
  | None => None
  end.

Lemma nondet_open_enc (sk : aenc_key) N n t :
  nondet_open sk N (Spec.enc (Spec.pkey sk) N (TPair n t)) = Some t.
Proof. by rewrite /nondet_open Spec.dec_aenc_key. Qed.

Lemma twp_nondet_adec `{!heapGS Σ} E k N c Ψ :
  Ψ (repr (nondet_open k N c)) ⊢
  WP nondet_adec k N c @ E [{ Ψ }].
Proof.
iIntros "post". rewrite /nondet_adec /adec /nondet_open. wp_pures.
wp_apply twp_dec. case: Spec.dec => [pl|] /=; wp_pures; last by iApply "post".
wp_apply twp_untuple. case: Spec.untuple => [[n t]|] /=; by wp_pures.
Qed.

End Programs.

Section NondetAenc.

Context `{!relocG Σ, !publicGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (sk : aenc_key) (k p t : term) (N : namespace).

Section Receipts.

Definition nondet_receipt sk sk' N c c' m m' : iProp :=
  ∃ n n',
    ⌜is_nonce n⌝ ∗ ⌜is_nonce n'⌝ ∗
    ⌜c = Spec.enc (Spec.pkey sk) (Tag N) (TPair n m)⌝ ∗
    ⌜c' = Spec.enc (Spec.pkey sk') (Tag N) (TPair n' m')⌝ ∗
    minted n ∗ minted_spec n' ∗
    protected_via_l (Spec.tag (Tag N) (TPair n m)) [TPair n m] n ∗
    protected_via_r (Spec.tag (Tag N) (TPair n' m')) [TPair n' m'] n' ∗
    pending_in_l (Spec.tag (Tag N) (TPair n m)) (Spec.tag (Tag N) (TPair n' m')) ∗
    pending_in_r (Spec.tag (Tag N) (TPair n m)) (Spec.tag (Tag N) (TPair n' m')) ∗
    prots_token_l (Spec.tag (Tag N) (TPair n m)) ∗
    prots_token_r (Spec.tag (Tag N) (TPair n' m')) ∗
    states_token_l n ∗ states_token_r n' ∗
    term_token n (↑termN.@"prots" ∖ ↑termN.@"prots".@(Spec.tag (Tag N) (TPair n m))) ∗
    term_token_spec n' (↑termN.@"prots" ∖ ↑termN.@"prots".@(Spec.tag (Tag N) (TPair n' m'))) ∗
    seal_release_l c ∗ seal_release_r c' ∗
    publicly_linked c c'.

#[global] Instance nondet_receipt_timeless sk sk' N c c' m m' :
  Timeless (nondet_receipt sk sk' N c c' m m').
Proof. rewrite /nondet_receipt. apply _. Qed.

End Receipts.

Section Specs.

Lemma nondet_release E sk sk' N c c' m m' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  nondet_receipt sk sk' N c c' m m' -∗
  PUB⟨m, m'⟩ ={E}=∗
  ∃ n n',
    ⌜c = Spec.enc (Spec.pkey sk) (Tag N) (TPair n m)⌝ ∗
    ⌜c' = Spec.enc (Spec.pkey sk') (Tag N) (TPair n' m')⌝ ∗
    PUB⟨n, n'⟩ ∗
    holds_key_l (Spec.tag (Tag N) (TPair n m)) (Spec.pkey sk) ∗
    holds_key_r (Spec.tag (Tag N) (TPair n' m')) (Spec.pkey sk').
Proof.
iIntros (HE) "#ctx (%n & %n' & %Hn & %Hn' & %Hc & %Hc' & #mint_n & #mint_n' &
  #rec & #rec' & pend & pend' & prots & prots' & st_n & st_n' & rest_n & rest_n' &
  rel & rel' & #link_c) #pub_m".
case/is_nonceP: (Hn) => a En. case/is_nonceP: (Hn') => a' En'. subst n n' c c'.
set pl := TPair (TNonce a) m. set tg := Spec.tag (Tag N) pl.
set pl' := TPair (TNonce a') m'. set tg' := Spec.tag (Tag N) pl'.
iAssert (□ (publicly_linked (TNonce a) (TNonce a') -∗ PUB⟨TNonce a, TNonce a'⟩))%I
  as "#pub_n".
{ iIntros "!> #link". rewrite public_TNonce. by iFrame "#". }
iAssert (□ (publicly_linked (TNonce a) (TNonce a') -∗ publicly_linked tg tg' -∗ PUB⟨tg, tg'⟩))%I
  as "#pub_tg".
{ iIntros "!> #link _". rewrite /tg /tg' public_tag public_TPair. iSplit; first done.
  iSplit; last done. by iApply "pub_n". }
have Htg : is_nonce tg = false by exact: Spec.is_nonce_tag.
have Htg' : is_nonce tg' = false by exact: Spec.is_nonce_tag.
iMod (public_lock_PublicLink_protector (t:=tg) (t':=tg') [pl] (TNonce a) [pl'] (TNonce a') HE
        ltac:(rewrite Htg /=; tauto) ltac:(rewrite Htg' /=; tauto) with
  "ctx rec rec' pub_tg pub_n [] [] prots prots' pend pend' [] [] [rest_n] [rest_n'] st_n st_n'")
  as "(#link_tg & #link_n & _ & _)".
{ by rewrite /public_deposit_l /tg [Spec.tag]unlock. }
{ by rewrite /public_deposit_r /tg' [Spec.tag]unlock. }
{ done. }
{ done. }
{ iIntros "hold". rewrite /prots_token_l /holds_subterm_l /=.
  rewrite (term_token_difference _ (↑termN.@"prots".@tg) (↑termN.@"prots")); last solve_ndisj.
  iFrame. }
{ iIntros "hold". rewrite /prots_token_r /holds_subterm_r /=.
  rewrite (term_token_spec_difference _ (↑termN.@"prots".@tg') (↑termN.@"prots")); last solve_ndisj.
  iFrame. }
iDestruct ("pub_tg" with "link_n link_tg") as "#Hpub_tg".
iDestruct ("pub_n" with "link_n") as "#Hpub_n".
rewrite /Spec.enc !Spec.aenc_key_pkey.
iDestruct "link_c" as "[link_cl link_cr]".
iMod (public_TSeal_release_AEnc_hold_l_fupd _ _ _ _ HE with "ctx Hpub_tg rel link_cl") as "hold".
iMod (public_TSeal_release_AEnc_hold_r_fupd _ _ _ _ HE with "ctx Hpub_tg rel' link_cr") as "hold'".
iModIntro. iExists (TNonce a), (TNonce a'). by iFrame "∗#".
Qed.

Lemma refines_nondet_aenc sk sk' N m m' (Ψ : val → val → iProp) :
  hypercryptis_ctx -∗
  minted sk -∗ minted_spec sk' -∗
  publicly_linked (Spec.pkey sk) (Spec.pkey sk') -∗
  linked (sk : term) (sk' : term) -∗
  minted m -∗ minted_spec m' -∗
  (∀ p p',
     ⌜nondet_open sk (Tag N) (TSeal (Spec.pkey sk) p) = Some m⌝ -∗
     ⌜nondet_open sk' (Tag N) (TSeal (Spec.pkey sk') p') = Some m'⌝ -∗
     term_token (TSeal (Spec.pkey sk) p) ⊤ -∗
     term_token_spec (TSeal (Spec.pkey sk') p') ⊤ -∗
     (∀ E, ⌜↑cryptisN ⊆ E⌝ -∗
        never_sealed_under (Spec.pkey sk) (Spec.pkey sk')
          (↑seal_namespace p) (↑seal_namespace p') -∗
        holds_key_l p (Spec.pkey sk) -∗ holds_key_r p' (Spec.pkey sk') ={E}=∗
        nondet_receipt sk sk' N (TSeal (Spec.pkey sk) p) (TSeal (Spec.pkey sk') p') m m' ∗
        publicly_linked (TSeal (Spec.pkey sk) p) (TSeal (Spec.pkey sk') p') ∗
        PUB⟨TSeal (Spec.pkey sk) p, TSeal (Spec.pkey sk') p'⟩) ={⊤}=∗
     Ψ (TSeal (Spec.pkey sk) p) (TSeal (Spec.pkey sk') p')) -∗
  REL nondet_aenc (Spec.pkey sk) (Tag N) m << nondet_aenc (Spec.pkey sk') (Tag N) m' : Ψ.
Proof.
iIntros "#ctx #mint_sk #mint_sk' #link_pk #link_sk #mint_m #mint_m' post".
iAssert (minted (Spec.pkey sk)) as "#mint_pk"; first by rewrite minted_pkey.
iAssert (minted_spec (Spec.pkey sk')) as "#mint_pk'"; first by rewrite minted_spec_pkey.
rewrite /nondet_aenc. rel_pures.
rel_apply_l (refines_mk_nonce_l _ _ (λ n, {[n; TPair n m; Spec.tag (Tag N) (TPair n m);
  Spec.enc (Spec.pkey sk) (Tag N) (TPair n m)]}) with "[//]").
{ iIntros (t). rewrite big_sepS_forall. iIntros (t' Ht').
  set_unfold in Ht'. destruct_or? Ht'; subst t'; solve_minted_iff_elem. }
iIntros (n) "%Hn #mint_n Htt".
rel_apply_r (refines_mk_nonce_r _ _ (λ n', {[n'; TPair n' m'; Spec.tag (Tag N) (TPair n' m');
  Spec.enc (Spec.pkey sk') (Tag N) (TPair n' m')]}) with "[//]").
{ iIntros (t). rewrite big_sepS_forall. iIntros (t' Ht').
  set_unfold in Ht'. destruct_or? Ht'; subst t'; solve_minted_iff_elem. }
iIntros (n') "%Hn' #mint_n' Htts".
split_term_tokens.
iDestruct "Htt" as "(((tt_n & tt_pl) & tt_tg) & tt_c)".
iDestruct "Htts" as "(((tts_n & tts_pl) & tts_tg) & tts_c)".
iDestruct (term_token_public_token_l with "tt_n") as "(tt_n & _ & _)"; first solve_not_TSeal.
iDestruct (term_token_public_token_l with "tt_pl") as "(tt_pl & _ & _)"; first solve_not_TSeal.
iDestruct (term_token_public_token_l with "tt_tg") as "(tt_tg & _ & _)"; first solve_not_TSeal.
iDestruct (term_token_public_token_r with "tts_n") as "(tts_n & _ & _)"; first solve_not_TSeal.
iDestruct (term_token_public_token_r with "tts_pl") as "(tts_pl & _ & _)"; first solve_not_TSeal.
iDestruct (term_token_public_token_r with "tts_tg") as "(tts_tg & _ & _)"; first solve_not_TSeal.
iDestruct (public_token_l_split with "tt_n") as "(st_n & prots_n & _)".
iDestruct (public_token_l_split with "tt_pl") as "(_ & prots_pl & _)".
iDestruct (public_token_l_split with "tt_tg") as "(st_tg & prots_tg & _)".
iDestruct (public_token_r_split with "tts_n") as "(st_n' & prots_n' & _)".
iDestruct (public_token_r_split with "tts_pl") as "(_ & prots_pl' & _)".
iDestruct (public_token_r_split with "tts_tg") as "(st_tg' & prots_tg' & _)".
case/is_nonceP: (Hn) => a En. case/is_nonceP: (Hn') => a' En'. subst n n'.
set pl := TPair (TNonce a) m. set tg := Spec.tag (Tag N) pl.
set pl' := TPair (TNonce a') m'. set tg' := Spec.tag (Tag N) pl'.
iAssert (holds_subterm_l tg (TNonce a) ∗
         term_token (TNonce a) (↑termN.@"prots" ∖ ↑termN.@"prots".@tg))%I
  with "[prots_n]" as "[hold_n rest_n]".
{ rewrite /prots_token_l /holds_subterm_l /=.
  rewrite -(term_token_difference _ (↑termN.@"prots".@tg) (↑termN.@"prots")); [done | solve_ndisj]. }
iAssert (holds_subterm_r tg' (TNonce a') ∗
         term_token_spec (TNonce a') (↑termN.@"prots" ∖ ↑termN.@"prots".@tg'))%I
  with "[prots_n']" as "[hold_n' rest_n']".
{ rewrite /prots_token_r /holds_subterm_r /=.
  rewrite -(term_token_spec_difference _ (↑termN.@"prots".@tg') (↑termN.@"prots"));
    [done | solve_ndisj]. }
iAssert (holds_subterm_l tg pl) with "[prots_pl]" as "hold_pl".
{ rewrite /pl /prots_token_l /holds_subterm_l /=.
  iApply (term_token_drop with "prots_pl"). solve_ndisj. }
iAssert (holds_subterm_r tg' pl') with "[prots_pl']" as "hold_pl'".
{ rewrite /pl' /prots_token_r /holds_subterm_r /=.
  iApply (term_token_spec_drop with "prots_pl'"). solve_ndisj. }
iMod (linked_extend_protected_via (E:=⊤) tg tg' [pl] (TNonce a) [pl'] (TNonce a') ltac:(solve_ndisj)
        with "ctx [hold_pl hold_n] [hold_pl' hold_n'] st_tg st_tg'")
  as "(#link_tg & pend & pend' & #rec & #rec')".
{ rewrite /protected_by_chain_l /=. iSplit.
  - iPureIntro. apply: SubtermPathStep;
      [solve_immediate_subterm | apply: SubtermPathOne; solve_immediate_subterm].
  - iSplitL "hold_pl"; first by iFrame. iRight. iFrame. by iLeft. }
{ rewrite /protected_by_chain_r /=. iSplit.
  - iPureIntro. apply: SubtermPathStep;
      [solve_immediate_subterm | apply: SubtermPathOne; solve_immediate_subterm].
  - iSplitL "hold_pl'"; first by iFrame. iRight. iFrame. by iLeft. }
iAssert (minted tg) as "#mint_tg".
{ rewrite /tg minted_tag /pl minted_TPair. by iSplit. }
iAssert (minted_spec tg') as "#mint_tg'".
{ rewrite /tg' minted_spec_tag /pl' minted_spec_TPair. by iSplit. }
iMod ("post" $! tg tg' with "[] [] tt_c tts_c [-]") as "post".
{ iPureIntro. exact: nondet_open_enc. }
{ iPureIntro. exact: nondet_open_enc. }
{ iIntros (E HE) "seal hold_tg hold_tg'".
  iMod (public_seal_held (t:=tg) (t':=tg') (Ek:=↑seal_namespace tg)
          (Ek':=↑seal_namespace tg') (Spec.pkey sk) (Spec.pkey sk') HE ltac:(done) ltac:(done)
          with "ctx [] [hold_tg] [hold_tg'] seal")
    as "(#link_c & #pub_c & _ & rel & rel')".
  { iIntros "!> #Hpl". rewrite public_TSeal. iRight.
    rewrite minted_TSeal minted_spec_TSeal.
    iSplit; first by iSplit. iSplit; first by iSplit. iSplit; first done.
    iLeft. iSplit; first by iApply publicly_linked_linked.
    rewrite !Spec.aenc_key_pkey. iModIntro. by iRight. }
  { rewrite !Spec.aenc_key_pkey /public_deposit_l /=. iRight. iFrame.
    iDestruct "link_sk" as "[Hl _]". rewrite [term_of_aenc_key]unlock.
    case: (sk) => s /=. by iExists _. }
  { rewrite !Spec.aenc_key_pkey /public_deposit_r /=. iRight. iFrame.
    iDestruct "link_sk" as "[_ Hl]". rewrite [term_of_aenc_key]unlock.
    case: (sk') => s' /=. by iExists _. }
  iModIntro. iSplitL; last by iFrame "#".
  iExists (TNonce a), (TNonce a'). by iFrame "∗#". }
rel_apply_l refines_tuple_l. rel_apply_l refines_aenc'_l. rel_later.
rel_apply_r refines_tuple_r. rel_apply_r refines_aenc'_r. by rel_values.
Qed.

End Specs.

End NondetAenc.

Section Decryption.

Context `{!relocG Σ}.

Lemma refines_nondet_adec_l E K e k N c Ψ :
  (REL fill K (repr (nondet_open k N c) : expr) << e @ E : Ψ) -∗
  REL fill K (nondet_adec k N c) << e @ E : Ψ.
Proof. pure_twp_rel twp_nondet_adec. Qed.

Lemma refines_nondet_adec_r E K e k N c Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (nondet_open k N c) : expr) @ E : Ψ) -∗
  REL e << fill K (nondet_adec k N c) @ E : Ψ.
Proof. pure_twp_rel twp_nondet_adec. Qed.

Definition rel_prim_l_nondet_adec (v1 v2 v3 : val) : RelPrimL Σ (nondet_adec v1 v2 v3) _ :=
  refines_nondet_adec_l.
Definition rel_prim_r_nondet_adec (v1 v2 v3 : val) : RelPrimR Σ (nondet_adec v1 v2 v3) _ :=
  refines_nondet_adec_r.

End Decryption.

#[global] Hint Resolve
  rel_prim_l_nondet_adec rel_prim_r_nondet_adec
  : rel_prims.
