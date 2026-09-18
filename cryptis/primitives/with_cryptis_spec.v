From reloc Require Import reloc.
From cryptis Require Import cryptis.
From cryptis.primitives Require Import simple with_cryptis.
From cryptis.core Require Import minted_spec term_meta_spec rel.
From cryptis Require Import lib_spec.
From cryptis.primitives Require Import simple_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Definition sender : val :=
  rec: "loop" "l" "t" :=
  "l" <- "t";;
  "loop" "l" "t".

Definition mk_channel_rel : val :=
  λ: <>,
  let: "l" := ref (TInt 0) in
  (λ: "t", Fork (sender "l" "t"), λ: <>, !"l").

Section Proofs.

Context `{!relocG Σ, !public_relGS Σ}.

Notation nonce := loc.
Implicit Types E : coPset.
Implicit Types a : nonce.
Implicit Types t : term.
Implicit Types v : val.
Implicit Types φ : val → iProp Σ.
Implicit Types Ψ : val → val → iProp Σ.

Definition channel_rel : val → val → iProp Σ := LRel (λ c c',
  ∃ (sf rf sf' rf' : val), ⌜c = (sf, rf)%V⌝ ∗ ⌜c' = (sf', rf')%V⌝  ∗
  □ (∀ t t' Ψ, PUB⟨t, t'⟩ -∗ Ψ #() #() -∗ REL sf t << sf' t' : Ψ) ∗
  □ (∀ Ψ, (∀ t t', PUB⟨t, t'⟩ -∗ Ψ t t') -∗ REL rf #() << rf' #() : Ψ))%I.

#[global] Instance channel_rel_persistent c c' : Persistent (channel_rel c c').
Proof. apply _. Qed.

Definition chan_rel_inv l l' : iProp Σ :=
  ∃ t t', l ↦ t ∗ l' ↦ₛ t' ∗ PUB⟨t, t'⟩.

#[local] Lemma rel_sender (l l': loc) t t' :
  inv (cryptisN.@"channel_rel") (chan_rel_inv l l') -∗
  PUB⟨t, t'⟩ -∗
  REL (sender #l t) << (sender #l' t') : lrel_unit.
Proof.
iIntros "#Hinv #Ht".
iLöb as "IH".
rel_rec_l. rel_rec_r.
rel_pures_l. rel_pures_r.
rel_store_l_atomic.
iInv (cryptisN.@"channel_rel") as "(%t1 & %t1' & (Hl & Hl' & #Hrel))" "Hclose".
iModIntro.
iExists t1. iFrame.
iIntros "!> Hl".
rel_pures_l.
rel_store_r. rel_pures_r.
iMod ("Hclose" with "[Hl Hl']").
by iFrame.
done.
Qed.

Lemma rel_mk_channel_rel :
  ⊢ REL mk_channel_rel #() << mk_channel_rel #() : channel_rel.
Proof.
rewrite /mk_channel_rel.
rel_pures_l. rel_pures_r.
rel_alloc_l l as "Hl". rel_alloc_r l' as "Hl'".
rel_pures_l. rel_pures_r.
iMod (inv_alloc (cryptisN.@"channel_rel") _ (chan_rel_inv l l') with "[Hl Hl']") as "#Hinv".
iFrame. by rewrite publicly_related_TInt.
rel_values.
iModIntro.
iExists _, _, _, _.
do 2 (iSplit; eauto).
iSplit.
- iIntros (t t' Ψ) "!> #H HΨ".
  rel_pures_l. rel_pures_r.
  iApply refines_wand.
  iApply refines_fork.
  iApply rel_sender; done.
  by iIntros (v1 v2) "[-> ->]".
- iIntros (Ψ) "!> H".
  rel_pures_l. rel_pures_r.
  rel_load_l_atomic.
  iInv (cryptisN.@"channel_rel") as "(%t & %t' & Hl & Hl' & #Hrel)" "Hclose".
  iModIntro.
  iExists t.
  iFrame.
  iIntros "!> Hl".
  rel_load_r.
  iMod ("Hclose" with "[Hl Hl']").
  by iFrame.
  rel_values.
  by iApply "H".
Qed.

Lemma rel_send c c' t t' :
  channel_rel c c' -∗
  (▷ PUB⟨t, t'⟩) -∗
  REL send c t << send c' t' : lrel_unit.
Proof.
iDestruct 1 as (sf rf sf' rf') "(-> & -> & #H & _)".
iIntros "#?"; rewrite /send; rel_pures_l; rel_pures_r.
by iApply "H".
Qed.

Lemma rel_recv c c' Ψ :
  channel_rel c c' -∗
  (∀ t t', PUB⟨t, t'⟩ -∗ Ψ t t') -∗
  REL recv c << recv c' : Ψ.
Proof.
iDestruct 1 as (sf rf sf' rf') "(-> & -> & #_ & #H)".
iIntros "?"; rewrite /recv; rel_pures_l; rel_pures_r.
by iApply "H".
Qed.

Lemma rel_mk_nonce_l K e (T': term → gset term) Ψ :
  cryptis_rel_ctx -∗
  (∀ t, [∗ set] t' ∈ T' t, □ (minted t ↔ minted t')) -∗
  (∀ t, ⌜is_nonce t⌝ -∗
        minted t -∗
        ([∗ set] t' ∈ T' t, term_token t' ⊤) -∗
        (REL fill K (t : expr) << e : Ψ)) -∗
  REL fill K (mk_nonce #()) << e : Ψ.
Proof.
iIntros "#Hctx #minted_T' mint"; rewrite /mk_nonce.
rel_pures_l. rel_alloc_meta_l l as "[_ Htoken]".
iPoseProof (mintable_alloc (Nonce l) with "Htoken") as "fresh".
set t:= TNonce (Nonce l).
iMod (term_token_alloc (T' t) (¬ minted t) (minted t) with "Hctx [] [] [fresh]") as "(#post & token)"=> //.
- iIntros "%t' %t'_t contra minted_t'". iApply "contra".
  iSpecialize ("minted_T'" $! t).
  rewrite big_sepS_delete //.
  iDestruct "minted_T'" as "[#e _]". by iApply "e".
- iIntros "%t' %t'_t minted_t".
  iSpecialize ("minted_T'" $! t).
  rewrite big_sepS_delete //.
  iDestruct "minted_T'" as "[#e _]". by iApply "e".
- iSplit.
  + by iDestruct "fresh" as "[fresh _]".
  + by iDestruct "fresh" as "[_ >fresh]".
rel_pures_l. rewrite val_of_term_unseal.
iApply ("mint" $! (TNonce (Nonce l)))=> //=.
Qed.

Lemma rel_mk_nonce_r K e (T': term → gset term) Ψ :
  cryptis_rel_ctx -∗
  (∀ t, [∗ set] t' ∈ T' t, □ (minted_spec t ↔ minted_spec t')) -∗
  (∀ t, ⌜is_nonce t⌝ -∗
        minted_spec t -∗
        ([∗ set] t' ∈ T' t, term_token_spec t' ⊤) -∗
        (REL e << fill K (t : expr) : Ψ)) -∗
  REL e << fill K (mk_nonce #()) : Ψ.
Proof.
iIntros "#Hctx #minted_spec_T' mint"; rewrite /mk_nonce.
rel_pures_r. rel_alloc_r l as "Hl".
iPoseProof (mintable_spec_alloc (Nonce l) with "Hl") as "fresh".
set t:= TNonce (Nonce l).
iMod (term_token_spec_alloc (T' t) (¬ minted_spec t) (minted_spec t) with "Hctx [] [] [fresh]") as "(#post & token)"=> //.
- iIntros "%t' %t'_t contra minted_spec_t'". iApply "contra".
  iSpecialize ("minted_spec_T'" $! t).
  rewrite big_sepS_delete //.
  iDestruct "minted_spec_T'" as "[#e _]". by iApply "e".
- iIntros "%t' %t'_t minted_spec_t".
  iSpecialize ("minted_spec_T'" $! t).
  rewrite big_sepS_delete //.
  iDestruct "minted_spec_T'" as "[#e _]". by iApply "e".
- iSplit.
  + by iDestruct "fresh" as "[fresh _]".
  + by iDestruct "fresh" as "[_ >fresh]".
rel_pures_r. rewrite val_of_term_unseal.
iApply ("mint" $! (TNonce (Nonce l)))=> //=.
Qed.

Lemma rel_mk_aenc_key_l K e (T_sk T_pk : term → gset term) Ψ :
  (∀ sk : aenc_key,
     seed_of_aenc_key sk ∉ T_sk sk ∧
     seed_of_aenc_key sk ∉ T_pk (Spec.pkey sk) ∧
     T_sk sk ## T_pk (Spec.pkey sk)) →
  cryptis_rel_ctx -∗
  (∀ sk : aenc_key, [∗ set] t' ∈ T_sk sk, □ (minted sk ↔ minted t')) -∗
  (∀ sk : aenc_key, [∗ set] t' ∈ T_pk (Spec.pkey sk),
     □ (minted (Spec.pkey sk) ↔ minted t')) -∗
  (∀ sk : aenc_key, ⌜is_nonce (seed_of_aenc_key sk)⌝ -∗
    minted sk -∗
    term_token (seed_of_aenc_key sk) ⊤ -∗
    ([∗ set] t' ∈ T_sk sk, term_token t' ⊤) -∗
    ([∗ set] t' ∈ T_pk (Spec.pkey sk), term_token t' ⊤) -∗
    (REL fill K (sk : expr) << e : Ψ)) -∗
  REL fill K (mk_aenc_key #()) << e : Ψ.
Proof.
iIntros (Hdisj) "#Hctx #minted_sk #minted_pk mint"; rewrite /mk_aenc_key.
rel_pures_l.
rel_apply_l (rel_mk_nonce_l _ _
  (λ t, {[t]} ∪ T_sk (AEncKey t) ∪ T_pk (Spec.pkey (AEncKey t))))=> //.
{ iIntros "%t".
  case: (Hdisj (AEncKey t)) => [Hseed_sk [Hseed_pk Hsk_pk]].
  have Hseed : seed_of_aenc_key (AEncKey t) = t by [].
  rewrite Hseed in Hseed_sk Hseed_pk.
  rewrite big_sepS_union; last set_solver.
  rewrite big_sepS_union; last set_solver.
  rewrite big_sepS_singleton.
  iSplit; first iSplit.
  - iModIntro. by iSplit; iIntros "?".
  - iSpecialize ("minted_sk" $! (AEncKey t)). by setoid_rewrite minted_aenc.
  - iSpecialize ("minted_pk" $! (AEncKey t)).
    by setoid_rewrite minted_pkey; setoid_rewrite minted_aenc. }
iIntros (t) "%Hnonce #Hmint Htt".
case: (Hdisj (AEncKey t)) => [Hseed_sk [Hseed_pk Hsk_pk]].
have Hseed : seed_of_aenc_key (AEncKey t) = t by [].
rewrite Hseed in Hseed_sk Hseed_pk.
rewrite big_sepS_union; last set_solver.
rewrite big_sepS_union; last set_solver.
rewrite big_sepS_singleton.
iDestruct "Htt" as "[[Htt_seed Htt_sk] Htt_pk]".
rel_pures_l. rel_apply_l rel_derive_aenc_key_l.
iApply ("mint" $! (AEncKey t) with "[//] [] Htt_seed Htt_sk Htt_pk").
by iApply minted_aenc.
Qed.

Lemma rel_mk_aenc_key_r K e (T_sk T_pk : term → gset term) Ψ :
  (∀ sk : aenc_key,
     seed_of_aenc_key sk ∉ T_sk sk ∧
     seed_of_aenc_key sk ∉ T_pk (Spec.pkey sk) ∧
     T_sk sk ## T_pk (Spec.pkey sk)) →
  cryptis_rel_ctx -∗
  (∀ sk : aenc_key, [∗ set] t' ∈ T_sk sk, □ (minted_spec sk ↔ minted_spec t')) -∗
  (∀ sk : aenc_key, [∗ set] t' ∈ T_pk (Spec.pkey sk),
     □ (minted_spec (Spec.pkey sk) ↔ minted_spec t')) -∗
  (∀ sk : aenc_key, ⌜is_nonce (seed_of_aenc_key sk)⌝ -∗
    minted_spec sk -∗
    term_token_spec (seed_of_aenc_key sk) ⊤ -∗
    ([∗ set] t' ∈ T_sk sk, term_token_spec t' ⊤) -∗
    ([∗ set] t' ∈ T_pk (Spec.pkey sk), term_token_spec t' ⊤) -∗
    (REL e << fill K (sk : expr) : Ψ)) -∗
  REL e << fill K (mk_aenc_key #()) : Ψ.
Proof.
iIntros (Hdisj) "#Hctx #minted_sk #minted_pk mint"; rewrite /mk_aenc_key.
rel_pures_r.
rel_apply_r (rel_mk_nonce_r _ _
  (λ t, {[t]} ∪ T_sk (AEncKey t) ∪ T_pk (Spec.pkey (AEncKey t))))=> //.
{ iIntros "%t".
  case: (Hdisj (AEncKey t)) => [Hseed_sk [Hseed_pk Hsk_pk]].
  have Hseed : seed_of_aenc_key (AEncKey t) = t by [].
  rewrite Hseed in Hseed_sk Hseed_pk.
  rewrite big_sepS_union; last set_solver.
  rewrite big_sepS_union; last set_solver.
  rewrite big_sepS_singleton.
  iSplit; first iSplit.
  - iModIntro. by iSplit; iIntros "?".
  - iSpecialize ("minted_sk" $! (AEncKey t)). by setoid_rewrite minted_spec_aenc.
  - iSpecialize ("minted_pk" $! (AEncKey t)).
    by setoid_rewrite minted_spec_pkey; setoid_rewrite minted_spec_aenc. }
iIntros (t) "%Hnonce #Hmint Htts".
case: (Hdisj (AEncKey t)) => [Hseed_sk [Hseed_pk Hsk_pk]].
have Hseed : seed_of_aenc_key (AEncKey t) = t by [].
rewrite Hseed in Hseed_sk Hseed_pk.
rewrite big_sepS_union; last set_solver.
rewrite big_sepS_union; last set_solver.
rewrite big_sepS_singleton.
iDestruct "Htts" as "[[Htts_seed Htts_sk] Htts_pk]".
rel_pures_r. rel_apply_r rel_derive_aenc_key_r.
iApply ("mint" $! (AEncKey t) with "[//] [] Htts_seed Htts_sk Htts_pk").
by iApply minted_spec_aenc.
Qed.

Lemma rel_mk_sign_key_l K e Ψ :
  cryptis_rel_ctx -∗
  (∀ sk : sign_key, ⌜is_nonce (seed_of_sign_key sk)⌝ -∗ minted sk -∗ term_token sk ⊤ -∗
    (REL fill K (sk : expr) << e : Ψ)) -∗
  REL fill K (mk_sign_key #()) << e : Ψ.
Proof.
iIntros "#Hctx mint"; rewrite /mk_sign_key.
rel_pures_l. rel_apply_l (rel_mk_nonce_l _ _ (λ t, {[(SignKey t) : term]}))=> //.
{ iIntros "%t". rewrite [term_of_sign_key]unlock big_sepS_singleton minted_TKey.
  iModIntro. by iSplit; iIntros "?". }
iIntros (t) " %Hnonce #Hmint Htt".
rewrite big_sepS_singleton.
rel_pures_l. rel_apply_l rel_derive_sign_key_l.
iApply "mint" => //. by iApply minted_sign.
Qed.

Lemma rel_mk_sign_key_r K e Ψ :
  cryptis_rel_ctx -∗
  (∀ sk : sign_key, ⌜is_nonce (seed_of_sign_key sk)⌝ -∗ minted_spec sk -∗ term_token_spec sk ⊤ -∗
    (REL e << fill K (sk : expr) : Ψ)) -∗
  REL e << fill K (mk_sign_key #()) : Ψ.
Proof.
iIntros "#Hctx mint"; rewrite /mk_sign_key.
rel_pures_r. rel_apply_r (rel_mk_nonce_r _ _ (λ t, {[(SignKey t) : term]}))=> //.
{ iIntros "%t". rewrite [term_of_sign_key]unlock big_sepS_singleton minted_spec_TKey.
  iModIntro. by iSplit; iIntros "?". }
iIntros (t) "%Hnonce #Hmint Htts".
rel_pures_r. rel_apply_r rel_derive_sign_key_r.
rewrite big_sepS_singleton.
iApply "mint"=> //. by iApply minted_spec_sign.
Qed.

Lemma rel_mk_senc_key_l K e Ψ :
  cryptis_rel_ctx -∗
  (∀ k : senc_key, ⌜is_nonce (seed_of_senc_key k)⌝ -∗ minted k -∗ term_token k ⊤ -∗
    (REL fill K (k : expr) << e : Ψ)) -∗
  REL fill K (mk_senc_key #()) << e : Ψ.
Proof.
iIntros "#Hctx mint"; rewrite /mk_senc_key.
rel_pures_l. rel_apply_l (rel_mk_nonce_l _ _ (λ t, {[(SEncKey t) : term]}))=> //.
{ iIntros "%t". rewrite [term_of_senc_key]unlock big_sepS_singleton minted_TKey.
  iModIntro. by iSplit; iIntros "?". }
iIntros (t) "%Hnonce #Hmint Htt".
rewrite big_sepS_singleton.
rel_pures_l. rel_apply_l rel_derive_senc_key_l.
iApply "mint"=> //. by iApply minted_senc.
Qed.

Lemma rel_mk_senc_key_r K e Ψ :
  cryptis_rel_ctx -∗
  (∀ k : senc_key, ⌜is_nonce (seed_of_senc_key k)⌝ -∗ minted_spec k -∗ term_token_spec k ⊤ -∗
    (REL e << fill K (k : expr) : Ψ)) -∗
  REL e << fill K (mk_senc_key #()) : Ψ.
Proof.
iIntros "#Hctx mint"; rewrite /mk_senc_key.
rel_pures_r. rel_apply_r (rel_mk_nonce_r _ _ (λ t, {[(SEncKey t) : term]}))=> //.
{ iIntros "%t". rewrite [term_of_senc_key]unlock big_sepS_singleton minted_spec_TKey.
  iModIntro. by iSplit; iIntros "?". }
iIntros (t) "%Hnonce #Hmint Htts".
rel_pures_r. rel_apply_r rel_derive_senc_key_r.
rewrite big_sepS_singleton.
iApply "mint"=> //. by iApply minted_spec_senc.
Qed.

(** Key-type tests.  These mirror [twp_is_*_key] in [primitives/with_cryptis.v]:
    the [_l] versions need [minted] and the [_r] versions [minted_spec]. *)

Lemma rel_is_aenc_key_l E K e (pk : term) Ψ :
  minted pk -∗
  (∀ sk : aenc_key, ⌜pk = Spec.pkey sk⌝ -∗ minted sk -∗
     REL fill K (#true : expr) << e @ E : Ψ) ∧
  (REL fill K (#false : expr) << e @ E : Ψ) -∗
  REL fill K (is_aenc_key pk) << e @ E : Ψ.
Proof.
iIntros "#m_pk post".
iApply (pure_twp_rel_l _ _ _ _ _ _ #(Spec.has_key_type AEnc pk)
          with "[post]") => //=.
- apply: term_pure.
- move=> ?; iIntros "_". wp_lam. by wp_apply (twp_has_key_type AEnc).
- case: pk => [| | |kt t| | |]; try by move=> *; iDestruct "post" as "[_ post]".
  case: kt; try by iDestruct "post" as "[_ post]".
  iDestruct "post" as "[post _]".
  by iApply ("post" $! (AEncKey t)) => //;
  rewrite [term_of_aenc_key]unlock // !minted_TKey.
Qed.

Lemma rel_is_aenc_key_r E K e (pk : term) Ψ :
  ↑specN ⊆ E →
  minted_spec pk -∗
  (∀ sk : aenc_key, ⌜pk = Spec.pkey sk⌝ -∗ minted_spec sk -∗
     REL e << fill K (#true : expr) @ E : Ψ) ∧
  (REL e << fill K (#false : expr) @ E : Ψ) -∗
  REL e << fill K (is_aenc_key pk) @ E : Ψ.
Proof.
iIntros (?) "#m_pk post".
iApply (pure_twp_rel_r _ _ _ _ _ _ #(Spec.has_key_type AEnc pk)
          with "[post]") => //=.
- apply: term_pure.
- move=> ?; iIntros "_". wp_lam. by wp_apply (twp_has_key_type AEnc).
- case: pk => [| | |kt t| | |]; try by move=> *; iDestruct "post" as "[_ post]".
  case: kt; try by iDestruct "post" as "[_ post]".
  iDestruct "post" as "[post _]".
  by iApply ("post" $! (AEncKey t)) => //;
  rewrite [term_of_aenc_key]unlock // !minted_spec_TKey.
Qed.

Lemma rel_is_adec_key_l E K e (sk : term) Ψ :
  minted sk -∗
  (∀ sk' : aenc_key, ⌜sk = sk'⌝ -∗ REL fill K (#true : expr) << e @ E : Ψ) ∧
  (REL fill K (#false : expr) << e @ E : Ψ) -∗
  REL fill K (is_adec_key sk) << e @ E : Ψ.
Proof.
iIntros "#m_sk post".
iApply (pure_twp_rel_l _ _ _ _ _ _ #(Spec.has_key_type ADec sk)
          with "[post]") => //=.
- apply: term_pure.
- move=> ?; iIntros "_". wp_lam. by wp_apply (twp_has_key_type ADec).
- case: sk => [| | |kt t| | |]; try by move=> *; iDestruct "post" as "[_ post]".
  case: kt; try by iDestruct "post" as "[_ post]".
  iDestruct "post" as "[post _]".
  by iApply ("post" $! (AEncKey t)) => //;
  rewrite [term_of_aenc_key]unlock.
Qed.

Lemma rel_is_adec_key_r E K e (sk : term) Ψ :
  ↑specN ⊆ E →
  minted_spec sk -∗
  (∀ sk' : aenc_key, ⌜sk = sk'⌝ -∗ REL e << fill K (#true : expr) @ E : Ψ) ∧
  (REL e << fill K (#false : expr) @ E : Ψ) -∗
  REL e << fill K (is_adec_key sk) @ E : Ψ.
Proof.
iIntros (?) "#m_sk post".
iApply (pure_twp_rel_r _ _ _ _ _ _ #(Spec.has_key_type ADec sk)
          with "[post]") => //=.
- apply: term_pure.
- move=> ?; iIntros "_". wp_lam. by wp_apply (twp_has_key_type ADec).
- case: sk => [| | |kt t| | |]; try by move=> *; iDestruct "post" as "[_ post]".
  case: kt; try by iDestruct "post" as "[_ post]".
  iDestruct "post" as "[post _]".
  by iApply ("post" $! (AEncKey t)) => //;
  rewrite [term_of_aenc_key]unlock.
Qed.

Lemma rel_is_senc_key_l E K e (k : term) Ψ :
  minted k -∗
  (∀ k' : senc_key, ⌜k = k'⌝ -∗ REL fill K (#true : expr) << e @ E : Ψ) ∧
  (REL fill K (#false : expr) << e @ E : Ψ) -∗
  REL fill K (is_senc_key k) << e @ E : Ψ.
Proof.
iIntros "#m_k post".
iApply (pure_twp_rel_l _ _ _ _ _ _ #(Spec.has_key_type SEnc k)
          with "[post]") => //=.
- apply: term_pure.
- move=> ?; iIntros "_". wp_lam. by wp_apply (twp_has_key_type SEnc).
- case: k => [| | |kt t| | |]; try by move=> *; iDestruct "post" as "[_ post]".
  case: kt; try by iDestruct "post" as "[_ post]".
  iDestruct "post" as "[post _]".
  by iApply ("post" $! (SEncKey t)) => //;
  rewrite [term_of_senc_key]unlock.
Qed.

Lemma rel_is_senc_key_r E K e (k : term) Ψ :
  ↑specN ⊆ E →
  minted_spec k -∗
  (∀ k' : senc_key, ⌜k = k'⌝ -∗ REL e << fill K (#true : expr) @ E : Ψ) ∧
  (REL e << fill K (#false : expr) @ E : Ψ) -∗
  REL e << fill K (is_senc_key k) @ E : Ψ.
Proof.
iIntros (?) "#m_k post".
iApply (pure_twp_rel_r _ _ _ _ _ _ #(Spec.has_key_type SEnc k)
          with "[post]") => //=.
- apply: term_pure.
- move=> ?; iIntros "_". wp_lam. by wp_apply (twp_has_key_type SEnc).
- case: k => [| | |kt t| | |]; try by move=> *; iDestruct "post" as "[_ post]".
  case: kt; try by iDestruct "post" as "[_ post]".
  iDestruct "post" as "[post _]".
  by iApply ("post" $! (SEncKey t)) => //;
  rewrite [term_of_senc_key]unlock.
Qed.

Lemma rel_is_verify_key_l E K e (pk : term) Ψ :
  minted pk -∗
  (∀ sk : sign_key, ⌜pk = Spec.pkey sk⌝ -∗ minted sk -∗
     REL fill K (#true : expr) << e @ E : Ψ) ∧
  (REL fill K (#false : expr) << e @ E : Ψ) -∗
  REL fill K (is_verify_key pk) << e @ E : Ψ.
Proof.
iIntros "#m_pk post".
iApply (pure_twp_rel_l _ _ _ _ _ _ #(Spec.has_key_type Verify pk)
          with "[post]") => //=.
- apply: term_pure.
- move=> ?; iIntros "_". wp_lam. by wp_apply (twp_has_key_type Verify).
- case: pk => [| | |kt t| | |]; try by move=> *; iDestruct "post" as "[_ post]".
  case: kt; try by iDestruct "post" as "[_ post]".
  iDestruct "post" as "[post _]".
  by iApply ("post" $! (SignKey t)) => //;
  rewrite [term_of_sign_key]unlock // !minted_TKey.
Qed.

Lemma rel_is_verify_key_r E K e (pk : term) Ψ :
  ↑specN ⊆ E →
  minted_spec pk -∗
  (∀ sk : sign_key, ⌜pk = Spec.pkey sk⌝ -∗ minted_spec sk -∗
     REL e << fill K (#true : expr) @ E : Ψ) ∧
  (REL e << fill K (#false : expr) @ E : Ψ) -∗
  REL e << fill K (is_verify_key pk) @ E : Ψ.
Proof.
iIntros (?) "#m_pk post".
iApply (pure_twp_rel_r _ _ _ _ _ _ #(Spec.has_key_type Verify pk)
          with "[post]") => //=.
- apply: term_pure.
- move=> ?; iIntros "_". wp_lam. by wp_apply (twp_has_key_type Verify).
- case: pk => [| | |kt t| | |]; try by move=> *; iDestruct "post" as "[_ post]".
  case: kt; try by iDestruct "post" as "[_ post]".
  iDestruct "post" as "[post _]".
  by iApply ("post" $! (SignKey t)) => //;
  rewrite [term_of_sign_key]unlock // !minted_spec_TKey.
Qed.

Lemma rel_is_sign_key_l E K e (sk : term) Ψ :
  minted sk -∗
  (∀ sk' : sign_key, ⌜sk = sk'⌝ -∗ REL fill K (#true : expr) << e @ E : Ψ) ∧
  (REL fill K (#false : expr) << e @ E : Ψ) -∗
  REL fill K (is_sign_key sk) << e @ E : Ψ.
Proof.
iIntros "#m_sk post".
iApply (pure_twp_rel_l _ _ _ _ _ _ #(Spec.has_key_type Sign sk)
          with "[post]") => //=.
- apply: term_pure.
- move=> ?; iIntros "_". wp_lam. by wp_apply (twp_has_key_type Sign).
- case: sk => [| | |kt t| | |]; try by move=> *; iDestruct "post" as "[_ post]".
  case: kt; try by iDestruct "post" as "[_ post]".
  iDestruct "post" as "[post _]".
  by iApply ("post" $! (SignKey t)) => //;
  rewrite [term_of_sign_key]unlock.
Qed.

Lemma rel_is_sign_key_r E K e (sk : term) Ψ :
  ↑specN ⊆ E →
  minted_spec sk -∗
  (∀ sk' : sign_key, ⌜sk = sk'⌝ -∗ REL e << fill K (#true : expr) @ E : Ψ) ∧
  (REL e << fill K (#false : expr) @ E : Ψ) -∗
  REL e << fill K (is_sign_key sk) @ E : Ψ.
Proof.
iIntros (?) "#m_sk post".
iApply (pure_twp_rel_r _ _ _ _ _ _ #(Spec.has_key_type Sign sk)
          with "[post]") => //=.
- apply: term_pure.
- move=> ?; iIntros "_". wp_lam. by wp_apply (twp_has_key_type Sign).
- case: sk => [| | |kt t| | |]; try by move=> *; iDestruct "post" as "[_ post]".
  case: kt; try by iDestruct "post" as "[_ post]".
  iDestruct "post" as "[post _]".
  by iApply ("post" $! (SignKey t)) => //;
  rewrite [term_of_sign_key]unlock.
Qed.

End Proofs.

Arguments channel_rel {Σ _ _}.
Arguments rel_mk_aenc_key_l {Σ _ _} K e T_sk T_pk Ψ.
Arguments rel_mk_aenc_key_r {Σ _ _} K e T_sk T_pk Ψ.
