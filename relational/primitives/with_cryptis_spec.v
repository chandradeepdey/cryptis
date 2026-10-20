From reloc Require Import reloc.
From cryptis Require Import lib cryptis.
From cryptis.primitives Require Import simple with_cryptis.
From cryptis.hyper.core Require Import minted_spec term_meta_spec rel.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.primitives Require Import simple_spec.
From cryptis.hyper.proofmode Require Import updates tactics.

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

Abbreviation nonce := loc.
Implicit Types E : coPset.
Implicit Types a : nonce.
Implicit Types t : term.
Implicit Types v : val.
Implicit Types sk : aenc_key.
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
rel_pures_l. rewrite [val_of_term]unlock.
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
rel_pures_r. rewrite [val_of_term]unlock.
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

Lemma rel_mk_sign_key_l K e (T_sk T_pk : term → gset term) Ψ :
  (∀ sk : sign_key,
     seed_of_sign_key sk ∉ T_sk sk ∧
     seed_of_sign_key sk ∉ T_pk (Spec.pkey sk) ∧
     T_sk sk ## T_pk (Spec.pkey sk)) →
  cryptis_rel_ctx -∗
  (∀ sk : sign_key, [∗ set] t' ∈ T_sk sk, □ (minted sk ↔ minted t')) -∗
  (∀ sk : sign_key, [∗ set] t' ∈ T_pk (Spec.pkey sk),
     □ (minted (Spec.pkey sk) ↔ minted t')) -∗
  (∀ sk : sign_key, ⌜is_nonce (seed_of_sign_key sk)⌝ -∗
    minted sk -∗
    term_token (seed_of_sign_key sk) ⊤ -∗
    ([∗ set] t' ∈ T_sk sk, term_token t' ⊤) -∗
    ([∗ set] t' ∈ T_pk (Spec.pkey sk), term_token t' ⊤) -∗
    (REL fill K (sk : expr) << e : Ψ)) -∗
  REL fill K (mk_sign_key #()) << e : Ψ.
Proof.
iIntros (Hdisj) "#Hctx #minted_sk #minted_pk mint"; rewrite /mk_sign_key.
rel_pures_l.
rel_apply_l (rel_mk_nonce_l _ _
  (λ t, {[t]} ∪ T_sk (SignKey t) ∪ T_pk (Spec.pkey (SignKey t))))=> //.
{ iIntros "%t".
  case: (Hdisj (SignKey t)) => [Hseed_sk [Hseed_pk Hsk_pk]].
  have Hseed : seed_of_sign_key (SignKey t) = t by [].
  rewrite Hseed in Hseed_sk Hseed_pk.
  rewrite big_sepS_union; last set_solver.
  rewrite big_sepS_union; last set_solver.
  rewrite big_sepS_singleton.
  iSplit; first iSplit.
  - iModIntro. by iSplit; iIntros "?".
  - iSpecialize ("minted_sk" $! (SignKey t)). by setoid_rewrite minted_sign.
  - iSpecialize ("minted_pk" $! (SignKey t)).
    by setoid_rewrite minted_pkey; setoid_rewrite minted_sign. }
iIntros (t) "%Hnonce #Hmint Htt".
case: (Hdisj (SignKey t)) => [Hseed_sk [Hseed_pk Hsk_pk]].
have Hseed : seed_of_sign_key (SignKey t) = t by [].
rewrite Hseed in Hseed_sk Hseed_pk.
rewrite big_sepS_union; last set_solver.
rewrite big_sepS_union; last set_solver.
rewrite big_sepS_singleton.
iDestruct "Htt" as "[[Htt_seed Htt_sk] Htt_pk]".
rel_pures_l. rel_apply_l rel_derive_sign_key_l.
iApply ("mint" $! (SignKey t) with "[//] [] Htt_seed Htt_sk Htt_pk").
by iApply minted_sign.
Qed.

Lemma rel_mk_sign_key_r K e (T_sk T_pk : term → gset term) Ψ :
  (∀ sk : sign_key,
     seed_of_sign_key sk ∉ T_sk sk ∧
     seed_of_sign_key sk ∉ T_pk (Spec.pkey sk) ∧
     T_sk sk ## T_pk (Spec.pkey sk)) →
  cryptis_rel_ctx -∗
  (∀ sk : sign_key, [∗ set] t' ∈ T_sk sk, □ (minted_spec sk ↔ minted_spec t')) -∗
  (∀ sk : sign_key, [∗ set] t' ∈ T_pk (Spec.pkey sk),
     □ (minted_spec (Spec.pkey sk) ↔ minted_spec t')) -∗
  (∀ sk : sign_key, ⌜is_nonce (seed_of_sign_key sk)⌝ -∗
    minted_spec sk -∗
    term_token_spec (seed_of_sign_key sk) ⊤ -∗
    ([∗ set] t' ∈ T_sk sk, term_token_spec t' ⊤) -∗
    ([∗ set] t' ∈ T_pk (Spec.pkey sk), term_token_spec t' ⊤) -∗
    (REL e << fill K (sk : expr) : Ψ)) -∗
  REL e << fill K (mk_sign_key #()) : Ψ.
Proof.
iIntros (Hdisj) "#Hctx #minted_sk #minted_pk mint"; rewrite /mk_sign_key.
rel_pures_r.
rel_apply_r (rel_mk_nonce_r _ _
  (λ t, {[t]} ∪ T_sk (SignKey t) ∪ T_pk (Spec.pkey (SignKey t))))=> //.
{ iIntros "%t".
  case: (Hdisj (SignKey t)) => [Hseed_sk [Hseed_pk Hsk_pk]].
  have Hseed : seed_of_sign_key (SignKey t) = t by [].
  rewrite Hseed in Hseed_sk Hseed_pk.
  rewrite big_sepS_union; last set_solver.
  rewrite big_sepS_union; last set_solver.
  rewrite big_sepS_singleton.
  iSplit; first iSplit.
  - iModIntro. by iSplit; iIntros "?".
  - iSpecialize ("minted_sk" $! (SignKey t)). by setoid_rewrite minted_spec_sign.
  - iSpecialize ("minted_pk" $! (SignKey t)).
    by setoid_rewrite minted_spec_pkey; setoid_rewrite minted_spec_sign. }
iIntros (t) "%Hnonce #Hmint Htts".
case: (Hdisj (SignKey t)) => [Hseed_sk [Hseed_pk Hsk_pk]].
have Hseed : seed_of_sign_key (SignKey t) = t by [].
rewrite Hseed in Hseed_sk Hseed_pk.
rewrite big_sepS_union; last set_solver.
rewrite big_sepS_union; last set_solver.
rewrite big_sepS_singleton.
iDestruct "Htts" as "[[Htts_seed Htts_sk] Htts_pk]".
rel_pures_r. rel_apply_r rel_derive_sign_key_r.
iApply ("mint" $! (SignKey t) with "[//] [] Htts_seed Htts_sk Htts_pk").
by iApply minted_spec_sign.
Qed.

Lemma rel_mk_senc_key_l K e (T_k : term → gset term) Ψ :
  (∀ k : senc_key, seed_of_senc_key k ∉ T_k k) →
  cryptis_rel_ctx -∗
  (∀ k : senc_key, [∗ set] t' ∈ T_k k, □ (minted k ↔ minted t')) -∗
  (∀ k : senc_key, ⌜is_nonce (seed_of_senc_key k)⌝ -∗
    minted k -∗
    term_token (seed_of_senc_key k) ⊤ -∗
    ([∗ set] t' ∈ T_k k, term_token t' ⊤) -∗
    (REL fill K (k : expr) << e : Ψ)) -∗
  REL fill K (mk_senc_key #()) << e : Ψ.
Proof.
iIntros (Hdisj) "#Hctx #minted_k mint"; rewrite /mk_senc_key.
rel_pures_l.
rel_apply_l (rel_mk_nonce_l _ _ (λ t, {[t]} ∪ T_k (SEncKey t)))=> //.
{ iIntros "%t".
  have Hseed_k := Hdisj (SEncKey t).
  have Hseed : seed_of_senc_key (SEncKey t) = t by [].
  rewrite Hseed in Hseed_k.
  rewrite big_sepS_union; last set_solver.
  rewrite big_sepS_singleton.
  iSplit.
  - iModIntro. by iSplit; iIntros "?".
  - iSpecialize ("minted_k" $! (SEncKey t)). by setoid_rewrite minted_senc. }
iIntros (t) "%Hnonce #Hmint Htt".
have Hseed_k := Hdisj (SEncKey t).
have Hseed : seed_of_senc_key (SEncKey t) = t by [].
rewrite Hseed in Hseed_k.
rewrite big_sepS_union; last set_solver.
rewrite big_sepS_singleton.
iDestruct "Htt" as "[Htt_seed Htt_k]".
rel_pures_l. rel_apply_l rel_derive_senc_key_l.
iApply ("mint" $! (SEncKey t) with "[//] [] Htt_seed Htt_k").
by iApply minted_senc.
Qed.

Lemma rel_mk_senc_key_r K e (T_k : term → gset term) Ψ :
  (∀ k : senc_key, seed_of_senc_key k ∉ T_k k) →
  cryptis_rel_ctx -∗
  (∀ k : senc_key, [∗ set] t' ∈ T_k k, □ (minted_spec k ↔ minted_spec t')) -∗
  (∀ k : senc_key, ⌜is_nonce (seed_of_senc_key k)⌝ -∗
    minted_spec k -∗
    term_token_spec (seed_of_senc_key k) ⊤ -∗
    ([∗ set] t' ∈ T_k k, term_token_spec t' ⊤) -∗
    (REL e << fill K (k : expr) : Ψ)) -∗
  REL e << fill K (mk_senc_key #()) : Ψ.
Proof.
iIntros (Hdisj) "#Hctx #minted_k mint"; rewrite /mk_senc_key.
rel_pures_r.
rel_apply_r (rel_mk_nonce_r _ _ (λ t, {[t]} ∪ T_k (SEncKey t)))=> //.
{ iIntros "%t".
  have Hseed_k := Hdisj (SEncKey t).
  have Hseed : seed_of_senc_key (SEncKey t) = t by [].
  rewrite Hseed in Hseed_k.
  rewrite big_sepS_union; last set_solver.
  rewrite big_sepS_singleton.
  iSplit.
  - iModIntro. by iSplit; iIntros "?".
  - iSpecialize ("minted_k" $! (SEncKey t)). by setoid_rewrite minted_spec_senc. }
iIntros (t) "%Hnonce #Hmint Htts".
have Hseed_k := Hdisj (SEncKey t).
have Hseed : seed_of_senc_key (SEncKey t) = t by [].
rewrite Hseed in Hseed_k.
rewrite big_sepS_union; last set_solver.
rewrite big_sepS_singleton.
iDestruct "Htts" as "[Htts_seed Htts_k]".
rel_pures_r. rel_apply_r rel_derive_senc_key_r.
iApply ("mint" $! (SEncKey t) with "[//] [] Htts_seed Htts_k").
by iApply minted_spec_senc.
Qed.

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

Lemma rel_random_adec_l E K e k N c Ψ :
  (REL fill K (repr (Spec.random_adec k N c) : expr) << e @ E : Ψ) -∗
  REL fill K (random_adec k N c) << e @ E : Ψ.
Proof. pure_twp_rel twp_random_adec'. Qed.

Lemma rel_random_adec_r E K e k N c Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (Spec.random_adec k N c) : expr) @ E : Ψ) -∗
  REL e << fill K (random_adec k N c) @ E : Ψ.
Proof. pure_twp_rel twp_random_adec'. Qed.

(** Randomized encryption, [random_aenc], pairs a fresh nonce with the
  plaintext before encrypting.  The nonce is what makes two ciphertexts of the
  same key and tag indistinguishable: it is kept secret, so neither run's
  plaintext can be recomputed and compared.  The two ciphertexts come out
  publicly related as long as the decryption key on the left is secret.

  Because the nonce is created inside the primitive, [rel_random_aenc] is the
  one place that hands out the nonce's tokens.  A caller that builds further
  fresh terms on top of the ciphertext, such as a signature of it, names them
  through the token sets [T] and [T'], one per side; they must stay clear of
  the four terms the primitive itself registers (the nonce, the pair, the
  tagged pair and the ciphertext) and the caller gets their tokens back
  untouched.

  The ciphertexts are linked only when the caller says so: the continuation
  receives a view shift that records the seal in the key's seal sets and
  returns the public relation between the ciphertexts.  Running it right away
  gives the plain spec; postponing it lets a protocol first store the
  ciphertext under an invariant, as a decryption oracle needs. *)

Definition random_terms sk (N : namespace) n m : gset term :=
  {[n; TPair n m; Spec.tag (Tag N) (TPair n m);
    Spec.random_aenc (Spec.pkey sk) (Tag N) n m]}.

Definition random_seal sk sk' (N : namespace) n n' m m' : wf_seal_data * wf_seal_data :=
  (Some (sk : term, Spec.tag (Tag N) (TPair n m)),
   Some (sk' : term, Spec.tag (Tag N) (TPair n' m'))).

Lemma rel_random_aenc (T T' : term → gset term) sk sk' (N : namespace) m m' Ψ :
  cryptis_rel_ctx -∗
  ⌜is_nonce (seed_of_aenc_key sk)⌝ -∗
  minted sk -∗
  minted_spec sk' -∗
  publicly_linked (Spec.pkey sk) (Spec.pkey sk') -∗
  secret_in_l (seed_of_aenc_key sk) -∗
  minted m -∗ minted_spec m' -∗
  ⌜∀ n, is_nonce n → random_terms sk N n m ## T n⌝ -∗
  ⌜∀ n', is_nonce n' → random_terms sk' N n' m' ## T' n'⌝ -∗
  (∀ n, [∗ set] t ∈ T n, □ (minted n ↔ minted t)) -∗
  (∀ n', [∗ set] t ∈ T' n', □ (minted_spec n' ↔ minted_spec t)) -∗
  (∀ n n', ⌜is_nonce n⌝ -∗ ⌜is_nonce n'⌝ -∗ minted n -∗ minted_spec n' -∗
    ([∗ set] t ∈ T n, term_token t ⊤) -∗
    ([∗ set] t ∈ T' n', term_token_spec t ⊤) -∗
    (∀ E S S', ⌜↑cryptisN ⊆ E⌝ -∗
      seals_auth_l (seed_of_aenc_key sk) S -∗
      seals_auth_r (seed_of_aenc_key sk') S' ={E}=∗
      seals_auth_l (seed_of_aenc_key sk) (S ∪ {[random_seal sk sk' N n n' m m']}) ∗
      seals_auth_r (seed_of_aenc_key sk') (S' ∪ {[random_seal sk sk' N n n' m m']}) ∗
      PUB⟨Spec.random_aenc (Spec.pkey sk) (Tag N) n m,
          Spec.random_aenc (Spec.pkey sk') (Tag N) n' m'⟩) ={⊤}=∗
    Ψ (Spec.random_aenc (Spec.pkey sk) (Tag N) n m)
      (Spec.random_aenc (Spec.pkey sk') (Tag N) n' m')) -∗
  REL random_aenc (Spec.pkey sk) (Tag N) m
   << random_aenc (Spec.pkey sk') (Tag N) m' : Ψ.
Proof.
iIntros "#Hctx %Hnonce #mint_sk #mint_sk' #elem_pk #secret #mint_m #mint_m'".
iIntros "%HT %HT' #mintT #mintT' post".
iAssert (minted (Spec.pkey sk)) as "#mint_pk"; first by rewrite minted_pkey.
iAssert (minted_spec (Spec.pkey sk')) as "#mint_pk'";
  first by rewrite minted_spec_pkey.
rewrite /random_aenc. rel_pures.
rel_apply_l (rel_mk_nonce_l _ _ (λ n, random_terms sk N n m ∪ T n) with "[//]").
{ iIntros (t). rewrite big_sepS_forall. iIntros (t' [Ht'|Ht']%elem_of_union).
  - rewrite /random_terms in Ht'. set_unfold in Ht'. destruct_or? Ht'; subst t';
      solve_minted_iff_elem.
  - iSpecialize ("mintT" $! t). rewrite big_sepS_forall. by iApply "mintT". }
iIntros (n) "%Hn #mint_n Htt".
rel_apply_r (rel_mk_nonce_r _ _ (λ n', random_terms sk' N n' m' ∪ T' n') with "[//]").
{ iIntros (t). rewrite big_sepS_forall. iIntros (t' [Ht'|Ht']%elem_of_union).
  - rewrite /random_terms in Ht'. set_unfold in Ht'. destruct_or? Ht'; subst t';
      solve_minted_iff_elem.
  - iSpecialize ("mintT'" $! t). rewrite big_sepS_forall. by iApply "mintT'". }
iIntros (n') "%Hn' #mint_n' Htts".
rewrite (big_sepS_union _ (random_terms sk N n m)); last exact: HT.
rewrite (big_sepS_union _ (random_terms sk' N n' m')); last exact: HT'.
iDestruct "Htt" as "[Htt tokT]". iDestruct "Htts" as "[Htts tokT']".
rewrite /random_terms. split_term_tokens.
iDestruct "Htt" as "(((tt_n & tt_pl) & tt_tg) & tt_c)".
iDestruct "Htts" as "(((tts_n & tts_pl) & tts_tg) & tts_c)".
set pl := TPair n m.
set tg := Spec.tag (Tag N) pl.
set c := Spec.random_aenc (Spec.pkey sk) (Tag N) n m.
set pl' := TPair n' m'.
set tg' := Spec.tag (Tag N) pl'.
set c' := Spec.random_aenc (Spec.pkey sk') (Tag N) n' m'.
(* The tagged payload is protected by the chain nonce → payload → tagged payload. *)
iMod (public_rel_protect_nonce_l (tsup:=pl) Hn ltac:(solve_immediate_subterm)
        ltac:(solve_ndisj) with "Hctx tt_n") as "protby_pl".
iMod (public_rel_protect_step_l (t:=pl) (tsup:=tg) ltac:(solve_immediate_subterm)
        ltac:(solve_ndisj) with "Hctx protby_pl tt_pl") as "protby_tg".
iMod (public_rel_protect_nonce_r (t'sup:=pl') Hn' ltac:(solve_immediate_subterm)
        ltac:(solve_ndisj) with "Hctx tts_n") as "protby_pl'".
iMod (public_rel_protect_step_r (t':=pl') (t'sup:=tg') ltac:(solve_immediate_subterm)
        ltac:(solve_ndisj) with "Hctx protby_pl' tts_pl") as "protby_tg'".
iMod (public_rel_link (E:=⊤) ltac:(solve_ndisj)
        with "Hctx protby_tg protby_tg' tt_tg tts_tg") as "#priv_tg".
(* The secret key can never become publicly related. *)
iAssert (□ (PUB⟨sk, sk'⟩ → PUB⟨pl, pl'⟩))%I as "#Hbox".
{ iIntros "!> #Hsk". iExFalso.
  rewrite publicly_related_adec_key'.
  iDestruct (publicly_related_nonce_term _ Hnonce with "Hsk") as "[Hl _]".
  by iDestruct (secret_in_l_publicly_linked_in_l with "secret Hl") as "[]". }
iAssert (minted pl) as "#mint_pl".
{ rewrite /pl minted_TPair. by iSplit. }
iAssert (minted_spec pl') as "#mint_pl'".
{ rewrite /pl' minted_spec_TPair. by iSplit. }
(* The ciphertexts are linked when the caller records the seal. *)
iMod ("post" $! n n' with "[//] [//] mint_n mint_n' tokT tokT' [tt_c tts_c]")
  as "post".
{ iIntros (E S S' HE) "seals_l seals_r".
  iMod (seals_auth_l_insert _ _ (random_seal sk sk' N n n' m m') with "seals_l")
    as "[seals_l #Hin_l]".
  iMod (seals_auth_r_insert _ _ (random_seal sk sk' N n n' m m') with "seals_r")
    as "[seals_r #Hin_r]".
  iMod (public_rel_publish HE with "Hctx [] tt_c tts_c") as "[_ #Hpub_c]".
  { iIntros "!> #elem_c". rewrite /c /c' /Spec.random_aenc publicly_related_aenc.
    iRight. do 5 (iSplit; first done).
    iSplit; first by iApply publicly_linked_linked.
    iSplit; first done. iSplit; first done.
    by iApply (wf_seal_rel_aenc_intro with "Hin_l Hin_r"). }
  iModIntro. by iFrame "#∗". }
(* Run the program. *)
rel_apply_l rel_tuple_l. rel_apply_l rel_aenc'_l. rel_later.
rel_apply_r rel_tuple_r. rel_apply_r rel_aenc'_r. by rel_values.
Qed.

End Proofs.

Arguments channel_rel {Σ _ _}.
Arguments rel_mk_aenc_key_l {Σ _ _} K e T_sk T_pk Ψ.
Arguments rel_mk_aenc_key_r {Σ _ _} K e T_sk T_pk Ψ.
Arguments rel_mk_sign_key_l {Σ _ _} K e T_sk T_pk Ψ.
Arguments rel_mk_sign_key_r {Σ _ _} K e T_sk T_pk Ψ.
Arguments rel_mk_senc_key_l {Σ _ _} K e T_k Ψ.
Arguments rel_mk_senc_key_r {Σ _ _} K e T_k Ψ.
