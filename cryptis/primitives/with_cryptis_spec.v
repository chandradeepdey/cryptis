From reloc Require Import reloc.
From cryptis Require Import cryptis.
From cryptis.primitives Require Import simple with_cryptis.
From cryptis.core Require Import minted_spec rel.
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
Implicit Types Ψ : lrel Σ.

Definition channel_rel : lrel Σ := LRel (λ c c',
  ∃ (sf rf sf' rf' : val), ⌜c = (sf, rf)%V⌝ ∗ ⌜c' = (sf', rf')%V⌝  ∗
  □ (∀ t t' Ψ, publicly_related t t' -∗ Ψ #() #() -∗ REL sf t << sf' t' : Ψ) ∗
  □ (∀ Ψ, (∀ t t', publicly_related t t' -∗ Ψ t t') -∗ REL rf #() << rf' #() : Ψ))%I.

#[global] Instance channel_rel_persistent c c' : Persistent (channel_rel c c').
Proof. apply _. Qed.

Definition chan_rel_inv l l' : iProp Σ :=
  ∃ t t', l ↦ t ∗ l' ↦ₛ t' ∗ publicly_related t t'.

#[local] Lemma rel_sender (l l': loc) t t' :
  inv cryptisN (chan_rel_inv l l') -∗
  publicly_related t t' -∗
  REL (sender #l t) << (sender #l' t') : lrel_unit.
Proof.
iIntros "#Hinv #Ht".
iLöb as "IH".
rel_rec_l. rel_rec_r.
rel_pures_l. rel_pures_r.
rel_store_l_atomic.
iInv cryptisN as "(%t1 & %t1' & (Hl & Hl' & #Hrel))" "Hclose".
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
iMod (inv_alloc cryptisN _ (chan_rel_inv l l') with "[Hl Hl']") as "#Hinv".
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
  iInv cryptisN as "(%t & %t' & Hl & Hl' & #Hrel)" "Hclose".
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
  ▷ publicly_related t t' -∗
  REL send c t << send c' t' : lrel_unit.
Proof.
iDestruct 1 as (sf rf sf' rf') "(-> & -> & #H & _)".
iIntros "#?"; rewrite /send; rel_pures_l; rel_pures_r.
by iApply "H".
Qed.

Lemma rel_recv c c' Ψ :
  channel_rel c c' -∗
  (∀ t t', publicly_related t t' -∗ Ψ t t') -∗
  REL recv c << recv c' : Ψ.
Proof.
iDestruct 1 as (sf rf sf' rf') "(-> & -> & #_ & #H)".
iIntros "?"; rewrite /recv; rel_pures_l; rel_pures_r.
by iApply "H".
Qed.

Lemma twp_mk_nonce_rel φ :
  (∀ t, ⌜is_nonce t⌝ -∗ mintable t -∗ φ t) -∗
  WP mk_nonce #()%V [{ φ }].
Proof.
rewrite /mk_nonce; iIntros "mint".
wp_pures.
wp_pures; wp_bind (ref _)%E; iApply twp_alloc=> //.
iIntros (l) "[_ Htoken]".
iPoseProof (mintable_alloc with "Htoken") as "fresh".
wp_pures. rewrite val_of_term_unseal /=.
iModIntro. iApply ("mint" $! (TNonce l))=> //=.
Qed.

Lemma wp_mk_nonce_rel φ :
  (∀ t, ⌜is_nonce t⌝ -∗ mintable t -∗ φ t) -∗
  WP mk_nonce #()%V {{ φ }}.
Proof.
  iIntros "H".
  by iApply twp_wp; iApply (twp_mk_nonce_rel with "H").
Qed.

Lemma tp_mk_nonce E j :
  ↑specN ⊆ E →
  refines_right j (mk_nonce #()) -∗
  |={E}=> ∃ t, refines_right j t ∗ ⌜is_nonce t⌝ ∗ mintable_spec t.
Proof.
iIntros "% Hj"; rewrite /mk_nonce.
tp_pures j.
tp_alloc j as a "Ha".
iPoseProof (mintable_spec_alloc with "Ha") as "Ha".
tp_pures j.
iExists (TNonce a).
rewrite val_of_term_unseal. by iFrame.
Qed.

(* twp ??? *)
Lemma wp_mk_aenc_key_rel φ :
  (∀ sk : aenc_key, minted sk -∗ φ sk) -∗
  WP mk_aenc_key #() {{ φ }}.
Proof.
iIntros "mint". rewrite /mk_aenc_key.
wp_pures.
wp_apply wp_mk_nonce_rel as "%t %Hnonce Hmint".
iDestruct "Hmint" as "[_ >Hmint]".
wp_pures; wp_apply wp_derive_aenc_key.
iApply "mint".
by iApply minted_aenc.
Qed.

Lemma tp_mk_aenc_key E j :
  ↑specN ⊆ E →
  refines_right j (mk_aenc_key #()) -∗
  |={E}=> ∃ (sk : aenc_key), refines_right j sk ∗ minted_spec sk.
Proof.
iIntros "% Hj"; rewrite /mk_aenc_key.
tp_pures j.
tp_bind j (mk_nonce _).
rewrite refines_right_bind.
iPoseProof (tp_mk_nonce with "Hj") as ">(%t & Hj & %Hnonce & Hmint)"=> //.
rewrite -refines_right_bind=> /=.
tp_pures j.
iPoseProof (tp_derive_aenc_key with "Hj") as ">Hj" => //=.
iPoseProof (mintable_spec_alloc_2 t (AEncKey t) with "[] Hmint") as "[_ >Hmint]";
  first by iModIntro; iSplit; iIntros "#H"; iApply minted_spec_aenc.
by iFrame.
Qed.

Lemma wp_mk_sign_key_rel φ :
  (∀ sk : sign_key, minted sk -∗ φ sk) -∗
  WP mk_sign_key #() {{ φ }}.
Proof.
iIntros "mint". rewrite /mk_sign_key.
wp_pures.
wp_apply wp_mk_nonce_rel as "%t %Hnonce Hmint".
iDestruct "Hmint" as "[_ >Hmint]".
wp_pures; wp_apply wp_derive_sign_key.
iApply "mint".
by iApply minted_sign.
Qed.

Lemma tp_mk_sign_key E j :
  ↑specN ⊆ E →
  refines_right j (mk_sign_key #()) -∗
  |={E}=> ∃ (sk : sign_key), refines_right j sk ∗ minted_spec sk.
Proof.
iIntros "% Hj"; rewrite /mk_sign_key.
tp_pures j.
tp_bind j (mk_nonce _).
rewrite refines_right_bind.
iPoseProof (tp_mk_nonce with "Hj") as ">(%t & Hj & %Hnonce & Hmint)"=> //.
rewrite -refines_right_bind=> /=.
tp_pures j.
iPoseProof (tp_derive_sign_key with "Hj") as ">Hj" => //=.
iPoseProof (mintable_spec_alloc_2 t (SignKey t) with "[] Hmint") as "[_ >Hmint]";
  first by iModIntro; iSplit; iIntros "#H"; iApply minted_spec_sign.
by iFrame.
Qed.

Lemma wp_mk_senc_key_rel φ :
  (∀ k : senc_key, minted k -∗ φ k) -∗
  WP mk_senc_key #() {{ φ }}.
Proof.
iIntros "mint". rewrite /mk_senc_key.
wp_pures.
wp_apply wp_mk_nonce_rel as "%t %Hnonce Hmint".
iDestruct "Hmint" as "[_ >Hmint]".
wp_pures; wp_apply wp_derive_senc_key.
iApply "mint".
by iApply minted_senc.
Qed.

Lemma tp_mk_senc_key E j :
  ↑specN ⊆ E →
  refines_right j (mk_senc_key #()) -∗
  |={E}=> ∃ (k : senc_key), refines_right j k ∗ minted_spec k.
Proof.
iIntros "% Hj"; rewrite /mk_senc_key.
tp_pures j.
tp_bind j (mk_nonce _).
rewrite refines_right_bind.
iPoseProof (tp_mk_nonce with "Hj") as ">(%t & Hj & %Hnonce & Hmint)"=> //.
rewrite -refines_right_bind=> /=.
tp_pures j.
iPoseProof (tp_derive_senc_key with "Hj") as ">Hj" => //=.
iPoseProof (mintable_spec_alloc_2 t (SEncKey t) with "[] Hmint") as "[_ >Hmint]";
  first by iModIntro; iSplit; iIntros "#H"; iApply minted_spec_senc.
by iFrame.
Qed.

End Proofs.

Arguments channel_rel {Σ _ _}.
