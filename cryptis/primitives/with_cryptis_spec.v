From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From mathcomp Require order.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap reservation_map.
From iris.base_logic.lib Require Import invariants saved_prop.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import nondet_bool ticket_lock.
From cryptis Require Import term cryptis.
From cryptis.primitives Require Import notations pre_term comp simple.

From cryptis.primitives Require Import with_cryptis.
From reloc Require Import reloc.
From cryptis.core Require Import rel minted_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance cryptisGS_tlock.
Local Existing Instance ticket_lock.

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

Lemma twp_mk_nonce_rel (Ψ : val -> iProp Σ) :
  (∀ t, ⌜is_nonce t⌝ -∗ mintable t -∗ Ψ t) -∗
  WP mk_nonce #()%V [{ Ψ }].
Proof.
rewrite /mk_nonce; iIntros "mint".
wp_pures.
wp_pures; wp_bind (ref _)%E; iApply twp_alloc=> //.
iIntros (l) "[_ Htoken]".
iPoseProof (mintable_alloc with "Htoken") as "fresh".
wp_pures. rewrite val_of_term_unseal /=.
iModIntro. iApply ("mint" $! (TNonce l))=> //=.
Qed.

Lemma wp_mk_nonce_rel (Ψ : val -> iProp Σ) :
  (∀ t, ⌜is_nonce t⌝ -∗ mintable t -∗ Ψ t) -∗
  WP mk_nonce #()%V {{ Ψ }}.
Proof.
  iIntros "H".
  by iApply twp_wp; iApply (twp_mk_nonce_rel with "H").
Qed.

Lemma tp_mk_nonce E j :
  ↑specN ⊆ E →
  refines_right j (mk_nonce #()) -∗
  |={E}=> ∃ t, refines_right j t ∗ ⌜is_nonce t⌝ ∗ mintable_spec t.
Proof.
iIntros "% j"; rewrite /mk_nonce.
tp_pures j.
tp_alloc j as a "Ha".
iPoseProof (mintable_spec_alloc with "Ha") as "Ha".
tp_pures j.
iExists (TNonce a).
rewrite val_of_term_unseal. by iFrame.
Qed.

Lemma tp_mk_aenc_key E j :
  ↑specN ⊆ E →
  refines_right j (mk_aenc_key #()) -∗
  |={E}=> ∃ t, refines_right j t.
Proof.
iIntros "#ctx post". iMod unknown_alloc as (γ) "unknown".
rewrite /mk_aenc_key. wp_pures.
wp_bind (mk_nonce _).
iApply (twp_mk_nonce_freshN ∅ (λ _, known γ 1) (λ _, False%I)
  (λ t, {[(AEncKey t) : term]})) => //.
- iIntros "% ?". by rewrite elem_of_empty.
- iIntros "%t". rewrite [term_of_aenc_key]unlock big_sepS_singleton minted_TKey.
  iModIntro. by iSplit; iIntros "?".
iIntros "%t %fresh % #m_t #s_t _ token".
rewrite big_sepS_singleton.
pose sk := AEncKey t.
iAssert (public sk ↔ ▷ □ known γ 1)%I as "s_sk".
{ by rewrite public_adec_key. }
iAssert (secret sk) with "[unknown]" as "tP"; first do 2?iSplit.
- iMod (known_alloc with "unknown") as "#known".
  by iSpecialize ("s_sk" with "known").
- iMod (known_alloc 2 with "unknown") as "#known".
  iIntros "!> !>". iSplit.
  + iIntros "#p_sk".
    iPoseProof ("s_sk" with "p_sk") as ">#known'".
    by iPoseProof (known_agree with "known known'") as "%".
  + iIntros "#contra".
    iApply "s_sk". by iDestruct "contra" as ">[]".
- iIntros "#p_sk".
  iPoseProof ("s_sk" with "p_sk") as ">#known".
  by iPoseProof (unknown_known with "[$] [//]") as "[]".
wp_pures. wp_lam. iApply twp_key.
rewrite [term_of_aenc_key]unlock /=.
iApply ("post" $! (AEncKey _) with "[] [$] [$]").
by rewrite minted_TKey.
Qed.

Lemma wp_mk_aenc_key Ψ :
  cryptis_ctx -∗
  (∀ sk : aenc_key,
      minted sk -∗
      secret sk -∗
      term_token sk ⊤ -∗
      Ψ sk) -∗
  WP mk_aenc_key #() {{ Ψ }}.
Proof.
iIntros "#? ?". iApply twp_wp. by wp_apply twp_mk_aenc_key.
Qed.

Lemma twp_mk_sign_key Ψ :
  cryptis_ctx -∗
  (∀ sk : sign_key,
      minted sk -∗
      secret sk -∗
      term_token sk ⊤ -∗
      Ψ sk) -∗
  WP mk_sign_key #() [{ Ψ }].
Proof.
iIntros "#ctx post". iMod unknown_alloc as (γ) "unknown".
rewrite /mk_sign_key. wp_pures.
wp_bind (mk_nonce _).
iApply (twp_mk_nonce_freshN ∅ (λ _, known γ 1) (λ _, False%I)
  (λ t, {[(SignKey t) : term]})) => //.
- iIntros "% ?". by rewrite elem_of_empty.
- iIntros "%t". rewrite [term_of_sign_key]unlock big_sepS_singleton minted_TKey.
  iModIntro. by iSplit; iIntros "?".
iIntros "%t %fresh % #m_t #s_t _ token".
rewrite big_sepS_singleton.
pose sk := SignKey t.
iAssert (public sk ↔ ▷ □ known γ 1)%I as "s_sk".
{ by rewrite public_sign_key. }
iAssert (secret sk) with "[unknown]" as "tP"; first do 2?iSplit.
- iMod (known_alloc with "unknown") as "#known".
  by iSpecialize ("s_sk" with "known").
- iMod (known_alloc 2 with "unknown") as "#known".
  iIntros "!> !>". iSplit.
  + iIntros "#p_sk".
    iPoseProof ("s_sk" with "p_sk") as ">#known'".
    by iPoseProof (known_agree with "known known'") as "%".
  + iIntros "#contra".
    iApply "s_sk". by iDestruct "contra" as ">[]".
- iIntros "#p_sk".
  iPoseProof ("s_sk" with "p_sk") as ">#known".
  by iPoseProof (unknown_known with "[$] [//]") as "[]".
wp_pures. wp_lam. iApply twp_key.
rewrite [term_of_sign_key]unlock /=.
iApply ("post" $! (SignKey _) with "[] [$] [$]").
by rewrite minted_TKey.
Qed.

Lemma wp_mk_sign_key Ψ :
  cryptis_ctx -∗
  (∀ sk : sign_key,
      minted sk -∗
      secret sk -∗
      term_token sk ⊤ -∗
      Ψ sk) -∗
  WP mk_sign_key #() {{ Ψ }}.
Proof.
iIntros "#? ?". iApply twp_wp. by wp_apply twp_mk_sign_key.
Qed.

Lemma twp_mk_senc_key Ψ :
  cryptis_ctx -∗
  (∀ k : senc_key,
      minted k -∗
      secret k -∗
      term_token k ⊤ -∗
      Ψ k) -∗
  WP mk_senc_key #() [{ Ψ }].
Proof.
iIntros "#ctx post". iMod unknown_alloc as (γ) "unknown".
rewrite /mk_senc_key. wp_pures.
wp_bind (mk_nonce _).
iApply (twp_mk_nonce_freshN ∅ (λ _, known γ 1) (λ _, False%I)
  (λ t, {[(SEncKey t) : term]})) => //.
- iIntros "% ?". by rewrite elem_of_empty.
- iIntros "%t". rewrite [term_of_senc_key]unlock big_sepS_singleton minted_TKey.
  iModIntro. by iSplit; iIntros "?".
iIntros "%t %fresh % #m_t #s_t _ token".
rewrite big_sepS_singleton.
pose sk := SEncKey t.
iAssert (public sk ↔ ▷ □ known γ 1)%I as "s_sk".
{ by rewrite public_senc_key. }
iAssert (secret sk) with "[unknown]" as "tP"; first do 2?iSplit.
- iMod (known_alloc with "unknown") as "#known".
  by iSpecialize ("s_sk" with "known").
- iMod (known_alloc 2 with "unknown") as "#known".
  iIntros "!> !>". iSplit.
  + iIntros "#p_sk".
    iPoseProof ("s_sk" with "p_sk") as ">#known'".
    by iPoseProof (known_agree with "known known'") as "%".
  + iIntros "#contra".
    iApply "s_sk". by iDestruct "contra" as ">[]".
- iIntros "#p_sk".
  iPoseProof ("s_sk" with "p_sk") as ">#known".
  by iPoseProof (unknown_known with "[$] [//]") as "[]".
wp_pures. wp_lam. iApply twp_key.
rewrite [term_of_senc_key]unlock /=.
iApply ("post" $! (SEncKey _) with "[] [$] [$]").
by rewrite minted_TKey.
Qed.

Lemma wp_mk_senc_key Ψ :
  cryptis_ctx -∗
  (∀ k : senc_key,
      minted k -∗
      secret k -∗
      term_token k ⊤ -∗
      Ψ k) -∗
  WP mk_senc_key #() {{ Ψ }}.
Proof.
iIntros "#? ?". iApply twp_wp. by wp_apply twp_mk_senc_key.
Qed.

Lemma twp_aenc (sk : aenc_key) N t φ Ψ :
  aenc_pred N φ -∗
  minted sk -∗
  minted t -∗
  public t ∨ □ φ sk t ∧ □ (public sk → public t) -∗
  (∀ m, public m → Ψ m) -∗
  WP aenc (Spec.pkey sk) (Tag N) t [{ Ψ }].
Proof.
iIntros "#? #? #? #inv post".
wp_lam. wp_pures. wp_apply twp_enc. iApply "post".
iDestruct "inv" as "[p_t|[??]]".
- iApply public_TSealIP.
  + by iApply public_aenc_key.
  + by rewrite public_tag.
- iApply public_aencIS => //.
Qed.

Lemma wp_aenc (sk : aenc_key) N t φ Ψ :
  aenc_pred N φ -∗
  minted sk -∗
  minted t -∗
  public t ∨ □ φ sk t ∧ □ (public sk → public t) -∗
  (∀ m, public m → Ψ m) -∗
  WP aenc (Spec.pkey sk) (Tag N) t {{ Ψ }}.
Proof.
iIntros "#? #? #? #? ?".
iApply twp_wp. by wp_apply twp_aenc.
Qed.

Lemma wp_adec (sk : aenc_key) N m φ Ψ :
  aenc_pred N φ -∗
  public m -∗
  (∀ t, minted t -∗
        public t ∨ □ φ sk t ∧ □ (public sk → public t) -∗
        Ψ (SOMEV t)) ∧
  Ψ NONEV -∗
  WP adec sk (Tag N) m {{ Ψ }}.
Proof.
iIntros "#? #p_m post".
wp_lam. wp_pure _ credit:"c". wp_pures. iApply wp_fupd. wp_apply wp_dec.
case: Spec.decP => [k_t t /Spec.open_key_aencK -> ->|]; last first.
{ iDestruct "post" as "[_ post]". iApply "post". }
iPoseProof (public_aencE with "p_m [//]") as "[? [p_t|[#inv #p_t]]]".
- iApply "post" => //. by eauto.
- iMod (lc_fupd_elim_later_pers with "c inv") as "#?".
  iApply "post" => //. by eauto.
Qed.

Lemma twp_senc (sk : senc_key) N t φ Ψ :
  senc_pred N φ -∗
  minted sk -∗
  minted t -∗
  public sk ∨ □ φ sk t -∗
  □ (public sk → public t) -∗
  (∀ m, public m → Ψ m) -∗
  WP senc sk (Tag N) t [{ Ψ }].
Proof.
iIntros "#? #? #? #inv #p_t post".
wp_lam. wp_pures. wp_apply twp_enc. iApply "post".
iDestruct "inv" as "[p_sk|inv]".
- iApply public_TSealIP => //.
  rewrite public_tag. by iApply "p_t".
- by iApply public_sencIS => //.
Qed.

Lemma wp_senc (sk : senc_key) N t φ Ψ :
  senc_pred N φ -∗
  minted sk -∗
  minted t -∗
  public sk ∨ □ φ sk t -∗
  □ (public sk → public t) -∗
  (∀ m, public m → Ψ m) -∗
  WP senc sk (Tag N) t {{ Ψ }}.
Proof. by iIntros "#?#?#?#?#??"; iApply twp_wp; iApply twp_senc. Qed.

Lemma wp_sdec (sk : senc_key) N m φ Ψ :
  senc_pred N φ -∗
  public m -∗
  (∀ t, minted t -∗
        public sk ∨ □ φ sk t -∗
        □ (public sk → public t) -∗
        Ψ (SOMEV t)) ∧
  Ψ NONEV -∗
  WP sdec sk (Tag N) m {{ Ψ }}.
Proof.
iIntros "#? #p_m post".
wp_lam. wp_pure _ credit:"c". wp_pures. iApply wp_fupd. wp_apply wp_dec.
case: Spec.decP => [k_t t /Spec.open_key_sencK -> ->|]; last first.
{ iDestruct "post" as "[_ post]". iApply "post". }
iPoseProof (public_sencE with "p_m [//]") as "(? & [p_k|inv] & #p_t)".
- iApply "post" => //. by eauto.
- iMod (lc_fupd_elim_later_pers with "c inv") as "#?".
  iApply "post" => //. by eauto.
Qed.

Lemma twp_sign (sk : sign_key) N t φ Ψ :
  sign_pred N φ -∗
  minted sk -∗
  public t -∗
  public sk ∨ □ φ sk t -∗
  (∀ m, public m → Ψ m) -∗
  WP sign sk (Tag N) t [{ Ψ }].
Proof.
iIntros "#? #? #? #inv post".
wp_lam. wp_pures. wp_apply twp_enc. iApply "post".
iDestruct "inv" as "[p_t|#?]".
- iApply public_TSealIP => //.
  by rewrite public_tag.
- by iApply public_signIS => //.
Qed.

Lemma wp_sign (sk : sign_key) N t φ Ψ :
  sign_pred N φ -∗
  minted sk -∗
  public t -∗
  public sk ∨ □ φ sk t -∗
  (∀ m, public m → Ψ m) -∗
  WP sign sk (Tag N) t {{ Ψ }}.
Proof.
iIntros "#? #? #? #? ?".
iApply twp_wp. by wp_apply twp_sign.
Qed.

Lemma wp_verify (sk : sign_key) N m φ Ψ :
  sign_pred N φ -∗
  public m -∗
  (∀ t, public t -∗
        public sk ∨ □ φ sk t -∗
        Ψ (SOMEV t)) ∧
  Ψ NONEV -∗
  WP verify (Spec.pkey sk) (Tag N) m {{ Ψ }}.
Proof.
iIntros "#? #p_m post".
wp_lam. wp_pure _ credit:"c". wp_pures. iApply wp_fupd. wp_apply wp_dec.
case: Spec.decP => [k_t t /Spec.open_key_signK -> ->|]; last first.
{ iDestruct "post" as "[_ post]". iApply "post". }
iPoseProof (public_signE with "p_m [//]") as "[? [p_t|#inv]]".
- iApply "post" => //. by eauto.
- iMod (lc_fupd_elim_later_pers with "c inv") as "#?".
  iApply "post" => //. by eauto.
Qed.

Lemma twp_is_aenc_key pk Ψ :
  minted pk -∗
  (∀ sk : aenc_key, ⌜pk = Spec.pkey sk⌝ -∗ minted sk -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_aenc_key pk [{ Ψ }].
Proof.
iIntros "#m_pk post".
wp_lam. wp_apply (twp_has_key_type AEnc).
case: pk; try by move=> *; iDestruct "post" as "[_ post]".
move=> kt t.
case: kt; try by iDestruct "post" as "[_ post]".
iDestruct "post" as "[post _]".
by iApply ("post" $! (AEncKey t)) => //;
rewrite [term_of_aenc_key]unlock // !minted_TKey.
Qed.

Lemma wp_is_aenc_key pk Ψ :
  minted pk -∗
  (∀ sk : aenc_key, ⌜pk = Spec.pkey sk⌝ -∗ minted sk -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_aenc_key pk {{ Ψ }}.
Proof.
by iIntros "H1 H2"; iApply twp_wp;
iApply (twp_is_aenc_key with "H1 H2").
Qed.

Lemma twp_is_adec_key sk Ψ :
  minted sk -∗
  (∀ sk' : aenc_key, ⌜sk = sk'⌝ -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_adec_key sk [{ Ψ }].
Proof.
iIntros "#m_pk post".
wp_lam. wp_apply (twp_has_key_type ADec).
case: sk; try by move=> *; iDestruct "post" as "[_ post]".
move=> kt t.
case: kt; try by iDestruct "post" as "[_ post]".
iDestruct "post" as "[post _]".
by iApply ("post" $! (AEncKey t)) => //;
rewrite [term_of_aenc_key]unlock // !minted_TKey.
Qed.

Lemma wp_is_adec_key sk Ψ :
  minted sk -∗
  (∀ sk' : aenc_key, ⌜sk = sk'⌝ -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_adec_key sk {{ Ψ }}.
Proof.
by iIntros "H1 H2"; iApply twp_wp;
iApply (twp_is_adec_key with "H1 H2").
Qed.

Lemma twp_is_senc_key k Ψ :
  minted k -∗
  (∀ k' : senc_key, ⌜k = k'⌝ -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_senc_key k [{ Ψ }].
Proof.
iIntros "#m_pk post".
wp_lam. wp_apply (twp_has_key_type SEnc).
case: k; try by move=> *; iDestruct "post" as "[_ post]".
move=> kt t.
case: kt; try by iDestruct "post" as "[_ post]".
iDestruct "post" as "[post _]".
by iApply ("post" $! (SEncKey t)) => //;
rewrite [term_of_senc_key]unlock // !minted_TKey.
Qed.

Lemma wp_is_senc_key k Ψ :
  minted k -∗
  (∀ k' : senc_key, ⌜k = k'⌝ -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_senc_key k {{ Ψ }}.
Proof.
by iIntros "H1 H2"; iApply twp_wp;
iApply (twp_is_senc_key with "H1 H2").
Qed.

Lemma twp_is_verify_key pk Ψ :
  minted pk -∗
  (∀ sk : sign_key, ⌜pk = Spec.pkey sk⌝ -∗ minted sk -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_verify_key pk [{ Ψ }].
Proof.
iIntros "#m_pk post".
wp_lam. wp_apply (twp_has_key_type Verify).
case: pk; try by move=> *; iDestruct "post" as "[_ post]".
move=> kt t.
case: kt; try by iDestruct "post" as "[_ post]".
iDestruct "post" as "[post _]".
by iApply ("post" $! (SignKey t)) => //;
rewrite [term_of_sign_key]unlock // !minted_TKey.
Qed.

Lemma wp_is_verify_key pk Ψ :
  minted pk -∗
  (∀ sk : sign_key, ⌜pk = Spec.pkey sk⌝ -∗ minted sk -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_verify_key pk {{ Ψ }}.
Proof.
by iIntros "H1 H2"; iApply twp_wp;
iApply (twp_is_verify_key with "H1 H2").
Qed.

Lemma twp_is_sign_key sk Ψ :
  minted sk -∗
  (∀ sk' : sign_key, ⌜sk = sk'⌝ -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_sign_key sk [{ Ψ }].
Proof.
iIntros "#m_pk post".
wp_lam. wp_apply (twp_has_key_type Sign).
case: sk; try by move=> *; iDestruct "post" as "[_ post]".
move=> kt t.
case: kt; try by iDestruct "post" as "[_ post]".
iDestruct "post" as "[post _]".
by iApply ("post" $! (SignKey t)) => //;
rewrite [term_of_sign_key]unlock // !minted_TKey.
Qed.

Lemma wp_is_sign_key sk Ψ :
  minted sk -∗
  (∀ sk' : sign_key, ⌜sk = sk'⌝ -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_sign_key sk {{ Ψ }}.
Proof.
by iIntros "H1 H2"; iApply twp_wp;
iApply (twp_is_sign_key with "H1 H2").
Qed.

End Proofs.

Arguments channel {Σ _ _} c.
