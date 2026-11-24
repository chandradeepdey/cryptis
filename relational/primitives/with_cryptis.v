(** Relational specs of the primitives of [cryptis/primitives/with_cryptis.v]:
    the network channel, creating nonces and keys, and checking the type of a
    key; and the primitives through which a protocol asks the attacker for a
    channel, a thread or its turn, with a lock built on them ([Locks]).

    A protocol should start threads and wait only through these primitives,
    and should not use [Fork] or Iris's nondeterministic choices.  A thread
    started with [Fork], a coin flipped with Iris's primitives, or a thread
    that waits in a loop of its own leaves a choice to the scheduler instead
    of the attacker.  Such a protocol can leak its secret under a real
    scheduler and still satisfy the security theorems: they only say that
    each result of one game is a possible result of the other, so the second
    game may make that choice in whichever way suits it. *)

From reloc Require Import reloc.
From cryptis Require Import lib cryptis.
From cryptis.primitives Require Import simple with_cryptis.
From cryptis.hyper.core Require Import minted_spec term_meta_spec public.
From cryptis.hyper Require Import lib.
From cryptis.hyper.primitives Require Import simple.
From cryptis.hyper.proofmode Require Import classes updates tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition new_channel : val := λ: "sys",
  Fst (Fst "sys") #().

Definition spawn : val := λ: "sys" "f",
  let: "started" := ref #false in
  Snd (Fst "sys")
    (λ: <>, if: CAS "started" #false #true then "f" #() else #()).

Definition yield : val := λ: "sys",
  Snd "sys" #().

Definition newlock : val := λ: <>, ref #false.

Definition acquire : val := rec: "acquire" "sys" "l" :=
  if: CAS "l" #false #true then #()
  else yield "sys";; "acquire" "sys" "l".

Definition release : val := λ: "l", "l" <- #false.

Abbreviation spawnN := (hypercryptisN.@"spawn").
Abbreviation lockN := (hypercryptisN.@"lock").

Section Proofs.

Context `{!relocG Σ, !publicGS Σ}.

Abbreviation nonce := loc.
Implicit Types E : coPset.
Implicit Types a : nonce.
Implicit Types t : term.
Implicit Types v : val.
Implicit Types sk : aenc_key.
Implicit Types φ : val → iProp Σ.
Implicit Types Ψ : val → val → iProp Σ.

Definition lrel_term : lrel Σ := LRel (λ v v',
  ∃ t t' : term, ⌜v = t⌝ ∗ ⌜v' = t'⌝ ∗ PUB⟨t, t'⟩)%I.

Lemma lrel_term_intro t t' : PUB⟨t, t'⟩ -∗ lrel_term t t'.
Proof. iIntros "#H". iExists t, t'. by eauto. Qed.

Definition lrel_channel : lrel Σ := ((lrel_term → ()) * (() → lrel_term))%lrel.

Definition lrel_attacker : lrel Σ :=
  ((() → lrel_channel) * ((() → ()) → ()) * (() → ()))%lrel.

Lemma refines_send c c' t t' :
  lrel_channel c c' -∗
  (▷ PUB⟨t, t'⟩) -∗
  REL send c t << send c' t' : ().
Proof.
iDestruct 1 as (sf sf' rf rf') "(-> & -> & #H & _)".
iIntros "#?"; rewrite /send; rel_pures_l; rel_pures_r.
iApply "H". by iApply lrel_term_intro.
Qed.

Lemma refines_recv c c' Ψ :
  lrel_channel c c' -∗
  (∀ t t', PUB⟨t, t'⟩ -∗ Ψ t t') -∗
  REL recv c << recv c' : Ψ.
Proof.
iDestruct 1 as (sf sf' rf rf') "(-> & -> & _ & #H)".
iIntros "HΨ"; rewrite /recv; rel_pures_l; rel_pures_r.
iApply (refines_wand with "[]"); first by iApply "H".
iIntros "%v %v' (%t & %t' & -> & -> & #Ht) !>". by iApply "HΨ".
Qed.

Lemma refines_new_channel adv adv' :
  lrel_attacker adv adv' -∗ REL new_channel adv << new_channel adv' : lrel_channel.
Proof.
iIntros "#Hadv".
iDestruct "Hadv" as (p p' y y') "(-> & -> & Hp & _)".
iDestruct "Hp" as (nc nc' sp sp') "(-> & -> & #Hnc & _)".
rewrite /new_channel. rel_pures_l. rel_pures_r.
iApply (refines_app _ _ _ _ ()%lrel); by rel_values.
Qed.

Lemma refines_yield adv adv' :
  lrel_attacker adv adv' -∗ REL yield adv << yield adv' : ().
Proof.
iIntros "#Hadv".
iDestruct "Hadv" as (p p' y y') "(-> & -> & _ & #Hy)".
rewrite /yield. rel_pures_l. rel_pures_r.
iApply (refines_app _ _ _ _ ()%lrel); by rel_values.
Qed.

Lemma refines_spawn adv adv' (f f' : val) :
  lrel_attacker adv adv' -∗
  (REL f #() << f' #() : ()) -∗
  REL spawn adv f << spawn adv' f' : ().
Proof.
iIntros "#Hadv Hf".
iDestruct "Hadv" as (p p' y y') "(-> & -> & Hp & _)".
iDestruct "Hp" as (nc nc' sp sp') "(-> & -> & _ & #Hsp)".
rewrite /spawn. rel_pures_l. rel_pures_r.
rel_alloc_l s as "Hs". rel_alloc_r s' as "Hs'".
rel_pures_l. rel_pures_r.
iMod (inv_alloc spawnN _
        ((s ↦ #false ∗ s' ↦ₛ #false ∗ REL f #() << f' #() : ()) ∨
         (s ↦ #true ∗ s' ↦ₛ #true))%I
        with "[Hs Hs' Hf]") as "#Hinv".
{ iNext. iLeft. iFrame. }
iApply (refines_app _ _ _ _ (() → ())%lrel); first by rel_values.
rel_values. iIntros "!> !> %v %v' [-> ->]".
rel_pures_l. rel_pures_r.
rel_cmpxchg_l_atomic.
iInv spawnN as "[(Hs & Hs' & Hf)|(Hs & Hs')]" "Hclose".
- iModIntro. iExists _. iFrame "Hs". iSplit.
  { by iIntros (?). }
  iIntros (_). iNext. iIntros "Hs".
  rel_cmpxchg_suc_r. rel_pures_l. rel_pures_r.
  iMod ("Hclose" with "[Hs Hs']") as "_".
  { iNext. iRight. iFrame. }
  iApply "Hf".
- iModIntro. iExists _. iFrame "Hs". iSplit; last first.
  { by iIntros (?). }
  iIntros (_). iNext. iIntros "Hs".
  rel_cmpxchg_fail_r. rel_pures_l. rel_pures_r.
  iMod ("Hclose" with "[Hs Hs']") as "_".
  { iNext. iRight. iFrame. }
  by rel_values.
Qed.

Lemma refines_mk_nonce_l K e (T': term → gset term) Ψ :
  hypercryptis_ctx -∗
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

Lemma refines_mk_nonce_r K e (T': term → gset term) Ψ :
  hypercryptis_ctx -∗
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

Lemma refines_mk_aenc_key_l K e (T_sk T_pk : term → gset term) Ψ :
  (∀ sk : aenc_key,
     seed_of_aenc_key sk ∉ T_sk sk ∧
     seed_of_aenc_key sk ∉ T_pk (Spec.pkey sk) ∧
     T_sk sk ## T_pk (Spec.pkey sk)) →
  hypercryptis_ctx -∗
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
rel_apply_l (refines_mk_nonce_l _ _
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
rel_pures_l. rel_apply_l refines_derive_aenc_key_l.
iApply ("mint" $! (AEncKey t) with "[//] [] Htt_seed Htt_sk Htt_pk").
by iApply minted_aenc.
Qed.

Lemma refines_mk_aenc_key_r K e (T_sk T_pk : term → gset term) Ψ :
  (∀ sk : aenc_key,
     seed_of_aenc_key sk ∉ T_sk sk ∧
     seed_of_aenc_key sk ∉ T_pk (Spec.pkey sk) ∧
     T_sk sk ## T_pk (Spec.pkey sk)) →
  hypercryptis_ctx -∗
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
rel_apply_r (refines_mk_nonce_r _ _
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
rel_pures_r. rel_apply_r refines_derive_aenc_key_r.
iApply ("mint" $! (AEncKey t) with "[//] [] Htts_seed Htts_sk Htts_pk").
by iApply minted_spec_aenc.
Qed.

Lemma refines_mk_sign_key_l K e (T_sk T_pk : term → gset term) Ψ :
  (∀ sk : sign_key,
     seed_of_sign_key sk ∉ T_sk sk ∧
     seed_of_sign_key sk ∉ T_pk (Spec.pkey sk) ∧
     T_sk sk ## T_pk (Spec.pkey sk)) →
  hypercryptis_ctx -∗
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
rel_apply_l (refines_mk_nonce_l _ _
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
rel_pures_l. rel_apply_l refines_derive_sign_key_l.
iApply ("mint" $! (SignKey t) with "[//] [] Htt_seed Htt_sk Htt_pk").
by iApply minted_sign.
Qed.

Lemma refines_mk_sign_key_r K e (T_sk T_pk : term → gset term) Ψ :
  (∀ sk : sign_key,
     seed_of_sign_key sk ∉ T_sk sk ∧
     seed_of_sign_key sk ∉ T_pk (Spec.pkey sk) ∧
     T_sk sk ## T_pk (Spec.pkey sk)) →
  hypercryptis_ctx -∗
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
rel_apply_r (refines_mk_nonce_r _ _
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
rel_pures_r. rel_apply_r refines_derive_sign_key_r.
iApply ("mint" $! (SignKey t) with "[//] [] Htts_seed Htts_sk Htts_pk").
by iApply minted_spec_sign.
Qed.

Lemma refines_mk_senc_key_l K e (T_k : term → gset term) Ψ :
  (∀ k : senc_key, seed_of_senc_key k ∉ T_k k) →
  hypercryptis_ctx -∗
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
rel_apply_l (refines_mk_nonce_l _ _ (λ t, {[t]} ∪ T_k (SEncKey t)))=> //.
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
rel_pures_l. rel_apply_l refines_derive_senc_key_l.
iApply ("mint" $! (SEncKey t) with "[//] [] Htt_seed Htt_k").
by iApply minted_senc.
Qed.

Lemma refines_mk_senc_key_r K e (T_k : term → gset term) Ψ :
  (∀ k : senc_key, seed_of_senc_key k ∉ T_k k) →
  hypercryptis_ctx -∗
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
rel_apply_r (refines_mk_nonce_r _ _ (λ t, {[t]} ∪ T_k (SEncKey t)))=> //.
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
rel_pures_r. rel_apply_r refines_derive_senc_key_r.
iApply ("mint" $! (SEncKey t) with "[//] [] Htts_seed Htts_k").
by iApply minted_spec_senc.
Qed.

Lemma refines_is_aenc_key_l E K e (pk : term) Ψ :
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

Lemma refines_is_aenc_key_r E K e (pk : term) Ψ :
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

Lemma refines_is_adec_key_l E K e (sk : term) Ψ :
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

Lemma refines_is_adec_key_r E K e (sk : term) Ψ :
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

Lemma refines_is_senc_key_l E K e (k : term) Ψ :
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

Lemma refines_is_senc_key_r E K e (k : term) Ψ :
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

Lemma refines_is_verify_key_l E K e (pk : term) Ψ :
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

Lemma refines_is_verify_key_r E K e (pk : term) Ψ :
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

Lemma refines_is_sign_key_l E K e (sk : term) Ψ :
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

Lemma refines_is_sign_key_r E K e (sk : term) Ψ :
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

Section Locks.

Context `{!relocG Σ, !publicGS Σ}.

Definition lock_inv (l l' : loc) (R : iProp Σ) : iProp Σ :=
  (l ↦ #false ∗ l' ↦ₛ #false ∗ R) ∨ (l ↦ #true ∗ l' ↦ₛ #true).

Definition is_lock (l l' : loc) (R : iProp Σ) : iProp Σ :=
  inv lockN (lock_inv l l' R).

Lemma refines_newlock R Ψ :
  R -∗
  (∀ l l' : loc, is_lock l l' R -∗ Ψ #l #l') -∗
  REL newlock #() << newlock #() : Ψ.
Proof.
iIntros "HR HΨ". rewrite /newlock. rel_pures_l. rel_pures_r.
rel_alloc_l l as "Hl". rel_alloc_r l' as "Hl'".
iMod (inv_alloc lockN _ (lock_inv l l' R) with "[Hl Hl' HR]") as "#Hlock".
{ iNext. iLeft. iFrame. }
rel_values. iModIntro. by iApply "HΨ".
Qed.

Lemma refines_acquire adv adv' (l l' : loc) R Ψ :
  lrel_attacker adv adv' -∗
  is_lock l l' R -∗
  (R -∗ Ψ #() #()) -∗
  REL acquire adv #l << acquire adv' #l' : Ψ.
Proof.
iIntros "#Hadv #Hlock HΨ".
iLöb as "IH".
rel_rec_l. rel_rec_r. rel_pures_l. rel_pures_r.
rel_cmpxchg_l_atomic.
iInv lockN as "[(Hl & Hl' & HR)|(Hl & Hl')]" "Hclose".
- iModIntro. iExists _. iFrame "Hl". iSplit.
  { by iIntros (?). }
  iIntros (_). iNext. iIntros "Hl".
  rel_cmpxchg_suc_r. rel_pures_l. rel_pures_r.
  iMod ("Hclose" with "[Hl Hl']") as "_".
  { iNext. iRight. iFrame. }
  rel_values. iModIntro. by iApply "HΨ".
- iModIntro. iExists _. iFrame "Hl". iSplit; last first.
  { by iIntros (?). }
  iIntros (_). iNext. iIntros "Hl".
  rel_cmpxchg_fail_r. rel_pures_l. rel_pures_r.
  iMod ("Hclose" with "[Hl Hl']") as "_".
  { iNext. iRight. iFrame. }
  rel_bind_l (yield _). rel_bind_r (yield _).
  iApply refines_bind; first by iApply refines_yield.
  iIntros (? ?) "[-> ->] /=". rel_pures_l. rel_pures_r.
  by iApply ("IH" with "HΨ").
Qed.

Lemma refines_release (l l' : loc) R Ψ :
  is_lock l l' R -∗
  R -∗
  Ψ #() #() -∗
  REL release #l << release #l' : Ψ.
Proof.
iIntros "#Hlock HR HΨ". rewrite /release. rel_pures_l. rel_pures_r.
rel_store_l_atomic.
iInv lockN as "[(Hl & Hl' & _)|(Hl & Hl')]" "Hclose";
  iModIntro; iExists _; iFrame "Hl"; iIntros "!> Hl";
  rel_store_r;
  iMod ("Hclose" with "[Hl Hl' HR]") as "_"; try (iNext; iLeft; iFrame);
  by rel_values.
Qed.

End Locks.

Arguments lrel_channel {Σ _ _}.
Arguments refines_mk_aenc_key_l {Σ _ _} K e T_sk T_pk Ψ.
Arguments refines_mk_aenc_key_r {Σ _ _} K e T_sk T_pk Ψ.
Arguments refines_mk_sign_key_l {Σ _ _} K e T_sk T_pk Ψ.
Arguments refines_mk_sign_key_r {Σ _ _} K e T_sk T_pk Ψ.
Arguments refines_mk_senc_key_l {Σ _ _} K e T_k Ψ.
Arguments refines_mk_senc_key_r {Σ _ _} K e T_k Ψ.
