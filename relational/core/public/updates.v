(** * Ghost state updates for [public_inv]

The right hand side lemmas are identical, but use primed names and refer to
[term_meta_spec] instead of [term_meta] wherever applicable.

** Section [StatesUpdates]

- [public_states_l_extend] adds [t ↦ Pending t'] in [states_l].  It takes
  [protected_deposit_l t], which keeps [t] hidden.
- [linked_extend] combines [public_states_l_extend] and
  [public_states_r_extend].  [linked_extend_protected_via] does the same for
  two terms protected by known chains, and gives back their records.
- [public_lock_Secret_l] turns [t ↦ Pending t'] into [t ↦ Secret].
- [public_secret_l] directly produces [t ↦ Secret].  It takes
  [protected_deposit_l t], like [public_states_l_extend].
- The [public_lock_PublicLink] family and [public_extend] produce
  [publicly_linked]. They accept various combinations of not being in
  [states_l] already and being marked [Pending] in it. See the comment on
  [public_lock_PublicLink] for more details.  They take
  [public_deposit_l] and [public_deposit_r], and the prots tokens of [t] and
  [t'], which no hidden term may hold back.  A [Pending] term gets its
  [protected_deposit_l] back.
- [public_lock_PublicLink_protector] makes public a term protected via a
  known chain together with the nonce that protects it at the end of the
  chain, and gives back what the term held on the rest of the chain.

** Section [SealRelease]

- [public_TSeal_release_AEnc_hold_l_fupd] and its symmetric counterparts
  release a public ciphertext's hold on its encryption key once its payload
  is public. *)

From iris.algebra Require Import gmap gset.
From reloc Require Import reloc.
From cryptis Require Import cryptis.
From cryptis.hyper.core Require Import term_meta_spec.
From cryptis.hyper.core.public Require Import state states base.
Import State.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicUpdates.

Context `{!relocG Σ, !publicGS Σ}.

Abbreviation iProp := (iProp Σ).
Abbreviation iPropO := (iPropO Σ).

Implicit Types t : term.
Implicit Types st : state.
Implicit Types states_l states_r : gmap term state.
Implicit Types P : term -> term -> iProp.

Section StatesUpdates.

#[local] Lemma public_states_l_extend_with E t t' (R : iProp) :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  (states_token_l t ==∗ states_meta_l t ∗ protects_deposit_l t ∗ R) -∗
  states_token_l t -∗
  |={E}=> linked_in_l t t' ∗ pending_in_l t t' ∗ R.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hprot Htt".
iInv "Hinv" as ">(%states_l & %states_r &
                  ([Hstates_l Hstates_l_frag] & Hstates_r & #Hmeta_states_l & #Hmeta_states_r) &
                  [Hdeposits_l Hdeposits_r] &
                  [HPublicLink_consistent HPublicLink_consistent_r])".
iPoseProof (public_states_l_fresh states_l t with "Hmeta_states_l Htt") as "%Hfresh".
iMod (own_update with "Hstates_l") as "[Hstates_l Hstates_frag_t]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t (● Some (Pending t') ⋅ ◯ Some (Pending t')));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hstates_frag_t" as "[[Hstates_t_frag Hstates_t_frag'] Hstates_frag_t]".
iMod ("Hprot" with "Htt") as "(#Hmeta_states_t & Hprot & HR)".
iModIntro. iSplitR "Hstates_frag_t Hstates_t_frag' HR"; last by iFrame "∗#".
iAssert (public_states_l_deposits (<[t := Pending t']> states_l))
  with "[Hprot Hdeposits_l]" as "Hdeposits_l".
{ rewrite /public_states_l_deposits big_sepM_insert //. iFrame. }
iModIntro. iExists (<[t := Pending t']> states_l), states_r.
iFrame. iFrame "#".
iSplitL "Hstates_l Hstates_l_frag Hstates_t_frag".
{ iSplitL.
  - rewrite /public_states_l_auth fmap_insert big_sepM_insert //. iFrame.
  - rewrite dom_insert_L big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iIntros (??) "%Hstates".
rewrite lookup_insert in Hstates; case_decide; first naive_solver.
by iApply "HPublicLink_consistent".
Qed.

#[local] Lemma public_states_r_extend_with E t t' (R : iProp) :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  (states_token_r t' ==∗ states_meta_r t' ∗ protects_deposit_r t' ∗ R) -∗
  states_token_r t' -∗
  |={E}=> linked_in_r t t' ∗ pending_in_r t t' ∗ R.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hprot Htts".
iInv "Hinv" as ">(%states_l & %states_r &
                  (Hstates_l & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  [Hdeposits_l Hdeposits_r] &
                  [HPublicLink_consistent HPublicLink_consistent_r])".
iPoseProof (public_states_r_fresh states_r t' with "Hmeta_states_r Htts") as "%Hfresh".
iMod (own_update with "Hstates_r") as "[Hstates_r Hstates_frag_t']".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t' (● Some (Pending t) ⋅ ◯ Some (Pending t)));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hstates_frag_t'" as "[[Hstates_t'_frag Hstates_t'_frag'] Hstates_frag_t']".
iMod ("Hprot" with "Htts") as "(#Hmeta_states_t' & Hprot & HR)".
iModIntro. iSplitR "Hstates_frag_t' Hstates_t'_frag' HR"; last by iFrame "∗#".
iAssert (public_states_r_deposits (<[t' := Pending t]> states_r))
  with "[Hprot Hdeposits_r]" as "Hdeposits_r".
{ rewrite /public_states_r_deposits big_sepM_insert //. iFrame. }
iModIntro. iExists states_l, (<[t' := Pending t]> states_r).
iFrame. iFrame "#".
iSplitL "Hstates_r Hstates_r_frag Hstates_t'_frag".
{ iSplitL.
  - rewrite /public_states_r_auth fmap_insert big_sepM_insert //. iFrame.
  - rewrite dom_insert_L big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iIntros (??) "%Hstates".
rewrite lookup_insert in Hstates; case_decide; first naive_solver.
by iApply "HPublicLink_consistent_r".
Qed.

Lemma public_states_l_extend E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_deposit_l t -∗
  states_token_l t -∗
  |={E}=> linked_in_l t t' ∗ pending_in_l t t'.
Proof.
iIntros (HE) "#Hctx Hprot Htt".
iMod (public_states_l_extend_with t t' True%I HE with "Hctx [Hprot] Htt") as "($ & $ & _)";
  last done.
iIntros "Htt". iDestruct "Hprot" as "[%Hn|(%path & %tprot & Hprot)]".
- iMod (states_meta_l_set with "Htt") as "$". iModIntro. by iSplit; first iLeft.
- iMod (protected_via_l_set _ path tprot with "Htt") as "[$ #via]".
  iModIntro.
  iSplit; last done. iRight. iExists path, tprot. by iFrame.
Qed.

Lemma public_states_r_extend E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_deposit_r t' -∗
  states_token_r t' -∗
  |={E}=> linked_in_r t t' ∗ pending_in_r t t'.
Proof.
iIntros (HE) "#Hctx Hprot Htts".
iMod (public_states_r_extend_with t t' True%I HE with "Hctx [Hprot] Htts") as "($ & $ & _)";
  last done.
iIntros "Htts". iDestruct "Hprot" as "[%Hn|(%path & %t'prot & Hprot)]".
- iMod (states_meta_r_set with "Htts") as "$". iModIntro. by iSplit; first iLeft.
- iMod (protected_via_r_set _ path t'prot with "Htts") as "[$ #via]".
  iModIntro.
  iSplit; last done. iRight. iExists path, t'prot. by iFrame.
Qed.

Lemma linked_extend_protected_via E t t' path tprot path' t'prot :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_by_chain_l t path tprot -∗
  protected_by_chain_r t' path' t'prot -∗
  states_token_l t -∗
  states_token_r t' -∗
  |={E}=> linked t t' ∗ pending_in_l t t' ∗ pending_in_r t t' ∗
          protected_via_l t path tprot ∗ protected_via_r t' path' t'prot.
Proof.
iIntros (HE) "#Hctx Hprot Hprot' Htt Htts".
iMod (public_states_l_extend_with t t' (protected_via_l t path tprot) HE
        with "Hctx [Hprot] Htt") as "(#? & $ & #$)".
{ iIntros "Htt". iMod (protected_via_l_set _ path tprot with "Htt") as "[$ #via]".
  iModIntro.
  iSplitL; last done. iRight. iExists path, tprot. by iFrame. }
iMod (public_states_r_extend_with t t' (protected_via_r t' path' t'prot) HE
        with "Hctx [Hprot'] Htts") as "(#? & $ & #$)".
{ iIntros "Htts". iMod (protected_via_r_set _ path' t'prot with "Htts") as "[$ #via]".
  iModIntro.
  iSplitL; last done. iRight. iExists path', t'prot. by iFrame. }
iModIntro. rewrite /linked. by iFrame "#".
Qed.

Lemma linked_extend E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_deposit_l t -∗
  protected_deposit_r t' -∗
  states_token_l t -∗
  states_token_r t' -∗
  |={E}=> linked t t' ∗ pending_in_l t t' ∗ pending_in_r t t'.
Proof.
iIntros (HE) "#Hctx Hprot Hprot' Htt Htts".
iMod (public_states_l_extend t t' with "Hctx Hprot Htt") as "[#? ?]" => //.
iMod (public_states_r_extend t t' with "Hctx Hprot' Htts") as "[#? ?]" => //.
iModIntro. rewrite /linked. iFrame "#∗".
Qed.

Lemma public_lock_Secret_l E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  pending_in_l t t' -∗
  |={E}=> secret_in_l t.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hl_frac".
iInv "Hinv" as ">(%states_l & %states_r &
                  ([Hstates_l Hstates_l_frag] & Hstates_r & #Hmeta_states_l & #Hmeta_states_r) &
                  [Hdeposits_l Hdeposits_r] &
                  [HPublicLink_consistent HPublicLink_consistent_r])".
iPoseProof (public_states_l_lookup with "Hstates_l Hl_frac") as "%Hpltt'".
iDestruct (big_sepM_delete _ _ t _ Hpltt' with "Hstates_l_frag") as "[Hl_frac2 Hstates_l_frag]".
iDestruct (big_sepM_delete _ _ t _ Hpltt' with "Hdeposits_l") as "[Hdep_t Hdeposits_l]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hstates_l Hl") as "[Hstates_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Some Secret ⋅ ◯ Some Secret)
    (● Some Secret ⋅ ◯ Some Secret)); first by rewrite lookup_fmap Hpltt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock_Secret. }
iDestruct "Hl" as "[_ #Hl]".
iModIntro. iSplitL; last by iFrame "#".
iAssert (public_states_l_deposits (<[t := Secret]> states_l))
  with "[Hdep_t Hdeposits_l]" as "Hdeposits_l".
{ rewrite /public_states_l_deposits big_sepM_insert_delete. iFrame. }
iModIntro. iExists (<[t := Secret]> states_l), states_r.
rewrite /public_inv. iFrame. iFrame "#".
iSplitL "Hstates_l Hstates_l_frag".
{ rewrite /public_states_l_auth fmap_insert big_sepM_insert_delete dom_insert_lookup_L //.
  iFrame. iFrame "#". }
iIntros (??) "%Hstates".
rewrite lookup_insert in Hstates; case_decide; first naive_solver.
by iApply "HPublicLink_consistent".
Qed.

Lemma public_lock_Secret_r E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  pending_in_r t t' -∗
  |={E}=> secret_in_r t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hr_frac".
iInv "Hinv" as ">(%states_l & %states_r &
                  (Hstates_l & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  [Hdeposits_l Hdeposits_r] &
                  [HPublicLink_consistent HPublicLink_consistent_r])".
iPoseProof (public_states_r_lookup with "Hstates_r Hr_frac") as "%Hprtt'".
iDestruct (big_sepM_delete _ _ t' _ Hprtt' with "Hstates_r_frag") as "[Hr_frac2 Hstates_r_frag]".
iDestruct (big_sepM_delete _ _ t' _ Hprtt' with "Hdeposits_r") as "[Hdep_t' Hdeposits_r]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hstates_r Hr") as "[Hstates_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Some Secret ⋅ ◯ Some Secret)
    (● Some Secret ⋅ ◯ Some Secret)); first by rewrite lookup_fmap Hprtt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock_Secret. }
iDestruct "Hr" as "[_ #Hr]".
iModIntro. iSplitL; last by iFrame "#".
iAssert (public_states_r_deposits (<[t' := Secret]> states_r))
  with "[Hdep_t' Hdeposits_r]" as "Hdeposits_r".
{ rewrite /public_states_r_deposits big_sepM_insert_delete. iFrame. }
iModIntro. iExists states_l, (<[t' := Secret]> states_r).
rewrite /public_inv. iFrame. iFrame "#".
iSplitL "Hstates_r Hstates_r_frag".
{ rewrite /public_states_r_auth fmap_insert big_sepM_insert_delete dom_insert_lookup_L //.
  iFrame. iFrame "#". }
iIntros (??) "%Hstates".
rewrite lookup_insert in Hstates; case_decide; first naive_solver.
by iApply "HPublicLink_consistent_r".
Qed.

Lemma public_secret_l E t :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_deposit_l t -∗
  states_token_l t -∗
  |={E}=> secret_in_l t.
Proof.
iIntros (HE) "#Hctx Hprot Htt".
iMod (public_states_l_extend t t with "Hctx Hprot Htt") as "[_ Hpend]" => //.
by iMod (public_lock_Secret_l with "Hctx Hpend") as "#?".
Qed.

Lemma public_secret_r E t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_deposit_r t' -∗
  states_token_r t' -∗
  |={E}=> secret_in_r t'.
Proof.
iIntros (HE) "#Hctx Hprot Htts".
iMod (public_states_r_extend t' t' with "Hctx Hprot Htts") as "[_ Hpend]" => //.
by iMod (public_lock_Secret_r with "Hctx Hpend") as "#?".
Qed.

(** You will probably need a custom version of this lemma tailored to the
declassification you want to attempt.

For example, say you have [(nonce, msg) ↦ Pending (nonce', msg')], where
[PUB⟨msg, msg'⟩], and the deposit of [(nonce, msg)] keeps
[holds_subterm_l (nonce, msg) nonce] and that of [(nonce', msg')] keeps
[holds_subterm_r (nonce', msg') nonce'].

When trying to change it to [(nonce, msg) ↦ PublicLink (nonce', msg')], proving
the precondition
[[
publicly_linked (nonce, msg) (nonce', msg') -∗ PUB⟨(nonce, msg), (nonce', msg')⟩
]]
will require that you have [publicly_linked nonce nonce'] in the recursive
case.

But to get that, you will need the whole [prots_token_l nonce] and
[prots_token_r nonce'], including the holds of [(nonce, msg)] and
[(nonce', msg')]. Those come back only when [(nonce, msg)] and
[(nonce', msg')] transition to [PublicLink], which will require you to prove
[PUB⟨(nonce, msg), (nonce', msg')⟩]. This is circular.

To get around this, you should open the invariant and do all of the
transitions at once. This depends on the structure of the terms you are trying
to declassify and the chains of parts that keep them hidden, so you need to
come up with your own custom lemma. Feel free to use these lemmas as
templates; [public_lock_PublicLink_protector] is one for the case above.

If the declassification is deterministic, you can directly construct
[t ↦ PublicLink t'] from the tokens instead of going through [t ↦ Pending t']
first ([public_extend]).

Since [publicly_linked t t' → linked t t'], you can use it to prove [PUB]. *)
Lemma public_lock_PublicLink E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  (publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  public_deposit_l t t' -∗
  public_deposit_r t t' -∗
  prots_token_l t -∗
  prots_token_r t' -∗
  pending_in_l t t' -∗
  pending_in_r t t' -∗
  |={E}=> publicly_linked t t' ∗ protected_deposit_l t ∗ protected_deposit_r t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hlink_pub Hsl Hsr Hprots_l Hprots_r Hl_frac Hr_frac".
iInv "Hinv" as ">(%states_l & %states_r &
                  ([Hstates_l Hstates_l_frag] & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  [Hdeposits_l Hdeposits_r] &
                  [HPublicLink_consistent HPublicLink_consistent_r])".
iPoseProof (public_states_l_lookup with "Hstates_l Hl_frac") as "%Hpltt'".
iPoseProof (public_states_r_lookup with "Hstates_r Hr_frac") as "%Hprtt'".
iDestruct (big_sepM_delete _ _ t _ Hpltt' with "Hstates_l_frag") as "[Hl_frac2 Hstates_l_frag]".
iDestruct (big_sepM_delete _ _ t' _ Hprtt' with "Hstates_r_frag") as "[Hr_frac2 Hstates_r_frag]".
iDestruct (big_sepM_delete _ _ t _ Hpltt' with "Hdeposits_l") as "[Hdep_t Hdeposits_l]".
iDestruct (big_sepM_delete _ _ t' _ Hprtt' with "Hdeposits_r") as "[Hdep_t' Hdeposits_r]".
iCombine "Hl_frac Hl_frac2" as "Hl". iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hstates_l Hl") as "[Hstates_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Some (PublicLink t') ⋅ ◯ Some (PublicLink t'))
    (● Some (PublicLink t') ⋅ ◯ Some (PublicLink t'))); first by rewrite lookup_fmap Hpltt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock_PublicLink. }
iMod (own_update_2 with "Hstates_r Hr") as "[Hstates_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Some (PublicLink t) ⋅ ◯ Some (PublicLink t))
    (● Some (PublicLink t) ⋅ ◯ Some (PublicLink t))); first by rewrite lookup_fmap Hprtt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock_PublicLink. }
iDestruct "Hl" as "[_ #Hl]". iDestruct "Hr" as "[_ #Hr]".
iAssert (public_states_l_deposits (<[t := PublicLink t']> states_l))
  with "[Hsl Hprots_l Hdeposits_l]" as "Hdeposits_l".
{ rewrite /public_states_l_deposits big_sepM_insert_delete. iFrame. }
iAssert (public_states_r_deposits (<[t' := PublicLink t]> states_r))
  with "[Hsr Hprots_r Hdeposits_r]" as "Hdeposits_r".
{ rewrite /public_states_r_deposits big_sepM_insert_delete. iFrame. }
iDestruct (protects_deposit_protected_l with "Hdep_t") as "Hdep_t".
iDestruct (protects_deposit_protected_r with "Hdep_t'") as "Hdep_t'".
iModIntro. iSplitR "Hdep_t Hdep_t'"; last by iFrame "#∗".
iModIntro. iExists (<[t := PublicLink t']> states_l), (<[t' := PublicLink t]> states_r).
rewrite /public_inv /public_states_l_auth /public_states_r_auth.
iFrame. iFrame "#".
iSplitL "Hstates_l Hstates_l_frag Hstates_r Hstates_r_frag".
{ iSplitL "Hstates_l Hstates_l_frag"; last iSplitL "Hstates_r Hstates_r_frag".
  - rewrite /public_states_l_auth fmap_insert big_sepM_insert_delete. iFrame.
  - rewrite /public_states_r_auth fmap_insert big_sepM_insert_delete. iFrame.
  - rewrite !dom_insert_lookup_L //. iFrame "#". }
iDestruct ("Hlink_pub" with "[]") as "#Hpub_tt'"; first by iFrame "#".
iSplitL "HPublicLink_consistent".
- iIntros (??) "%Hstates".
  rewrite lookup_insert in Hstates; case_decide; subst.
  + by injection Hstates as <-.
  + by iApply "HPublicLink_consistent".
- iIntros (??) "%Hstates".
  rewrite lookup_insert in Hstates; case_decide; subst.
  + by injection Hstates as <-.
  + by iApply "HPublicLink_consistent_r".
Qed.

Lemma public_lock_PublicLink_protector E t t' path tprot path' t'prot :
  ↑cryptisN ⊆ E →
  ¬ is_nonce t → ¬ is_nonce t' →
  hypercryptis_ctx -∗
  protected_via_l t path tprot -∗
  protected_via_r t' path' t'prot -∗
  (publicly_linked tprot t'prot -∗ publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  (publicly_linked tprot t'prot -∗ PUB⟨tprot, t'prot⟩) -∗
  public_deposit_l t t' -∗
  public_deposit_r t t' -∗
  prots_token_l t -∗
  prots_token_r t' -∗
  pending_in_l t t' -∗
  pending_in_r t t' -∗
  public_deposit_l tprot t'prot -∗
  public_deposit_r tprot t'prot -∗
  (holds_subterm_l t tprot -∗ prots_token_l tprot) -∗
  (holds_subterm_r t' t'prot -∗ prots_token_r t'prot) -∗
  states_token_l tprot -∗
  states_token_r t'prot -∗
  |={E}=> publicly_linked t t' ∗ publicly_linked tprot t'prot ∗
          ([∗ list] t1 ∈ path, holds_subterm_l t t1) ∗
          ([∗ list] t1' ∈ path', holds_subterm_r t' t1').
Proof.
iIntros (HE Ht Ht') "#(_ & _ & Hinv) #Hvia #Hvia' Hpub_t Hpub_prot Hsl Hsr Hprots_l Hprots_r
  Hl_frac Hr_frac Hsl_prot Hsr_prot Hprots_prot Hprots_prot' Htt Htts".
iInv "Hinv" as ">(%states_l & %states_r &
                  ([Hstates_l Hstates_l_frag] & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  [Hdeposits_l Hdeposits_r] &
                  [HPublicLink_consistent HPublicLink_consistent_r])".
iPoseProof (public_states_l_lookup with "Hstates_l Hl_frac") as "%Hpltt'".
iPoseProof (public_states_r_lookup with "Hstates_r Hr_frac") as "%Hprtt'".
iPoseProof (public_states_l_fresh states_l tprot with "Hmeta_states_l Htt") as "%Hfresh_l".
iPoseProof (public_states_r_fresh states_r t'prot with "Hmeta_states_r Htts") as "%Hfresh_r".
have Hne_l : t ≠ tprot by move=> e; rewrite -e Hpltt' in Hfresh_l.
have Hne_r : t' ≠ t'prot by move=> e; rewrite -e Hprtt' in Hfresh_r.
iDestruct (big_sepM_delete _ _ t _ Hpltt' with "Hstates_l_frag") as "[Hl_frac2 Hstates_l_frag]".
iDestruct (big_sepM_delete _ _ t' _ Hprtt' with "Hstates_r_frag") as "[Hr_frac2 Hstates_r_frag]".
iDestruct (big_sepM_delete _ _ t _ Hpltt' with "Hdeposits_l") as "[Hdep_t Hdeposits_l]".
iDestruct (big_sepM_delete _ _ t' _ Hprtt' with "Hdeposits_r") as "[Hdep_t' Hdeposits_r]".
iDestruct (protects_deposit_chain_l path tprot Ht with "Hvia Hdep_t") as "(_ & Hpath & Hprot)".
iDestruct (protects_deposit_chain_r path' t'prot Ht' with "Hvia' Hdep_t'") as "(_ & Hpath' & Hprot')".
iDestruct "Hprot" as "[#Hsec|[_ Hhold]]".
{ iDestruct (secret_in_l_lookup with "Hstates_l Hsec") as %Hsec.
  by rewrite Hfresh_l in Hsec. }
iDestruct "Hprot'" as "[#Hsec|[_ Hhold']]".
{ iDestruct (secret_in_r_lookup with "Hstates_r Hsec") as %Hsec.
  by rewrite Hfresh_r in Hsec. }
iDestruct ("Hprots_prot" with "Hhold") as "Hprots_prot".
iDestruct ("Hprots_prot'" with "Hhold'") as "Hprots_prot'".
iMod (states_meta_l_set with "Htt") as "#Hmeta_prot".
iMod (states_meta_r_set with "Htts") as "#Hmeta_prot'".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hstates_l Hl") as "[Hstates_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Some (PublicLink t') ⋅ ◯ Some (PublicLink t'))
    (● Some (PublicLink t') ⋅ ◯ Some (PublicLink t'))); first by rewrite lookup_fmap Hpltt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock_PublicLink. }
iMod (own_update with "Hstates_l") as "[Hstates_l Hl_prot]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ tprot
           (● Some (PublicLink t'prot) ⋅ ◯ Some (PublicLink t'prot)));
    last by apply auth_both_valid.
  by rewrite lookup_insert_ne // lookup_fmap Hfresh_l. }
iMod (own_update_2 with "Hstates_r Hr") as "[Hstates_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Some (PublicLink t) ⋅ ◯ Some (PublicLink t))
    (● Some (PublicLink t) ⋅ ◯ Some (PublicLink t))); first by rewrite lookup_fmap Hprtt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock_PublicLink. }
iMod (own_update with "Hstates_r") as "[Hstates_r Hr_prot]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t'prot
           (● Some (PublicLink tprot) ⋅ ◯ Some (PublicLink tprot)));
    last by apply auth_both_valid.
  by rewrite lookup_insert_ne // lookup_fmap Hfresh_r. }
iDestruct "Hl" as "[_ #Hl]". iDestruct "Hr" as "[_ #Hr]".
iDestruct "Hl_prot" as "[_ #Hl_prot]". iDestruct "Hr_prot" as "[_ #Hr_prot]".
iAssert (publicly_linked t t') as "#Hlink"; first by iSplit.
iAssert (publicly_linked tprot t'prot) as "#Hlink_prot"; first by iSplit.
iDestruct ("Hpub_prot" with "Hlink_prot") as "#Hpub_prot".
iDestruct ("Hpub_t" with "Hlink_prot Hlink") as "#Hpub_t".
have Hfresh_l' : <[t := PublicLink t']> states_l !! tprot = None
  by rewrite lookup_insert_ne.
have Hfresh_r' : <[t' := PublicLink t]> states_r !! t'prot = None
  by rewrite lookup_insert_ne.
iAssert (public_states_l_deposits
           (<[tprot := PublicLink t'prot]> (<[t := PublicLink t']> states_l)))
  with "[Hsl Hprots_l Hdeposits_l Hsl_prot Hprots_prot]" as "Hdeposits_l".
{ rewrite /public_states_l_deposits big_sepM_insert // big_sepM_insert_delete. iFrame. }
iAssert (public_states_r_deposits
           (<[t'prot := PublicLink tprot]> (<[t' := PublicLink t]> states_r)))
  with "[Hsr Hprots_r Hdeposits_r Hsr_prot Hprots_prot']" as "Hdeposits_r".
{ rewrite /public_states_r_deposits big_sepM_insert // big_sepM_insert_delete. iFrame. }
iModIntro. iSplitR "Hpath Hpath'"; last by iFrame "#∗".
iModIntro.
iExists (<[tprot := PublicLink t'prot]> (<[t := PublicLink t']> states_l)),
        (<[t'prot := PublicLink tprot]> (<[t' := PublicLink t]> states_r)).
rewrite /public_inv /public_states_l_auth /public_states_r_auth.
iFrame. iFrame "#".
iSplitL "Hstates_l Hstates_l_frag Hstates_r Hstates_r_frag".
{ iSplitL "Hstates_l Hstates_l_frag"; last iSplitL "Hstates_r Hstates_r_frag".
  - rewrite /public_states_l_auth !fmap_insert big_sepM_insert // big_sepM_insert_delete /=. iFrame.
  - rewrite /public_states_r_auth !fmap_insert big_sepM_insert // big_sepM_insert_delete /=. iFrame.
  - iSplit.
    + rewrite dom_insert_L dom_insert_lookup_L; last by eexists.
      rewrite big_sepS_insert; last by apply not_elem_of_dom. by iFrame "#".
    + rewrite dom_insert_L dom_insert_lookup_L; last by eexists.
      rewrite big_sepS_insert; last by apply not_elem_of_dom. by iFrame "#". }
iSplitL "HPublicLink_consistent".
- iIntros (??) "%Hstates".
  rewrite !lookup_insert in Hstates; repeat case_decide; subst.
  + by injection Hstates as <-.
  + by injection Hstates as <-.
  + by iApply "HPublicLink_consistent".
- iIntros (??) "%Hstates".
  rewrite !lookup_insert in Hstates; repeat case_decide; subst.
  + by injection Hstates as <-.
  + by injection Hstates as <-.
  + by iApply "HPublicLink_consistent_r".
Qed.

Lemma public_lock_PublicLink_l E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  (publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  public_deposit_l t t' -∗
  public_deposit_r t t' -∗
  prots_token_l t -∗
  prots_token_r t' -∗
  pending_in_l t t' -∗
  states_token_r t' -∗
  |={E}=> publicly_linked t t' ∗ protected_deposit_l t.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hlink_pub Hsl Hsr Hprots_l Hprots_r Hl_frac Htts".
iInv "Hinv" as ">(%states_l & %states_r &
                  ([Hstates_l Hstates_l_frag] & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  [Hdeposits_l Hdeposits_r] &
                  [HPublicLink_consistent HPublicLink_consistent_r])".
iPoseProof (public_states_l_lookup with "Hstates_l Hl_frac") as "%Hpltt'".
iPoseProof (public_states_r_fresh states_r t' with "Hmeta_states_r Htts") as "%Hfresh".
iDestruct (big_sepM_delete _ _ t _ Hpltt' with "Hstates_l_frag") as "[Hl_frac2 Hstates_l_frag]".
iDestruct (big_sepM_delete _ _ t _ Hpltt' with "Hdeposits_l") as "[Hdep_t Hdeposits_l]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (states_meta_r_set with "Htts") as "#Hmeta_states_t'".
iMod (own_update_2 with "Hstates_l Hl") as "[Hstates_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Some (PublicLink t') ⋅ ◯ Some (PublicLink t'))
    (● Some (PublicLink t') ⋅ ◯ Some (PublicLink t'))); first by rewrite lookup_fmap Hpltt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock_PublicLink. }
iMod (own_update with "Hstates_r") as "[Hstates_r Hr]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t' (● Some (PublicLink t) ⋅ ◯ Some (PublicLink t)));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hl" as "[_ #Hl]". iDestruct "Hr" as "[_ #Hr]".
iAssert (public_states_l_deposits (<[t := PublicLink t']> states_l))
  with "[Hsl Hprots_l Hdeposits_l]" as "Hdeposits_l".
{ rewrite /public_states_l_deposits big_sepM_insert_delete. iFrame. }
iAssert (public_states_r_deposits (<[t' := PublicLink t]> states_r))
  with "[Hsr Hprots_r Hdeposits_r]" as "Hdeposits_r".
{ rewrite /public_states_r_deposits big_sepM_insert //. iFrame. }
iDestruct (protects_deposit_protected_l with "Hdep_t") as "Hdep_t".
iModIntro. iSplitR "Hdep_t"; last by iFrame "#∗".
iModIntro. iExists (<[t := PublicLink t']> states_l), (<[t' := PublicLink t]> states_r).
rewrite /public_inv /public_states_l_auth /public_states_r_auth.
iFrame. iFrame "#".
iSplitL "Hstates_l Hstates_l_frag Hstates_r Hstates_r_frag".
{ iSplitL "Hstates_l Hstates_l_frag"; last iSplitL "Hstates_r Hstates_r_frag".
  - rewrite /public_states_l_auth fmap_insert big_sepM_insert_delete /=. iFrame.
  - rewrite /public_states_r_auth fmap_insert big_sepM_insert //. iFrame.
  - rewrite (dom_insert_lookup_L states_l) // dom_insert_L big_sepS_insert;
      last by apply not_elem_of_dom.
    iFrame "#". }
iDestruct ("Hlink_pub" with "[]") as "#Hpub_tt'"; first by iFrame "#".
iSplitL "HPublicLink_consistent".
- iIntros (??) "%Hstates".
  rewrite lookup_insert in Hstates; case_decide; subst.
  + by injection Hstates as <-.
  + by iApply "HPublicLink_consistent".
- iIntros (??) "%Hstates".
  rewrite lookup_insert in Hstates; case_decide; subst.
  + by injection Hstates as <-.
  + by iApply "HPublicLink_consistent_r".
Qed.

Lemma public_lock_PublicLink_r E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  (publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  public_deposit_l t t' -∗
  public_deposit_r t t' -∗
  prots_token_l t -∗
  prots_token_r t' -∗
  states_token_l t -∗
  pending_in_r t t' -∗
  |={E}=> publicly_linked t t' ∗ protected_deposit_r t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hlink_pub Hsl Hsr Hprots_l Hprots_r Htt Hr_frac".
iInv "Hinv" as ">(%states_l & %states_r &
                  ([Hstates_l Hstates_l_frag] & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  [Hdeposits_l Hdeposits_r] &
                  [HPublicLink_consistent HPublicLink_consistent_r])".
iPoseProof (public_states_l_fresh states_l t with "Hmeta_states_l Htt") as "%Hfresh".
iPoseProof (public_states_r_lookup with "Hstates_r Hr_frac") as "%Hprtt'".
iDestruct (big_sepM_delete _ _ t' _ Hprtt' with "Hstates_r_frag") as "[Hr_frac2 Hstates_r_frag]".
iDestruct (big_sepM_delete _ _ t' _ Hprtt' with "Hdeposits_r") as "[Hdep_t' Hdeposits_r]".
iMod (states_meta_l_set with "Htt") as "#Hmeta_states_t".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update with "Hstates_l") as "[Hstates_l Hl]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t (● Some (PublicLink t') ⋅ ◯ Some (PublicLink t')));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iMod (own_update_2 with "Hstates_r Hr") as "[Hstates_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Some (PublicLink t) ⋅ ◯ Some (PublicLink t))
    (● Some (PublicLink t) ⋅ ◯ Some (PublicLink t))); first by rewrite lookup_fmap Hprtt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock_PublicLink. }
iDestruct "Hr" as "[_ #Hr]". iDestruct "Hl" as "[_ #Hl]".
iAssert (public_states_l_deposits (<[t := PublicLink t']> states_l))
  with "[Hsl Hprots_l Hdeposits_l]" as "Hdeposits_l".
{ rewrite /public_states_l_deposits big_sepM_insert //. iFrame. }
iAssert (public_states_r_deposits (<[t' := PublicLink t]> states_r))
  with "[Hsr Hprots_r Hdeposits_r]" as "Hdeposits_r".
{ rewrite /public_states_r_deposits big_sepM_insert_delete. iFrame. }
iDestruct (protects_deposit_protected_r with "Hdep_t'") as "Hdep_t'".
iModIntro. iSplitR "Hdep_t'"; last by iFrame "#∗".
iModIntro. iExists (<[t := PublicLink t']> states_l), (<[t' := PublicLink t]> states_r).
rewrite /public_inv /public_states_l_auth /public_states_r_auth.
iFrame. iFrame "#".
iSplitL "Hstates_l Hstates_l_frag Hstates_r Hstates_r_frag".
{ iSplitL "Hstates_l Hstates_l_frag"; last iSplitL "Hstates_r Hstates_r_frag".
  - rewrite /public_states_l_auth fmap_insert big_sepM_insert //. iFrame.
  - rewrite /public_states_r_auth fmap_insert big_sepM_insert_delete /=. iFrame.
  - rewrite dom_insert_L big_sepS_insert; last by apply not_elem_of_dom.
    rewrite dom_insert_lookup_L //. iFrame "#". }
iDestruct ("Hlink_pub" with "[]") as "#Hpub_tt'"; first by iFrame "#".
iSplitL "HPublicLink_consistent".
- iIntros (??) "%Hstates".
  rewrite lookup_insert in Hstates; case_decide; subst.
  + by injection Hstates as <-.
  + by iApply "HPublicLink_consistent".
- iIntros (??) "%Hstates".
  rewrite lookup_insert in Hstates; case_decide; subst.
  + by injection Hstates as <-.
  + by iApply "HPublicLink_consistent_r".
Qed.

Lemma public_extend E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  (publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  public_deposit_l t t' -∗
  public_deposit_r t t' -∗
  prots_token_l t -∗
  prots_token_r t' -∗
  states_token_l t -∗
  states_token_r t' -∗
  |={E}=> publicly_linked t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hlink_pub Hsl Hsr Hprots_l Hprots_r Htt Htts".
iInv "Hinv" as ">(%states_l & %states_r &
                  ([Hstates_l Hstates_l_frag] & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  [Hdeposits_l Hdeposits_r] &
                  [HPublicLink_consistent HPublicLink_consistent_r])".
iPoseProof (public_states_l_fresh states_l t with "Hmeta_states_l Htt") as "%Hfresh_l".
iPoseProof (public_states_r_fresh states_r t' with "Hmeta_states_r Htts") as "%Hfresh_r".
iMod (states_meta_l_set with "Htt") as "#Hmeta_states_t".
iMod (states_meta_r_set with "Htts") as "#Hmeta_states_t'".
iMod (own_update with "Hstates_l") as "[Hstates_l Hl]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t (● Some (PublicLink t') ⋅ ◯ Some (PublicLink t')));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh_l //. }
iMod (own_update with "Hstates_r") as "[Hstates_r Hr]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t' (● Some (PublicLink t) ⋅ ◯ Some (PublicLink t)));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh_r //. }
iDestruct "Hl" as "[_ #Hl]". iDestruct "Hr" as "[_ #Hr]".
iAssert (public_states_l_deposits (<[t := PublicLink t']> states_l))
  with "[Hsl Hprots_l Hdeposits_l]" as "Hdeposits_l".
{ rewrite /public_states_l_deposits big_sepM_insert //. iFrame. }
iAssert (public_states_r_deposits (<[t' := PublicLink t]> states_r))
  with "[Hsr Hprots_r Hdeposits_r]" as "Hdeposits_r".
{ rewrite /public_states_r_deposits big_sepM_insert //. iFrame. }
iModIntro. iSplitL; last by iFrame "#".
iModIntro. iExists (<[t := PublicLink t']> states_l), (<[t' := PublicLink t]> states_r).
rewrite /public_inv /public_states_l_auth /public_states_r_auth.
iFrame. iFrame "#".
iSplitL "Hstates_l Hstates_l_frag Hstates_r Hstates_r_frag".
{ iSplitL "Hstates_l Hstates_l_frag"; last iSplitL "Hstates_r Hstates_r_frag".
  - rewrite /public_states_l_auth fmap_insert big_sepM_insert //. iFrame.
  - rewrite /public_states_r_auth fmap_insert big_sepM_insert //. iFrame.
  - rewrite !dom_insert_L !big_sepS_insert; try by apply not_elem_of_dom.
    iFrame "#". }
iDestruct ("Hlink_pub" with "[]") as "#Hpub_tt'"; first by iFrame "#".
iSplitL "HPublicLink_consistent".
- iIntros (??) "%Hstates".
  rewrite lookup_insert in Hstates; case_decide; subst.
  + by injection Hstates as <-.
  + by iApply "HPublicLink_consistent".
- iIntros (??) "%Hstates".
  rewrite lookup_insert in Hstates; case_decide; subst.
  + by injection Hstates as <-.
  + by iApply "HPublicLink_consistent_r".
Qed.

End StatesUpdates.

Section SealRelease.

Lemma public_TSeal_release_AEnc_hold_l_fupd E s t k' t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  PUB⟨t, t'⟩ -∗
  seal_release_l (TSeal (TKey AEnc s) t) -∗
  publicly_linked_in_l (TSeal (TKey AEnc s) t) (TSeal k' t') ={E}=∗
  holds_key_l t (TKey AEnc s).
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Ht Hseal #Hl".
iInv "Hinv" as ">(%states_l & %states_r &
                  ([Hstates_l Hstates_l_frag] & Hstates_rest) &
                  [Hpublic_deposit_l Hpublic_deposit_r] & Hrest)".
iDestruct (publicly_linked_in_l_lookup with "Hstates_l Hl") as %Hc.
iDestruct (big_sepM_delete _ _ _ _ Hc with "Hpublic_deposit_l") as "[[He Hprots] Hothers]".
iAssert (holds_key_l t (TKey AEnc s) ∗ public_states_l_deposits states_l)%I
  with "[He Hprots Hothers Hseal]" as "[Hkey Hpublic_deposit_l]".
{ rewrite /public_states_l_deposits (big_sepM_delete _ states_l _ _ Hc).
  iFrame "Hothers Hprots".
  iSimpl in "He"; iSimpl; iDestruct "He" as "[[_ Hseal']|[_ Hkey]]".
  - iDestruct (term_token_disj with "Hseal Hseal'") as %Hdisj; exfalso;
      pose proof (nclose_non_empty (seal_namespace t.@"release")); set_solver.
  - iFrame "Hkey"; iLeft; iFrame "Hseal"; by iLeft. }
iModIntro. iSplitR "Hkey"; last done.
iModIntro. iExists states_l, states_r. iFrame.
Qed.

Lemma public_TSeal_release_AEnc_hold_r_fupd E s' t' k t :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  PUB⟨t, t'⟩ -∗
  seal_release_r (TSeal (TKey AEnc s') t') -∗
  publicly_linked_in_r (TSeal k t) (TSeal (TKey AEnc s') t') ={E}=∗
  holds_key_r t' (TKey AEnc s').
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Ht Hseal #Hl".
iInv "Hinv" as ">(%states_l & %states_r &
                  (Hstates_l & [Hstates_r Hstates_r_frag] & Hstates_rest) &
                  [Hpublic_deposit_l Hpublic_deposit_r] & Hrest)".
iDestruct (publicly_linked_in_r_lookup with "Hstates_r Hl") as %Hc.
iDestruct (big_sepM_delete _ _ _ _ Hc with "Hpublic_deposit_r") as "[[He Hprots] Hothers]".
iAssert (holds_key_r t' (TKey AEnc s') ∗ public_states_r_deposits states_r)%I
  with "[He Hprots Hothers Hseal]" as "[Hkey Hpublic_deposit_r]".
{ rewrite /public_states_r_deposits (big_sepM_delete _ states_r _ _ Hc).
  iFrame "Hothers Hprots".
  iSimpl in "He"; iSimpl; iDestruct "He" as "[[_ Hseal']|[_ Hkey]]".
  - iDestruct (term_token_spec_disj with "Hseal Hseal'") as %Hdisj; exfalso;
      pose proof (nclose_non_empty (seal_namespace t'.@"release")); set_solver.
  - iFrame "Hkey"; iLeft; iFrame "Hseal"; by iLeft. }
iModIntro. iSplitR "Hkey"; last done.
iModIntro. iExists states_l, states_r. iFrame.
Qed.

Lemma public_TSeal_release_SEnc_hold_l_fupd E s t k' t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  PUB⟨t, t'⟩ -∗
  seal_release_l (TSeal (TKey SEnc s) t) -∗
  publicly_linked_in_l (TSeal (TKey SEnc s) t) (TSeal k' t') ={E}=∗
  holds_key_l t (TKey SEnc s).
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Ht Hseal #Hl".
iInv "Hinv" as ">(%states_l & %states_r &
                  ([Hstates_l Hstates_l_frag] & Hstates_rest) &
                  [Hpublic_deposit_l Hpublic_deposit_r] & Hrest)".
iDestruct (publicly_linked_in_l_lookup with "Hstates_l Hl") as %Hc.
iDestruct (big_sepM_delete _ _ _ _ Hc with "Hpublic_deposit_l") as "[[He Hprots] Hothers]".
iAssert (holds_key_l t (TKey SEnc s) ∗ public_states_l_deposits states_l)%I
  with "[He Hprots Hothers Hseal]" as "[Hkey Hpublic_deposit_l]".
{ rewrite /public_states_l_deposits (big_sepM_delete _ states_l _ _ Hc).
  iFrame "Hothers Hprots".
  iSimpl in "He"; iSimpl; iDestruct "He" as "[[_ Hseal']|[_ Hkey]]".
  - iDestruct (term_token_disj with "Hseal Hseal'") as %Hdisj; exfalso;
      pose proof (nclose_non_empty (seal_namespace t.@"release")); set_solver.
  - iFrame "Hkey"; iLeft; iFrame "Hseal"; by iLeft. }
iModIntro. iSplitR "Hkey"; last done.
iModIntro. iExists states_l, states_r. iFrame.
Qed.

Lemma public_TSeal_release_SEnc_hold_r_fupd E s' t' k t :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  PUB⟨t, t'⟩ -∗
  seal_release_r (TSeal (TKey SEnc s') t') -∗
  publicly_linked_in_r (TSeal k t) (TSeal (TKey SEnc s') t') ={E}=∗
  holds_key_r t' (TKey SEnc s').
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Ht Hseal #Hl".
iInv "Hinv" as ">(%states_l & %states_r &
                  (Hstates_l & [Hstates_r Hstates_r_frag] & Hstates_rest) &
                  [Hpublic_deposit_l Hpublic_deposit_r] & Hrest)".
iDestruct (publicly_linked_in_r_lookup with "Hstates_r Hl") as %Hc.
iDestruct (big_sepM_delete _ _ _ _ Hc with "Hpublic_deposit_r") as "[[He Hprots] Hothers]".
iAssert (holds_key_r t' (TKey SEnc s') ∗ public_states_r_deposits states_r)%I
  with "[He Hprots Hothers Hseal]" as "[Hkey Hpublic_deposit_r]".
{ rewrite /public_states_r_deposits (big_sepM_delete _ states_r _ _ Hc).
  iFrame "Hothers Hprots".
  iSimpl in "He"; iSimpl; iDestruct "He" as "[[_ Hseal']|[_ Hkey]]".
  - iDestruct (term_token_spec_disj with "Hseal Hseal'") as %Hdisj; exfalso;
      pose proof (nclose_non_empty (seal_namespace t'.@"release")); set_solver.
  - iFrame "Hkey"; iLeft; iFrame "Hseal"; by iLeft. }
iModIntro. iSplitR "Hkey"; last done.
iModIntro. iExists states_l, states_r. iFrame.
Qed.

End SealRelease.

End PublicUpdates.
