(** * Ghost state updates for [public_inv]

The right hand side lemmas are identical, but use primed names and refer to
[term_meta_spec] instead of [term_meta] wherever applicable.

** Section [StatesUpdates]

- [public_states_l_extend] adds [t ↦ Pending t'] in [states_l].  It takes
  [protected_deposit_l t], which keeps [t] hidden.
- [linked_extend] combines [public_states_l_extend] and
  [public_states_r_extend].
- [public_lock_Secret_l] turns [t ↦ Pending t'] into [t ↦ Secret].
- [public_secret_l] directly produces [t ↦ Secret].  It takes
  [protected_deposit_l t], like [public_states_l_extend].
- The [public_lock_PublicLink] family and [public_extend] produce
  [publicly_linked]. They accept various combinations of not being in
  [states_l] already and being marked [Pending] in it. See the comment on
  [public_lock_PublicLink] for more details.  They take
  [public_deposit_l] and [public_deposit_r], and the prots tokens of [t] and
  [t'], which no hidden term may hold back.  A [Pending] term gets its
  [protected_deposit_l] back. *)

From iris.algebra Require Import gmap gset.
From reloc Require Import reloc.
From cryptis Require Import cryptis.
From cryptis.hyper.core.public Require Import state base.
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

Lemma public_states_l_extend E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_deposit_l t -∗
  states_token_l t -∗
  |={E}=> linked_in_l t t' ∗ pending_in_l t t'.
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
iMod (states_meta_l_set with "Htt") as "#Hmeta_states_t".
iModIntro. iSplitR "Hstates_frag_t Hstates_t_frag'"; last by iFrame.
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

Lemma public_states_r_extend E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_deposit_r t' -∗
  states_token_r t' -∗
  |={E}=> linked_in_r t t' ∗ pending_in_r t t'.
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
iMod (states_meta_r_set with "Htts") as "#Hmeta_states_t'".
iModIntro. iSplitR "Hstates_frag_t' Hstates_t'_frag'"; last by iFrame.
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
templates.

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

End PublicUpdates.
