(** * Ghost state updates for [public_inv]

The right hand side lemmas are identical, but use primed names and refer to
[term_meta_spec] instead of [term_meta] wherever applicable.

** Section [ProtsUpdates]

- [public_prots_l_extend] consumes the prots token for [t] and adds it to
  [prots_l].
- The [public_prots_l_grow] family marks [tsup] as protected by [t].
  - [public_prots_l_grow] is allowed when [t] already protects another
    term, thus already satisfying the conditions of the invariant.
  - [public_prots_l_grow_2] is allowed when [t] already maps to [Secret] in
    [states_l]. The constraints on this [t] allow it to protect [tsub].
  - [public_prots_l_grow_3] is allowed when [t] is not already in [states_l],
    has a protector [tsub] to satisfy the protection chain requirement, and
    has not protected anything before.
  - [public_prots_l_grow_4] is the same as [public_prots_l_grow_3],
    except [t] is marked [Pending t1'] in [states_l].
  - [public_prots_l_grow_5] is the same as [public_prots_l_grow_3],
    except [t] is a nonce, and so does not need a protector.
  - [public_prots_l_grow_6] is the same as [public_prots_l_grow_5],
    except [t] is marked [Pending t1'] in [states_l].
- The [public_prots_l_shrink] family removes [tsup] from the protection of
  [t].
  - [public_prots_l_shrink] is allowed when [tsup] has an alternative
    protector [t1].
  - [public_prots_l_shrink_2] is allowed when [tsup] itself is not
    protecting anything above it, and it is not in [states_l].
  - [public_prots_l_shrink_3] is allowed when [tsup] has been marked
    [PublicLink t'] in [states_l].

** Section [StatesUpdates]

- The [public_states_l_extend] family adds [t ↦ Pending t'] in [states_l].
  - [public_states_l_extend] is allowed when [t] is protected by a subterm.
  - [public_states_l_extend_2] is the same as [public_states_l_extend],
    except [t] is a nonce, and so does not need a protector.
- The [linked_extend] family provides convenience wrappers around the possible
  combinations of [public_states_l_extend] and [public_states_r_extend].
- [public_lock_Secret_l] turns [t ↦ Pending t'] into [t ↦ Secret].
- The [public_secret_l] family directly produces [t ↦ Secret].
  - [public_secret_l] is allowed when [t] is protected by some subterm
    [tsub], satisfying the protection chain requirement.
  - [public_secret_l_2] is the same as [public_secret_l], except [t]
    is a nonce, and so does not require protection.
- The [public_lock_PublicLink] family and [public_extend] produce
  [publicly_linked]. They accept various combinations of not being in
  [states_l] already and being marked [Pending] in it. See the comment on
  [public_lock_PublicLink] for more details. *)

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
Implicit Types prots_l prots_r : gmap term (gset term).
Implicit Types P : term -> term -> iProp.

Section ProtsUpdates.

Lemma public_prots_l_extend E t :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  prots_token_l t -∗
  |={E}=> protects_superterms_l t ∅.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Httf".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  Hstates_inv &
                  ([Hprots_l Hprots_l_frag] & Hprots_r & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_prots_l_fresh prots_l t with "Hmeta_prots_l Httf") as "%Hfresh".
iMod (own_update with "Hprots_l") as "[Hprots_l Hprots_frag_t]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t (● (GSet ∅) ⋅ ◯ (GSet ∅)));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hprots_frag_t" as "[[Hprots_t_frag Hprots_t_frag'] _]".
iMod (prots_meta_l_set with "Httf") as "#Hmeta_prots_t".
iModIntro. iSplitR "Hprots_t_frag'"; last by iFrame.
iModIntro. iExists states_l, states_r, (<[t := ∅]> prots_l), prots_r.
iFrame. iFrame "#".
iSplitL "Hprots_l Hprots_l_frag Hprots_t_frag".
{ iSplitL.
  - rewrite /public_prots_l_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iPureIntro. split.
- split; last done.
  move=> t1 ? Hstates Hst.
  destruct (HPending_l _ _ Hstates Hst) as [? | (t1sub & ts1 & ?)]; first eauto.
  right. exists t1sub, ts1.
  rewrite lookup_insert_ne; naive_solver.
- split; last done.
  move=> t1 ts1 Hprots Hts1.
  rewrite lookup_insert in Hprots; case_decide; first naive_solver.
  destruct (Hprots_l_cons _ _ Hprots Hts1) as (Hsubs & [?|(t1sub & ts2 & ? & ?)] & Hstates).
  + naive_solver.
  + do 2 (split=> //). right. exists t1sub, ts2.
    rewrite lookup_insert_ne; naive_solver.
Qed.

Lemma public_prots_r_extend E t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  prots_token_r t' -∗
  |={E}=> protects_superterms_r t' ∅.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Httf".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  Hstates_inv &
                  (Hprots_l & [Hprots_r Hprots_r_frag] & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_prots_r_fresh prots_r t' with "Hmeta_prots_r Httf") as "%Hfresh".
iMod (own_update with "Hprots_r") as "[Hprots_r Hprots_frag_t']".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t' (● (GSet ∅) ⋅ ◯ (GSet ∅)));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hprots_frag_t'" as "[[Hprots_t'_frag Hprots_t'_frag'] _]".
iMod (prots_meta_r_set with "Httf") as "#Hmeta_prots_t'".
iModIntro. iSplitR "Hprots_t'_frag'"; last by iFrame.
iModIntro. iExists states_l, states_r, prots_l, (<[t' := ∅]> prots_r).
iFrame. iFrame "#".
iSplitL "Hprots_r Hprots_r_frag Hprots_t'_frag".
{ iSplitL.
  - rewrite /public_prots_r_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iPureIntro. split.
- split; first done.
  move=> t1' ? Hstates Hst.
  destruct (HPending_r _ _ Hstates Hst) as [? | (t1'sub & ts1 & ?)]; first eauto.
  right. exists t1'sub, ts1.
  rewrite lookup_insert_ne; naive_solver.
- split; first done.
  move=> t1' ts1 Hprots Hts1.
  rewrite lookup_insert in Hprots; case_decide; first naive_solver.
  destruct (Hprots_r_cons _ _ Hprots Hts1) as (Hsubs & [?|(t1'sub & ts2 & ? & ?)] & Hstates).
  + naive_solver.
  + do 2 (split=> //). right. exists t1'sub, ts2.
    rewrite lookup_insert_ne; naive_solver.
Qed.

Lemma public_prots_l_grow E t ts tsup :
  ↑cryptisN ⊆ E →
  ts ≠ ∅ →
  tsup ∉ ts →
  is_immediate_subterm t tsup →
  hypercryptis_ctx -∗
  protects_superterms_l t ts -∗
  |={E}=> protects_superterms_l t (ts ∪ {[ tsup ]}) ∗
          protected_by_subterm_l tsup t.
Proof.
iIntros (HE Hts Hni Hsub) "#(_ & _ & Hinv) Hl_frac".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  Hstates &
                  ([Hprots_l Hprots_l_frag] & Hprots_r & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_prots_l_lookup_2 with "Hprots_l Hl_frac") as "%Hfltts".
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hprots_l_frag") as "[Hl_frac2 Hprots_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hprots_l Hl") as "[Hprots_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∪ {[ tsup ]})) ⋅ ◯ (GSet (ts ∪ {[ tsup ]})))
    (● (GSet (ts ∪ {[ tsup ]})) ⋅ ◯ (GSet {[ tsup ]})));
    first by rewrite lookup_fmap Hfltts.
  change (● GSet ts) with (● GSet ts ⋅ ◯ (GSet ∅)) at 2.
  apply auth_local_update=> //.
  replace (ts ∪ {[ tsup ]}) with ({[ tsup ]} ∪ ts) by set_solver.
  apply gset_disj_alloc_empty_local_update.
  set_solver. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] Hl]".
iModIntro. iSplitR "Hl_frac Hl"; last by iFrame.
iModIntro. iExists states_l, states_r, (<[t := ts ∪ {[ tsup ]}]> prots_l), prots_r.
iFrame. iFrame "#".
iSplitL "Hprots_l Hprots_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
destruct (Hprots_l_cons _ _ Hfltts Hts) as (Hsubs & Hchain & Hstates).
iPureIntro. split.
- split; last done.
  move=> t1 ? Hstates1 Hst1.
  destruct (HPending_l _ _ Hstates1 Hst1) as [? | (t1sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = t)) as [->|?].
  + exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1sub, ts1. by rewrite lookup_insert_ne.
- split; last done.
  move=> t1 ts1 Hprots Hts1.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_l_cons _ _ Hprots Hts1) as (? & [?|(t1sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1sub = t)) as [->|?].
    - exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1sub, ts2. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t1.
  split; first by (apply set_Forall_union; [done|by apply set_Forall_singleton]).
  split; last done.
  destruct Hchain as [?|(tsub & ts2 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t)) as [->|?].
  + exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_prots_r_grow E t' ts t'sup :
  ↑cryptisN ⊆ E →
  ts ≠ ∅ →
  t'sup ∉ ts →
  is_immediate_subterm t' t'sup →
  hypercryptis_ctx -∗
  protects_superterms_r t' ts -∗
  |={E}=> protects_superterms_r t' (ts ∪ {[ t'sup ]}) ∗
          protected_by_subterm_r t'sup t'.
Proof.
iIntros (HE Hts Hni Hsub) "#(_ & _ & Hinv) Hr_frac".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  Hstates &
                  (Hprots_l & [Hprots_r Hprots_r_frag] & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_prots_r_lookup_2 with "Hprots_r Hr_frac") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hprots_r_frag") as "[Hr_frac2 Hprots_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hprots_r Hr") as "[Hprots_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∪ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∪ {[ t'sup ]})))
    (● (GSet (ts ∪ {[ t'sup ]})) ⋅ ◯ (GSet {[ t'sup ]})));
    first by rewrite lookup_fmap Hfrt'ts.
  change (● GSet ts) with (● GSet ts ⋅ ◯ (GSet ∅)) at 2.
  apply auth_local_update=> //.
  replace (ts ∪ {[ t'sup ]}) with ({[ t'sup ]} ∪ ts) by set_solver.
  apply gset_disj_alloc_empty_local_update.
  set_solver. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] Hr]".
iModIntro. iSplitR "Hr_frac Hr"; last by iFrame.
iModIntro. iExists states_l, states_r, prots_l, (<[t' := ts ∪ {[ t'sup ]}]> prots_r).
iFrame. iFrame "#".
iSplitL "Hprots_r Hprots_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
destruct (Hprots_r_cons _ _ Hfrt'ts Hts) as (Hsubs & Hchain & Hstates).
iPureIntro. split.
- split; first done.
  move=> t1' ? Hstates1 Hst1.
  destruct (HPending_r _ _ Hstates1 Hst1) as [? | (t1'sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = t')) as [->|?].
  + exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1'sub, ts1. by rewrite lookup_insert_ne.
- split; first done.
  move=> t1' ts1 Hprots Hts1.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_r_cons _ _ Hprots Hts1) as (? & [?|(t1'sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1'sub = t')) as [->|?].
    - exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1'sub, ts2. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t1'.
  split; first by (apply set_Forall_union; [done|by apply set_Forall_singleton]).
  split; last done.
  destruct Hchain as [?|(t'sub & ts2 & ? & ?)]; first by left.
  right. destruct (decide (t'sub = t')) as [->|?].
  + exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t'sub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_prots_l_grow_2 E t ts tsup :
  ↑cryptisN ⊆ E →
  tsup ∉ ts →
  is_immediate_subterm t tsup →
  hypercryptis_ctx -∗
  protects_superterms_l t ts -∗
  secret_in_l t -∗
  |={E}=> protects_superterms_l t (ts ∪ {[ tsup ]}) ∗
          protected_by_subterm_l tsup t.
Proof.
iIntros (HE Hni Hsub) "#(_ & _ & Hinv) Hl_frac #Hsec".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  ([Hstates_l Hstates_l_frag] & Hstates_r & #Hmeta_states_l & #Hmeta_states_r) &
                  ([Hprots_l Hprots_l_frag] & Hprots_r & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (secret_in_l_lookup with "Hstates_l Hsec") as "%Hstates_t".
iPoseProof (public_prots_l_lookup_2 with "Hprots_l Hl_frac") as "%Hfltts".
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hprots_l_frag") as "[Hl_frac2 Hprots_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hprots_l Hl") as "[Hprots_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∪ {[ tsup ]})) ⋅ ◯ (GSet (ts ∪ {[ tsup ]})))
    (● (GSet (ts ∪ {[ tsup ]})) ⋅ ◯ (GSet {[ tsup ]})));
    first by rewrite lookup_fmap Hfltts.
  change (● GSet ts) with (● GSet ts ⋅ ◯ (GSet ∅)) at 2.
  apply auth_local_update=> //.
  replace (ts ∪ {[ tsup ]}) with ({[ tsup ]} ∪ ts) by set_solver.
  apply gset_disj_alloc_empty_local_update.
  set_solver. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] Hl]".
iAssert (public_states_l_auth states_l) with "[Hstates_l Hstates_l_frag]" as "Hstates_l".
{ rewrite /public_states_l_auth. iFrame. }
iModIntro. iSplitR "Hl_frac Hl"; last by iFrame.
iModIntro. iExists states_l, states_r, (<[t := ts ∪ {[ tsup ]}]> prots_l), prots_r.
iFrame. iFrame "#".
iSplitL "Hprots_l Hprots_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
have Hchain := HPending_l _ _ Hstates_t I.
iPureIntro. split.
- split; last done.
  move=> t1 ? Hstates1 Hst1.
  destruct (HPending_l _ _ Hstates1 Hst1) as [? | (t1sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = t)) as [->|?].
  + exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1sub, ts2. by rewrite lookup_insert_ne.
- split; last done.
  move=> t1 ts2 Hprots Hts2.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_l_cons _ _ Hprots Hts2) as (? & [?|(t1sub & ts3 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1sub = t)) as [->|?].
    - exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1sub, ts3. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t1.
  split.
  { apply set_Forall_union; last by apply set_Forall_singleton.
    destruct (decide (ts = ∅)) as [->|Hts]; first by apply set_Forall_empty.
    by destruct (Hprots_l_cons _ _ Hfltts Hts) as (? & _). }
  split; last by right; exists Secret.
  destruct Hchain as [?|(tsub & ts3 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t)) as [->|?].
  + exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts3. by rewrite lookup_insert_ne.
Qed.

Lemma public_prots_r_grow_2 E t' ts t'sup :
  ↑cryptisN ⊆ E →
  t'sup ∉ ts →
  is_immediate_subterm t' t'sup →
  hypercryptis_ctx -∗
  protects_superterms_r t' ts -∗
  secret_in_r t' -∗
  |={E}=> protects_superterms_r t' (ts ∪ {[ t'sup ]}) ∗
          protected_by_subterm_r t'sup t'.
Proof.
iIntros (HE Hni Hsub) "#(_ & _ & Hinv) Hr_frac #Hsec".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  (Hstates_l & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  (Hprots_l & [Hprots_r Hprots_r_frag] & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (secret_in_r_lookup with "Hstates_r Hsec") as "%Hstates_t".
iPoseProof (public_prots_r_lookup_2 with "Hprots_r Hr_frac") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hprots_r_frag") as "[Hr_frac2 Hprots_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hprots_r Hr") as "[Hprots_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∪ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∪ {[ t'sup ]})))
    (● (GSet (ts ∪ {[ t'sup ]})) ⋅ ◯ (GSet {[ t'sup ]})));
    first by rewrite lookup_fmap Hfrt'ts.
  change (● GSet ts) with (● GSet ts ⋅ ◯ (GSet ∅)) at 2.
  apply auth_local_update=> //.
  replace (ts ∪ {[ t'sup ]}) with ({[ t'sup ]} ∪ ts) by set_solver.
  apply gset_disj_alloc_empty_local_update.
  set_solver. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] Hr]".
iAssert (public_states_r_auth states_r) with "[Hstates_r Hstates_r_frag]" as "Hstates_r".
{ rewrite /public_states_r_auth. iFrame. }
iModIntro. iSplitR "Hr_frac Hr"; last by iFrame.
iModIntro. iExists states_l, states_r, prots_l, (<[t' := ts ∪ {[ t'sup ]}]> prots_r).
iFrame. iFrame "#".
iSplitL "Hprots_r Hprots_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
have Hchain := HPending_r _ _ Hstates_t I.
iPureIntro. split.
- split; first done.
  move=> t1' ? Hstates1 Hst1.
  destruct (HPending_r _ _ Hstates1 Hst1) as [? | (t1'sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = t')) as [->|?].
  + exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1'sub, ts2. by rewrite lookup_insert_ne.
- split; first done.
  move=> t1' ts2 Hprots Hts2.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_r_cons _ _ Hprots Hts2) as (? & [?|(t1'sub & ts3 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1'sub = t')) as [->|?].
    - exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1'sub, ts3. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t1'.
  split.
  { apply set_Forall_union; last by apply set_Forall_singleton.
    destruct (decide (ts = ∅)) as [->|Hts]; first by apply set_Forall_empty.
    by destruct (Hprots_r_cons _ _ Hfrt'ts Hts) as (? & _). }
  split; last by right; exists Secret.
  destruct Hchain as [?|(t'sub & ts3 & ? & ?)]; first by left.
  right. destruct (decide (t'sub = t')) as [->|?].
  + exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t'sub, ts3. by rewrite lookup_insert_ne.
Qed.

Lemma public_prots_l_grow_3 E t tsub tsup :
  ↑cryptisN ⊆ E →
  is_immediate_subterm t tsup →
  hypercryptis_ctx -∗
  protected_by_subterm_l t tsub -∗
  protects_superterms_l t ∅ -∗
  states_token_l t -∗
  |={E}=> protects_superterms_l t {[ tsup ]} ∗
          protected_by_subterm_l tsup t ∗
          protected_by_subterm_l t tsub ∗
          states_token_l t.
Proof.
iIntros (HE Hsub) "#(_ & _ & Hinv) Hprot Hl_frac Htt".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  (Hstates_l & Hstates_r & #Hmeta_states_l & #Hmeta_states_r) &
                  ([Hprots_l Hprots_l_frag] & Hprots_r & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_l_fresh states_l t with "Hmeta_states_l Htt") as "%Hfresh".
iPoseProof (public_prots_l_lookup_2 with "Hprots_l Hl_frac") as "%Hflt".
iPoseProof (public_prots_l_lookup with "Hprots_l Hprot") as "%Hprot".
iDestruct (big_sepM_delete _ _ t _ Hflt with "Hprots_l_frag") as "[Hl_frac2 Hprots_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hprots_l Hl") as "[Hprots_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]}))
    (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]})));
    first by rewrite lookup_fmap Hflt.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ tsup ]} with ({[ tsup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] Hl]".
iModIntro. iSplitR "Hl_frac Hl Hprot Htt"; last by iFrame.
iModIntro. iExists states_l, states_r, (<[t := {[ tsup ]}]> prots_l), prots_r.
iFrame. iFrame "#".
iSplitL "Hprots_l Hprots_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split.
- split; last done.
  move=> t1 ? Hstates1 Hst1.
  destruct (HPending_l _ _ Hstates1 Hst1) as [? | (t1sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = t)) as [->|?].
  + exists t, ({[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1sub, ts1. by rewrite lookup_insert_ne.
- split; last done.
  move=> t1 ts1 Hprots Hts1.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_l_cons _ _ Hprots Hts1) as (? & [?|(t1sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1sub = t)) as [->|?].
    - exists t, ({[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1sub, ts2. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t1.
  split; first by apply set_Forall_singleton.
  split; last by left.
  destruct Hprot as (ts2 & ? & ?).
  right. destruct (decide (tsub = t)) as [->|?].
  + set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_prots_r_grow_3 E t' t'sub t'sup :
  ↑cryptisN ⊆ E →
  is_immediate_subterm t' t'sup →
  hypercryptis_ctx -∗
  protected_by_subterm_r t' t'sub -∗
  protects_superterms_r t' ∅ -∗
  states_token_r t' -∗
  |={E}=> protects_superterms_r t' {[ t'sup ]} ∗
          protected_by_subterm_r t'sup t' ∗
          protected_by_subterm_r t' t'sub ∗
          states_token_r t'.
Proof.
iIntros (HE Hsub) "#(_ & _ & Hinv) Hprot Hr_frac Htts".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  (Hstates_l & Hstates_r & #Hmeta_states_l & #Hmeta_states_r) &
                  (Hprots_l & [Hprots_r Hprots_r_frag] & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_r_fresh states_r t' with "Hmeta_states_r Htts") as "%Hfresh".
iPoseProof (public_prots_r_lookup_2 with "Hprots_r Hr_frac") as "%Hfrt'".
iPoseProof (public_prots_r_lookup with "Hprots_r Hprot") as "%Hprot".
iDestruct (big_sepM_delete _ _ t' _ Hfrt' with "Hprots_r_frag") as "[Hr_frac2 Hprots_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hprots_r Hr") as "[Hprots_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]}))
    (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]})));
    first by rewrite lookup_fmap Hfrt'.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ t'sup ]} with ({[ t'sup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] Hr]".
iModIntro. iSplitR "Hr_frac Hr Hprot Htts"; last by iFrame.
iModIntro. iExists states_l, states_r, prots_l, (<[t' := {[ t'sup ]}]> prots_r).
iFrame. iFrame "#".
iSplitL "Hprots_r Hprots_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split.
- split; first done.
  move=> t1' ? Hstates1 Hst1.
  destruct (HPending_r _ _ Hstates1 Hst1) as [? | (t1'sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = t')) as [->|?].
  + exists t', ({[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1'sub, ts1. by rewrite lookup_insert_ne.
- split; first done.
  move=> t1' ts1 Hprots Hts1.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_r_cons _ _ Hprots Hts1) as (? & [?|(t1'sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1'sub = t')) as [->|?].
    - exists t', ({[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1'sub, ts2. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t1'.
  split; first by apply set_Forall_singleton.
  split; last by left.
  destruct Hprot as (ts2 & ? & ?).
  right. destruct (decide (t'sub = t')) as [->|?].
  + set_solver.
  + exists t'sub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_prots_l_grow_4 E t t1' tsub tsup :
  ↑cryptisN ⊆ E →
  is_immediate_subterm t tsup →
  hypercryptis_ctx -∗
  protected_by_subterm_l t tsub -∗
  protects_superterms_l t ∅ -∗
  pending_in_l t t1' -∗
  |={E}=> protects_superterms_l t {[ tsup ]} ∗
          protected_by_subterm_l tsup t ∗
          protected_by_subterm_l t tsub ∗
          pending_in_l t t1'.
Proof.
iIntros (HE Hsub) "#(_ & _ & Hinv) Hprot Hl_frac Hfrag".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  ([Hstates_l Hstates_l_frag] & Hstates_r & #Hmeta_states_l & #Hmeta_states_r) &
                  ([Hprots_l Hprots_l_frag] & Hprots_r & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_l_lookup with "Hstates_l Hfrag") as "%Hpltts".
iPoseProof (public_prots_l_lookup_2 with "Hprots_l Hl_frac") as "%Hflt".
iPoseProof (public_prots_l_lookup with "Hprots_l Hprot") as "%Hprot".
iDestruct (big_sepM_delete _ _ t _ Hflt with "Hprots_l_frag") as "[Hl_frac2 Hprots_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hprots_l Hl") as "[Hprots_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]}))
    (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]})));
    first by rewrite lookup_fmap Hflt.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ tsup ]} with ({[ tsup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] Hl]".
iAssert (public_states_l_auth states_l) with "[Hstates_l Hstates_l_frag]" as "Hstates_l".
{ rewrite /public_states_l_auth. iFrame. }
iModIntro. iSplitR "Hl_frac Hl Hprot Hfrag"; last by iFrame.
iModIntro. iExists states_l, states_r, (<[t := {[ tsup ]}]> prots_l), prots_r.
iFrame. iFrame "#".
iSplitL "Hprots_l Hprots_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split.
- split; last done.
  move=> t1 ? Hstates1 Hst1.
  destruct (HPending_l _ _ Hstates1 Hst1) as [? | (t1sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = t)) as [->|?].
  + exists t, ({[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1sub, ts1. by rewrite lookup_insert_ne.
- split; last done.
  move=> t1 ts1 Hprots Hts1.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_l_cons _ _ Hprots Hts1) as (? & [?|(t1sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1sub = t)) as [->|?].
    - exists t, ({[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1sub, ts2. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t1.
  split; first by apply set_Forall_singleton.
  split; last by right; exists (Pending t1').
  destruct Hprot as (ts2 & ? & ?).
  right. destruct (decide (tsub = t)) as [->|?].
  + set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_prots_r_grow_4 E t' t1 t'sub t'sup :
  ↑cryptisN ⊆ E →
  is_immediate_subterm t' t'sup →
  hypercryptis_ctx -∗
  protected_by_subterm_r t' t'sub -∗
  protects_superterms_r t' ∅ -∗
  pending_in_r t1 t' -∗
  |={E}=> protects_superterms_r t' {[ t'sup ]} ∗
          protected_by_subterm_r t'sup t' ∗
          protected_by_subterm_r t' t'sub ∗
          pending_in_r t1 t'.
Proof.
iIntros (HE Hsub) "#(_ & _ & Hinv) Hprot Hr_frac Hfrag".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  (Hstates_l & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  (Hprots_l & [Hprots_r Hprots_r_frag] & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_r_lookup with "Hstates_r Hfrag") as "%Hprtst'".
iPoseProof (public_prots_r_lookup_2 with "Hprots_r Hr_frac") as "%Hfrt'".
iPoseProof (public_prots_r_lookup with "Hprots_r Hprot") as "%Hprot".
iDestruct (big_sepM_delete _ _ t' _ Hfrt' with "Hprots_r_frag") as "[Hr_frac2 Hprots_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hprots_r Hr") as "[Hprots_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]}))
    (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]})));
    first by rewrite lookup_fmap Hfrt'.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ t'sup ]} with ({[ t'sup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] Hr]".
iAssert (public_states_r_auth states_r) with "[Hstates_r Hstates_r_frag]" as "Hstates_r".
{ rewrite /public_states_r_auth. iFrame. }
iModIntro. iSplitR "Hr_frac Hr Hprot Hfrag"; last by iFrame.
iModIntro. iExists states_l, states_r, prots_l, (<[t' := {[ t'sup ]}]> prots_r).
iFrame. iFrame "#".
iSplitL "Hprots_r Hprots_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split.
- split; first done.
  move=> t1' ? Hstates1 Hst1.
  destruct (HPending_r _ _ Hstates1 Hst1) as [? | (t1'sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = t')) as [->|?].
  + exists t', ({[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1'sub, ts1. by rewrite lookup_insert_ne.
- split; first done.
  move=> t1' ts1 Hprots Hts1.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_r_cons _ _ Hprots Hts1) as (? & [?|(t1'sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1'sub = t')) as [->|?].
    - exists t', ({[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1'sub, ts2. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t1'.
  split; first by apply set_Forall_singleton.
  split; last by right; exists (Pending t1).
  destruct Hprot as (ts2 & ? & ?).
  right. destruct (decide (t'sub = t')) as [->|?].
  + set_solver.
  + exists t'sub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_prots_l_grow_5 E t tsup :
  is_nonce t →
  ↑cryptisN ⊆ E →
  is_immediate_subterm t tsup →
  hypercryptis_ctx -∗
  protects_superterms_l t ∅ -∗
  states_token_l t -∗
  |={E}=> protects_superterms_l t {[ tsup ]} ∗
          protected_by_subterm_l tsup t ∗
          states_token_l t.
Proof.
move=> /is_nonceP [a ->].
iIntros (HE Hsub) "#(_ & _ & Hinv) Hl_frac Htt".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  (Hstates_l & Hstates_r & #Hmeta_states_l & #Hmeta_states_r) &
                  ([Hprots_l Hprots_l_frag] & Hprots_r & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_l_fresh states_l (TNonce a) with "Hmeta_states_l Htt") as "%Hfresh".
iPoseProof (public_prots_l_lookup_2 with "Hprots_l Hl_frac") as "%Hflt".
iDestruct (big_sepM_delete _ _ (TNonce a) _ Hflt with "Hprots_l_frag") as "[Hl_frac2 Hprots_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hprots_l Hl") as "[Hprots_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]}))
    (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]})));
    first by rewrite lookup_fmap Hflt.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ tsup ]} with ({[ tsup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] Hl]".
iModIntro. iSplitR "Hl_frac Hl Htt"; last by iFrame.
iModIntro. iExists states_l, states_r, (<[TNonce a := {[ tsup ]}]> prots_l), prots_r.
iFrame. iFrame "#".
iSplitL "Hprots_l Hprots_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split.
- split; last done.
  move=> t1 ? Hstates1 Hst1.
  destruct (HPending_l _ _ Hstates1 Hst1) as [? | (t1sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = TNonce a)) as [->|?].
  + exists (TNonce a), ({[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1sub, ts1. by rewrite lookup_insert_ne.
- split; last done.
  move=> t1 ts1 Hprots Hts1.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_l_cons _ _ Hprots Hts1) as (? & [?|(t1sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1sub = TNonce a)) as [->|?].
    - exists (TNonce a), ({[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1sub, ts2. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t1.
  split; first by apply set_Forall_singleton.
  split; first by left; eauto.
  by left.
Qed.

Lemma public_prots_r_grow_5 E t' t'sup :
  is_nonce t' →
  ↑cryptisN ⊆ E →
  is_immediate_subterm t' t'sup →
  hypercryptis_ctx -∗
  protects_superterms_r t' ∅ -∗
  states_token_r t' -∗
  |={E}=> protects_superterms_r t' {[ t'sup ]} ∗
          protected_by_subterm_r t'sup t' ∗
          states_token_r t'.
Proof.
move=> /is_nonceP [a' ->].
iIntros (HE Hsub) "#(_ & _ & Hinv) Hr_frac Htts".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  (Hstates_l & Hstates_r & #Hmeta_states_l & #Hmeta_states_r) &
                  (Hprots_l & [Hprots_r Hprots_r_frag] & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_r_fresh states_r (TNonce a') with "Hmeta_states_r Htts") as "%Hfresh".
iPoseProof (public_prots_r_lookup_2 with "Hprots_r Hr_frac") as "%Hfrt'".
iDestruct (big_sepM_delete _ _ (TNonce a') _ Hfrt' with "Hprots_r_frag") as "[Hr_frac2 Hprots_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hprots_r Hr") as "[Hprots_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]}))
    (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]})));
    first by rewrite lookup_fmap Hfrt'.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ t'sup ]} with ({[ t'sup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] Hr]".
iModIntro. iSplitR "Hr_frac Hr Htts"; last by iFrame.
iModIntro. iExists states_l, states_r, prots_l, (<[TNonce a' := {[ t'sup ]}]> prots_r).
iFrame. iFrame "#".
iSplitL "Hprots_r Hprots_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split.
- split; first done.
  move=> t1' ? Hstates1 Hst1.
  destruct (HPending_r _ _ Hstates1 Hst1) as [? | (t1'sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = TNonce a')) as [->|?].
  + exists (TNonce a'), ({[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1'sub, ts1. by rewrite lookup_insert_ne.
- split; first done.
  move=> t1' ts1 Hprots Hts1.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_r_cons _ _ Hprots Hts1) as (? & [?|(t1'sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1'sub = TNonce a')) as [->|?].
    - exists (TNonce a'), ({[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1'sub, ts2. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t1'.
  split; first by apply set_Forall_singleton.
  split; first by left; eauto.
  by left.
Qed.

Lemma public_prots_l_grow_6 E t t1' tsup :
  is_nonce t →
  ↑cryptisN ⊆ E →
  is_immediate_subterm t tsup →
  hypercryptis_ctx -∗
  protects_superterms_l t ∅ -∗
  pending_in_l t t1' -∗
  |={E}=> protects_superterms_l t {[ tsup ]} ∗
          protected_by_subterm_l tsup t ∗
          pending_in_l t t1'.
Proof.
move=> /is_nonceP [a ->].
iIntros (HE Hsub) "#(_ & _ & Hinv) Hl_frac Hfrag".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  ([Hstates_l Hstates_l_frag] & Hstates_r & #Hmeta_states_l & #Hmeta_states_r) &
                  ([Hprots_l Hprots_l_frag] & Hprots_r & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_l_lookup with "Hstates_l Hfrag") as "%Hpltts".
iPoseProof (public_prots_l_lookup_2 with "Hprots_l Hl_frac") as "%Hflt".
iDestruct (big_sepM_delete _ _ (TNonce a) _ Hflt with "Hprots_l_frag") as "[Hl_frac2 Hprots_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hprots_l Hl") as "[Hprots_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]}))
    (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]})));
    first by rewrite lookup_fmap Hflt.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ tsup ]} with ({[ tsup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] Hl]".
iAssert (public_states_l_auth states_l) with "[Hstates_l Hstates_l_frag]" as "Hstates_l".
{ rewrite /public_states_l_auth. iFrame. }
iModIntro. iSplitR "Hl_frac Hl Hfrag"; last by iFrame.
iModIntro. iExists states_l, states_r, (<[TNonce a := {[ tsup ]}]> prots_l), prots_r.
iFrame. iFrame "#".
iSplitL "Hprots_l Hprots_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split.
- split; last done.
  move=> t1 ? Hstates1 Hst1.
  destruct (HPending_l _ _ Hstates1 Hst1) as [? | (t1sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = TNonce a)) as [->|?].
  + exists (TNonce a), ({[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1sub, ts1. by rewrite lookup_insert_ne.
- split; last done.
  move=> t1 ts1 Hprots Hts1.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_l_cons _ _ Hprots Hts1) as (? & [?|(t1sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1sub = TNonce a)) as [->|?].
    - exists (TNonce a), ({[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1sub, ts2. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t1.
  split; first by apply set_Forall_singleton.
  split; first by left; eauto.
  right. by exists (Pending t1').
Qed.

Lemma public_prots_r_grow_6 E t' t1 t'sup :
  is_nonce t' →
  ↑cryptisN ⊆ E →
  is_immediate_subterm t' t'sup →
  hypercryptis_ctx -∗
  protects_superterms_r t' ∅ -∗
  pending_in_r t1 t' -∗
  |={E}=> protects_superterms_r t' {[ t'sup ]} ∗
          protected_by_subterm_r t'sup t' ∗
          pending_in_r t1 t'.
Proof.
move=> /is_nonceP [a' ->].
iIntros (HE Hsub) "#(_ & _ & Hinv) Hr_frac Hfrag".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  (Hstates_l & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  (Hprots_l & [Hprots_r Hprots_r_frag] & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_r_lookup with "Hstates_r Hfrag") as "%Hprtst'".
iPoseProof (public_prots_r_lookup_2 with "Hprots_r Hr_frac") as "%Hfrt'".
iDestruct (big_sepM_delete _ _ (TNonce a') _ Hfrt' with "Hprots_r_frag") as "[Hr_frac2 Hprots_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hprots_r Hr") as "[Hprots_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]}))
    (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]})));
    first by rewrite lookup_fmap Hfrt'.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ t'sup ]} with ({[ t'sup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] Hr]".
iAssert (public_states_r_auth states_r) with "[Hstates_r Hstates_r_frag]" as "Hstates_r".
{ rewrite /public_states_r_auth. iFrame. }
iModIntro. iSplitR "Hr_frac Hr Hfrag"; last by iFrame.
iModIntro. iExists states_l, states_r, prots_l, (<[TNonce a' := {[ t'sup ]}]> prots_r).
iFrame. iFrame "#".
iSplitL "Hprots_r Hprots_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split.
- split; first done.
  move=> t1' ? Hstates1 Hst1.
  destruct (HPending_r _ _ Hstates1 Hst1) as [? | (t1'sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = TNonce a')) as [->|?].
  + exists (TNonce a'), ({[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1'sub, ts1. by rewrite lookup_insert_ne.
- split; first done.
  move=> t1' ts1 Hprots Hts1.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_r_cons _ _ Hprots Hts1) as (? & [?|(t1'sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1'sub = TNonce a')) as [->|?].
    - exists (TNonce a'), ({[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1'sub, ts2. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t1'.
  split; first by apply set_Forall_singleton.
  split; first by left; eauto.
  right. by exists (Pending t1).
Qed.

Lemma public_prots_l_shrink E t ts tsup t1 :
  ↑cryptisN ⊆ E →
  tsup ∈ ts →
  hypercryptis_ctx -∗
  protects_superterms_l t ts -∗
  protected_by_subterm_l tsup t -∗
  protected_by_subterm_l tsup t1 -∗
  |={E}=> protects_superterms_l t (ts ∖ {[ tsup ]}) ∗
          protected_by_subterm_l tsup t1.
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot Hprot1".
iPoseProof (public_prots_l_ne with "Hprot Hprot1") as "%Hne".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  Hstates &
                  ([Hprots_l Hprots_l_frag] & Hprots_r & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_prots_l_lookup_2 with "Hprots_l Hl_frac") as "%Hfltts".
iPoseProof (public_prots_l_lookup with "Hprots_l Hprot1") as "(%ts1 & % & %)".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hprots_l_cons _ _ Hfltts Hts) as (Hsubs & Hchain & Hstates).
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hprots_l_frag") as "[Hl_frac2 Hprots_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hprots_l Hl") as "[Hprots_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet (ts ∖ {[ tsup ]})))
    (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
iModIntro. iSplitR "Hl_frac Hprot1"; last by iFrame.
iModIntro. iExists states_l, states_r, (<[t := ts ∖ {[ tsup ]}]> prots_l), prots_r.
iFrame. iFrame "#".
iSplitL "Hprots_l Hprots_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split.
- split; last done.
  move=> t2 ? Hstates1 Hst1.
  destruct (HPending_l _ _ Hstates1 Hst1) as [? | (t2sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t2sub = t)) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (tsup = t2)) as [->|?].
    * exists t1, ts1. by rewrite lookup_insert_ne.
    * exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2sub, ts2. by rewrite lookup_insert_ne.
- split; last done.
  move=> t2 ts2 Hprots Hts2.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_l_cons _ _ Hprots Hts2) as (? & [?|(t2sub & ts3 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2sub = t)) as [->|?].
    - assert (ts3 = ts) as -> by congruence.
      destruct (decide (tsup = t2)) as [->|?].
      + exists t1, ts1. by rewrite lookup_insert_ne.
      + exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2sub, ts3. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t2.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts2 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t)) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (tsup = t)) as [->|?].
    * exists t1, ts1. by rewrite lookup_insert_ne.
    * exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_prots_r_shrink E t' ts t'sup t1' :
  ↑cryptisN ⊆ E →
  t'sup ∈ ts →
  hypercryptis_ctx -∗
  protects_superterms_r t' ts -∗
  protected_by_subterm_r t'sup t' -∗
  protected_by_subterm_r t'sup t1' -∗
  |={E}=> protects_superterms_r t' (ts ∖ {[ t'sup ]}) ∗
          protected_by_subterm_r t'sup t1'.
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hr_frac Hprot Hprot1".
iPoseProof (public_prots_r_ne with "Hprot Hprot1") as "%Hne".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  Hstates &
                  (Hprots_l & [Hprots_r Hprots_r_frag] & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_prots_r_lookup_2 with "Hprots_r Hr_frac") as "%Hfrt'ts".
iPoseProof (public_prots_r_lookup with "Hprots_r Hprot1") as "(%ts1 & % & %)".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hprots_r_cons _ _ Hfrt'ts Hts) as (Hsubs & Hchain & Hstates).
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hprots_r_frag") as "[Hr_frac2 Hprots_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iCombine "Hr Hprot" as "Hr".
iMod (own_update_2 with "Hprots_r Hr") as "[Hprots_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∖ {[ t'sup ]})))
    (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfrt'ts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] _]".
iModIntro. iSplitR "Hr_frac Hprot1"; last by iFrame.
iModIntro. iExists states_l, states_r, prots_l, (<[t' := ts ∖ {[ t'sup ]}]> prots_r).
iFrame. iFrame "#".
iSplitL "Hprots_r Hprots_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split.
- split; first done.
  move=> t2' ? Hstates1 Hst1.
  destruct (HPending_r _ _ Hstates1 Hst1) as [? | (t2'sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t2'sub = t')) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (t'sup = t2')) as [->|?].
    * exists t1', ts1. by rewrite lookup_insert_ne.
    * exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2'sub, ts2. by rewrite lookup_insert_ne.
- split; first done.
  move=> t2' ts2 Hprots Hts2.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_r_cons _ _ Hprots Hts2) as (? & [?|(t2'sub & ts3 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2'sub = t')) as [->|?].
    - assert (ts3 = ts) as -> by congruence.
      destruct (decide (t'sup = t2')) as [->|?].
      + exists t1', ts1. by rewrite lookup_insert_ne.
      + exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2'sub, ts3. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t2'.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts2 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t')) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (t'sup = t')) as [->|?].
    * exists t1', ts1. by rewrite lookup_insert_ne.
    * exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_prots_l_shrink_2 E t ts tsup :
  ↑cryptisN ⊆ E →
  tsup ∈ ts →
  hypercryptis_ctx -∗
  protects_superterms_l t ts -∗
  protected_by_subterm_l tsup t -∗
  protects_superterms_l tsup ∅ -∗
  states_token_l tsup -∗
  |={E}=> protects_superterms_l t (ts ∖ {[ tsup ]}) ∗
          protects_superterms_l tsup ∅ ∗
          states_token_l tsup.
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot Hl_frac_sup Htt_sup".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  (Hstates_l & Hstates_r & #Hmeta_states_l & #Hmeta_states_r) &
                  ([Hprots_l Hprots_l_frag] & Hprots_r & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_l_fresh states_l tsup with "Hmeta_states_l Htt_sup") as "%Hfresh".
iPoseProof (public_prots_l_lookup_2 with "Hprots_l Hl_frac") as "%Hfltts".
iPoseProof (public_prots_l_lookup_2 with "Hprots_l Hl_frac_sup") as "%Hfltsup".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hprots_l_cons _ _ Hfltts Hts) as (Hsubs & Hchain & Hstates).
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hprots_l_frag") as "[Hl_frac2 Hprots_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hprots_l Hl") as "[Hprots_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet (ts ∖ {[ tsup ]})))
    (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
iModIntro. iSplitR "Hl_frac Hl_frac_sup Htt_sup"; last by iFrame.
iModIntro. iExists states_l, states_r, (<[t := ts ∖ {[ tsup ]}]> prots_l), prots_r.
iFrame. iFrame "#".
iSplitL "Hprots_l Hprots_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split.
- split; last done.
  move=> t2 ? Hstates1 Hst1.
  destruct (HPending_l _ _ Hstates1 Hst1) as [? | (t2sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t2sub = t)) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (tsup = t2)) as [->|?]; first by set_solver.
    exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2sub, ts2. by rewrite lookup_insert_ne.
- split; last done.
  move=> t2 ts2 Hprots Hts2.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_l_cons _ _ Hprots Hts2) as (? & [?|(t2sub & ts3 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2sub = t)) as [->|?].
    - assert (ts3 = ts) as -> by congruence.
      destruct (decide (tsup = t2)) as [->|?]; first by congruence.
      exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2sub, ts3. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t2.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts2 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t)) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (tsup = t)) as [->|?]; first by set_solver.
    exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_prots_r_shrink_2 E t' ts t'sup :
  ↑cryptisN ⊆ E →
  t'sup ∈ ts →
  hypercryptis_ctx -∗
  protects_superterms_r t' ts -∗
  protected_by_subterm_r t'sup t' -∗
  protects_superterms_r t'sup ∅ -∗
  states_token_r t'sup -∗
  |={E}=> protects_superterms_r t' (ts ∖ {[ t'sup ]}) ∗
          protects_superterms_r t'sup ∅ ∗
          states_token_r t'sup.
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hr_frac Hprot Hr_frac_sup Htts_sup".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  (Hstates_l & Hstates_r & #Hmeta_states_l & #Hmeta_states_r) &
                  (Hprots_l & [Hprots_r Hprots_r_frag] & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_r_fresh states_r t'sup with "Hmeta_states_r Htts_sup") as "%Hfresh".
iPoseProof (public_prots_r_lookup_2 with "Hprots_r Hr_frac") as "%Hfrt'ts".
iPoseProof (public_prots_r_lookup_2 with "Hprots_r Hr_frac_sup") as "%Hfrt'sup".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hprots_r_cons _ _ Hfrt'ts Hts) as (Hsubs & Hchain & Hstates).
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hprots_r_frag") as "[Hr_frac2 Hprots_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iCombine "Hr Hprot" as "Hr".
iMod (own_update_2 with "Hprots_r Hr") as "[Hprots_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∖ {[ t'sup ]})))
    (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfrt'ts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] _]".
iModIntro. iSplitR "Hr_frac Hr_frac_sup Htts_sup"; last by iFrame.
iModIntro. iExists states_l, states_r, prots_l, (<[t' := ts ∖ {[ t'sup ]}]> prots_r).
iFrame. iFrame "#".
iSplitL "Hprots_r Hprots_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split.
- split; first done.
  move=> t2' ? Hstates1 Hst1.
  destruct (HPending_r _ _ Hstates1 Hst1) as [? | (t2'sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t2'sub = t')) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (t'sup = t2')) as [->|?]; first by set_solver.
    exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2'sub, ts2. by rewrite lookup_insert_ne.
- split; first done.
  move=> t2' ts2 Hprots Hts2.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_r_cons _ _ Hprots Hts2) as (? & [?|(t2'sub & ts3 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2'sub = t')) as [->|?].
    - assert (ts3 = ts) as -> by congruence.
      destruct (decide (t'sup = t2')) as [->|?]; first by congruence.
      exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2'sub, ts3. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t2'.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts2 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t')) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (t'sup = t')) as [->|?]; first by set_solver.
    exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_prots_l_shrink_3 E t ts tsup t' :
  ↑cryptisN ⊆ E →
  tsup ∈ ts →
  hypercryptis_ctx -∗
  protects_superterms_l t ts -∗
  protected_by_subterm_l tsup t -∗
  publicly_linked tsup t' -∗
  |={E}=> protects_superterms_l t (ts ∖ {[ tsup ]}).
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot #Hpub".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  ([Hstates_l Hstates_l_frag] & Hstates_r & #Hmeta_states_l & #Hmeta_states_r) &
                  ([Hprots_l Hprots_l_frag] & Hprots_r & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (publicly_linked_lookup_l with "Hstates_l Hpub") as "%Hpltsupt'".
iPoseProof (public_prots_l_lookup_2 with "Hprots_l Hl_frac") as "%Hfltts".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hprots_l_cons _ _ Hfltts Hts) as (Hsubs & Hchain & Hstates).
have Hfltsup : ∀ ts, prots_l !! tsup = Some ts → ts ≠ ∅ → False.
{ move=> ts1 Hprots Hts1.
  destruct (Hprots_l_cons _ _ Hprots Hts1) as (_ & _ & [?|(st & ? & Hst)]); first congruence.
  by destruct st; [congruence | destruct Hst | congruence | congruence]. }
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hprots_l_frag") as "[Hl_frac2 Hprots_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hprots_l Hl") as "[Hprots_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet (ts ∖ {[ tsup ]})))
    (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
iModIntro. iSplitR "Hl_frac"; last by iFrame.
iModIntro. iExists states_l, states_r, (<[t := ts ∖ {[ tsup ]}]> prots_l), prots_r.
iFrame. iFrame "#".
iSplitL "Hprots_l Hprots_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split.
- split; last done.
  move=> t2 ? Hstates1 Hst1.
  destruct (HPending_l _ _ Hstates1 Hst1) as [? | (t2sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t2sub = t)) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (tsup = t2)) as [->|?]; first by set_solver.
    exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2sub, ts2. by rewrite lookup_insert_ne.
- split; last done.
  move=> t2 ts2 Hprots Hts2.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_l_cons _ _ Hprots Hts2) as (? & [?|(t2sub & ts3 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2sub = t)) as [->|?].
    - assert (ts3 = ts) as -> by congruence.
      destruct (decide (tsup = t2)) as [->|?]; first by case: (Hfltsup _ Hprots Hts2).
      exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2sub, ts3. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t2.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts2 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t)) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (tsup = t)) as [->|?]; first by set_solver.
    exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_prots_r_shrink_3 E t' ts t'sup t :
  ↑cryptisN ⊆ E →
  t'sup ∈ ts →
  hypercryptis_ctx -∗
  protects_superterms_r t' ts -∗
  protected_by_subterm_r t'sup t' -∗
  publicly_linked t t'sup -∗
  |={E}=> protects_superterms_r t' (ts ∖ {[ t'sup ]}).
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hr_frac Hprot #Hpub".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  (Hstates_l & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  (Hprots_l & [Hprots_r Hprots_r_frag] & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & HPublicLink_consistent &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (publicly_linked_lookup_r with "Hstates_r Hpub") as "%Hprtt'sup".
iPoseProof (public_prots_r_lookup_2 with "Hprots_r Hr_frac") as "%Hfrt'ts".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hprots_r_cons _ _ Hfrt'ts Hts) as (Hsubs & Hchain & Hstates).
have Hfrt'sup : ∀ ts, prots_r !! t'sup = Some ts → ts ≠ ∅ → False.
{ move=> ts1 Hprots Hts1.
  destruct (Hprots_r_cons _ _ Hprots Hts1) as (_ & _ & [?|(st & ? & Hst)]); first congruence.
  by destruct st; [congruence | destruct Hst | congruence | congruence]. }
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hprots_r_frag") as "[Hr_frac2 Hprots_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iCombine "Hr Hprot" as "Hr".
iMod (own_update_2 with "Hprots_r Hr") as "[Hprots_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∖ {[ t'sup ]})))
    (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfrt'ts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] _]".
iModIntro. iSplitR "Hr_frac"; last by iFrame.
iModIntro. iExists states_l, states_r, prots_l, (<[t' := ts ∖ {[ t'sup ]}]> prots_r).
iFrame. iFrame "#".
iSplitL "Hprots_r Hprots_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_prots_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split.
- split; first done.
  move=> t2' ? Hstates1 Hst1.
  destruct (HPending_r _ _ Hstates1 Hst1) as [? | (t2'sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t2'sub = t')) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (t'sup = t2')) as [->|?]; first by set_solver.
    exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2'sub, ts2. by rewrite lookup_insert_ne.
- split; first done.
  move=> t2' ts2 Hprots Hts2.
  rewrite lookup_insert in Hprots; case_decide as Heq; last first.
  { destruct (Hprots_r_cons _ _ Hprots Hts2) as (? & [?|(t2'sub & ts3 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2'sub = t')) as [->|?].
    - assert (ts3 = ts) as -> by congruence.
      destruct (decide (t'sup = t2')) as [->|?]; first by case: (Hfrt'sup _ Hprots Hts2).
      exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2'sub, ts3. by rewrite lookup_insert_ne. }
  injection Hprots as <-. subst t2'.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts2 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t')) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (t'sup = t')) as [->|?]; first by set_solver.
    exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

End ProtsUpdates.

Section StatesUpdates.

Lemma public_states_l_extend E t t' tsub :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_by_subterm_l t tsub -∗
  states_token_l t -∗
  |={E}=> protected_by_subterm_l t tsub ∗
          linked_in_l t t' ∗
          pending_in_l t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hprot Htt".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  ([Hstates_l Hstates_l_frag] & Hstates_r & #Hmeta_states_l & #Hmeta_states_r) &
                  ([Hprots_l Hprots_l_frag] & Hprots_r & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & [HPublicLink_consistent HPublicLink_consistent_r] &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_l_fresh states_l t with "Hmeta_states_l Htt") as "%Hfresh".
iPoseProof (public_prots_l_lookup with "Hprots_l Hprot") as "%Hprot".
iMod (own_update with "Hstates_l") as "[Hstates_l Hstates_frag_t]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t (● Some (Pending t') ⋅ ◯ Some (Pending t')));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hstates_frag_t" as "[[Hstates_t_frag Hstates_t_frag'] Hstates_frag_t]".
iMod (states_meta_l_set with "Htt") as "#Hmeta_states_t".
iModIntro. iSplitR "Hprot Hstates_frag_t Hstates_t_frag'"; last by iFrame.
iModIntro. iExists (<[t := Pending t']> states_l), states_r.
iFrame. iFrame "#".
iSplitL "Hstates_l Hstates_l_frag Hstates_t_frag".
{ iSplitL.
  - rewrite /public_states_l_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iSplit.
{ iPureIntro. split; last done. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iSplitL "HPublicLink_consistent".
{ iIntros (??) "%Hstates".
  rewrite lookup_insert in Hstates; case_decide; first naive_solver.
  by iApply "HPublicLink_consistent". }
iPureIntro. split; last done.
move=> t1 ts1 Hprots Hts1.
destruct (Hprots_l_cons _ _ Hprots Hts1) as (? & ? & ?).
do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_states_r_extend E t t' t'sub :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_by_subterm_r t' t'sub -∗
  states_token_r t' -∗
  |={E}=> protected_by_subterm_r t' t'sub ∗
          linked_in_r t t' ∗
          pending_in_r t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hprot Htts".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  (Hstates_l & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  (Hprots_l & [Hprots_r Hprots_r_frag] & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & [HPublicLink_consistent HPublicLink_consistent_r] &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_r_fresh states_r t' with "Hmeta_states_r Htts") as "%Hfresh".
iPoseProof (public_prots_r_lookup with "Hprots_r Hprot") as "%Hprot".
iMod (own_update with "Hstates_r") as "[Hstates_r Hstates_frag_t']".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t' (● Some (Pending t) ⋅ ◯ Some (Pending t)));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hstates_frag_t'" as "[[Hstates_t'_frag Hstates_t'_frag'] Hstates_frag_t']".
iMod (states_meta_r_set with "Htts") as "#Hmeta_states_t'".
iModIntro. iSplitR "Hprot Hstates_frag_t' Hstates_t'_frag'"; last by iFrame.
iModIntro. iExists states_l, (<[t' := Pending t]> states_r).
iFrame. iFrame "#".
iSplitL "Hstates_r Hstates_r_frag Hstates_t'_frag".
{ iSplitL.
  - rewrite /public_states_r_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iSplit.
{ iPureIntro. split; first done. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iSplitL "HPublicLink_consistent_r".
{ iIntros (??) "%Hstates".
  rewrite lookup_insert in Hstates; case_decide; first naive_solver.
  by iApply "HPublicLink_consistent_r". }
iPureIntro. split; first done.
  move=> t1' ts1 Hprots Hts1.
  destruct (Hprots_r_cons _ _ Hprots Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_states_l_extend_2 E t t' :
  is_nonce t →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  states_token_l t -∗
  |={E}=> linked_in_l t t' ∗
          pending_in_l t t'.
Proof.
move=> /is_nonceP [a ->].
iIntros (HE) "#(_ & _ & Hinv) Htt".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  ([Hstates_l Hstates_l_frag] & Hstates_r & #Hmeta_states_l & #Hmeta_states_r) &
                  ([Hprots_l Hprots_l_frag] & Hprots_r & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & [HPublicLink_consistent HPublicLink_consistent_r] &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_l_fresh states_l (TNonce a) with "Hmeta_states_l Htt") as "%Hfresh".
iMod (own_update with "Hstates_l") as "[Hstates_l Hstates_frag_t]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ (TNonce a) (● Some (Pending t') ⋅ ◯ Some (Pending t')));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hstates_frag_t" as "[[Hstates_t_frag Hstates_t_frag'] Hstates_frag_t]".
iMod (states_meta_l_set with "Htt") as "#Hmeta_states_t".
iModIntro. iSplitR "Hstates_frag_t Hstates_t_frag'"; last by iFrame.
iModIntro. iExists (<[TNonce a := Pending t']> states_l), states_r, prots_l, prots_r.
iFrame. iFrame "#".
iSplitL "Hstates_l Hstates_l_frag Hstates_t_frag".
{ iSplitL.
  - rewrite /public_states_l_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iSplit.
{ iPureIntro. split; last done. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iSplitL "HPublicLink_consistent".
{ iIntros (??) "%Hstates".
  rewrite lookup_insert in Hstates; case_decide; first naive_solver.
  by iApply "HPublicLink_consistent". }
iPureIntro. split; last done.
move=> t1 ts1 Hprots Hts1.
destruct (Hprots_l_cons _ _ Hprots Hts1) as (? & ? & ?).
do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_states_r_extend_2 E t t' :
  is_nonce t' →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  states_token_r t' -∗
  |={E}=> linked_in_r t t' ∗
          pending_in_r t t'.
Proof.
move=> /is_nonceP [a' ->].
iIntros (HE) "#(_ & _ & Hinv) Htts".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  (Hstates_l & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  (Hprots_l & [Hprots_r Hprots_r_frag] & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & [HPublicLink_consistent HPublicLink_consistent_r] &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_r_fresh states_r (TNonce a') with "Hmeta_states_r Htts") as "%Hfresh".
iMod (own_update with "Hstates_r") as "[Hstates_r Hstates_frag_t']".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ (TNonce a') (● Some (Pending t) ⋅ ◯ Some (Pending t)));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hstates_frag_t'" as "[[Hstates_t'_frag Hstates_t'_frag'] Hstates_frag_t']".
iMod (states_meta_r_set with "Htts") as "#Hmeta_states_t'".
iModIntro. iSplitR "Hstates_frag_t' Hstates_t'_frag'"; last by iFrame.
iModIntro. iExists states_l, (<[TNonce a' := Pending t]> states_r), prots_l, prots_r.
iFrame. iFrame "#".
iSplitL "Hstates_r Hstates_r_frag Hstates_t'_frag".
{ iSplitL.
  - rewrite /public_states_r_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iSplit.
{ iPureIntro. split; first done. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iSplitL "HPublicLink_consistent_r".
{ iIntros (??) "%Hstates".
  rewrite lookup_insert in Hstates; case_decide; first naive_solver.
  by iApply "HPublicLink_consistent_r". }
iPureIntro. split; first done.
  move=> t1' ts1 Hprots Hts1.
  destruct (Hprots_r_cons _ _ Hprots Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma linked_extend E t t' tsub t'sub :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_by_subterm_l t tsub -∗
  protected_by_subterm_r t' t'sub -∗
  states_token_l t -∗
  states_token_r t' -∗
  |={E}=> protected_by_subterm_l t tsub ∗ protected_by_subterm_r t' t'sub ∗
          linked t t' ∗
          pending_in_l t t' ∗
          pending_in_r t t'.
Proof.
iIntros (HE) "#Hctx Hprot Hprot1 Htt Htts".
iPoseProof (public_states_l_extend t t' with "Hctx Hprot Htt") as ">[? [??]]"=> //.
iPoseProof (public_states_r_extend t t' with "Hctx Hprot1 Htts") as ">[? [??]]"=> //.
rewrite /linked.
by iFrame.
Qed.

Lemma linked_extend_2 E t t' t'sub :
  is_nonce t →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_by_subterm_r t' t'sub -∗
  states_token_l t -∗
  states_token_r t' -∗
  |={E}=> protected_by_subterm_r t' t'sub ∗
          linked t t' ∗
          pending_in_l t t' ∗
          pending_in_r t t'.
Proof.
iIntros (Hnonce HE) "#Hctx Hprot Htt Htts".
iPoseProof (public_states_l_extend_2 t' Hnonce with "Hctx Htt") as ">[? ?]"=> //.
iPoseProof (public_states_r_extend t t' with "Hctx Hprot Htts") as ">[? [??]]"=> //.
rewrite /linked.
by iFrame.
Qed.

Lemma linked_extend_3 E t t' tsub :
  is_nonce t' →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_by_subterm_l t tsub -∗
  states_token_l t -∗
  states_token_r t' -∗
  |={E}=> protected_by_subterm_l t tsub ∗
          linked t t' ∗
          pending_in_l t t' ∗
          pending_in_r t t'.
Proof.
iIntros (Hnonce' HE) "#Hctx Hprot Htt Htts".
iPoseProof (public_states_l_extend t t' with "Hctx Hprot Htt") as ">[? [??]]"=> //.
iPoseProof (public_states_r_extend_2 t Hnonce' with "Hctx Htts") as ">[? ?]"=> //.
rewrite /linked.
by iFrame.
Qed.

Lemma linked_extend_4 E t t' :
  is_nonce t →
  is_nonce t' →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  states_token_l t -∗
  states_token_r t' -∗
  |={E}=> linked t t' ∗
          pending_in_l t t' ∗
          pending_in_r t t'.
Proof.
iIntros (Hnonce Hnonce' HE) "#Hctx Htt Htts".
iPoseProof (public_states_l_extend_2 t' Hnonce with "Hctx Htt") as ">[? ?]"=> //.
iPoseProof (public_states_r_extend_2 t Hnonce' with "Hctx Htts") as ">[? ?]"=> //.
rewrite /linked.
by iFrame.
Qed.

Lemma public_lock_Secret_l E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  pending_in_l t t' -∗
  |={E}=> secret_in_l t.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hl_frac".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  ([Hstates_l Hstates_l_frag] & Hstates_r & #Hmeta_states_l & #Hmeta_states_r) &
                  Hprots &
                  [%HPending_l %HPending_r] & [HPublicLink_consistent HPublicLink_consistent_r] &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_l_lookup with "Hstates_l Hl_frac") as "%Hpltt'".
iDestruct (big_sepM_delete _ _ t _ Hpltt' with "Hstates_l_frag") as "[Hl_frac2 Hstates_l_frag]".
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
iModIntro. iExists (<[t := Secret]> states_l), states_r, prots_l, prots_r.
rewrite /public_inv.
iFrame. iFrame "#".
iSplitL "Hstates_l Hstates_l_frag".
{ rewrite /public_states_l_auth fmap_insert big_sepM_insert_delete dom_insert_lookup_L=> //.
  iFrame. iFrame "#". }
iSplit.
{ iPureIntro. split; last done. move=> t1 st Hstates Hst.
  rewrite lookup_insert in Hstates; case_decide; last by eapply HPending_l.
  simplify_eq. exact: (HPending_l _ _ Hpltt' I). }
iSplitL "HPublicLink_consistent".
{ iIntros (??) "%Hstates".
  rewrite lookup_insert in Hstates; case_decide; first naive_solver.
  by iApply "HPublicLink_consistent". }
iPureIntro. split; last done.
move=> t1 ts1 Hprots Hts1.
destruct (Hprots_l_cons _ _ Hprots Hts1) as (? & ? & ?).
do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_lock_Secret_r E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  pending_in_r t t' -∗
  |={E}=> secret_in_r t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hr_frac".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  (Hstates_l & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  Hprots &
                  [%HPending_l %HPending_r] & [HPublicLink_consistent HPublicLink_consistent_r] &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_r_lookup with "Hstates_r Hr_frac") as "%Hprtt'".
iDestruct (big_sepM_delete _ _ t' _ Hprtt' with "Hstates_r_frag") as "[Hr_frac2 Hstates_r_frag]".
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
iModIntro. iExists states_l, (<[t' := Secret]> states_r), prots_l, prots_r.
rewrite /public_inv.
iFrame. iFrame "#".
iSplitL "Hstates_r Hstates_r_frag".
{ rewrite /public_states_r_auth fmap_insert big_sepM_insert_delete dom_insert_lookup_L=> //.
  iFrame. iFrame "#". }
iSplit.
{ iPureIntro. split; first done. move=> t1' st Hstates Hst.
  rewrite lookup_insert in Hstates; case_decide; last by eapply HPending_r.
  simplify_eq. exact: (HPending_r _ _ Hprtt' I). }
iSplitL "HPublicLink_consistent_r".
{ iIntros (??) "%Hstates".
  rewrite lookup_insert in Hstates; case_decide; first naive_solver.
  by iApply "HPublicLink_consistent_r". }
iPureIntro. split; first done.
move=> t1' ts1 Hprots Hts1.
destruct (Hprots_r_cons _ _ Hprots Hts1) as (? & ? & ?).
do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_secret_l E t tsub :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_by_subterm_l t tsub -∗
  states_token_l t -∗
  |={E}=> protected_by_subterm_l t tsub ∗ secret_in_l t.
Proof.
iIntros (HE) "#Hctx Hprot Htt".
iMod (public_states_l_extend t t with "Hctx Hprot Htt") as "(Hprot & _ & Hpend)"=> //.
iMod (public_lock_Secret_l with "Hctx Hpend") as "#?"=> //.
by iFrame.
Qed.

Lemma public_secret_r E t' t'sub :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_by_subterm_r t' t'sub -∗
  states_token_r t' -∗
  |={E}=> protected_by_subterm_r t' t'sub ∗ secret_in_r t'.
Proof.
iIntros (HE) "#Hctx Hprot Htts".
iMod (public_states_r_extend t' t' with "Hctx Hprot Htts") as "(Hprot & _ & Hpend)"=> //.
iMod (public_lock_Secret_r with "Hctx Hpend") as "#?"=> //.
by iFrame.
Qed.

Lemma public_secret_l_2 E t :
  is_nonce t →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  states_token_l t -∗
  |={E}=> secret_in_l t.
Proof.
iIntros (Hnonce HE) "#Hctx Htt".
iMod (public_states_l_extend_2 t Hnonce with "Hctx Htt") as "[_ Hpend]"=> //.
by iMod (public_lock_Secret_l with "Hctx Hpend") as "#?".
Qed.

Lemma public_secret_r_2 E t' :
  is_nonce t' →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  states_token_r t' -∗
  |={E}=> secret_in_r t'.
Proof.
iIntros (Hnonce' HE) "#Hctx Htts".
iMod (public_states_r_extend_2 t' Hnonce' with "Hctx Htts") as "[_ Hpend]"=> //.
by iMod (public_lock_Secret_r with "Hctx Hpend") as "#?".
Qed.

(** You will probably need a custom version of this lemma tailored to the
declassification you want to attempt.

For example, say you have [(nonce, msg) ↦ Pending (nonce', msg')], where
[PUB⟨msg, msg'⟩], [prots_l !! nonce = {[ (nonce, msg) ]}] and
[prots_r !! nonce' = {[ (nonce', msg') ]}].

When trying to change it to [(nonce, msg) ↦ PublicLink (nonce', msg')], proving
the precondition
[[
publicly_linked (nonce, msg) (nonce', msg') -∗ PUB⟨(nonce, msg), (nonce', msg')⟩
]]
will require that you have [publicly_linked nonce nonce'] in the recursive
case.

But to get that, you will need to show that [prots_l !! nonce = ∅] and
[prots_r !! nonce' = ∅]. Since [(nonce, msg)] and [(nonce', msg')] can have no
other protectors, you will need to transition them to [PublicLink], which will
require you to prove [PUB⟨(nonce, msg), (nonce', msg')⟩]. This is circular.

To get around this, you should open the invariant and do all of the
transitions at once. This depends on the structure of the terms you are trying
to declassify and the nature of the recursive prots chain, so you need to come
up with your own custom lemma. Feel free to use these lemmas as templates.

If the declassification is deterministic, you can directly construct
[t ↦ PublicLink t'] from the tokens instead of going through [t ↦ Pending t']
first ([public_extend]).

Since [publicly_linked t t' → linked t t'], you can use it to prove [PUB]. *)
Lemma public_lock_PublicLink E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  (publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  protects_superterms_l t ∅ -∗
  protects_superterms_r t' ∅ -∗
  pending_in_l t t' -∗
  pending_in_r t t' -∗
  |={E}=> publicly_linked t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hlink_pub Hprot Hprot1 Hl_frac Hr_frac".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  ([Hstates_l Hstates_l_frag] & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  ([Hprots_l Hprots_l_frag] & [Hprots_r Hprots_r_frag] & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & [HPublicLink_consistent HPublicLink_consistent_r] &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_l_lookup with "Hstates_l Hl_frac") as "%Hpltt'".
iPoseProof (public_states_r_lookup with "Hstates_r Hr_frac") as "%Hprtt'".
iPoseProof (public_prots_l_lookup_2 with "Hprots_l Hprot") as "%Hfltts".
iPoseProof (public_prots_r_lookup_2 with "Hprots_r Hprot1") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ t _ Hpltt' with "Hstates_l_frag") as "[Hl_frac2 Hstates_l_frag]".
iDestruct (big_sepM_delete _ _ t' _ Hprtt' with "Hstates_r_frag") as "[Hr_frac2 Hstates_r_frag]".
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
iModIntro. iSplitL; last by iFrame "#".
iModIntro. iExists (<[t := PublicLink t']> states_l), (<[t' := PublicLink t]> states_r), prots_l, prots_r.
rewrite /public_inv /public_states_l_auth /public_states_r_auth.
iFrame. iFrame "#".
iSplitL "Hstates_l Hstates_l_frag Hstates_r Hstates_r_frag".
{ iSplitL "Hstates_l Hstates_l_frag"; last iSplitL "Hstates_r Hstates_r_frag".
  - rewrite /public_states_l_auth.
    rewrite fmap_insert big_sepM_insert_delete.
    iFrame.
  - rewrite /public_states_r_auth.
    rewrite fmap_insert big_sepM_insert_delete.
    iFrame.
  - rewrite !dom_insert_lookup_L=> //.
    iFrame "#". }
iSplit.
{ iPureIntro. split.
  - move=> ??. rewrite lookup_insert; case_decide; naive_solver.
  - move=> ??. rewrite lookup_insert; case_decide; naive_solver. }
iDestruct ("Hlink_pub" with "[]") as "#Hpub_tt'"; first by iFrame "#".
iSplitL "HPublicLink_consistent HPublicLink_consistent_r".
{ try rewrite /public_PublicLink_consistent. iSplitL "HPublicLink_consistent".
  - iIntros (??) "%Hstates".
    rewrite lookup_insert in Hstates; case_decide; subst.
    + by injection Hstates as <-.
    + by iApply "HPublicLink_consistent".
  - iIntros (??) "%Hstates".
    rewrite lookup_insert in Hstates; case_decide; subst.
    + by injection Hstates as <-.
    + by iApply "HPublicLink_consistent_r". }
iPureIntro. split.
- move=> t1 ts1 Hprots Hts1.
  destruct (Hprots_l_cons _ _ Hprots Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
- move=> t1' ts1 Hprots Hts1.
  destruct (Hprots_r_cons _ _ Hprots Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_lock_PublicLink_l E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  (publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  protects_superterms_l t ∅ -∗
  protects_superterms_r t' ∅ -∗
  pending_in_l t t' -∗
  states_token_r t' -∗
  |={E}=> publicly_linked t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hlink_pub Hprot Hprot1 Hl_frac Htts".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  ([Hstates_l Hstates_l_frag] & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  ([Hprots_l Hprots_l_frag] & [Hprots_r Hprots_r_frag] & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & [HPublicLink_consistent HPublicLink_consistent_r] &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_l_lookup with "Hstates_l Hl_frac") as "%Hpltt'".
iPoseProof (public_states_r_fresh states_r t' with "Hmeta_states_r Htts") as "%Hfresh".
iPoseProof (public_prots_l_lookup_2 with "Hprots_l Hprot") as "%Hfltts".
iPoseProof (public_prots_r_lookup_2 with "Hprots_r Hprot1") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ t _ Hpltt' with "Hstates_l_frag") as "[Hl_frac2 Hstates_l_frag]".
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
iModIntro. iSplitL; last by iFrame "#".
iModIntro. iExists (<[t := PublicLink t']> states_l), (<[t' := PublicLink t]> states_r), prots_l, prots_r.
rewrite /public_inv /public_states_l_auth /public_states_r_auth.
iFrame. iFrame "#".
iSplitL "Hstates_l Hstates_l_frag Hstates_r Hstates_r_frag".
{ iSplitL "Hstates_l Hstates_l_frag"; last iSplitL "Hstates_r Hstates_r_frag".
  - rewrite /public_states_l_auth fmap_insert.
    rewrite big_sepM_insert_delete /=.
    iFrame.
  - rewrite /public_states_r_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite (dom_insert_lookup_L states_l)=> //.
    rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iSplit.
{ iPureIntro. split.
  - move=> ??. rewrite lookup_insert; case_decide; naive_solver.
  - move=> ??. rewrite lookup_insert; case_decide; naive_solver. }
iDestruct ("Hlink_pub" with "[]") as "#Hpub_tt'"; first by iFrame "#".
iSplitL "HPublicLink_consistent HPublicLink_consistent_r".
{ try rewrite /public_PublicLink_consistent. iSplitL "HPublicLink_consistent".
  - iIntros (??) "%Hstates".
    rewrite lookup_insert in Hstates; case_decide; subst.
    + by injection Hstates as <-.
    + by iApply "HPublicLink_consistent".
  - iIntros (??) "%Hstates".
    rewrite lookup_insert in Hstates; case_decide; subst.
    + by injection Hstates as <-.
    + by iApply "HPublicLink_consistent_r". }
iPureIntro. split.
- move=> t1 ts1 Hprots Hts1.
  destruct (Hprots_l_cons _ _ Hprots Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
- move=> t1' ts1 Hprots Hts1.
  destruct (Hprots_r_cons _ _ Hprots Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_lock_PublicLink_r E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  (publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  protects_superterms_l t ∅ -∗
  protects_superterms_r t' ∅ -∗
  states_token_l t -∗
  pending_in_r t t' -∗
  |={E}=> publicly_linked t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hlink_pub Hprot Hprot1 Htt Hr_frac".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  ([Hstates_l Hstates_l_frag] & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  ([Hprots_l Hprots_l_frag] & [Hprots_r Hprots_r_frag] & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & [HPublicLink_consistent HPublicLink_consistent_r] &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_l_fresh states_l t with "Hmeta_states_l Htt") as "%Hfresh".
iPoseProof (public_states_r_lookup with "Hstates_r Hr_frac") as "%Hprtt'".
iPoseProof (public_prots_l_lookup_2 with "Hprots_l Hprot") as "%Hfltts".
iPoseProof (public_prots_r_lookup_2 with "Hprots_r Hprot1") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ t' _ Hprtt' with "Hstates_r_frag") as "[Hr_frac2 Hstates_r_frag]".
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
iModIntro. iSplitL; last by iFrame "#".
iModIntro. iExists (<[t := PublicLink t']> states_l), (<[t' := PublicLink t]> states_r), prots_l, prots_r.
rewrite /public_inv /public_states_l_auth /public_states_r_auth.
iFrame. iFrame "#".
iSplitL "Hstates_l Hstates_l_frag Hstates_r Hstates_r_frag".
{ iSplitL "Hstates_l Hstates_l_frag"; last iSplitL "Hstates_r Hstates_r_frag".
  - rewrite /public_states_l_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite /public_states_r_auth fmap_insert.
    rewrite big_sepM_insert_delete /=.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    rewrite dom_insert_lookup_L => //.
    iFrame "#". }
iSplit.
{ iPureIntro. split.
  - move=> ??. rewrite lookup_insert; case_decide; naive_solver.
  - move=> ??. rewrite lookup_insert; case_decide; naive_solver. }
iDestruct ("Hlink_pub" with "[]") as "#Hpub_tt'"; first by iFrame "#".
iSplitL "HPublicLink_consistent HPublicLink_consistent_r".
{ try rewrite /public_PublicLink_consistent. iSplitL "HPublicLink_consistent".
  - iIntros (??) "%Hstates".
    rewrite lookup_insert in Hstates; case_decide; subst.
    + by injection Hstates as <-.
    + by iApply "HPublicLink_consistent".
  - iIntros (??) "%Hstates".
    rewrite lookup_insert in Hstates; case_decide; subst.
    + by injection Hstates as <-.
    + by iApply "HPublicLink_consistent_r". }
iPureIntro. split.
- move=> t1 ts1 Hprots Hts1.
  destruct (Hprots_l_cons _ _ Hprots Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
- move=> t1' ts1 Hprots Hts1.
  destruct (Hprots_r_cons _ _ Hprots Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_extend E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  (publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  protects_superterms_l t ∅ -∗
  protects_superterms_r t' ∅ -∗
  states_token_l t -∗
  states_token_r t' -∗
  |={E}=> publicly_linked t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hlink_pub Hprot Hprot1 Htt Htts".
iInv "Hinv" as ">(%states_l & %states_r & %prots_l & %prots_r &
                  ([Hstates_l Hstates_l_frag] & [Hstates_r Hstates_r_frag] & #Hmeta_states_l & #Hmeta_states_r) &
                  ([Hprots_l Hprots_l_frag] & [Hprots_r Hprots_r_frag] & #Hmeta_prots_l & #Hmeta_prots_r) &
                  [%HPending_l %HPending_r] & [HPublicLink_consistent HPublicLink_consistent_r] &
                  [%Hprots_l_cons %Hprots_r_cons])".
iPoseProof (public_states_l_fresh states_l t with "Hmeta_states_l Htt") as "%Hfresh_l".
iPoseProof (public_states_r_fresh states_r t' with "Hmeta_states_r Htts") as "%Hfresh_r".
iPoseProof (public_prots_l_lookup_2 with "Hprots_l Hprot") as "%Hfltts".
iPoseProof (public_prots_r_lookup_2 with "Hprots_r Hprot1") as "%Hfrt'ts".
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
iModIntro. iSplitL; last by iFrame "#".
iModIntro. iExists (<[t := PublicLink t']> states_l), (<[t' := PublicLink t]> states_r), prots_l, prots_r.
rewrite /public_inv /public_states_l_auth /public_states_r_auth.
iFrame. iFrame "#".
iSplitL "Hstates_l Hstates_l_frag Hstates_r Hstates_r_frag".
{ iSplitL "Hstates_l Hstates_l_frag"; last iSplitL "Hstates_r Hstates_r_frag".
  - rewrite /public_states_l_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite /public_states_r_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite !dom_insert_L.
    rewrite !big_sepS_insert; try by apply not_elem_of_dom.
    iFrame "#". }
iSplit.
{ iPureIntro. split.
  - move=> ??. rewrite lookup_insert; case_decide; naive_solver.
  - move=> ??. rewrite lookup_insert; case_decide; naive_solver. }
iDestruct ("Hlink_pub" with "[]") as "#Hpub_tt'"; first by iFrame "#".
iSplitL "HPublicLink_consistent HPublicLink_consistent_r".
{ try rewrite /public_PublicLink_consistent. iSplitL "HPublicLink_consistent".
  - iIntros (??) "%Hstates".
    rewrite lookup_insert in Hstates; case_decide; subst.
    + by injection Hstates as <-.
    + by iApply "HPublicLink_consistent".
  - iIntros (??) "%Hstates".
    rewrite lookup_insert in Hstates; case_decide; subst.
    + by injection Hstates as <-.
    + by iApply "HPublicLink_consistent_r". }
iPureIntro. split.
- move=> t1 ts1 Hprots Hts1.
  destruct (Hprots_l_cons _ _ Hprots Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
- move=> t1' ts1 Hprots Hts1.
  destruct (Hprots_r_cons _ _ Hprots Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

End StatesUpdates.

End PublicUpdates.
