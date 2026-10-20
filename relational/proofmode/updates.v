(** Shortcuts for the ghost state updates of [rel_inv_updates.v], for terms
  that have just been created and still hold their whole token.  Creating a
  term through [rel_mk_nonce_l] or [rel_mk_aenc_key_l] hands out one such
  token per term of the token set; the lemmas below spend it in the ways the
  case studies need, so that a proof never splits a token by hand.  The right
  hand side lemmas are identical, but use primed names and tokens of the
  specification side.

  - [public_rel_fresh_l] registers a term in the flow map, protecting nothing
    yet, and gives back the part of the token that later map updates want.
  - Protecting a superterm.  Both lemmas spend the token of the protecting
    term and return the protection fact for the superterm.
    + [public_rel_protect_nonce_l] is for a protecting term that is a nonce,
      typically the start of a chain nonce → payload → tagged payload.
    + [public_rel_protect_step_l] is for a protecting term that is itself
      protected, typically the next link of such a chain.
  - Making a term secret.
    + [public_rel_secret_seals_l] is for a nonce, typically the seed of a key.
      Besides marking it secret it allocates its seal set, registers it in
      the flow map so that it can protect the key built from it, and gives
      back the part of the token outside the relational namespaces for other
      uses such as per-protocol metadata.
    + [public_rel_secret_step_l] is for a term built on top of a secret one,
      typically the signing key built from its seed.  It spends the token of
      the new term and makes it secret in turn; the secret subterm protects
      it, so nothing else is needed.
  - [public_rel_link] links two terms protected on their respective sides,
    which is what the payload of an honest encryption needs.
  - [public_rel_publish] makes two fresh terms publicly linked and publicly
    related, given a proof that linking them is enough for them to be
    publicly related: public keys, ciphertexts and signatures all go through
    it. *)

From reloc Require Import reloc.
From cryptis Require Import lib cryptis.
From cryptis.hyper.core Require Import term_meta_spec rel rel_inv_updates.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Updates.

Context `{!relocG Σ, !public_relGS Σ}.

Implicit Types (t tsub tsup : term) (E : coPset).

Lemma public_rel_fresh_l E t :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token t ⊤ ={E}=∗
  protects_superterms_l t ∅ ∗ term_token t (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (?) "#ctx tok".
rewrite (term_token_difference t (↑cryptisN.@"public_rel".@"flow") ⊤) //.
iDestruct "tok" as "[flow tok]".
rewrite (term_token_difference t (↑cryptisN.@"public_rel".@"map")
           (⊤ ∖ ↑cryptisN.@"public_rel".@"flow")); last solve_ndisj.
iDestruct "tok" as "[map _]". iFrame "map".
by iApply (public_rel_flow_l_extend with "ctx flow").
Qed.

Lemma public_rel_fresh_r E t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token_spec t' ⊤ ={E}=∗
  protects_superterms_r t' ∅ ∗ term_token_spec t' (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (?) "#ctx tok".
rewrite (term_token_spec_difference t' (↑cryptisN.@"public_rel".@"flow") ⊤) //.
iDestruct "tok" as "[flow tok]".
rewrite (term_token_spec_difference t' (↑cryptisN.@"public_rel".@"map")
           (⊤ ∖ ↑cryptisN.@"public_rel".@"flow")); last solve_ndisj.
iDestruct "tok" as "[map _]". iFrame "map".
by iApply (public_rel_flow_r_extend with "ctx flow").
Qed.

Lemma public_rel_protect_nonce_l E t tsup :
  is_nonce t →
  is_immediate_subterm t tsup →
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token t ⊤ ={E}=∗
  protected_by_subterm_l tsup t.
Proof.
iIntros (Ht Hsup HE) "#ctx tok".
iMod (public_rel_fresh_l t HE with "ctx tok") as "[prot map]".
by iMod (public_rel_flow_l_grow_5 Ht HE Hsup with "ctx prot map") as "(_ & $ & _)".
Qed.

Lemma public_rel_protect_nonce_r E t' t'sup :
  is_nonce t' →
  is_immediate_subterm t' t'sup →
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token_spec t' ⊤ ={E}=∗
  protected_by_subterm_r t'sup t'.
Proof.
iIntros (Ht Hsup HE) "#ctx tok".
iMod (public_rel_fresh_r t' HE with "ctx tok") as "[prot map]".
by iMod (public_rel_flow_r_grow_5 Ht HE Hsup with "ctx prot map") as "(_ & $ & _)".
Qed.

Lemma public_rel_protect_step_l E t {tsub} tsup :
  is_immediate_subterm t tsup →
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  protected_by_subterm_l t tsub -∗
  term_token t ⊤ ={E}=∗
  protected_by_subterm_l tsup t.
Proof.
iIntros (Hsup HE) "#ctx by tok".
iMod (public_rel_fresh_l t HE with "ctx tok") as "[prot map]".
by iMod (public_rel_flow_l_grow_3 tsub HE Hsup with "ctx by prot map")
  as "(_ & $ & _)".
Qed.

Lemma public_rel_protect_step_r E t' {t'sub} t'sup :
  is_immediate_subterm t' t'sup →
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  protected_by_subterm_r t' t'sub -∗
  term_token_spec t' ⊤ ={E}=∗
  protected_by_subterm_r t'sup t'.
Proof.
iIntros (Hsup HE) "#ctx by tok".
iMod (public_rel_fresh_r t' HE with "ctx tok") as "[prot map]".
by iMod (public_rel_flow_r_grow_3 t'sub HE Hsup with "ctx by prot map")
  as "(_ & $ & _)".
Qed.

Lemma public_rel_secret_seals_l E t :
  is_nonce t →
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token t ⊤ ={E}=∗
  secret_in_l t ∗ seals_auth_l t ∅ ∗ protects_superterms_l t ∅ ∗
  term_token t (⊤ ∖ ↑cryptisN.@"public_rel").
Proof.
iIntros (Ht HE) "#ctx tok".
rewrite (term_token_difference t (↑cryptisN.@"public_rel") ⊤) //.
iDestruct "tok" as "[tok $]".
rewrite (term_token_difference t (↑cryptisN.@"public_rel".@"map")
           (↑cryptisN.@"public_rel")); last solve_ndisj.
iDestruct "tok" as "[map tok]".
rewrite (term_token_difference t (↑cryptisN.@"public_rel".@"flow")
           (↑cryptisN.@"public_rel" ∖ ↑cryptisN.@"public_rel".@"map")); last solve_ndisj.
iDestruct "tok" as "[flow tok]".
iMod (seals_auth_l_alloc with "tok") as "[$ _]"; first solve_ndisj.
iMod (public_rel_flow_l_extend with "ctx flow") as "$"; first done.
by iApply (public_rel_secret_l_2 Ht HE with "ctx map").
Qed.

Lemma public_rel_secret_seals_r E t' :
  is_nonce t' →
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token_spec t' ⊤ ={E}=∗
  secret_in_r t' ∗ seals_auth_r t' ∅ ∗ protects_superterms_r t' ∅ ∗
  term_token_spec t' (⊤ ∖ ↑cryptisN.@"public_rel").
Proof.
iIntros (Ht HE) "#ctx tok".
rewrite (term_token_spec_difference t' (↑cryptisN.@"public_rel") ⊤) //.
iDestruct "tok" as "[tok $]".
rewrite (term_token_spec_difference t' (↑cryptisN.@"public_rel".@"map")
           (↑cryptisN.@"public_rel")); last solve_ndisj.
iDestruct "tok" as "[map tok]".
rewrite (term_token_spec_difference t' (↑cryptisN.@"public_rel".@"flow")
           (↑cryptisN.@"public_rel" ∖ ↑cryptisN.@"public_rel".@"map")); last solve_ndisj.
iDestruct "tok" as "[flow tok]".
iMod (seals_auth_r_alloc with "tok") as "[$ _]"; first solve_ndisj.
iMod (public_rel_flow_r_extend with "ctx flow") as "$"; first done.
by iApply (public_rel_secret_r_2 Ht HE with "ctx map").
Qed.

Lemma public_rel_secret_step_l E t tsup :
  is_immediate_subterm t tsup →
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  secret_in_l t -∗
  protects_superterms_l t ∅ -∗
  term_token tsup ⊤ ={E}=∗
  secret_in_l tsup ∗ protects_superterms_l tsup ∅ ∗
  term_token tsup (⊤ ∖ ↑cryptisN.@"public_rel").
Proof.
iIntros (Hsup HE) "#ctx #sec prot tok".
iMod (public_rel_flow_l_grow_2 (tsup:=tsup) with "ctx prot sec") as "[_ by]";
  [done | apply not_elem_of_empty | done |].
rewrite (term_token_difference tsup (↑cryptisN.@"public_rel") ⊤) //.
iDestruct "tok" as "[tok $]".
rewrite (term_token_difference tsup (↑cryptisN.@"public_rel".@"map")
           (↑cryptisN.@"public_rel")); last solve_ndisj.
iDestruct "tok" as "[map tok]".
rewrite (term_token_difference tsup (↑cryptisN.@"public_rel".@"flow")
           (↑cryptisN.@"public_rel" ∖ ↑cryptisN.@"public_rel".@"map")); last solve_ndisj.
iDestruct "tok" as "[flow _]".
iMod (public_rel_flow_l_extend with "ctx flow") as "$"; first done.
by iMod (public_rel_secret_l with "ctx by map") as "[_ $]".
Qed.

Lemma public_rel_secret_step_r E t' t'sup :
  is_immediate_subterm t' t'sup →
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  secret_in_r t' -∗
  protects_superterms_r t' ∅ -∗
  term_token_spec t'sup ⊤ ={E}=∗
  secret_in_r t'sup ∗ protects_superterms_r t'sup ∅ ∗
  term_token_spec t'sup (⊤ ∖ ↑cryptisN.@"public_rel").
Proof.
iIntros (Hsup HE) "#ctx #sec prot tok".
iMod (public_rel_flow_r_grow_2 (t'sup:=t'sup) with "ctx prot sec") as "[_ by]";
  [done | apply not_elem_of_empty | done |].
rewrite (term_token_spec_difference t'sup (↑cryptisN.@"public_rel") ⊤) //.
iDestruct "tok" as "[tok $]".
rewrite (term_token_spec_difference t'sup (↑cryptisN.@"public_rel".@"map")
           (↑cryptisN.@"public_rel")); last solve_ndisj.
iDestruct "tok" as "[map tok]".
rewrite (term_token_spec_difference t'sup (↑cryptisN.@"public_rel".@"flow")
           (↑cryptisN.@"public_rel" ∖ ↑cryptisN.@"public_rel".@"map")); last solve_ndisj.
iDestruct "tok" as "[flow _]".
iMod (public_rel_flow_r_extend with "ctx flow") as "$"; first done.
by iMod (public_rel_secret_r with "ctx by map") as "[_ $]".
Qed.

Lemma public_rel_link E {t t' tsub t'sub} :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  protected_by_subterm_l t tsub -∗
  protected_by_subterm_r t' t'sub -∗
  term_token t ⊤ -∗
  term_token_spec t' ⊤ ={E}=∗
  linked t t'.
Proof.
iIntros (HE) "#ctx by by' tok tok'".
rewrite (term_token_difference t (↑cryptisN.@"public_rel".@"map") ⊤) //.
rewrite (term_token_spec_difference t' (↑cryptisN.@"public_rel".@"map") ⊤) //.
iDestruct "tok" as "[map _]". iDestruct "tok'" as "[map' _]".
by iMod (linked_extend t t' tsub t'sub HE with "ctx by by' map map'") as "(_ & _ & $ & _)".
Qed.

Lemma public_rel_publish E {t t'} :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  □ (publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  term_token t ⊤ -∗
  term_token_spec t' ⊤ ={E}=∗
  publicly_linked t t' ∗ PUB⟨t, t'⟩.
Proof.
iIntros (HE) "#ctx #wand tok tok'".
iMod (public_rel_fresh_l t HE with "ctx tok") as "[prot map]".
iMod (public_rel_fresh_r t' HE with "ctx tok'") as "[prot' map']".
iMod (public_rel_extend t t' HE with "ctx wand prot prot' map map'") as "#link".
iModIntro. iSplit => //. by iApply "wand".
Qed.

End Updates.
