(** Shortcuts for the ghost state updates of [core/public/updates.v].  Each lemma
  spends the relational token of a term, the part of the ghost state that
  decides how the two runs treat it.  A fresh term that is not a ciphertext
  takes it from its own token, through [term_token_rel_token_l]; a ciphertext
  takes it from the never-sealed tokens of the seed of its key, through
  [never_sealed_under_rel_token].  The right hand side lemmas are identical,
  but use primed names and tokens of the specification side.

  - [public_rel_fresh_l] registers a term in the flow map, protecting nothing
    yet, and gives back the part of the token that later map updates want.
  - Protecting a superterm.  Both lemmas spend the token of the protecting
    term and return the protection fact for the superterm.
    - [public_rel_protect_nonce_l] is for a protecting term that is a nonce,
      typically the start of a chain nonce → payload → tagged payload.
    - [public_rel_protect_step_l] is for a protecting term that is itself
      protected, typically the next link of such a chain.
  - Making a term secret.
    - [public_rel_secret_seals_l] is for a nonce, typically the seed of a key.
      It spends the whole token of the nonce, and besides marking it secret it
      gives back its never-sealed tokens, registers it in the flow map so that
      it can protect the key built from it, and gives back the part of the
      token outside the relational namespaces for other uses such as
      per-protocol metadata.
    - [public_rel_secret_step_l] is for a term built on top of a secret one,
      typically the signing key built from its seed.  The secret subterm
      protects it, so nothing else is needed.
  - [public_rel_link] links two terms protected on their respective sides,
    which is what the payload of an honest encryption needs.
  - [public_rel_publish] makes two fresh terms publicly linked and publicly
    related, given a proof that linking them is enough for them to be
    publicly related.  [public_rel_seal] does the same for two ciphertexts,
    spending the never-sealed tokens of the seeds of their keys. *)

From reloc Require Import reloc.
From cryptis Require Import cryptis.
From cryptis.hyper.core Require Import term_meta_spec public.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Updates.

Context `{!relocG Σ, !public_relGS Σ}.

Implicit Types (t tsub tsup : term) (E : coPset).

Lemma public_rel_fresh_l E t :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  rel_token_l t ={E}=∗
  protects_superterms_l t ∅ ∗ map_token_l t.
Proof.
iIntros (?) "#ctx tok". iDestruct (rel_token_l_split with "tok") as "[$ flow]".
by iApply (public_rel_flow_l_extend with "ctx flow").
Qed.

Lemma public_rel_fresh_r E t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  rel_token_r t' ={E}=∗
  protects_superterms_r t' ∅ ∗ map_token_r t'.
Proof.
iIntros (?) "#ctx tok". iDestruct (rel_token_r_split with "tok") as "[$ flow]".
by iApply (public_rel_flow_r_extend with "ctx flow").
Qed.

Lemma public_rel_protect_nonce_l E t tsup :
  is_nonce t →
  is_immediate_subterm t tsup →
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  rel_token_l t ={E}=∗
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
  rel_token_r t' ={E}=∗
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
  rel_token_l t ={E}=∗
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
  rel_token_r t' ={E}=∗
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
  secret_in_l t ∗ term_token t (↑sealN) ∗ protects_superterms_l t ∅ ∗
  term_token t (⊤ ∖ ↑hypercryptisN).
Proof.
iIntros (Ht HE) "#ctx tok".
iDestruct (term_token_rel_token_l with "tok") as "(tok & $ & $)";
  first exact: is_nonce_not_TSeal.
iDestruct (rel_token_l_split with "tok") as "[map flow]".
iMod (public_rel_flow_l_extend with "ctx flow") as "$"; first done.
by iApply (public_rel_secret_l_2 Ht HE with "ctx map").
Qed.

Lemma public_rel_secret_seals_r E t' :
  is_nonce t' →
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token_spec t' ⊤ ={E}=∗
  secret_in_r t' ∗ term_token_spec t' (↑sealN) ∗
  protects_superterms_r t' ∅ ∗ term_token_spec t' (⊤ ∖ ↑hypercryptisN).
Proof.
iIntros (Ht HE) "#ctx tok".
iDestruct (term_token_rel_token_r with "tok") as "(tok & $ & $)";
  first exact: is_nonce_not_TSeal.
iDestruct (rel_token_r_split with "tok") as "[map flow]".
iMod (public_rel_flow_r_extend with "ctx flow") as "$"; first done.
by iApply (public_rel_secret_r_2 Ht HE with "ctx map").
Qed.

Lemma public_rel_secret_step_l E t tsup :
  is_immediate_subterm t tsup →
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  secret_in_l t -∗
  protects_superterms_l t ∅ -∗
  rel_token_l tsup ={E}=∗
  secret_in_l tsup ∗ protects_superterms_l tsup ∅.
Proof.
iIntros (Hsup HE) "#ctx #sec prot tok".
iMod (public_rel_flow_l_grow_2 (tsup:=tsup) with "ctx prot sec") as "[_ by]";
  [done | apply not_elem_of_empty | done |].
iDestruct (rel_token_l_split with "tok") as "[map flow]".
iMod (public_rel_flow_l_extend with "ctx flow") as "$"; first done.
by iMod (public_rel_secret_l with "ctx by map") as "[_ $]".
Qed.

Lemma public_rel_secret_step_r E t' t'sup :
  is_immediate_subterm t' t'sup →
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  secret_in_r t' -∗
  protects_superterms_r t' ∅ -∗
  rel_token_r t'sup ={E}=∗
  secret_in_r t'sup ∗ protects_superterms_r t'sup ∅.
Proof.
iIntros (Hsup HE) "#ctx #sec prot tok".
iMod (public_rel_flow_r_grow_2 (t'sup:=t'sup) with "ctx prot sec") as "[_ by]";
  [done | apply not_elem_of_empty | done |].
iDestruct (rel_token_r_split with "tok") as "[map flow]".
iMod (public_rel_flow_r_extend with "ctx flow") as "$"; first done.
by iMod (public_rel_secret_r with "ctx by map") as "[_ $]".
Qed.

Lemma public_rel_link E {t t' tsub t'sub} :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  protected_by_subterm_l t tsub -∗
  protected_by_subterm_r t' t'sub -∗
  rel_token_l t -∗
  rel_token_r t' ={E}=∗
  linked t t'.
Proof.
iIntros (HE) "#ctx by by' tok tok'".
iDestruct (rel_token_l_split with "tok") as "[map _]".
iDestruct (rel_token_r_split with "tok'") as "[map' _]".
by iMod (linked_extend t t' tsub t'sub HE with "ctx by by' map map'") as "(_ & _ & $ & _)".
Qed.

Lemma public_rel_publish E {t t'} :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  □ (publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  rel_token_l t -∗
  rel_token_r t' ={E}=∗
  publicly_linked t t' ∗ PUB⟨t, t'⟩.
Proof.
iIntros (HE) "#ctx #wand tok tok'".
iMod (public_rel_fresh_l t HE with "ctx tok") as "[prot map]".
iMod (public_rel_fresh_r t' HE with "ctx tok'") as "[prot' map']".
iMod (public_rel_extend t t' HE with "ctx wand prot prot' map map'") as "#link".
iModIntro. iSplit => //. by iApply "wand".
Qed.

Lemma public_rel_seal E kt s kt' s' t t' Ek Ek' :
  ↑cryptisN ⊆ E →
  ↑seal_ns (TKey kt s) t ⊆ Ek →
  ↑seal_ns (TKey kt' s') t' ⊆ Ek' →
  cryptis_rel_ctx -∗
  □ (publicly_linked (TSeal (TKey kt s) t) (TSeal (TKey kt' s') t') -∗
     PUB⟨TSeal (TKey kt s) t, TSeal (TKey kt' s') t'⟩) -∗
  never_sealed_under s s' Ek Ek' ={E}=∗
  publicly_linked (TSeal (TKey kt s) t) (TSeal (TKey kt' s') t') ∗
  PUB⟨TSeal (TKey kt s) t, TSeal (TKey kt' s') t'⟩ ∗
  never_sealed_under s s' (Ek ∖ ↑seal_ns (TKey kt s) t) (Ek' ∖ ↑seal_ns (TKey kt' s') t').
Proof.
iIntros (HE sub sub') "#ctx #wand ns".
rewrite (never_sealed_under_rel_token sub sub').
iDestruct "ns" as "(tok & tok' & $)".
by iApply (public_rel_publish HE with "ctx wand tok tok'").
Qed.

End Updates.
