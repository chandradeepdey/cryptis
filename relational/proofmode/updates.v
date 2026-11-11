(** Shortcuts for the ghost state updates of [core/public/updates.v].  Each lemma
  spends the public token of a term, the part of the ghost state that
  decides how the two runs treat it.  A fresh term that is not a ciphertext
  takes it from its own token, through [term_token_public_token_l]; a ciphertext
  takes it from the never-sealed tokens of the seed of its key, through
  [never_sealed_under_public_token].  The right hand side lemmas are identical,
  but use primed names and tokens of the specification side.

  - [public_fresh_l] registers a term in the prots map, protecting nothing
    yet, and gives back the part of the token that later states updates
    want.
  - Protecting a superterm.  Both lemmas spend the token of the protecting
    term and return the protection fact for the superterm.
    - [public_protect_nonce_l] is for a protecting term that is a nonce,
      typically the start of a chain nonce → payload → tagged payload.
    - [public_protect_step_l] is for a protecting term that is itself
      protected, typically the next link of such a chain.
  - Making a term secret.
    - [public_secret_seals_l] is for a nonce, typically the seed of a key.
      It spends the whole token of the nonce, and besides marking it secret it
      gives back its never-sealed tokens, registers it in the prots map so that
      it can protect the key built from it, and gives back the part of the
      token outside the namespaces of its public token for other uses such as
      per-protocol metadata.
    - [public_secret_step_l] is for a term built on top of a secret one,
      typically the signing key built from its seed.  The secret subterm
      protects it, so nothing else is needed.
  - [public_link] links two terms protected on their respective sides,
    which is what the payload of an honest encryption needs.
  - [public_publish] makes two fresh terms publicly linked and related by
    [PUB], given a proof that linking them is enough for [PUB].
    [public_seal] does the same for two ciphertexts,
    spending the never-sealed tokens of the seeds of their keys. *)

From reloc Require Import reloc.
From cryptis Require Import cryptis.
From cryptis.hyper.core Require Import term_meta_spec public.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Updates.

Context `{!relocG Σ, !publicGS Σ}.

Implicit Types (t tsub tsup : term) (E : coPset).

Lemma public_fresh_l E t :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  public_token_l t ={E}=∗
  protects_superterms_l t ∅ ∗ states_token_l t.
Proof.
iIntros (?) "#ctx tok". iDestruct (public_token_l_split with "tok") as "[$ prots]".
by iApply (public_prots_l_extend with "ctx prots").
Qed.

Lemma public_fresh_r E t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  public_token_r t' ={E}=∗
  protects_superterms_r t' ∅ ∗ states_token_r t'.
Proof.
iIntros (?) "#ctx tok". iDestruct (public_token_r_split with "tok") as "[$ prots]".
by iApply (public_prots_r_extend with "ctx prots").
Qed.

Lemma public_protect_nonce_l E t tsup :
  is_nonce t →
  is_immediate_subterm t tsup →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  public_token_l t ={E}=∗
  protected_by_subterm_l tsup t.
Proof.
iIntros (Ht Hsup HE) "#ctx tok".
iMod (public_fresh_l t HE with "ctx tok") as "[prot states]".
by iMod (public_prots_l_grow_5 Ht HE Hsup with "ctx prot states") as "(_ & $ & _)".
Qed.

Lemma public_protect_nonce_r E t' t'sup :
  is_nonce t' →
  is_immediate_subterm t' t'sup →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  public_token_r t' ={E}=∗
  protected_by_subterm_r t'sup t'.
Proof.
iIntros (Ht Hsup HE) "#ctx tok".
iMod (public_fresh_r t' HE with "ctx tok") as "[prot states]".
by iMod (public_prots_r_grow_5 Ht HE Hsup with "ctx prot states") as "(_ & $ & _)".
Qed.

Lemma public_protect_step_l E t {tsub} tsup :
  is_immediate_subterm t tsup →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_by_subterm_l t tsub -∗
  public_token_l t ={E}=∗
  protected_by_subterm_l tsup t.
Proof.
iIntros (Hsup HE) "#ctx by tok".
iMod (public_fresh_l t HE with "ctx tok") as "[prot states]".
by iMod (public_prots_l_grow_3 tsub HE Hsup with "ctx by prot states")
  as "(_ & $ & _)".
Qed.

Lemma public_protect_step_r E t' {t'sub} t'sup :
  is_immediate_subterm t' t'sup →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_by_subterm_r t' t'sub -∗
  public_token_r t' ={E}=∗
  protected_by_subterm_r t'sup t'.
Proof.
iIntros (Hsup HE) "#ctx by tok".
iMod (public_fresh_r t' HE with "ctx tok") as "[prot states]".
by iMod (public_prots_r_grow_3 t'sub HE Hsup with "ctx by prot states")
  as "(_ & $ & _)".
Qed.

Lemma public_secret_seals_l E t :
  is_nonce t →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  term_token t ⊤ ={E}=∗
  secret_in_l t ∗ term_token t (↑sealN) ∗ protects_superterms_l t ∅ ∗
  term_token t (⊤ ∖ ↑hypercryptisN).
Proof.
iIntros (Ht HE) "#ctx tok".
iDestruct (term_token_public_token_l with "tok") as "(tok & $ & $)";
  first exact: is_nonce_not_TSeal.
iDestruct (public_token_l_split with "tok") as "[states prots]".
iMod (public_prots_l_extend with "ctx prots") as "$"; first done.
by iApply (public_secret_l_2 Ht HE with "ctx states").
Qed.

Lemma public_secret_seals_r E t' :
  is_nonce t' →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  term_token_spec t' ⊤ ={E}=∗
  secret_in_r t' ∗ term_token_spec t' (↑sealN) ∗
  protects_superterms_r t' ∅ ∗ term_token_spec t' (⊤ ∖ ↑hypercryptisN).
Proof.
iIntros (Ht HE) "#ctx tok".
iDestruct (term_token_public_token_r with "tok") as "(tok & $ & $)";
  first exact: is_nonce_not_TSeal.
iDestruct (public_token_r_split with "tok") as "[states prots]".
iMod (public_prots_r_extend with "ctx prots") as "$"; first done.
by iApply (public_secret_r_2 Ht HE with "ctx states").
Qed.

Lemma public_secret_step_l E t tsup :
  is_immediate_subterm t tsup →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  secret_in_l t -∗
  protects_superterms_l t ∅ -∗
  public_token_l tsup ={E}=∗
  secret_in_l tsup ∗ protects_superterms_l tsup ∅.
Proof.
iIntros (Hsup HE) "#ctx #sec prot tok".
iMod (public_prots_l_grow_2 (tsup:=tsup) with "ctx prot sec") as "[_ by]";
  [done | apply not_elem_of_empty | done |].
iDestruct (public_token_l_split with "tok") as "[states prots]".
iMod (public_prots_l_extend with "ctx prots") as "$"; first done.
by iMod (public_secret_l with "ctx by states") as "[_ $]".
Qed.

Lemma public_secret_step_r E t' t'sup :
  is_immediate_subterm t' t'sup →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  secret_in_r t' -∗
  protects_superterms_r t' ∅ -∗
  public_token_r t'sup ={E}=∗
  secret_in_r t'sup ∗ protects_superterms_r t'sup ∅.
Proof.
iIntros (Hsup HE) "#ctx #sec prot tok".
iMod (public_prots_r_grow_2 (t'sup:=t'sup) with "ctx prot sec") as "[_ by]";
  [done | apply not_elem_of_empty | done |].
iDestruct (public_token_r_split with "tok") as "[states prots]".
iMod (public_prots_r_extend with "ctx prots") as "$"; first done.
by iMod (public_secret_r with "ctx by states") as "[_ $]".
Qed.

Lemma public_link E {t t' tsub t'sub} :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_by_subterm_l t tsub -∗
  protected_by_subterm_r t' t'sub -∗
  public_token_l t -∗
  public_token_r t' ={E}=∗
  linked t t'.
Proof.
iIntros (HE) "#ctx by by' tok tok'".
iDestruct (public_token_l_split with "tok") as "[states _]".
iDestruct (public_token_r_split with "tok'") as "[states' _]".
by iMod (linked_extend t t' tsub t'sub HE with "ctx by by' states states'") as "(_ & _ & $ & _)".
Qed.

Lemma public_publish E {t t'} :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  □ (publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  public_token_l t -∗
  public_token_r t' ={E}=∗
  publicly_linked t t' ∗ PUB⟨t, t'⟩.
Proof.
iIntros (HE) "#ctx #wand tok tok'".
iMod (public_fresh_l t HE with "ctx tok") as "[prot states]".
iMod (public_fresh_r t' HE with "ctx tok'") as "[prot' states']".
iMod (public_extend t t' HE with "ctx wand prot prot' states states'") as "#link".
iModIntro. iSplit => //. by iApply "wand".
Qed.

Lemma public_seal E kt s kt' s' t t' Ek Ek' :
  ↑cryptisN ⊆ E →
  ↑seal_namespace (TKey kt s) t ⊆ Ek →
  ↑seal_namespace (TKey kt' s') t' ⊆ Ek' →
  hypercryptis_ctx -∗
  □ (publicly_linked (TSeal (TKey kt s) t) (TSeal (TKey kt' s') t') -∗
     PUB⟨TSeal (TKey kt s) t, TSeal (TKey kt' s') t'⟩) -∗
  never_sealed_under s s' Ek Ek' ={E}=∗
  publicly_linked (TSeal (TKey kt s) t) (TSeal (TKey kt' s') t') ∗
  PUB⟨TSeal (TKey kt s) t, TSeal (TKey kt' s') t'⟩ ∗
  never_sealed_under s s' (Ek ∖ ↑seal_namespace (TKey kt s) t) (Ek' ∖ ↑seal_namespace (TKey kt' s') t').
Proof.
iIntros (HE sub sub') "#ctx #wand ns".
rewrite (never_sealed_under_public_token sub sub').
iDestruct "ns" as "(tok & tok' & $)".
by iApply (public_publish HE with "ctx wand tok tok'").
Qed.

End Updates.
