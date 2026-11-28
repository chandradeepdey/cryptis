(** Shortcuts for the ghost state updates of [core/public/updates.v], from
  the tokens of fresh terms.  The right hand side lemmas are the same, on
  the specification side.

  - [protected_deposit_secret_l] and [protected_deposit_nonce_l] build what
    keeps a term hidden, from the tokens of the parts on a chain down to a
    secret term or a nonce.
  - [public_secret_nonce_l] makes a nonce secret, and [public_secret_step_l]
    a term built on a secret one.
  - [public_link] links two hidden terms.
  - [public_publish] makes two terms public and related.  [public_seal] does
    the same for ciphertexts, [public_seal_held] for ciphertexts that hold
    their keys back, and [public_seal_senc] for ciphertexts under symmetric
    keys. *)

From reloc Require Import reloc.
From cryptis Require Import cryptis.
From cryptis.hyper.core Require Import minted_spec term_meta_spec public.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Updates.

Context `{!relocG Σ, !publicGS Σ}.

Implicit Types (t tsub tsup troot t'sub t'sup t'root : term) (E : coPset).

#[local] Lemma public_token_l_holds_subterm t tsub :
  public_token_l tsub -∗ holds_subterm_l t tsub.
Proof.
iIntros "tok". iDestruct (public_token_l_split with "tok") as "(_ & prots & _)".
rewrite /prots_token_l /holds_subterm_l.
rewrite (term_token_difference _ (↑(home_of_term tsub).2.@"prots".@t));
  last solve_ndisj.
by iDestruct "prots" as "[$ _]".
Qed.

#[local] Lemma public_token_r_holds_subterm t' t'sub :
  public_token_r t'sub -∗ holds_subterm_r t' t'sub.
Proof.
iIntros "tok". iDestruct (public_token_r_split with "tok") as "(_ & prots & _)".
rewrite /prots_token_r /holds_subterm_r.
rewrite (term_token_spec_difference _ (↑(home_of_term t'sub).2.@"prots".@t'));
  last solve_ndisj.
by iDestruct "prots" as "[$ _]".
Qed.

Lemma protected_deposit_secret_l t path troot :
  subterm_path t path troot →
  ([∗ list] t1 ∈ path, public_token_l t1) -∗
  secret_in_l troot -∗
  protected_deposit_l t.
Proof.
iIntros (Hpath) "Htoks #Hsec". iRight. iExists path, troot.
iSplit; first done. iSplitL "Htoks"; last by iLeft.
iApply (big_sepL_impl with "Htoks").
iIntros "!>" (? t1 _) "tok". by iApply public_token_l_holds_subterm.
Qed.

Lemma protected_deposit_secret_r t' path t'root :
  subterm_path t' path t'root →
  ([∗ list] t1' ∈ path, public_token_r t1') -∗
  secret_in_r t'root -∗
  protected_deposit_r t'.
Proof.
iIntros (Hpath) "Htoks #Hsec". iRight. iExists path, t'root.
iSplit; first done. iSplitL "Htoks"; last by iLeft.
iApply (big_sepL_impl with "Htoks").
iIntros "!>" (? t1' _) "tok". by iApply public_token_r_holds_subterm.
Qed.

Lemma protected_deposit_nonce_l t path troot :
  is_nonce troot →
  subterm_path t path troot →
  ([∗ list] t1 ∈ path, public_token_l t1) -∗
  public_token_l troot -∗
  protected_deposit_l t.
Proof.
iIntros (Hn Hpath) "Htoks Hroot". iRight. iExists path, troot.
iSplit; first done. iSplitL "Htoks".
- iApply (big_sepL_impl with "Htoks").
  iIntros "!>" (? t1 _) "tok". by iApply public_token_l_holds_subterm.
- iRight. iSplitR; first by iLeft. by iApply public_token_l_holds_subterm.
Qed.

Lemma protected_deposit_nonce_r t' path t'root :
  is_nonce t'root →
  subterm_path t' path t'root →
  ([∗ list] t1' ∈ path, public_token_r t1') -∗
  public_token_r t'root -∗
  protected_deposit_r t'.
Proof.
iIntros (Hn Hpath) "Htoks Hroot". iRight. iExists path, t'root.
iSplit; first done. iSplitL "Htoks".
- iApply (big_sepL_impl with "Htoks").
  iIntros "!>" (? t1' _) "tok". by iApply public_token_r_holds_subterm.
- iRight. iSplitR; first by iLeft. by iApply public_token_r_holds_subterm.
Qed.

Lemma public_secret_nonce_l E t :
  is_nonce t →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  term_token t ⊤ ={E}=∗
  secret_in_l t ∗ term_token t (⊤ ∖ ↑hypercryptisN).
Proof.
iIntros (Ht HE) "#ctx tok".
iDestruct (term_token_public_token_l with "tok") as "(tok & _ & _ & $)";
  first by move: Ht => /is_nonceP [? ->].
iDestruct (public_token_l_split with "tok") as "(states & _ & _)".
iApply (public_secret_l _ HE with "ctx [] states"). by iLeft.
Qed.

Lemma public_secret_nonce_r E t' :
  is_nonce t' →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  term_token_spec t' ⊤ ={E}=∗
  secret_in_r t' ∗ term_token_spec t' (⊤ ∖ ↑hypercryptisN).
Proof.
iIntros (Ht HE) "#ctx tok".
iDestruct (term_token_public_token_r with "tok") as "(tok & _ & _ & $)";
  first by move: Ht => /is_nonceP [? ->].
iDestruct (public_token_r_split with "tok") as "(states & _ & _)".
iApply (public_secret_r _ HE with "ctx [] states"). by iLeft.
Qed.

Lemma public_secret_step_l E t tsup :
  is_immediate_subterm t tsup →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  secret_in_l t -∗
  public_token_l tsup ={E}=∗
  secret_in_l tsup.
Proof.
iIntros (Hsup HE) "#ctx #sec tok".
iDestruct (public_token_l_split with "tok") as "(states & _ & _)".
iApply (public_secret_l _ HE with "ctx [] states").
iApply (protected_deposit_secret_l (SubtermPathOne Hsup) with "[] sec") => //.
Qed.

Lemma public_secret_step_r E t' t'sup :
  is_immediate_subterm t' t'sup →
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  secret_in_r t' -∗
  public_token_r t'sup ={E}=∗
  secret_in_r t'sup.
Proof.
iIntros (Hsup HE) "#ctx #sec tok".
iDestruct (public_token_r_split with "tok") as "(states & _ & _)".
iApply (public_secret_r _ HE with "ctx [] states").
iApply (protected_deposit_secret_r (SubtermPathOne Hsup) with "[] sec") => //.
Qed.

Lemma public_link E {t t'} :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  protected_deposit_l t -∗
  protected_deposit_r t' -∗
  public_token_l t -∗
  public_token_r t' ={E}=∗
  linked t t'.
Proof.
iIntros (HE) "#ctx prot prot' tok tok'".
iDestruct (public_token_l_split with "tok") as "[states _]".
iDestruct (public_token_r_split with "tok'") as "[states' _]".
by iMod (linked_extend t t' HE with "ctx prot prot' states states'") as "($ & _ & _)".
Qed.

Lemma public_publish E {t t'} :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  □ (publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  public_deposit_l t t' -∗
  public_deposit_r t t' -∗
  public_token_l t -∗
  public_token_r t' ={E}=∗
  publicly_linked t t' ∗ PUB⟨t, t'⟩.
Proof.
iIntros (HE) "#ctx #wand pl pr tok tok'".
iDestruct (public_token_l_split with "tok") as "(states & prots & _)".
iDestruct (public_token_r_split with "tok'") as "(states' & prots' & _)".
iMod (public_extend t t' HE with "ctx wand pl pr prots prots' states states'") as "#link".
iModIntro. iSplit => //. by iApply "wand".
Qed.

Lemma public_seal E k k' t t' Ek Ek' :
  ↑cryptisN ⊆ E →
  ↑seal_namespace t ⊆ Ek →
  ↑seal_namespace t' ⊆ Ek' →
  hypercryptis_ctx -∗
  □ (publicly_linked (TSeal k t) (TSeal k' t') -∗ PUB⟨TSeal k t, TSeal k' t'⟩) -∗
  (seal_release_l (TSeal k t) -∗ seal_release_r (TSeal k' t') -∗
   public_deposit_l (TSeal k t) (TSeal k' t') ∗
   public_deposit_r (TSeal k t) (TSeal k' t')) -∗
  never_sealed_under_l k Ek -∗
  never_sealed_under_r k' Ek' ={E}=∗
  publicly_linked (TSeal k t) (TSeal k' t') ∗
  PUB⟨TSeal k t, TSeal k' t'⟩ ∗
  never_sealed_under_l k (Ek ∖ ↑seal_namespace t) ∗
  never_sealed_under_r k' (Ek' ∖ ↑seal_namespace t').
Proof.
iIntros (HE sub sub') "#ctx #wand prot ns ns'".
rewrite (never_sealed_under_public_token_l k sub) (never_sealed_under_public_token_r k' sub').
iDestruct "ns" as "[tok $]". iDestruct "ns'" as "[tok' $]".
iDestruct (public_token_l_split with "tok") as "(states & prots & rel)".
iDestruct (public_token_r_split with "tok'") as "(states' & prots' & rel')".
iDestruct ("prot" with "rel rel'") as "[pl pr]".
iMod (public_extend _ _ HE with "ctx wand pl pr prots prots' states states'") as "#link".
iModIntro. iSplit => //. by iApply "wand".
Qed.

Lemma public_seal_held E k k' t t' Ek Ek' :
  ↑cryptisN ⊆ E →
  ↑seal_namespace t ⊆ Ek →
  ↑seal_namespace t' ⊆ Ek' →
  hypercryptis_ctx -∗
  □ (publicly_linked (TSeal k t) (TSeal k' t') -∗ PUB⟨TSeal k t, TSeal k' t'⟩) -∗
  public_deposit_l (TSeal k t) (TSeal k' t') -∗
  public_deposit_r (TSeal k t) (TSeal k' t') -∗
  never_sealed_under_l k Ek -∗
  never_sealed_under_r k' Ek' ={E}=∗
  publicly_linked (TSeal k t) (TSeal k' t') ∗
  PUB⟨TSeal k t, TSeal k' t'⟩ ∗
  never_sealed_under_l k (Ek ∖ ↑seal_namespace t) ∗
  never_sealed_under_r k' (Ek' ∖ ↑seal_namespace t') ∗
  seal_release_l (TSeal k t) ∗ seal_release_r (TSeal k' t').
Proof.
iIntros (HE sub sub') "#ctx #wand pl pr ns ns'".
rewrite (never_sealed_under_public_token_l k sub) (never_sealed_under_public_token_r k' sub').
iDestruct "ns" as "[tok $]". iDestruct "ns'" as "[tok' $]".
iDestruct (public_token_l_split with "tok") as "(states & prots & $)".
iDestruct (public_token_r_split with "tok'") as "(states' & prots' & $)".
iMod (public_extend _ _ HE with "ctx wand pl pr prots prots' states states'") as "#link".
iModIntro. iSplit => //. by iApply "wand".
Qed.

Lemma public_seal_senc E (k k' : senc_key) (N : namespace) t t' Ek Ek' :
  ↑cryptisN ⊆ E →
  ↑seal_namespace (Spec.tag (Tag N) t) ⊆ Ek →
  ↑seal_namespace (Spec.tag (Tag N) t') ⊆ Ek' →
  hypercryptis_ctx -∗
  minted k -∗ minted_spec k' -∗ minted t -∗ minted_spec t' -∗
  linked (k : term) (k' : term) -∗
  PUB⟨t, t'⟩ ∨ secret_in_l k ∧ secret_in_r k' -∗
  never_sealed_under_l k Ek -∗
  never_sealed_under_r k' Ek' ={E}=∗
  PUB⟨Spec.enc k (Tag N) t, Spec.enc k' (Tag N) t'⟩ ∗
  publicly_linked (Spec.enc k (Tag N) t) (Spec.enc k' (Tag N) t') ∗
  never_sealed_under_l k (Ek ∖ ↑seal_namespace (Spec.tag (Tag N) t)) ∗
  never_sealed_under_r k' (Ek' ∖ ↑seal_namespace (Spec.tag (Tag N) t')).
Proof.
move=> HE sub sub'. rewrite /Spec.enc (senc_key_TKey k) (senc_key_TKey k').
iIntros "#ctx #mk #mk' #mt #mt' #Hl #Hcase ns ns'".
iMod (public_seal _ _ HE sub sub' with "ctx [] [] ns ns'") as "(#Hpl & #Hpub & $ & $)";
  last by iFrame "#".
- iIntros "!> #Hpl". rewrite public_TSeal. iRight.
  rewrite minted_TSeal minted_spec_TSeal minted_tag minted_spec_tag.
  iSplit; first by iSplit. iSplit; first by iSplit. iSplit; first done.
  iLeft. by iSplit.
- iIntros "rel rel'". iSplitL "rel"; iLeft; iFrame.
  all: iDestruct "Hcase" as "[Ht|[Hs Hs']]"; [|by iRight].
  all: iLeft; rewrite public_tag; by iSplit.
Qed.

End Updates.
