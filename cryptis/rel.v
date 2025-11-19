From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth lib.gset_bij gmap list excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib gmeta nown.
From cryptis.core Require Import term minted.

From reloc Require Import reloc.
From cryptis.core Require Import minted_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition term_part_bijR := gset_bijUR term term.

Class publicGpreS Σ := PublicGPreS {
  publicGpreS_term_part_bij : inG Σ term_part_bijR;
  publicGpreS_meta : metaGS Σ;
}.

Local Existing Instance publicGpreS_term_part_bij.
Local Existing Instance publicGpreS_meta.

Class publicGS Σ := PublicGS {
  public_inG : publicGpreS Σ;
  public_term_part_bij_name : gname;
}.

Global Existing Instance public_inG.

Definition publicΣ : gFunctors :=
  #[GFunctor term_part_bijR; metaΣ].

Global Instance subG_publicGpreS Σ : subG publicΣ Σ → publicGpreS Σ.
Proof. solve_inG. Qed.

Section Rel.

Context `{!relocG Σ, !publicGS Σ}.
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).

Implicit Types (k : senc_key) (t : term) (R : gset (term * term)).

Definition enc_rel_auth t R : iProp :=
  nown public_term_part_bij_name (nroot.@"enc".@t)
    (gset_bij_auth (DfracOwn 1) R).

Definition enc_rel_frag t t1 t2 : iProp :=
  nown public_term_part_bij_name (nroot.@"enc".@t)
    (gset_bij_elem t1 t2).

Lemma enc_rel_alloc t1 t2 t R :
  (∀ t2', (t1, t2') ∉ R) → (∀ t1', (t1', t2) ∉ R) →
  enc_rel_auth t R ==∗
  enc_rel_auth t ({[(t1, t2)]} ∪ R) ∗
  enc_rel_frag t t1 t2.
Proof.
iIntros "%fresh1 %fresh2 own".
iMod (nown_update with "own") as "own".
apply: gset_bij_auth_extend => //=.
iDestruct "own" as "[auth #frag]".
rewrite -gset_op view_frag_op nown_op.
iDestruct "frag" as "[#frag1 #frag2]".
iModIntro. iFrame "#".
iCombine "frag1 frag2" as "#frag".
rewrite /enc_rel_auth /gset_bij_auth nown_op.
by iFrame "#".
Qed.

Definition nonce_rel_auth R : iProp :=
  nown public_term_part_bij_name (nroot.@"nonce")
    (gset_bij_auth (DfracOwn 1) R).

Definition nonce_rel_frag t1 t2 : iProp :=
  nown public_term_part_bij_name (nroot.@"nonce")
    (gset_bij_elem t1 t2) ∗
    minted_spec t1 ∗ minted t2.

Lemma nonce_rel_alloc t1 t2 R :
  (∀ t2', (t1, t2') ∉ R) → (∀ t1', (t1', t2) ∉ R) →
  minted_spec t1 ∗ minted t2 ∗
  nonce_rel_auth R ==∗
  nonce_rel_auth ({[(t1, t2)]} ∪ R) ∗
  nonce_rel_frag t1 t2.
Proof.
iIntros "%fresh1 %fresh2 (mt1 & mt2 & own)".
iMod (nown_update with "own") as "own".
apply: gset_bij_auth_extend => //=.
iDestruct "own" as "[auth #frag]".
rewrite -gset_op view_frag_op nown_op.
iDestruct "frag" as "[#frag1 #frag2]".
iModIntro. iFrame "#". iFrame.
iCombine "frag1 frag2" as "#frag".
rewrite /nonce_rel_auth /gset_bij_auth nown_op.
by iFrame "#".
Qed.

Fixpoint public t1 t2 : iProp :=
  match t1, t2 with
  | TInt n1, TInt n2 => ⌜n1 = n2⌝
  | TPair t11 t12, TPair t21 t22 =>
      public t11 t21 ∧ public t12 t22
  | TNonce _, TNonce _ => nonce_rel_frag t1 t2
  | TKey kt1 t1, TKey kt2 t2 =>
      False (* FIXME *)
  | TSeal k1 t1, TSeal k2 t2 =>
      ⌜k1 = k2⌝ ∧ enc_rel_frag k1 t1 t2
  | THash _, THash _ =>
      False (* FIXME *)
  | TExpN' _ _ _, TExpN' _ _ _ =>
      False (* FIXME *)
  | _, _ =>
      False (* WIP *)
  end.

Lemma public_TSeal k R t1 t2 :
  (∀ t2', (t1, t2') ∉ R) → (∀ t1', (t1', t2) ∉ R) →
  enc_rel_auth k R ==∗
  enc_rel_auth k ({[(t1, t2)]} ∪ R) ∗
  public (TSeal k t1) (TSeal k t2).
Proof.
iIntros "%fresh1 %fresh2 H●".
iMod (enc_rel_alloc _ fresh1 fresh2 with "H●") as "[H● H◯]".
by iFrame.
Qed.

Lemma public_TNonce R (t1 t2: loc) :
  (∀ t2', (TNonce t1, t2') ∉ R) → (∀ t1', (t1', TNonce t2) ∉ R) →
  minted_spec (TNonce t1) ∗ minted (TNonce t2) ∗
  nonce_rel_auth R ==∗
  nonce_rel_auth ({[((TNonce t1), (TNonce t2))]} ∪ R) ∗
  public (TNonce t1) (TNonce t2).
Proof.
  iIntros "%fresh1 %fresh2 (#Ht1 & #Ht2 & H●)".
  iMod (nonce_rel_alloc fresh1 fresh2 with "[H●]") as "[H● H◯]".
  - by iFrame "#".
  by iFrame.
Qed.

End Rel.
