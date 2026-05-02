From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list excl.
From iris.algebra Require Import functions.
From iris.algebra.lib Require Import gset_bij mono_list.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib gmeta nown.
From cryptis.core Require Import term minted public.

From reloc Require Import reloc.
From cryptis.core Require Import minted_spec.
From cryptis.core Require Import term_meta_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class public_relGpreS Σ := Public_relGpreS {
  #[local] public_relGpreS_pub :: inG Σ (gset_bijUR term term);
  #[local] public_relGpreS_priv :: inG Σ (authUR (gset_disjUR (term * term)));
}.

Class public_relGS Σ := Public_relGS {
  #[local] public_rel_inG :: public_relGpreS Σ;
  public_rel_pub_name  : gname;
  public_rel_priv_name  : gname;
}.

Definition public_relΣ : gFunctors :=
  #[GFunctor (gset_bijUR term term);
    GFunctor (authUR (gset_disjUR (term * term)))].

Global Instance subG_public_relGpreS Σ : subG public_relΣ Σ → public_relGpreS Σ.
Proof. solve_inG. Qed.

Implicit Types (pub priv : gset (term * term)).

Section Rel.

Context `{!relocG Σ, !public_relGS Σ, !publicGS Σ}.

Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).

Definition public_rel_pub_auth (pub: gset (term * term)) : iProp :=
  own public_rel_pub_name (gset_bij_auth (DfracOwn 1) pub).

Definition public_rel_priv_auth (priv: gset (term * term)) : iProp :=
  own public_rel_priv_name (● (GSet priv)).

Definition cryptis_rel_N := nroot .@ "cryptis_rel".

(* to be addressed- probably should not have existentials *)
Definition cryptis_rel_inv : iProp :=
  ∃ pub priv,
      public_rel_pub_auth pub ∗
      public_rel_priv_auth priv.

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
