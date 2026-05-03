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

Definition relational_cryptis_N := nroot.@"cryptis".@"relational".

Definition relational_cryptis_inv : iProp :=
  ∃ pub priv, public_rel_pub_auth pub ∗ public_rel_priv_auth priv.

End Rel.
