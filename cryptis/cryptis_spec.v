From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list reservation_map excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib.
From cryptis.core Require Export term term_meta minted public.

From cryptis Require Import cryptis.
From reloc Require Import reloc.
From cryptis.core Require Import public_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation cryptis_specN := (nroot.@"cryptis_spec").

Local Existing Instance cryptisGpreS_term_meta.
Local Existing Instance cryptisGpreS_public.
Local Existing Instance cryptisGpreS_tlock.

Class cryptis_specGS Σ := CryptisSpecGS {
  #[global] cryptis_specGS_term_meta :: term_metaGS Σ;
  #[global] cryptis_specGS_public :: public_specGS Σ;
  #[local] cryptis_specGS_tlock :: tlockG Σ;
}.

Definition cryptis_specΣ : gFunctors :=
  #[term_metaΣ; public_specΣ; tlockΣ].

Global Instance subG_cryptisGpreS Σ : subG cryptis_specΣ Σ → cryptisGpreS Σ.
Proof. solve_inG. Qed.

Section CryptisSpec.

Context `{!relocG Σ, !cryptis_specGS Σ}.
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).

Definition cryptis_spec_ctx : iProp :=
  term_meta_ctx.

#[global]
Instance cryptis_spec_ctx_persistent : Persistent cryptis_spec_ctx.
Proof. apply _. Qed.

#[global]
Instance cryptis_ctx_spec_has_term_meta_ctx : HasTermMetaCtx cryptis_spec_ctx.
Proof. split; last apply _. by []. Qed.

End CryptisSpec.

Arguments cryptis_spec_ctx {Σ _ _}.

Lemma cryptis_spec_GS_alloc `{!relocG Σ} E :
  cryptisGpreS Σ →
  ⊢ |={E}=> ∃ (H : cryptis_specGS Σ),
             cryptis_spec_ctx ∗
             seal_spec_pred_token AENC ⊤ ∗
             seal_spec_pred_token SIGN ⊤ ∗
             seal_spec_pred_token SENC ⊤ ∗
             hash_spec_pred_token ⊤.
Proof.
move=> ?; iStartProof.
iMod term_metaGS_alloc as "[% #?]".
iMod public_specGS_alloc as "(% & ? & ? & ? & ?)".
iExists (CryptisSpecGS _ _ _). iFrame. by iModIntro.
Qed.
