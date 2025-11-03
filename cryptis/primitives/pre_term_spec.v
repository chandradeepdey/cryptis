From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From mathcomp Require order.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis.core Require Import pre_term.
From cryptis.primitives Require Import notations.

From cryptis.primitives Require Import pre_term.
From reloc Require Import reloc.
From cryptis Require Import lib_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Proofs.

Import ssreflect ssrbool.

Context `{!relocG Σ}.
Notation nonce := loc.

Implicit Types E : coPset.
Implicit Types a : nonce.
Implicit Types pt : PreTerm.pre_term.
Implicit Types v : val.
Implicit Types Ψ : val → iProp Σ.
Implicit Types N : namespace.

Lemma tp_eq_pre_term E j (pt1 pt2 : PreTerm.pre_term) :
  nclose specN ⊆ E →
  refines_right j (eq_term (repr pt1) (repr pt2)) -∗
  |={E}=> refines_right j #(bool_decide (pt1 = pt2)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_eq_pre_term => //.
rewrite andb_True; split; apply val_of_pre_term_pure.
Qed.

Import ssrbool seq path.

Import ssreflect.eqtype ssreflect.order.

Lemma tp_leq_pre_term E j (pt1 pt2 : PreTerm.pre_term) :
  nclose specN ⊆ E →
  refines_right j (leq_term (repr pt1) (repr pt2)) -∗
  |={E}=> refines_right j #(pt1 <= pt2)%O.
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_leq_pre_term => //.
rewrite andb_True; split; apply val_of_pre_term_pure.
Qed.

End Proofs.
