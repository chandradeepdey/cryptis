From reloc Require Import reloc.
From cryptis Require Import lib.
From cryptis.core Require Import pre_term.
From cryptis.primitives Require Import pre_term.
From cryptis Require Import lib_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Proofs.

Context `{!relocG Σ}.

Implicit Types E : coPset.
Implicit Types pt : PreTerm.pre_term.

Lemma tp_eq_pre_term E j pt1 pt2 :
  nclose specN ⊆ E →
  refines_right j (eq_term (repr pt1) (repr pt2)) -∗
  |={E}=> refines_right j #(bool_decide (pt1 = pt2)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_eq_pre_term => //.
rewrite andb_True; split; apply val_of_pre_term_pure.
Qed.

Import all_order.

Lemma tp_leq_pre_term E j pt1 pt2 :
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
