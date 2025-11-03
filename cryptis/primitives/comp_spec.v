From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From mathcomp Require order.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis.core Require Import term.
From cryptis.primitives Require Import notations pre_term.

From cryptis.primitives Require Import comp.
From reloc Require Import reloc.
From cryptis Require Import lib_spec.
From cryptis.primitives Require Import pre_term_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Proofs.

Context `{!relocG Σ}.
Notation nonce := loc.

Implicit Types E : coPset.
Implicit Types a : nonce.
Implicit Types t : term.
Implicit Types v : val.
Implicit Types Ψ : val → iProp Σ.
Implicit Types N : namespace.

Lemma tp_eq_term E j t1 t2 Ψ :
  nclose specN ⊆ E →
  refines_right j (eq_term t1 t2) ={E}=∗
  refines_right j #(bool_decide (t1 = t2)).
Proof.
move=> HE.
iIntros "Hj".
rewrite -!val_of_pre_term_unfold.
iPoseProof (tp_eq_pre_term with "Hj") as ">Hj" => //.
rewrite (_ : bool_decide (t1 = t2) =
             bool_decide (unfold_term t1 = unfold_term t2)) //.
by apply: bool_decide_ext; split => [->|/unfold_term_inj] //.
Qed.

Import ssrbool seq path ssreflect.eqtype ssreflect.order.

Lemma tp_texp E j t1 t2 Ψ :
  nclose specN ⊆ E →
  refines_right j (texp t1 t2) ={E}=∗
  refines_right j (TExp t1 t2).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
first by rewrite andb_True; split; apply term_pure.
move=> ?; iIntros "_"; iApply twp_texp => //.
Qed.

End Proofs.
