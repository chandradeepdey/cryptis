(* These proofs take much longer to check than the rest of the
development. Since they don't have many dependencies, they are left in their own
file to avoid slowing down the compilation process. *)

From cryptis Require Import lib lib_spec.
From mathcomp Require Import ssreflect.
From mathcomp Require order.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis.core Require Import pre_term.
From cryptis.primitives Require Import notations pre_term.
From reloc Require Import reloc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Proofs.

Import ssreflect ssrbool.

Lemma val_of_pre_term_pure (pt : PreTerm.pre_term) :
  pure_val (val_of_pre_term pt).
Proof.
  induction pt; try (destruct o; eauto;
    simpl; by apply andb_prop_intro).
  simpl; apply andb_prop_intro; split; first done.
  induction ts; first by rewrite repr_list_unseal.
  simpl in *.
  destruct X as [X1 X2].
  rewrite repr_list_unseal.
  simpl.
  rewrite -repr_list_unseal.
  apply andb_prop_intro; split; by [| apply IHts].
Qed.

Context `{!heapGpreS Σ, !relocG Σ}.
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
intros HE.
iApply pure_twp_tp; eauto.
- simpl. apply andb_prop_intro; split; by apply val_of_pre_term_pure.
- iIntros (?) "#?".
  iApply twp_eq_pre_term.
  by iPureIntro.
Qed.

Import ssrbool seq path.

Import ssreflect.eqtype ssreflect.order.

Lemma tp_leq_pre_term E j (pt1 pt2 : PreTerm.pre_term) :
  nclose specN ⊆ E →
  refines_right j (leq_term (repr pt1) (repr pt2)) -∗
  |={E}=> refines_right j #(pt1 <= pt2)%O.
Proof.
intros HE.
iApply pure_twp_tp; eauto.
- simpl. apply andb_prop_intro; split; by apply val_of_pre_term_pure.
- iIntros (?) "#?".
  iApply twp_leq_pre_term.
  by iPureIntro.
Qed.

End Proofs.
