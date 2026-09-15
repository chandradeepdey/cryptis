From reloc Require Import reloc.
From cryptis Require Import lib.
From cryptis.core Require Import pre_term.
From cryptis.primitives Require Import pre_term.
From cryptis Require Import lib_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Relational counterparts of the pre-term comparison specs in
    [primitives/pre_term.v]. *)

Section Proofs.

Context `{!relocG Σ}.

Implicit Types E : coPset.
Implicit Types pt : PreTerm.pre_term.
Implicit Types Ψ : val → val → iProp Σ.

Lemma rel_eq_pre_term_l E K e pt1 pt2 Ψ :
  (REL fill K (#(bool_decide (pt1 = pt2)) : expr) << e @ E : Ψ) -∗
  REL fill K (eq_term (repr pt1) (repr pt2)) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_eq_pre_term => //.
rewrite andb_True; split; apply val_of_pre_term_pure.
Qed.

Lemma rel_eq_pre_term_r E K e pt1 pt2 Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (#(bool_decide (pt1 = pt2)) : expr) @ E : Ψ) -∗
  REL e << fill K (eq_term (repr pt1) (repr pt2)) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_eq_pre_term => //.
rewrite andb_True; split; apply val_of_pre_term_pure.
Qed.

Lemma rel_leq_pre_term_l E K e pt1 pt2 Ψ :
  (REL fill K (#(bool_decide (pt_order pt1 pt2)) : expr) << e @ E : Ψ) -∗
  REL fill K (leq_term (repr pt1) (repr pt2)) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=;
last by move=> ?; iIntros "_"; iApply twp_leq_pre_term => //.
rewrite andb_True; split; apply val_of_pre_term_pure.
Qed.

Lemma rel_leq_pre_term_r E K e pt1 pt2 Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (#(bool_decide (pt_order pt1 pt2)) : expr) @ E : Ψ) -∗
  REL e << fill K (leq_term (repr pt1) (repr pt2)) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=;
last by move=> ?; iIntros "_"; iApply twp_leq_pre_term => //.
rewrite andb_True; split; apply val_of_pre_term_pure.
Qed.

End Proofs.
