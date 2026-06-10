From reloc Require Import reloc.
From cryptis.core Require Import term.
From cryptis.primitives Require Import pre_term comp.
From cryptis Require Import lib_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Proofs.

Context `{!relocG Σ}.

Implicit Types E : coPset.
Implicit Types t : term.
Implicit Types Ψ : lrel Σ.

Lemma tp_eq_term E j t1 t2 :
  ↑specN ⊆ E →
  refines_right j (eq_term t1 t2) ={E}=∗
  refines_right j #(bool_decide (t1 = t2)).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_eq_term => //.
rewrite andb_True; split; apply term_pure.
Qed.

Lemma rel_eq_term t1 t2 t1' t2' Ψ :
  Ψ #(bool_decide (t1 = t2)) #(bool_decide (t1' = t2')) -∗
  REL (eq_term t1 t2) << (eq_term t1' t2') : Ψ.
Proof.
iIntros "HΨ".
rel_bind_l (eq_term _ _)%E. iApply refines_wp_l.
iApply wp_eq_term => /=.
rel_bind_r (eq_term _ _)%E. iApply refines_step_r. iIntros (j) "Hj".
iPoseProof (tp_eq_term with "Hj") as ">Hj" => //=.
iFrame. rel_values.
Qed.

Lemma tp_texp E j t1 t2 :
  ↑specN ⊆ E →
  refines_right j (texp t1 t2) ={E}=∗
  refines_right j (TExp t1 t2).
Proof.
move=> HE.
iApply pure_twp_tp => //=;
last by move=> ?; iIntros "_"; iApply twp_texp => //.
rewrite andb_True; split; apply term_pure.
Qed.

Lemma rel_texp t1 t2 t1' t2' Ψ :
  Ψ (TExp t1 t2) (TExp t1' t2') -∗
  REL (texp t1 t2) << (texp t1' t2') : Ψ.
Proof.
iIntros "HΨ".
rel_bind_l (texp _ _)%E. iApply refines_wp_l.
iApply wp_texp => /=.
rel_bind_r (texp _ _)%E. iApply refines_step_r. iIntros (j) "Hj".
iPoseProof (tp_texp with "Hj") as ">Hj" => //=.
iFrame. rel_values.
Qed.

End Proofs.
