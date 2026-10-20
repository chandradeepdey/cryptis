From reloc Require Import reloc.
From cryptis.core Require Import term.
From cryptis.primitives Require Import pre_term comp.
From cryptis.hyper Require Import lib_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Proofs.

Context `{!relocG Σ}.

Implicit Types E : coPset.
Implicit Types t : term.
Implicit Types Ψ : val → val → iProp Σ.

Lemma rel_eq_term_l E K e t1 t2 Ψ :
  (REL fill K (#(bool_decide (t1 = t2)) : expr) << e @ E : Ψ) -∗
  REL fill K (eq_term t1 t2) << e @ E : Ψ.
Proof. pure_twp_rel twp_eq_term. Qed.

Lemma rel_eq_term_r E K e t1 t2 Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (#(bool_decide (t1 = t2)) : expr) @ E : Ψ) -∗
  REL e << fill K (eq_term t1 t2) @ E : Ψ.
Proof. pure_twp_rel twp_eq_term. Qed.

Lemma rel_eq_term t1 t2 t1' t2' Ψ :
  Ψ #(bool_decide (t1 = t2)) #(bool_decide (t1' = t2')) -∗
  REL (eq_term t1 t2) << (eq_term t1' t2') : Ψ.
Proof.
iIntros "HΨ".
rel_apply_l rel_eq_term_l. rel_apply_r rel_eq_term_r.
rel_values.
Qed.

Lemma rel_texp_l E K e t1 t2 Ψ :
  (REL fill K (TExp t1 t2 : expr) << e @ E : Ψ) -∗
  REL fill K (texp t1 t2) << e @ E : Ψ.
Proof. pure_twp_rel twp_texp. Qed.

Lemma rel_texp_r E K e t1 t2 Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (TExp t1 t2 : expr) @ E : Ψ) -∗
  REL e << fill K (texp t1 t2) @ E : Ψ.
Proof. pure_twp_rel twp_texp. Qed.

Lemma rel_texp t1 t2 t1' t2' Ψ :
  Ψ (TExp t1 t2) (TExp t1' t2') -∗
  REL (texp t1 t2) << (texp t1' t2') : Ψ.
Proof.
iIntros "HΨ".
rel_apply_l rel_texp_l. rel_apply_r rel_texp_r.
rel_values.
Qed.

Lemma rel_tmul_l E K e t1 t2 Ψ :
  (REL fill K (TMulN [t1; t2] : expr) << e @ E : Ψ) -∗
  REL fill K (tmul t1 t2) << e @ E : Ψ.
Proof. pure_twp_rel twp_tmul. Qed.

Lemma rel_tmul_r E K e t1 t2 Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (TMulN [t1; t2] : expr) @ E : Ψ) -∗
  REL e << fill K (tmul t1 t2) @ E : Ψ.
Proof. pure_twp_rel twp_tmul. Qed.

Lemma rel_tinv_l E K e t Ψ :
  (REL fill K (TInv t : expr) << e @ E : Ψ) -∗
  REL fill K (tinv t) << e @ E : Ψ.
Proof. pure_twp_rel twp_tinv. Qed.

Lemma rel_tinv_r E K e t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (TInv t : expr) @ E : Ψ) -∗
  REL e << fill K (tinv t) @ E : Ψ.
Proof. pure_twp_rel twp_tinv. Qed.

Lemma rel_tone_l E K e Ψ :
  (REL fill K (TMulN [] : expr) << e @ E : Ψ) -∗
  REL fill K (tone #()) << e @ E : Ψ.
Proof. pure_twp_rel twp_tone. Qed.

Lemma rel_tone_r E K e Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (TMulN [] : expr) @ E : Ψ) -∗
  REL e << fill K (tone #()) @ E : Ψ.
Proof. pure_twp_rel twp_tone. Qed.

Lemma rel_tgmul_l E K e t1 t2 Ψ :
  (REL fill K (TGMulN [t1; t2] : expr) << e @ E : Ψ) -∗
  REL fill K (tgmul t1 t2) << e @ E : Ψ.
Proof. pure_twp_rel twp_tgmul. Qed.

Lemma rel_tgmul_r E K e t1 t2 Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (TGMulN [t1; t2] : expr) @ E : Ψ) -∗
  REL e << fill K (tgmul t1 t2) @ E : Ψ.
Proof. pure_twp_rel twp_tgmul. Qed.

Lemma rel_tginv_l E K e t Ψ :
  (REL fill K (TGInv t : expr) << e @ E : Ψ) -∗
  REL fill K (tginv t) << e @ E : Ψ.
Proof. pure_twp_rel twp_tginv. Qed.

Lemma rel_tginv_r E K e t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (TGInv t : expr) @ E : Ψ) -∗
  REL e << fill K (tginv t) @ E : Ψ.
Proof. pure_twp_rel twp_tginv. Qed.

Lemma rel_tgone_l E K e Ψ :
  (REL fill K (TGMulN [] : expr) << e @ E : Ψ) -∗
  REL fill K (tgone #()) << e @ E : Ψ.
Proof. pure_twp_rel twp_tgone. Qed.

Lemma rel_tgone_r E K e Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (TGMulN [] : expr) @ E : Ψ) -∗
  REL e << fill K (tgone #()) @ E : Ψ.
Proof. pure_twp_rel twp_tgone. Qed.

End Proofs.
