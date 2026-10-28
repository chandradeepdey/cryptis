(** The one-sided specs that [rel_prims_l] and [rel_prims_r] apply.

  An instance of [RelPrimL Σ e A] is a spec of type [A] that takes the left
  program past the redex [e], a primitive applied to values; [RelPrimR] does
  the same on the right.  The spec files declare the instances of their
  primitives in the [rel_prims] database, which keeps every constant opaque:
  an instance then matches its own primitive only, and not another one whose
  code is the same, such as [senc] and [sign]. *)
From reloc Require Import reloc.

Class RelPrimL Σ `{!relocG Σ} (e : expr) (A : Type) := rel_prim_l_spec : A.
Class RelPrimR Σ `{!relocG Σ} (e : expr) (A : Type) := rel_prim_r_spec : A.
Global Arguments rel_prim_l_spec {_ _ _ _} _.
Global Arguments rel_prim_r_spec {_ _ _ _} _.

Create HintDb rel_prims discriminated.
Global Hint Constants Opaque : rel_prims.
