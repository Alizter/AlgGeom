From HoTT Require Import Basics Types Algebra.Rings.

(** TODO: move into main Rings library. *)
(** * Invertible elements in rings. *)

(** *** Definition of invertible elements. *)

(** Invertible elements have a corresponding element which is a left and right inverse. *)
Class IsInvertible {R : CRing} (r : R) : Type := Build_IsInvertible' {
  isinv_inv : R ;
  isinv_left_inv  : isinv_inv * r = 1 ;
  isinv_right_inv : r * isinv_inv = 1 ;
}.

Arguments Build_IsInvertible' {R}.

(** Since our rings are commutative, we only need to show one side. *)
Definition Build_IsInvertible {R : CRing} (r : R)
  (inv : R) (l : inv * r = 1)
  : IsInvertible r.
Proof.
  snrapply Build_IsInvertible'.
  1: exact inv.
  1: exact l.
  rewrite rng_mult_comm.
  exact l.
Defined.

Definition issig_IsInvertible {R : CRing} (r : R)
  : _ <~> IsInvertible r := ltac:(issig).

(** The type of an element being invertible is a hprop. *)
Global Instance ishprop_isinvertible {R r} : IsHProp (@IsInvertible R r).
Proof.
  nrapply istrunc_equiv_istrunc.
  1: rapply issig_IsInvertible.
  rapply hprop_allpath.
  (** We can show that any inverses must be unique. *)
  intros [x [px qx]] [y [py qy]].
  apply path_sigma_hprop; cbn.
  refine (_ @ rng_mult_one_l _).
  refine (_ @ ap011 _ px idpath).
  refine (_ @ rng_mult_assoc _ _ _).
  symmetry.
  refine (_ @ rng_mult_one_r _).
  f_ap.
Defined.
