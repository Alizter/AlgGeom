From HoTT Require Import Basics Types Algebra.Rings Spaces.Nat.
Require Import Invertible.

Local Open Scope nat_scope.
Local Open Scope mc_scope.

(** * Localization of rings *)

(** ** Multiplicative subsets *)

(** *** Definitions *)

(** Multiplicative subsets of a ring [R] consist of: *)
Class IsMultiplicativeSubset {R : CRing} (S : R -> Type) : Type := {
  (** Being a hprop *)
  mss_ishprop : forall x, IsHProp (S x) ;
  (** Contains one *)
  mss_one : S 1 ;
  (** Closed under multiplication *)
  mss_mult : forall x y, S x -> S y -> S (x * y) ;
}.

Arguments mss_one {R _}.
Arguments mss_mult {R _}.

(** *** Examples *)

(** The multplicative subset of powers of a ring element. *)
Global Instance ismultiplicative_powers (R : CRing) (x : R)
  : IsMultiplicativeSubset (fun r => hexists (fun n : nat => rng_power x n = r)).
Proof.
  srapply Build_IsMultiplicativeSubset.
  1: by apply tr; exists 0%nat.
  intros a b np mq.
  strip_truncations.
  destruct np as [n p], mq as [m q].
  apply tr; exists (n + m)%nat.
  refine ((rng_power_mult_law _ _ _)^ @ _).
  f_ap.
Defined.

(** Invertible elements of a ring form a multiplicative subset. *)
Global Instance ismultiplicative_isinvertible (R : CRing)
  : IsMultiplicativeSubset (@IsInvertible R) := {}.



