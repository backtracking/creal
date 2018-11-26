(*
 * Exact real arithmetic (Constructive reals).
 * Copyright (C) 2000 Jean-Christophe FILLIATRE
 *
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License version 2, as published by the Free Software Foundation.
 *
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 * See the GNU Library General Public License version 2 for more details
 * (enclosed in the file LGPL).
 *)

(*s {\bf Constructive reals} are implemented by the following abstract
    datatype [t]. If [x] is a constructive real, then the function call
    [approx x n] returns an approximation of [x] up to $4^{-n}$, as
    an arbitrary precision integer $x_n$ such that $|4^n\cdot x - x_n| < 1$. *)

type t

val create' : (int -> t) -> t

val approx : t -> int -> Z.t

val msd : t -> int

(*s Basic operations. *)

val add : t -> t -> t
val neg : t -> t
val sub : t -> t -> t

val abs : t -> t

val mul : t -> t -> t
val inv : t -> t
val div : t -> t -> t

val pow_int : t -> int -> t
val root : int -> t -> t

val sqrt : t -> t

(*s Transcendental functions. [log ~base:x y] is $\log_x(y)$. *)

val ln : t -> t
val log : base:t -> t -> t

val exp : t -> t
val pow : t -> t -> t

(*s Trigonometric functions. *)

val sin : t -> t
val cos : t -> t
val tan : t -> t

val arcsin : t -> t
val arccos : t -> t
val arctan : t -> t

(*s [arctan_reciproqual n] is $\arctan(1/n)$, but is more efficient than
    using [arctan]. *)

val arctan_reciproqual : int -> t

(*s Hyperbolic functions. *)

val sinh : t -> t
val cosh : t -> t
val tanh : t -> t

val arcsinh : t -> t
val arccosh : t -> t
val arctanh : t -> t

(*s Some constants. *)

val zero : t
val one : t
val two : t

val pi : t
val half_pi : t

val e : t

(*s Comparisons. [cmp] is absolute comparison: it may not terminate and only
    returns [-1] or [+1]. [rel_cmp] is relative comparison, up to $4^{-k}$,
    and it returns [-1], [0] or [+1]. *)

val compare : t -> t -> int
val rel_cmp : int -> t -> t -> int

val min : t -> t -> t
val max : t -> t -> t

(*s Coercions. [to_q] and [to_float] expect a precision. [to_float x
    n] returns the best floating point representation of the rational
    $\ap{x}{n} / 4^n$. [of_string] expects a base as second argument. *)

val of_int : int -> t
val of_z : Z.t -> t
val of_q : Q.t -> t
val of_float : float -> t
val of_string : ?radix:int -> string -> t

val to_float : t -> int -> float
val to_q : t -> int -> Q.t

(*s Coercion to type [string]. Given a decimal precision [p],
    [to_string x p] returns a decimal approximation [d] of [x] with
    either [p] digits such that $|d - x| < 10^{-p}$, or [p+1] digits
    such that $|d - x| < 10^{-p-1}$.

    [to_beautiful_string] returns the same decimal number but with
    digits packed 5 by 5. *)

val to_string : t -> int -> string
val to_beautiful_string : t -> int -> string

(*s Format pretty-printer. *)

val print : Format.formatter -> t -> unit
val set_print_precision : int -> unit

(*s Infix notations. *)

module Infixes : sig
  val ( +! ) : t -> t -> t
  val ( -! ) : t -> t -> t
  val ( *! ) : t -> t -> t
  val ( /! ) : t -> t -> t
end

