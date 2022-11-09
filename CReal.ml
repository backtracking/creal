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

(*s This module implements constructive reals (exact real numbers),
    following the algorithms given in Valérie Ménissier-Morain's
    thesis (\small\verb!http://www-calfor.lip6.fr/~vmm/!).
    In the following, pages refer to this document. *)

(*s {\bf Representation.} A constructive real is represented by an
    approximation function (field [approximate]).  If $x$ is a real
    number, its approximation function applied to an integer $n$ (in
    type [int]) returns an integer $\ap{x}{n}$ (in type [Z.t]) such
    that $|4^n\cdot x - \ap{x}{n}| < 1$.

    For efficiency, we add a field [cache] to keep the best
    approximation computed so far.  (Notice that it is safe to use
    type [int] for the number of digits, since an integer with a
    number of digits exceeding the capacity of machine integers would
    exceed the memory capacity.)

    The field [msd] is a cache for the most significant digit
    (see section~\ref{msd} below). *)

type t = {
  mutable cache : (int * Z.t) option;
  mutable msd : int option;
  approximate : int -> Z.t }

let create f = { cache = None; msd = None; approximate = f }

(*s Computing the approximation of [x] to precision [n] is easy:
    either we have already computed a better approximation and the
    result is just a ``shift'' of that value (Property 6 page 46), or
    we compute [x.approximate n] and we cache its result before
    returning it. *)

let fdiv_Bexp z n =
  if n == 0 then
    z
  else if n > 0 then
    Z.shift_right z (n + n)
  else
    Z.shift_left z (-(n + n))

(*i
let max_prec = ref 0
let _ = at_exit (fun () -> Printf.printf "max_prec=%d\n" !max_prec)
i*)

let approx x n =
  let compute () =
    let z = x.approximate n in x.cache <- Some (n,z); z
  in
  match x.cache with
    | None -> compute ()
    | Some (m,a) -> if n <= m then fdiv_Bexp a (m - n) else compute ()


let create' f =
  let f' k = approx (f k) k in
  create f'


(*s Some useful constants in [Z.t] and [Q.t]. *)

let z_zero = Z.of_int 0
let z_one = Z.of_int 1
let z_two = Z.of_int 2
let z_three = Z.of_int 3
let z_four = Z.of_int 4

let q_half = Q.of_ints 1 2
let q_zero = Q.of_ints 0 1
let q_one = Q.of_ints 1 1
let q_two = Q.of_ints 2 1
let q_four = Q.of_ints 4 1

(*s Utility functions over [Z.t] and [Q.t]. *)

let z_gt x y = Z.compare x y > 0
let z_le x y = Z.compare x y <= 0

let z_between lb x up = z_le lb x && z_le x up

let z_even x = not (Z.testbit x 0)

let q_max q1 q2 = if Q.compare q1 q2 >= 0 then q1 else q2

let q_abs q = if Q.sign q < 0 then Q.neg q else q

(*s Roundings. Floor, ceil and Gau\ss\ rounding over [Q.t]. The Gau\ss\
    rounding of $x$, written $\gauss{x}$, is the (only) integer such that
    $\gauss{x} - \half \le x < \gauss{x} + \half$. *)

let q_floor q = Z.fdiv (Q.num q) (Q.den q)

let q_ceil q = Z.cdiv (Q.num q) (Q.den q)

let gauss_round q =
  let q' = Q.add q q_half in
  Z.fdiv (Q.num q') (Q.den q')

let gauss_round_z_over_4 z = Z.shift_right (Z.add z z_two) 2

(*s Addition (Algorithm 2 page 50).
    We have $\ap{(x+y)}{n} = \lfloor(\ap{x}{n+1}+\ap{y}{n+1})/4\rceil$.
    We do not try to cache a value for [x+y] given the cached values for
    [x] and [y], if any, since it may require some computation (some shifts).
    Moreover, this is exactly what will be done by the first call to
    [approx] on [x+y] if the precision asked is less than $min(x,y)-2$. *)

let add x y =
  create
    (function n ->
       let sn = succ n in
       gauss_round_z_over_4 (Z.add (approx x sn) (approx y sn)))

let (+!) = add

(*s Negation is immediate and subtraction is the composition of
    addition and negation (Algorithm 3 page 51). The cached value for
    [x] is immediatly cached in [-x] (at no cost). *)

let cache_neg = function
  | None -> None
  | Some (n,a) -> Some (n, Z.neg a)

let neg x =
  { cache = cache_neg x.cache;
    msd = x.msd;
    approximate = function n -> Z.neg (approx x n) }

let sub x y = x +! (neg y)

let (-!) = sub

(*s Absolute value. *)

let abs x = create (function n -> Z.abs (approx x n))

(*s Most significant digit ([msd], Definition 9 page 47). \label{msd}
    It is defined by $$\msd{x} =  \min\ \{n\in Z ~|~ |x_n|>1 \}$$
    Note that it does not terminate in 0. *)

let compute_msd x =
  let rec look_up n =
    (* $|\ap{x}{n-1}| \le 1$ *)
    let xn = Z.abs (approx x n) in
    if z_gt xn z_one then n else look_up (succ n)
  and look_down n =
    (* $|\ap{x}{n+1}| > 1$ *)
    let xn = Z.abs (approx x n) in
    if z_gt xn z_one then look_down (pred n) else succ n
  in
  let x0 = Z.abs (approx x 0) in
  if z_gt x0 z_one then look_down (-1) else look_up 1

let msd x = match x.msd with
  | None -> let m = compute_msd x in x.msd <- Some m; m
  | Some m -> m

(*s Version of [msd] with a maximal bound on the iteration process
    (used in function [mul] to avoid non-termination when
    multiplicating by 0). *)

let msd_with_max m x =
  let rec look_up n =
    if n >= m then n else
    let xn = Z.abs (approx x n) in
    if z_gt xn z_one then n else look_up (succ n)
  and look_down n =
    let xn = Z.abs (approx x n) in
    if z_gt xn z_one then look_down (pred n) else succ n
  in
  let x0 = Z.abs (approx x 0) in
  if z_gt x0 z_one then look_down (-1) else look_up 1

(*s [mul_Bexp] and [div_Bexp] respectively multiplies and divides
    an integer by $B^n$ (works whatever the sign of [n] is).
    The result is a rational. *)

let mul_Bexp z n =
  if n == 0 then
    Q.of_bigint z
  else if n > 0 then
    Q.of_bigint (Z.shift_left z (n + n))
  else
    Q.make z (Z.shift_left z_one (-(n + n)))

let bexp n = mul_Bexp z_one n

let div_Bexp z n =
  if n == 0 then
    Q.of_bigint z
  else if n > 0 then
    Q.make z (Z.shift_left z_one (n + n))
  else
    Q.of_bigint (Z.shift_left z (-(n + n)))

(*s Multiplication (Algorithm 4 page 51). *)

let mul x y =
  create
    (function n ->
       let d = (n + 2) / 2 in
       let msd' = msd_with_max (n + 3 - d) in
       let px = max (n - (msd' y) + 3) d
       and py = max (n - (msd' x) + 3) d in
       let xpx = approx x px
       and ypy = approx y py in
       let z = gauss_round (div_Bexp (Z.add (Z.abs (Z.mul xpx ypy)) Z.one)
			      (px + py - n)) in
       if Z.sign xpx = Z.sign ypy then z else Z.neg z)

let ( *! ) = mul

(*s Inverse (Algorithm 5 page 53) and division. *)

let inv x =
   create
     (function n ->
	let msdx = msd x in
	if n <= -msdx then
	  z_zero
	else
	  let k = n + 2 * msdx + 1 in
	  let xk = approx x k in
	  let q = Q.div (bexp (k + n)) (Q.of_bigint xk) in
	  if z_gt xk z_one then q_ceil q else q_floor q)

let div x y = x *! (inv y)

let (/!) = div

(*s Square root (Algorithm 6 page 56). *)

let sqrt x =
  create
    (function n ->
       let x2n = approx x (n + n) in
       if Z.sign x2n < 0 then invalid_arg "Creal.sqrt";
       Z.sqrt x2n)

(*s Coercions from integers and rationals (Algorithm 1 page 49)
    and coercion to rationals. *)

let fmul_Bexp q n =
  if n == 0 then
    q_floor q
  else if n > 0 then
    Z.fdiv (Z.shift_left (Q.num q) (n + n)) (Q.den q)
  else
    q_floor (Q.div q (Q.of_bigint (Z.shift_left z_one (-(n + n)))))

let of_z z =
  { cache = Some (0,z);
    msd = None;
    approximate = function n -> fmul_Bexp (Q.of_bigint z) n }

let of_q q = create (fmul_Bexp q)

let to_q x n =
  let xn = approx x n in
  Q.div (Q.of_bigint xn) (bexp n)

let of_int n = of_z (Z.of_int n)

let zero = of_int 0
let one = of_int 1
let two = of_int 2
let four = of_int 4

(*s Power of a real to a small integer. *)

let rec pow_int x n =
  if n == 0 then
    one
  else if n < 0 then
    inv (pow_int x (-n))
  else
    let y = pow_int (mul x x) (n / 2) in
    if n mod 2 == 0 then y else mul y x

let rec pow_z x n =
  let c = Z.compare n Z.zero in
  if c == 0 then
    one
  else if c < 0 then
    inv (pow_z x (Z.neg n))
  else
    let y = pow_z (mul x x) (Z.shift_right n 1) in
    if not (Z.testbit n 0) then y else mul y x

(*s Alternate power series. The following function
    [alternate_powerserie_] computes $B^p S$ where $S$ is the partial
    sum of an alternate power serie such that the remainder is less
    than $B^{-p}$, that is $S = \sum_{i=0}^{i=n}(-1)^ia_i$ with
    $a_{n+1} < B^{-p}$. The alternate power serie is given by its
    first term $a_0$ and a function [next] such that $a_{n+1} =
    \textit{next} ~ n ~ a_n$. *)

let alternate_powerserie_ a0 next p =
  let eps = bexp (-p) in
  let rec sum s n an =
    (* [s] is already the sum up to $a_n$ *)
    let asn = next n an in
    if Q.compare (q_abs asn) eps < 0 then
      s
    else
      sum (if n mod 2 == 0 then Q.sub s asn else Q.add s asn) (n + 1) asn
  in
  Q.div (sum a0 0 a0) eps

(*s A specialized function to compute $atan(1/m)$ where [m] is a small
    integer. *)

let arctan_reciproqual m =
  let m_inverse = Q.of_ints 1 m in
  let m_inverse_square = Q.mul m_inverse m_inverse in
  create
    (fun n ->
       let eps = bexp (-n) in
       let rec sum s sign k p =
	 (* [s] is already the sum up to $a_k$ *)
	 let p' = Q.mul p m_inverse_square in
	 let t = Q.mul p' (Q.of_ints 1 (k + 2)) in
	 if Q.compare t eps < 0 then
	   s
	 else
	   sum (if sign then Q.add s t else Q.sub s t) (not sign) (k + 2) p'
       in
       fmul_Bexp (sum m_inverse false 1 m_inverse) n)


(*s $\pi$ is defined using [arctan], with the well-known formula (Algorithm
    13 page 68)
    $$\frac{\pi}{4} = 12 \arctan\left(\frac{1}{18}\right)
                    +  8 \arctan\left(\frac{1}{57}\right)
                    -  5 \arctan\left(\frac{1}{239}\right)$$ *)

let pi =
     (of_int 48 *! arctan_reciproqual 18)
  +! (of_int 32 *! arctan_reciproqual 57)
  -! (of_int 20 *! arctan_reciproqual 239)

(*i
let pi =  (of_int 16 *! arctan_reciproqual 5)
       -! (of_int 4  *! arctan_reciproqual 239)
i*)

let half_pi = pi /! two

(*s Arctangent (Algorithm 12 page 64). *)

let arctan_ x =
  let square_x = Q.mul x x in
  let next n an =
    Q.mul (Q.mul an square_x) (Q.of_ints (2 * n + 1) (2 * n + 3))
  in
  alternate_powerserie_ x next

let arctan_def x =
  create
    (function n ->
       let k = max 0 (n + 1) in
       let xk = approx x k in
       if Z.compare xk Z.zero == 0 then
	 z_zero
       else
	 let q = Q.make xk (Z.pow z_four k) in
	 q_floor (Q.add
		    (Q.div (Q.add (arctan_ q (n + 1)) q_one) q_four)
		    (Q.div
		       (bexp (n + k))
		       (Q.add (bexp (2 * n + 2))
			  (Q.of_bigint (Z.add (Z.mul xk xk) xk))))))

(*s The above definition of [arctan] converges very slowly when $|x|\ge 1$.
    The convergence is accelerated using the following identities:
    \begin{displaymath}
      \begin{array}{lll}
      \arctan(x)
        & = -\pi/2 - \arctan(1/x) & \mbox{ when }x<-1 \\
        & = -\pi/4 - \arctan((1-x^2)/(2x))/2 & \mbox{ when }x\approx-1 \\
        & = +\pi/4 - \arctan((1-x^2)/(2x))/2 & \mbox{ when }x\approx1 \\
        & = +\pi/2 - \arctan(1/x) & \mbox{ when }x>1
      \end{array}
    \end{displaymath}
    We use the approximation of $x$ at order 1 to discriminate between the
    cases. *)

let arctan x =
  let x1 = approx x 1 in
  if Z.compare x1 (Z.of_int (-5)) < 0 then
    (* $x < -1$ *)
    neg (half_pi +! arctan_def (inv x))
  else if Z.compare x1 (Z.of_int (-3)) <= 0 then
    (* $x$ close to $-1$ *)
    neg (half_pi +! arctan_def ((one -! x *! x) /! (two *! x))) /! two
  else if Z.compare x1 (Z.of_int 5) >  0 then
    (* $x > 1$ *)
    half_pi -! arctan_def (inv x)
  else if Z.compare x1 (Z.of_int 3) >= 0 then
    (* $x$ close to 1 *)
    (half_pi -! arctan_def ((one -! x *! x) /! (two *! x))) /! two
  else
    (* $x$ close to 0 *)
    arctan_def x

(*s Arcsinus and arccosinus are derived from arctangent (Algorithm 14
    page 69). We use $\arcsin(x)+\arccos(x)=\pi/2$ to avoid
    non-termination of $\arcsin(1)$ and $\arccos(0)$. *)

let arcsin_def x = arctan (x /! (sqrt (one -! (x *! x))))

let arccos_def x = arctan ((sqrt (one -! (x *! x))) /! x)

let arcsin x =
  let x1 = approx x 1 in
  if z_le (Z.abs x1) z_two then (* |x| < 3/4 *) arcsin_def x
  else if z_le z_three x1 then (* x > 1/2 *) half_pi -! arccos_def x
  else (* x < -1/2 *) arccos_def (neg x) -! half_pi

let arccos x =
  let x1 = approx x 1 in
  if z_le (Z.abs x1) z_two then (* |x| < 3/4 *) half_pi -! arcsin_def x
  else if z_le z_three x1 then  (* x > 1/2 *)arccos_def x
  else (* x < -1/2 *) pi -! arccos_def (neg x)

(*s Sinus (Algorithm 15 page 69). *)

let rec sin_ x p =
  if Q.compare x q_zero >= 0 then
    let square_x = Q.mul x x in
    let next n an =
      Q.mul (Q.mul (Q.mul an square_x) (Q.of_ints 1 (2 * n + 2)))
	    (Q.of_ints 1 (2 * n + 3))
    in
    alternate_powerserie_ x next p
  else
    Q.neg (sin_ (Q.neg x) p)

let sin x =
  let p = Z.pred (approx (x /! pi) 0) in
  let theta = if Z.compare p Z.zero == 0 then x else x -! ((of_z p) *! pi) in
  let z = half_pi in
  create
    (fun n ->
       let k = max 2 (n + 2) in
       let zk = approx z k in
       let twozk = Z.shift_left zk 1 in
       let threezk = Z.mul zk z_three in
       let fourzk = Z.shift_left zk 2 in
       let thetak = approx theta k in
       if (z_between z_zero thetak z_one) ||
	  (z_between (Z.sub fourzk z_four) thetak (Z.add fourzk z_four)) ||
	  (z_between (Z.sub twozk z_two) thetak (Z.add twozk z_two)) then
         z_zero
       else if z_between (Z.pred zk) thetak (Z.succ zk) then
	 let bn = Z.shift_left z_one (n + n) in
	 if z_even p then bn else Z.neg bn
       else if z_between (Z.sub threezk z_three) thetak (Z.add threezk z_three) then
	 let bn = Z.shift_left z_one (n + n) in
	 if z_even p then Z.neg bn else bn
       else
         let q = Q.make thetak (Z.pow z_four k) in
	 let s = sin_ q (n + 2) in
	 let bw = Q.of_ints 16 1 in
	 let bn_k = bexp (n - k) in
	 let r =
	   if (z_between z_two thetak (Z.sub zk z_two)) ||
              (z_between (Z.add zk z_two) thetak (Z.sub twozk z_three)) then
	     q_floor (Q.add (Q.div (Q.add s q_one) bw) bn_k)
	   else
	     q_ceil (Q.sub (Q.div (Q.sub s q_one) bw) bn_k)
	 in
	 if z_even p then r else Z.neg r)

(*s Cosinus and tangent are derived from sinus (Algorithm 16 page 78). *)

let cos x = sin (half_pi -! x)

let tan x = (sin x) /! (cos x)

(*s Euler constant [e]. *)

type sum_cache = {
  mutable order : int;
  mutable sum : Q.t; (* sum up to [order] *)
  mutable term : Q.t; (* last term $a_{order}$ *)
  mutable prec : int
}

let e =
  let e_cache = { order = 1; sum = q_two; term = q_one; prec = 0 } in
  create
    (fun p ->
       if p <= e_cache.prec then
	 fmul_Bexp e_cache.sum p
       else
	 let eps = bexp (-p) in
	 let rec sum s n an =
	   let rn = Q.mul (Q.of_ints 1 n) an in
	   if Q.compare rn eps <= 0 then begin
	     e_cache.order <- n;
	     e_cache.sum <- s;
	     e_cache.term <- an;
	     e_cache.prec <- p;
	     fmul_Bexp s p
	   end else
	     let asn = Q.mul (Q.of_ints 1 (n + 1)) an in
	     sum (Q.add s asn) (n + 1) asn
	 in
	 sum e_cache.sum e_cache.order e_cache.term)

(*s Natural logarithm (Algorithm 9 page 62). *)

let ln_above_1 r =
  let y = Q.div (Q.sub r q_one) (Q.add r q_one) in
  let y_square = Q.mul y y in
  let one_minus_y_square = Q.sub q_one y_square in
  fun n ->
    let eps = bexp (-n) in
    let rec sum s k p =
      (* [s] is already the sum up to $a_k$ *)
      let p' = Q.mul p y_square in
      let t = Q.mul p' (Q.of_ints 1 (k + 2)) in
      if Q.compare (Q.div t one_minus_y_square) eps < 0 then
	Q.mul q_two s
      else
	sum (Q.add s t) (k + 2) p'
    in
    Q.div (sum y 1 y) eps

let rec ln_ r =
  if Q.compare r q_zero <= 0 then invalid_arg "Creal.ln";
  let cmp1 = Q.compare r q_one in
  if cmp1 < 0 then
    (* $r < 1$ *)
    let ln_inverse_r = ln_ (Q.inv r) in
    (fun n -> Q.neg (ln_inverse_r n))
  else if cmp1 == 0 then
    (* $r = 1$ *)
    (fun _ -> q_zero)
  else
    (* $r > 1$ *)
    ln_above_1 r

let ln_4 = let f = ln_above_1 q_four in create (fun n -> q_floor (f n))

let rec ln x =
  let msd_x = msd x in
  let k = -msd_x + 1 in
  if k != 0 then
    ln (x /! (of_q (bexp k))) +! (of_int k) *! ln_4
  else
    create
      (fun n ->
	 let w = 2 - min 0 n in
	 let k = n + msd_x + w in
	 let xk = Q.of_bigint (approx x k) in
	 let q = Q.div xk (bexp k) in
	 q_floor (Q.add (Q.div (Q.add (ln_ q (n + w)) q_one) (bexp w))
		        (Q.div (bexp n) xk)))

let log ~base:x y = ln y /! ln x

(*s Inverses of hyperbolic functions. *)

let arcsinh x = ln (x +! sqrt (x *! x +! one))
let arccosh x = ln (x +! sqrt (x *! x -! one))
let arctanh x = ln ((one +! x) /! (one -! x)) /! two

(*s Exponential (Algorithm 7 page 57). *)

let exp_neg_ r =
  (* $-1 \le r < 0$ *)
  let r = q_abs r in
  let next n an = Q.mul (Q.mul an r) (Q.of_ints 1 (n + 1)) in
  create (fun n -> q_floor (alternate_powerserie_ q_one next n))

let exp_ r =
  if Q.compare r q_zero == 0 then
    one
  else
    let s_floor_r = Z.add (q_floor r) z_one in
    mul (pow_z e s_floor_r) (exp_neg_ (Q.sub r (Q.of_bigint s_floor_r)))

let exp x =
  create
    (fun n_ ->
      let n = max n_ 1 in
      let r =
       let qbn = bexp n in
       let bn = of_q qbn in
       let invqbn = Q.inv qbn in
       let one_plus_invqbn = Q.add q_one invqbn in
       let test1 () =
	 let lsup = log ~base:four (of_int 7 /! ln ((bn +! one) /! (bn -! one))) in
	 let l = Z.to_int (approx lsup 0) + 1 in
	 let xl = approx x l in
	 let log1 = q_floor (ln_ (Q.sub q_one invqbn) l) in
	 let log2 = q_floor (ln_ one_plus_invqbn l) in
	 (Z.compare (Z.add log1 z_two) xl < 0) &&
	 (Z.compare xl (Z.sub log2 z_two) < 0)
       in
       let test2 () =
	 let x0 = approx x 0 in
	 let m = Z.sub (q_floor (ln_ one_plus_invqbn 0)) z_two in
	 Z.compare x0 m <= 0
       in
       if (n > 0 && test1 ()) || (n <= 0 && test2 ()) then
	 fmul_Bexp q_one n
       else
	 let msd_x = msd x in
	 let clogBe =
	   if Z.compare (approx x msd_x) z_one >= 0 then
	     Q.of_ints 577080 100000
	   else
	     Q.of_ints (-72134) 100000
	 in
	 let d2 = Q.div clogBe (bexp msd_x) in
	 let p = max 0 (n + 1) in
	 let d = q_max (Q.of_ints (-p) 1) d2 in
	 let k2 = q_ceil (Q.add d (Q.of_ints 44732 100000)) in
	 let k = max 1 (max msd_x (p + 1 + Z.to_int k2)) in
	 let bk = bexp k in
	 let xk = approx x k in
	 let xkBk = Q.div (Q.of_bigint xk) bk in
	 let exp_xkBk_p = approx (exp_ xkBk) p in
	 if Z.compare exp_xkBk_p z_zero <= 0 then
	   z_zero
	 else
	   q_ceil (Q.mul (Q.sub (Q.div (Q.of_bigint exp_xkBk_p) q_four) q_one)
		         (Q.sub q_one (Q.inv bk)))
      in
      Z.shift_right r (2 * (n - n_)))

let pow x y = exp (y *! ln x)

let root n x = pow x (inv (of_int n))

(*s Hyperbolic functions. *)

let sinh x = (exp x -! exp (neg x)) /! two

let cosh x = (exp x +! exp (neg x)) /! two

let tanh x = sinh x /! cosh x

(*s Comparisons. [cmp] is absolute comparison and [rel_cmp] is comparison
    up to $4^{-k}$. *)

let compare x y =
  let rec cmp_rec n =
    let xn = approx x n in
    let yn = approx y n in
    if z_gt (Z.succ xn) (Z.pred yn) &&
       z_gt (Z.succ yn) (Z.pred xn)
    then
      cmp_rec (succ n)
    else
      if z_le (Z.succ xn) (Z.pred yn) then -1 else 1
  in
  cmp_rec 0

let rel_cmp k x y =
  let rec cmp_rec n =
    let xn = approx x n in
    let yn = approx y n in
    if z_gt (Z.succ xn) (Z.pred yn) &&
       z_gt (Z.succ yn) (Z.pred xn) && n <= k + 2
    then
      cmp_rec (succ n)
    else if z_le (Z.succ xn) (Z.pred yn) then
      -1
    else if z_le (Z.succ yn) (Z.pred xn) then
      1
    else
      0
  in
  cmp_rec 0

(*s Coercions to and from type [float]. *)

let of_float f = of_q (Q.of_float f)

let to_float x n = Q.to_float (to_q x n)

(*s Coercion to and from type [string]. *)

let of_string ?(radix=10) s =
  try
    begin
      try
	let n = String.length s in
	let p = String.index s '.' in
	let dec = n - p - 1 in
	let s' = (String.sub s 0 p) ^ (String.sub s (p + 1) dec) in
	of_q (Q.make (Z.of_string_base radix s') (Z.pow (Z.of_int radix) dec))
      with Not_found ->
	of_z (Z.of_string_base radix s)
    end
  with Invalid_argument _ -> invalid_arg "Creal.of_string"

(*s Decimal approximation of [x] at order [p]. We look for an integer [n]
    such that $|10^px - n| < 1/2$ i.e. the integer closest to
    $10^px$. There is sometimes no such integer but then we can find a
    decimal approximation at order [p+1].

    We first compute $y = 10^px$ and [approx y 3] i.e. an approximation
    $y_3/64$ of $y$. Let $q$ and $r$ be the quotient and remainder of the
    division $y_3/64$ such that $y_3 = 64q+r$ and $0\le r<63$.
    If $r\le 31$ then $n$ is $q$; If $r\ge 33$ then $n$ is $q+1$;
    Otherwise $10q+5$ is a decimal approximation of $x$ at order $p+1$. *)

let to_string_aux x p =
  if p < 0 then invalid_arg "Creal.to_string";
  let tenp = Z.pow (Z.of_int 10) p in
  let y = mul (of_z tenp) x in
  let y3 = approx y 3 in
  let r = Z.extract y3 0 6 in
  let r = Z.to_int r in
  let q = Z.shift_right y3 6 in
  let n,p =
    if r <= 31 then q, p
    else if r >= 33 then Z.succ q, p
    else Z.add (Z.mul q (Z.of_int 10)) (Z.of_int 5), succ p
  in
  let ns = Z.to_string (Z.abs n) in
  let lns = String.length ns in
  let ins,dns =
    if lns >= p+1 then
      String.sub ns 0 (lns - p), String.sub ns (lns - p) p
    else
      "0", String.make (p - lns) '0' ^ ns
  in
  Z.sign n, ins, dns

let to_string x p =
  let sgn,i,f = to_string_aux x p in
  (if sgn < 0 then "-" else "") ^ i ^ "." ^ f

(*s Coercion to type [string] with digits packed 5 by 5. *)

let string_concat = String.concat ""

let beautiful s =
  let n = String.length s in
  let eol i = if (i + 5) mod 65 == 0 then "\n" else " " in
  let rec cut i =
    String.sub s i (min 5 (n - i)) ::
    if i < n - 5 then eol i :: cut (i + 5) else []
  in
  string_concat (cut 0)

let to_beautiful_string x p =
  let sgn,i,f = to_string_aux x p in
  let nl = if String.length i + String.length f > 75 then "\n" else "" in
  (if sgn < 0 then "-" else "") ^ i ^ "." ^ nl ^ beautiful f

(* min and max here not to hide Pervasives's min and max *)

(**
let min x y = create (fun n -> Z.min (approx x n) (approx y n))
let max x y = create (fun n -> Z.max (approx x n) (approx y n))
**)
let min x y =
  let min_xy = ref None in
  create
    (fun n -> match !min_xy with
       | Some r -> approx r n
       | None ->
	   let xn = approx x n in
	   let yn = approx y n in
	   if z_le (Z.succ xn) (Z.pred yn) then begin
	     min_xy := Some x; xn
	   end else if z_le (Z.succ yn) (Z.pred xn) then begin
	     min_xy := Some y; yn
	   end else Z.min xn yn)

let max x y =
  let max_xy = ref None in
  create
    (fun n -> match !max_xy with
       | Some r -> approx r n
       | None ->
	   let xn = approx x n in
	   let yn = approx y n in
	   if z_le (Z.succ xn) (Z.pred yn) then begin
	     max_xy := Some y; yn
	   end else if z_le (Z.succ yn) (Z.pred xn) then begin
	     max_xy := Some x; xn
	   end else Z.max xn yn)

(*s Format pretty-printer. *)

let print_precision = ref 10
let set_print_precision = (:=) print_precision
let print fmt x = Format.fprintf fmt "%s" (to_string x !print_precision)

module Infixes = struct
  let (+!) = add
  let (-!) = sub
  let ( *! ) = mul
  let (/!) = div
end
