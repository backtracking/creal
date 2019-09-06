
(*s Test program for [Creal]. *)

open Printf
open CReal
open CReal.Infixes

(*s Options *)

let prec = ref 50
let display = ref true
let sanity_check = ref false
let exit_on_error = ref false

let _ = 
  Arg.parse 
      ["-p", Arg.Int ((:=) prec), "n  set the precision";
       "-silent", Arg.Clear display, "  no display";
       "-check", Arg.Set sanity_check, "  only sanity checks";
       "-exit-on-error", Arg.Set exit_on_error, " exit with error code 1 if an error occurs"
      ]
      (fun s -> raise (Arg.Bad ("unknown option " ^ s)))
      "test [-p prec] [silent]"

(*s Sanity checks. Compare two numbers up to the precision. *)

let _ = 
  if true then begin 
    printf "*** Sanity checks ***\n\n"; flush stdout
  end

let check msg x y =
  if true then begin
    printf "%s... " msg; flush stdout;
    let delta = Z.sub (approx x !prec) (approx y !prec) in
    if Z.compare (Z.abs delta) Z.one <= 0 then 
      printf "ok\n\n"
    else begin
      printf "FAILED!\n\n"; if !exit_on_error then exit 1
    end;
    flush stdout
  end

let sqrt_2 = sqrt two

let _ = check "sqrt(2)^2 = 2" (sqrt_2 *! sqrt_2) two

let _ = check "1/sqrt(2) = sqrt(2)/2" (inv sqrt_2) (sqrt_2 /! two)

let sqrt_3 = sqrt (of_int 3)

let _ = check "1 = (sqrt(3) + sqrt(2)) * (sqrt(3) - sqrt(2))"
	  one ((sqrt_3 +! sqrt_2) *! (sqrt_3 -! sqrt_2))

let _ = check "(sqrt(2) ^ sqrt(2)) ^ sqrt(2) = 2"
	  (pow (pow sqrt_2 sqrt_2) sqrt_2) two

let one_third = of_int 1 /! of_int 3
let root3 x = pow x one_third

let _ = check "54^1/3 - 2^1/3 = 16^1/3" 
	  (root3 (of_int 54) -! root3 two) (root3 (of_int 16))

let _ = check "cos(0)=1" (cos zero) one
let _ = check "cos(pi/2)=0" (cos half_pi) zero
let _ = check "sin(0)=0" (sin zero) zero
let _ = check "sin(pi/2)=1" (sin half_pi) one

let pi_over_4 = pi /! (of_int 4)
let square x = x *! x
let _ = check "cos^2(pi/4) + sin^2(pi/4) = 1"
	  (square (cos pi_over_4) +! square (sin pi_over_4)) one

let _ = check "tan(pi/4) = 1" (tan pi_over_4) one

let _ = check "pi/4 = 4arctan(1/5) - arctan(1/239)" pi_over_4 
	  (of_int 4 *! arctan_reciproqual 5 -! arctan_reciproqual 239)

let _ = check "ln(1) = 0" (ln one) zero

let _ = check "ln(e) = 1" (ln e) one

let _ = check "ln(pi*pi) = 2ln(pi)" (ln (square pi)) (two *! ln pi)

let _ = check "exp(-pi) = exp(-pi/2) * exp(-pi/2)"
	  (exp (neg pi)) (let y = exp (neg half_pi) in y *! y)

let _ = if !sanity_check then exit 0


(*s Benchmark. *)

(* Test function: display the real number, if not [silent] ; otherwise, 
   just compute the approximation (for timings). *)

let _ = printf "\n*** Benchmarks ***\n\n"; flush stdout

let test msg beautiful x =
  if !display then begin
    printf "%s = " msg; flush stdout;
    printf "%s\n\n"
      (if beautiful then to_beautiful_string x !prec else to_string x !prec);
    flush stdout
  end else begin
    printf "%s\n" msg;
    flush stdout;
    ignore (approx x !prec)
  end

(*s golden ratio *)
let phi = (one +! sqrt (of_int 5)) /! (of_int 2)
let _ = test "golden ratio" true phi

(* e (predefined in [Creal]) *)
let _ = test "e" true e

(* pi (predefined in [Creal]) *)
let _ = test "pi" true pi

(*s The Exact Arithmetic Competition: Level 0 Tests 
   http://www.cs.man.ac.uk/arch/dlester/arithmetic/level0t.html *)

(* sqrt(pi) *)
let _ = test "sqrt(pi)" false (sqrt pi)

(* sin(exp(1)) *)
let _ = test "sin(e)" false (sin e)

(* cos(exp(1)) *)
let _ = test "cos(e)" false (cos e)

(* sin(sin(sin(1))) *)
let x = sin (sin (sin one))
let _ = test "sin(sin(sin(1)))" false x

(* cos(cos(cos(1))) *)
let x = cos (cos (cos one))
let _ = test "cos(cos(cos(1)))" false x

(* exp(exp(exp(1))) *)
let x = exp (exp (exp one))
let _ = test "exp(exp(exp(1)))" false x

(* log(pi) *)
let _ = test "ln(pi)" false (ln pi)

(* log(1+log(1+log(1+pi))) *)
let ln_ln_ln_pi = ln (one +! ln (one +! ln (one +! pi)))
let _ = test "ln(1+ln(1+ln(1+pi)))" false ln_ln_ln_pi

(* log(1+log(1+log(1+exp(1)))) *)
let ln_ln_ln_e = ln (one +! ln (one +! ln (one +! e)))
let _ = test "ln(1+ln(1+ln(1+e)))" false ln_ln_ln_e

(*i
(* log(1+log(1+log(1+log(1+log(1+log(1+pi)))))) *)
let x = ln (one +! ln (one +! ln (one +! ln_ln_ln_pi)))
let _ = test "ln(1+ln(1+ln(1+ln(1+ln(1+ln(1+pi))))))" false x

(* log(1+log(1+log(1+log(1+log(1+log(1+exp(1))))))) *)
let x = ln (one +! ln (one +! ln (one +! ln_ln_ln_e)))
let _ = test "ln(1+ln(1+ln(1+ln(1+ln(1+ln(1+e))))))" false x
i*)

(* sin(1e50) *)
let ten_to_50 = pow_int (of_int 10) 50
let x = sin ten_to_50
let _ = test "sin(1e50)" false x

(* cos(1e50) *)
let x = cos ten_to_50
let _ = test "cos(1e50)" false x

(* arctan(1) *)
		    (*let _ = test "arctan(1)" false (arctan one)*)

(*i

(* BUG GMP 2 *)
let q = 
  Q.from_zs (Z.from_int 1) (Z.from_string "19807040628566084398385987584" 10)
let _ = Q.add q (Q.from_ints 1 2)

(* BUG GMP 3 *)
let q = Q.from_zs (Z.from_string "112803124130337404998606757686274889113032882986303222429756948481" 10) (Z.from_string "5192296858534827628530496329220096" 10)
let q' = Q.add q (Q.from_ints 1 2)
let _ = Z.fdiv_q (Q.get_num q') (Q.get_den q')

let time f x = 
  let old = Sys.time () in 
  let y = f x in 
  Printf.printf "%f\n" (Sys.time () -. old); 
  y
;;

i*)
