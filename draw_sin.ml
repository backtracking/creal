
(* Drawing the sin function accurately using exact real arithmetic *)

open Format
open Graphics
open CReal

let xmin = of_string Sys.argv.(1)
let xmax = of_string Sys.argv.(2)
let () = printf "%a..%a@." print xmin print xmax

let width = 800
let height = 600
let () = open_graph (sprintf " %dx%d" width height)

let ymin = of_string "-1.0"
let ymax = of_string "1.0"

let px = 2. /. float height
let prec = truncate (ceil (-. Stdlib.log px /. Stdlib.log 4.))
let () = printf "prec = %d@." prec

let xstep = div (sub xmax xmin) (of_int width)
let stepy = div (of_int height) (sub ymax ymin)

let sin gx =
  let x = add xmin (mul (of_int gx) xstep) in
  let y = sin x in
  let gy = mul (sub y ymin) stepy in
  truncate (to_float gy prec)

let () =
  moveto 0 (sin 0);
  for i = 1 to width - 1 do
    lineto i (sin i)
  done



let () = ignore (read_key ())
