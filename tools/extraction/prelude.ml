(* the literals of the terms of tools/spec/sql2coq.py, as values of the extracted types *)
open Sqlfs_lib

let rec nat k = if k <= 0 then O else S (nat (k - 1))

let rec pos_of_int k = if k = 1 then XH else if k land 1 = 1 then XI (pos_of_int (k lsr 1)) else XO (pos_of_int (k lsr 1))

let z_of_int k = if k = 0 then Z0 else if k > 0 then Zpos (pos_of_int k) else Zneg (pos_of_int (- k))

(* a decimal numeral of any size, digit by digit *)
let z s =
  let neg = String.length s > 0 && s.[0] = '-' in
  let digits = if neg then String.sub s 1 (String.length s - 1) else s in
  let ten = z_of_int 10 in
  let v = ref Z0 in
  String.iter (fun c -> v := Z.add (Z.mul !v ten) (z_of_int (Char.code c - 48))) digits;
  if neg then Z.opp !v else !v

let pos s = match z s with Zpos p -> p | _ -> failwith "positive"

let n s = match z s with Z0 -> N0 | Zpos p -> Npos p | Zneg _ -> failwith "N"

let qmake a b = { qnum = a; qden = b }

let print_rows d rows =
  List.iter (fun row -> print_endline (String.concat "\t" (List.map (result_text d) row))) rows

(* the dates and times of Values.v ([VDate], [VTime], [VTs]), which extraction inlines *)
let vdate days = NullValues.Value_T (Some (days, O))
let vtime us fsp = NullValues.Value_T (Some (us, nat (1 + 10 * fsp)))
let vts ts fsp = NullValues.Value_T (Some (ts, nat (2 + 10 * fsp)))

(* the rows of a table written by term2ml.externalize_tables: a line per row, a tab between the values, each
   value a tag and its fields *)
let unhex s = String.init (String.length s / 2) (fun i -> Char.chr (int_of_string ("0x" ^ String.sub s (2 * i) 2)))

let value_of_cell c =
  match String.split_on_char '|' c with
  | ["Z"; v] -> vZ (z v)
  | ["S"; h] -> vS (unhex h)
  | ["NZ"] -> nullZ
  | ["NS"] -> nullS
  | ["NQ"] -> nullQ
  | ["NB"] -> NullValues.Value_bool None
  | ["D"; v; sc] -> vD (z v) (nat (int_of_string sc))
  | ["F"; b; v; e] -> vFl (b = "1") (z v) (z e)
  | ["DT"; d] -> vdate (z d)
  | ["TS"; v; f] -> vts (z v) (int_of_string f)
  | ["TM"; v; f] -> vtime (z v) (int_of_string f)
  | _ -> failwith ("unknown cell " ^ c)

let rows path =
  let ic = open_in_bin path in
  let rec go acc =
    match input_line ic with
    | line -> go (List.rev_map value_of_cell (String.split_on_char '\t' line) |> List.rev |> fun r -> r :: acc)
    | exception End_of_file -> close_in ic; List.rev acc in
  go []
