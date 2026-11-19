(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Message digests: MD5 (RFC 1321), SHA-1, SHA-224/256, SHA-384/512 (FIPS 180-4), *)
(**   on lists of bytes, for the functions [md5], [sha1], [sha2], [sha256], ...     *)
(**                                                                                 *)
(************************************************************************************)

Require Import List ZArith Ascii String Bool.

Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

(** * Words *)
Definition wmask (w : Z) (x : Z) : Z := Z.land x (Z.ones w).
Definition rotl (w : Z) (x n : Z) : Z := wmask w (Z.lor (Z.shiftl x n) (Z.shiftr x (w - n))).
Definition rotr (w : Z) (x n : Z) : Z := wmask w (Z.lor (Z.shiftr x n) (Z.shiftl x (w - n))).
Definition wadd (w : Z) (l : list Z) : Z := wmask w (fold_left Z.add l 0).
Definition bnot (w : Z) (x : Z) : Z := wmask w (Z.lnot x).

(** the bytes of a word, big or little endian, and back *)
Fixpoint bytes_be (n : nat) (x : Z) : list Z :=
  match n with O => nil | S k => bytes_be k (Z.shiftr x 8) ++ [wmask 8 x] end.
Definition bytes_le (n : nat) (x : Z) : list Z := rev (bytes_be n x).
Definition word_be (l : list Z) : Z := fold_left (fun acc b => acc * 256 + b) l 0.
Definition word_le (l : list Z) : Z := word_be (rev l).

Fixpoint chunks (n : nat) (fuel : nat) (l : list Z) : list (list Z) :=
  match fuel with
  | O => nil
  | S f => match l with nil => nil | _ => firstn n l :: chunks n f (skipn n l) end
  end.

(** padding: [0x80], zeros, the length in bits on [lenbytes] bytes ([be]: big endian) *)
Definition md_pad (block lenbytes : nat) (be : bool) (m : list Z) : list Z :=
  let len := List.length m in
  let k := ((block + block - (len + 1 + lenbytes) mod block) mod block)%nat in
  let bits := Z.of_nat len * 8 in
  m ++ [128] ++ repeat 0 k ++ (if be then bytes_be lenbytes bits else bytes_le lenbytes bits).

(** * MD5 *)
Definition md5_s : list Z :=
  [7;12;17;22;7;12;17;22;7;12;17;22;7;12;17;22;5;9;14;20;5;9;14;20;5;9;14;20;5;9;14;20;
   4;11;16;23;4;11;16;23;4;11;16;23;4;11;16;23;6;10;15;21;6;10;15;21;6;10;15;21;6;10;15;21].

Definition md5_k : list Z :=
  [3614090360;3905402710;606105819;3250441966;4118548399;1200080426;2821735955;4249261313;
   1770035416;2336552879;4294925233;2304563134;1804603682;4254626195;2792965006;1236535329;
   4129170786;3225465664;643717713;3921069994;3593408605;38016083;3634488961;3889429448;
   568446438;3275163606;4107603335;1163531501;2850285829;4243563512;1735328473;2368359562;
   4294588738;2272392833;1839030562;4259657740;2763975236;1272893353;4139469664;3200236656;
   681279174;3936430074;3572445317;76029189;3654602809;3873151461;530742520;3299628645;
   4096336452;1126891415;2878612391;4237533241;1700485571;2399980690;4293915773;2240044497;
   1873313359;4264355552;2734768916;1309151649;4149444226;3174756917;718787259;3951481745].

Definition md5_block (h : Z * Z * Z * Z) (blk : list Z) : Z * Z * Z * Z :=
  let m := map word_le (chunks 4 16 blk) in
  let '(a0, b0, c0, d0) := h in
  let step (st : Z * Z * Z * Z) (i : nat) :=
      let '(a, b, c, d) := st in
      let '(f, g) :=
          if (i <? 16)%nat then (Z.lor (Z.land b c) (Z.land (bnot 32 b) d), i)
          else if (i <? 32)%nat then (Z.lor (Z.land d b) (Z.land (bnot 32 d) c), (5 * i + 1) mod 16)%nat
          else if (i <? 48)%nat then (Z.lxor b (Z.lxor c d), (3 * i + 5) mod 16)%nat
          else (Z.lxor c (Z.lor b (bnot 32 d)), (7 * i) mod 16)%nat in
      let f := wadd 32 [f; a; nth i md5_k 0; nth g m 0] in
      (d, wadd 32 [b; rotl 32 f (nth i md5_s 0)], b, c) in
  let '(a, b, c, d) := fold_left step (seq 0 64) (a0, b0, c0, d0) in
  (wadd 32 [a0; a], wadd 32 [b0; b], wadd 32 [c0; c], wadd 32 [d0; d]).

Definition md5 (m : list Z) : list Z :=
  let p := md_pad 64 8 false m in
  let '(a, b, c, d) := fold_left md5_block (chunks 64 (List.length p) p)
                                 (1732584193, 4023233417, 2562383102, 271733878) in
  bytes_le 4 a ++ bytes_le 4 b ++ bytes_le 4 c ++ bytes_le 4 d.

(** * SHA-1 *)
Fixpoint sched (w : Z) (f : list Z -> Z) (n : nat) (acc : list Z) : list Z :=
  (* [acc] in reverse order *)
  match n with O => rev acc | S k => sched w f k (f acc :: acc) end.

Definition sha1_block (h : list Z) (blk : list Z) : list Z :=
  let m := map word_be (chunks 4 16 blk) in
  let ws := sched 32 (fun r => rotl 32 (Z.lxor (Z.lxor (nth 2 r 0) (nth 7 r 0)) (Z.lxor (nth 13 r 0) (nth 15 r 0))) 1)
                  64 (rev m) in
  let step (st : list Z) (i : nat) :=
      match st with
      | [a; b; c; d; e] =>
        let '(f, k) :=
            if (i <? 20)%nat then (Z.lor (Z.land b c) (Z.land (bnot 32 b) d), 1518500249)
            else if (i <? 40)%nat then (Z.lxor b (Z.lxor c d), 1859775393)
            else if (i <? 60)%nat then (Z.lor (Z.lor (Z.land b c) (Z.land b d)) (Z.land c d), 2400959708)
            else (Z.lxor b (Z.lxor c d), 3395469782) in
        [wadd 32 [rotl 32 a 5; f; e; k; nth i ws 0]; a; rotl 32 b 30; c; d]
      | _ => st
      end in
  map (fun p => wadd 32 [fst p; snd p]) (combine h (fold_left step (seq 0 80) h)).

Definition sha1 (m : list Z) : list Z :=
  let p := md_pad 64 8 true m in
  flat_map (bytes_be 4) (fold_left sha1_block (chunks 64 (List.length p) p)
                                   [1732584193; 4023233417; 2562383102; 271733878; 3285377520]).

(** * SHA-2 *)
Definition sha256_k : list Z :=
  [1116352408;1899447441;3049323471;3921009573;961987163;1508970993;2453635748;2870763221;
   3624381080;310598401;607225278;1426881987;1925078388;2162078206;2614888103;3248222580;
   3835390401;4022224774;264347078;604807628;770255983;1249150122;1555081692;1996064986;
   2554220882;2821834349;2952996808;3210313671;3336571891;3584528711;113926993;338241895;
   666307205;773529912;1294757372;1396182291;1695183700;1986661051;2177026350;2456956037;
   2730485921;2820302411;3259730800;3345764771;3516065817;3600352804;4094571909;275423344;
   430227734;506948616;659060556;883997877;958139571;1322822218;1537002063;1747873779;
   1955562222;2024104815;2227730452;2361852424;2428436474;2756734187;3204031479;3329325298].

Definition sha512_k : list Z :=
  [4794697086780616226;8158064640168781261;13096744586834688815;16840607885511220156;
   4131703408338449720;6480981068601479193;10538285296894168987;12329834152419229976;
   15566598209576043074;1334009975649890238;2608012711638119052;6128411473006802146;
   8268148722764581231;9286055187155687089;11230858885718282805;13951009754708518548;
   16472876342353939154;17275323862435702243;1135362057144423861;2597628984639134821;
   3308224258029322869;5365058923640841347;6679025012923562964;8573033837759648693;
   10970295158949994411;12119686244451234320;12683024718118986047;13788192230050041572;
   14330467153632333762;15395433587784984357;489312712824947311;1452737877330783856;
   2861767655752347644;3322285676063803686;5560940570517711597;5996557281743188959;
   7280758554555802590;8532644243296465576;9350256976987008742;10552545826968843579;
   11727347734174303076;12113106623233404929;14000437183269869457;14369950271660146224;
   15101387698204529176;15463397548674623760;17586052441742319658;1182934255886127544;
   1847814050463011016;2177327727835720531;2830643537854262169;3796741975233480872;
   4115178125766777443;5681478168544905931;6601373596472566643;7507060721942968483;
   8399075790359081724;8693463985226723168;9568029438360202098;10144078919501101548;
   10430055236837252648;11840083180663258601;13761210420658862357;14299343276471374635;
   14566680578165727644;15097957966210449927;16922976911328602910;17689382322260857208;
   500013540394364858;748580250866718886;1242879168328830382;1977374033974150939;
   2944078676154940804;3659926193048069267;4368137639120453308;4836135668995329356;
   5532061633213252278;6448918945643986474;6902733635092675308;7801388544844847127].

(** [w]: the word size (32 or 64); [rot]: the rotations of [Sigma0], [Sigma1], [sigma0], [sigma1] *)
Definition sha2_block (w : Z) (rounds : nat) (ks : list Z) (rot : list Z) (h : list Z) (blk : list Z) : list Z :=
  let r i := nth i rot 0 in
  let bw := Z.to_nat (w / 8) in
  let m := map word_be (chunks bw 16 blk) in
  let s0 x := Z.lxor (Z.lxor (rotr w x (r 6%nat)) (rotr w x (r 7%nat))) (Z.shiftr x (r 8%nat)) in
  let s1 x := Z.lxor (Z.lxor (rotr w x (r 9%nat)) (rotr w x (r 10%nat))) (Z.shiftr x (r 11%nat)) in
  let ws := sched w (fun rv => wadd w [s1 (nth 1 rv 0); nth 6 rv 0; s0 (nth 14 rv 0); nth 15 rv 0])
                  (rounds - 16) (rev m) in
  let step (st : list Z) (i : nat) :=
      match st with
      | [a; b; c; d; e; f; g; hh] =>
        let S1 := Z.lxor (Z.lxor (rotr w e (r 3%nat)) (rotr w e (r 4%nat))) (rotr w e (r 5%nat)) in
        let ch := Z.lxor (Z.land e f) (Z.land (bnot w e) g) in
        let t1 := wadd w [hh; S1; ch; nth i ks 0; nth i ws 0] in
        let S0 := Z.lxor (Z.lxor (rotr w a (r 0%nat)) (rotr w a (r 1%nat))) (rotr w a (r 2%nat)) in
        let mj := Z.lxor (Z.lxor (Z.land a b) (Z.land a c)) (Z.land b c) in
        [wadd w [t1; S0; mj]; a; b; c; wadd w [d; t1]; e; f; g]
      | _ => st
      end in
  map (fun p => wadd w [fst p; snd p]) (combine h (fold_left step (seq 0 rounds) h)).

Definition sha256_rot : list Z := [2; 13; 22; 6; 11; 25; 7; 18; 3; 17; 19; 10].
Definition sha512_rot : list Z := [28; 34; 39; 14; 18; 41; 1; 8; 7; 19; 61; 6].

Definition sha2_32 (init : list Z) (out : nat) (m : list Z) : list Z :=
  let p := md_pad 64 8 true m in
  firstn out (flat_map (bytes_be 4) (fold_left (sha2_block 32 64 sha256_k sha256_rot) (chunks 64 (List.length p) p) init)).

Definition sha2_64 (init : list Z) (out : nat) (m : list Z) : list Z :=
  let p := md_pad 128 16 true m in
  firstn out (flat_map (bytes_be 8) (fold_left (sha2_block 64 80 sha512_k sha512_rot) (chunks 128 (List.length p) p) init)).

Definition sha224 := sha2_32 [3238371032; 914150663; 812702999; 4144912697; 4290775857; 1750603025; 1694076839; 3204075428] 28.
Definition sha256 := sha2_32 [1779033703; 3144134277; 1013904242; 2773480762; 1359893119; 2600822924; 528734635; 1541459225] 32.
Definition sha384 := sha2_64 [14680500436340154072; 7105036623409894663; 10473403895298186519; 1526699215303891257;
                              7436329637833083697; 10282925794625328401; 15784041429090275239; 5167115440072839076] 48.
Definition sha512 := sha2_64 [7640891576956012808; 13503953896175478587; 4354685564936845355; 11912009170470909681;
                              5840696475078001361; 11170449401992604703; 2270897969802886507; 6620516959819538809] 64.

(** * Bytes and text *)
Definition bytes_of_string (s : string) : list Z := map (fun c => Z.of_nat (nat_of_ascii c)) (list_ascii_of_string s).
Definition string_of_bytes (l : list Z) : string := string_of_list_ascii (map (fun b => ascii_of_nat (Z.to_nat b)) l).

Definition hex_digit (upper : bool) (d : Z) : ascii :=
  ascii_of_nat (Z.to_nat (if d <? 10 then 48 + d else (if upper then 55 else 87) + d)).

(** the hexadecimal text of bytes *)
Definition hex_of_bytes (upper : bool) (l : list Z) : string :=
  string_of_list_ascii (flat_map (fun b => [hex_digit upper (b / 16); hex_digit upper (b mod 16)]) l).

Definition hex_value (c : ascii) : option Z :=
  let n := Z.of_nat (nat_of_ascii c) in
  if (48 <=? n) && (n <=? 57) then Some (n - 48)
  else if (65 <=? n) && (n <=? 70) then Some (n - 55)
  else if (97 <=? n) && (n <=? 102) then Some (n - 87)
  else None.

(** the bytes of a hexadecimal text; [None] when a digit is not one; an odd length has a leading 0 *)
Definition bytes_of_hex (s : string) : option (list Z) :=
  let cs := list_ascii_of_string s in
  let cs := if Nat.odd (List.length cs) then "0"%char :: cs else cs in
  let fix go (l : list ascii) :=
      match l with
      | a :: b :: r => match hex_value a, hex_value b, go r with
                       | Some x, Some y, Some t => Some (x * 16 + y :: t)
                       | _, _, _ => None end
      | nil => Some nil
      | _ => None
      end in
  go cs.

(** Base64 (RFC 4648) *)
Definition b64_char (n : Z) : ascii :=
  ascii_of_nat (Z.to_nat (if n <? 26 then 65 + n else if n <? 52 then 71 + n else if n <? 62 then n - 4
                          else if n =? 62 then 43 else 47)).

Fixpoint to_base64_aux (fuel : nat) (l : list Z) : list ascii :=
  match fuel with
  | O => nil
  | S f =>
    match l with
    | a :: b :: c :: r => let x := a * 65536 + b * 256 + c in
                          b64_char (x / 262144) :: b64_char ((x / 4096) mod 64) :: b64_char ((x / 64) mod 64)
                                   :: b64_char (x mod 64) :: to_base64_aux f r
    | a :: b :: nil => let x := a * 65536 + b * 256 in
                       [b64_char (x / 262144); b64_char ((x / 4096) mod 64); b64_char ((x / 64) mod 64); "="%char]
    | a :: nil => let x := a * 65536 in [b64_char (x / 262144); b64_char ((x / 4096) mod 64); "="%char; "="%char]
    | nil => nil
    end
  end.

Definition to_base64 (l : list Z) : string := string_of_list_ascii (to_base64_aux (List.length l) l).

Definition b64_value (c : ascii) : option Z :=
  let n := Z.of_nat (nat_of_ascii c) in
  if (65 <=? n) && (n <=? 90) then Some (n - 65)
  else if (97 <=? n) && (n <=? 122) then Some (n - 71)
  else if (48 <=? n) && (n <=? 57) then Some (n + 4)
  else if n =? 43 then Some 62 else if n =? 47 then Some 63 else None.

(** the bytes of a Base64 text; [None] if it is not one *)
Definition from_base64 (s : string) : option (list Z) :=
  let cs := filter (fun c => negb (Ascii.eqb c "="%char)) (list_ascii_of_string s) in
  let fix go (l : list ascii) :=
      match l with
      | a :: b :: c :: d :: r =>
        match b64_value a, b64_value b, b64_value c, b64_value d, go r with
        | Some w, Some x, Some y, Some z, Some t =>
          let v := ((w * 64 + x) * 64 + y) * 64 + z in Some (v / 65536 :: (v / 256) mod 256 :: v mod 256 :: t)
        | _, _, _, _, _ => None end
      | a :: b :: c :: nil =>
        match b64_value a, b64_value b, b64_value c with
        | Some w, Some x, Some y => let v := ((w * 64 + x) * 64 + y) * 64 in Some [v / 65536; (v / 256) mod 256]
        | _, _, _ => None end
      | a :: b :: nil =>
        match b64_value a, b64_value b with
        | Some w, Some x => let v := (w * 64 + x) * 4096 in Some [v / 65536]
        | _, _ => None end
      | nil => Some nil
      | _ => None
      end in
  go cs.
