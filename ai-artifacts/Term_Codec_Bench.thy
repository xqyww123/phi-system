theory Term_Codec_Bench
  imports Minilang_AoA.Minilang_AoA
begin

ML \<open>
(* ---------------------------------------------------------------- *)
(* Codec A: Pure's XML term codec + YXML text                        *)
(* ---------------------------------------------------------------- *)

fun xml_encode (t: term) : string = YXML.string_of_body (Term_XML.Encode.term_raw t)
fun xml_decode (s: string) : term = Term_XML.Decode.term_raw (YXML.parse_body s)

(* ---------------------------------------------------------------- *)
(* Codec B: Isabelle_RPC's msgpack term codec.                       *)
(* RPC_Pretty.pack_raw_term is a MessagePackBinIO packer, i.e. it can *)
(* only be driven through a BinIO.StreamIO stream (the BytesIO twin  *)
(* is not instantiated for terms).  We therefore build an in-memory  *)
(* BinPrimIO reader/writer -- no temp file, no syscalls.             *)
(* ---------------------------------------------------------------- *)

fun binio_pack (packer: 'a MessagePackBinIO.Pack.packer) (x: 'a) : string =
  let
    val chunks = Unsynchronized.ref ([]: Word8Vector.vector list)
    val wr = BinPrimIO.WR {
      name = "mem_out", chunkSize = 4096,
      writeVec = SOME (fn slice =>
        let val n = Word8VectorSlice.length slice
        in chunks := Word8VectorSlice.vector slice :: ! chunks; n end),
      writeArr = SOME (fn slice =>
        let val n = Word8ArraySlice.length slice
        in chunks := Word8ArraySlice.vector slice :: ! chunks; n end),
      writeVecNB = NONE, writeArrNB = NONE,
      block = NONE, canOutput = SOME (fn () => true),
      getPos = NONE, setPos = NONE, endPos = NONE, verifyPos = NONE,
      close = fn () => (), ioDesc = NONE}
    val outs = BinIO.StreamIO.mkOutstream (wr, IO.BLOCK_BUF)
    val _ = packer x outs
    val _ = BinIO.StreamIO.closeOut outs
  in Byte.bytesToString (Word8Vector.concat (rev (! chunks))) end

fun binio_unpack (unpacker: 'a MessagePackBinIO.Unpack.unpacker) (s: string) : 'a =
  let
    val rd = BinPrimIO.RD {
      name = "mem_in", chunkSize = 4096,
      readVec = SOME (fn _ => Word8Vector.fromList []),
      readArr = NONE, readVecNB = NONE, readArrNB = NONE,
      block = NONE, canInput = SOME (fn () => true), avail = fn () => SOME 0,
      getPos = NONE, setPos = NONE, endPos = NONE, verifyPos = NONE,
      close = fn () => (), ioDesc = NONE}
    val ins = BinIO.StreamIO.mkInstream (rd, Byte.stringToBytes s)
  in #1 (unpacker ins) end

fun mp_encode (t: term) : string = binio_pack RPC_Pretty.pack_raw_term t
fun mp_decode (s: string) : term = binio_unpack RPC_Pretty.unpack_raw_term s
\<close>

ML \<open>
(* ---------------------------------------------------------------- *)
(* Test data                                                        *)
(* ---------------------------------------------------------------- *)

val all_props = map (Thm.prop_of o snd) (Global_Theory.all_thms_of \<^theory> false);

val set_first5000 = take 5000 all_props;
val set_top500 =
  all_props
  |> map (fn t => (size_of_term t, t))
  |> sort (fn ((a, _), (b, _)) => int_ord (b, a))
  |> take 500
  |> map snd;

fun total_size ts = fold (fn t => fn n => n + size_of_term t) ts 0;

val _ = writeln ("all theorems in scope: " ^ string_of_int (length all_props));
val _ = writeln ("SET1 (first 5000): n=" ^ string_of_int (length set_first5000) ^
                 " total size_of_term=" ^ string_of_int (total_size set_first5000));
val _ = writeln ("SET2 (top 500 by size): n=" ^ string_of_int (length set_top500) ^
                 " total size_of_term=" ^ string_of_int (total_size set_top500));
\<close>

ML \<open>
(* ---------------------------------------------------------------- *)
(* Measurement                                                      *)
(* ---------------------------------------------------------------- *)

fun ms (t: Time.time) = Real.fmt (StringCvt.FIX (SOME 1)) (Time.toReal t * 1000.0);

fun run3 (f: unit -> 'a) : Timing.timing list * 'a =
  let
    val (t1, _) = Timing.timing f ();
    val (t2, _) = Timing.timing f ();
    val (t3, r) = Timing.timing f ();
  in ([t1, t2, t3], r) end;

fun show_runs (ts: Timing.timing list) =
  "elapsed[" ^ space_implode ", " (map (ms o #elapsed) ts) ^ "] ms; " ^
  "cpu[" ^ space_implode ", " (map (ms o #cpu) ts) ^ "] ms";

fun first_diff (xs, ys) =
  let
    fun go _ [] [] = NONE
      | go i (x :: xs) (y :: ys) = if x = y then go (i + 1) xs ys else SOME (i, x, y)
      | go i _ _ = SOME (i, Term.dummy, Term.dummy);
  in go 0 xs ys end;

fun bench (codec_name, enc, dec) (set_name, terms) =
  let
    val n = length terms;
    val (enc_runs, encoded) = run3 (fn () => map enc terms);
    val bytes = fold (fn s => fn a => a + size s) encoded 0;
    val (dec_runs, decoded) = run3 (fn () => map dec encoded);
    val diff = first_diff (terms, decoded);
    val rt =
      (case diff of
        NONE => "ROUNDTRIP OK"
      | SOME (i, x, y) =>
          "ROUNDTRIP FAIL at index " ^ string_of_int i ^ "\n    orig: " ^
          ML_Syntax.print_term x ^ "\n    back: " ^ ML_Syntax.print_term y);
    val avg_bytes = Real.fmt (StringCvt.FIX (SOME 2)) (real bytes / real n);
    fun avg_us (ts: Timing.timing list) =
      space_implode ", "
        (map (fn t => Real.fmt (StringCvt.FIX (SOME 2)) (Time.toReal (#elapsed t) * 1.0E6 / real n)) ts);
  in
    writeln ("### " ^ codec_name ^ " | " ^ set_name ^ " (n=" ^ string_of_int n ^ ")\n" ^
      "  encode: " ^ show_runs enc_runs ^ "\n" ^
      "  encode per-term elapsed us: [" ^ avg_us enc_runs ^ "]\n" ^
      "  decode: " ^ show_runs dec_runs ^ "\n" ^
      "  decode per-term elapsed us: [" ^ avg_us dec_runs ^ "]\n" ^
      "  bytes: " ^ string_of_int bytes ^ " (avg " ^ avg_bytes ^ " B/term)\n" ^
      "  " ^ rt)
  end;

val codec_xml = ("XML+YXML (Term_XML.Encode.term_raw / YXML)", xml_encode, xml_decode);
val codec_mp = ("msgpack (RPC_Pretty.pack_raw_term)", mp_encode, mp_decode);
\<close>

ML \<open>bench codec_xml ("SET1 first5000", set_first5000)\<close>

ML \<open>bench codec_mp ("SET1 first5000", set_first5000)\<close>

ML \<open>bench codec_xml ("SET2 top500", set_top500)\<close>

ML \<open>bench codec_mp ("SET2 top500", set_top500)\<close>

end
