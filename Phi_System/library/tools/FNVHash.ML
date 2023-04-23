(*
STANDARD ML OF NEW JERSEY COPYRIGHT NOTICE, LICENSE AND DISCLAIMER.

Copyright (c) 2001-2020 by The Fellowship of SML/NJ
Copyright (c) 1989-2001 by Lucent Technologies

Permission to use, copy, modify, and distribute this software and its documentation for any purpose
and without fee is hereby granted, provided that the above copyright notice appear in all copies and
that both the copyright notice and this permission notice and warranty disclaimer appear in supporting
documentation, and that the name of Lucent Technologies, Bell Labs or any Lucent entity not be used
in advertising or publicity pertaining to distribution of the software without specific,
written prior permission.

Lucent disclaims all warranties with regard to this software, including all implied warranties of
merchantability and fitness. In no event shall Lucent be liable for any special, indirect or
consequential damages or any damages whatsoever resulting from loss of use, data or profits, whether
in an action of contract, negligence or other tortious action, arising out of or in connection with
the use or performance of this software.
*)

(* fnv-hash.sml
 *
 * COPYRIGHT (c) 2020 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * The interface to an implementation of the Fowler–Noll–Vo (FNV) hashing
 * algorithm.  We use the 64-bit FNV-1a algorithm.
 *
 * See https://en.wikipedia.org/wiki/Fowler–Noll–Vo_hash_function for details.
 *)

structure FNVHash : sig

    val offsetBasis : Word64.word

    val hashByte : Word8.word * Word64.word -> Word64.word
    val hashChar : char * Word64.word -> Word64.word

    val hashString : string -> Word64.word
    val hashSubstring : substring -> Word64.word

    val hashOne : Word64.word * Word64.word -> Word64.word

  end = struct

  (* values from https://en.wikipedia.org/wiki/Fowler–Noll–Vo_hash_function *)
    val offsetBasis : Word64.word = 0wxcbf29ce484222325
    val prime : Word64.word = 0wx00000100000001B3

    fun hashOne (b, h) = Word64.xorb(b, h) * prime

    fun hashByte (b, h) = hashOne (Word64.fromLargeWord(Word8.toLargeWord b), h)

    fun hashChar (c, h) = hashOne (Word64.fromInt(Char.ord c), h)

    fun hashString s = CharVector.foldl hashChar offsetBasis s
    fun hashSubstring ss = Substring.foldl hashChar offsetBasis ss

  end