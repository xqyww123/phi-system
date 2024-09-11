structure Ag_Semantics = struct

fun size bvtys (Abs (_,T,X)) = size (T::bvtys) X
  | size bvtys tm =
      let fun is_TY \<^Type>\<open>TY\<close> = true
            | is_TY \<^Type>\<open>fun _ X\<close> = is_TY X
            | is_TY _ = false
          val (h,args) = Term.strip_comb tm
          val args' = filter (is_TY o curry fastype_of1 bvtys) args
       in if is_TY (fastype_of1 (bvtys, h))
       then 1 + fold (fn x => fn m => Int.max (size bvtys x,m)) args' 0
       else 0
      end

end