theory ERC20
  imports "../Phi_Solidity"
begin

consts Total_Supply :: nat

specification (Total_Supply)
  Total_Supply_LE[useful]: \<open>Total_Supply < 2 ^ Big 256\<close>
  unfolding Big_def
  using less_exp by blast

context solidity begin


definition Currency :: \<open>('VAL, nat) \<phi>\<close>
  where \<open>Currency = (\<lambda>x. (x \<Ztypecolon> \<nat>[256]) \<^bold>s\<^bold>u\<^bold>b\<^bold>j x \<le> Total_Supply)\<close>

lemma Currency_expn[\<phi>expns]:
  \<open>(x \<Ztypecolon> Currency) = ((x \<Ztypecolon> \<nat>[256]) \<^bold>s\<^bold>u\<^bold>b\<^bold>j x \<le> Total_Supply)\<close>
  unfolding \<phi>Type_def[where T=Currency]
  unfolding Currency_def
  ..

lemma [\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> Currency) \<Longrightarrow> (x \<le> Total_Supply \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def
  by (simp add: \<phi>expns)

lemma Currency_D[\<phi>reason on \<open>?x \<Ztypecolon> Currency \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> \<nat>[?b] \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x'
\<Longrightarrow> x \<Ztypecolon> Currency \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> \<nat>[256] \<^bold>a\<^bold>n\<^bold>d x \<le> Total_Supply\<close>
  unfolding Currency_expn \<medium_left_bracket> \<medium_right_bracket>. .

lemma Currency_I[\<phi>reason on \<open>?y \<Ztypecolon> \<nat>[?b] \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?x \<Ztypecolon> Currency \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<le> Total_Supply \<and> x = x'
\<Longrightarrow> x \<Ztypecolon> \<nat>[256] \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> Currency\<close>
  unfolding Currency_expn \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> Currency) ?TY\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> Currency) (\<tau>Int 256)\<close>
  unfolding \<phi>SemType_def subset_iff
  by (simp add: \<phi>expns)



proc balance_of:
  argument \<open>msg \<Ztypecolon> Msg\<heavy_comma>
      balance \<Ztypecolon> ledge: msg.contract msg \<^bold>\<rightarrow> \<bbbS>\<f>\<i>\<e>\<l>\<d> ''balance'' \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (account \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub>[\<^sub>] n \<Znrres> \<fish_eye>\<lbrakk>\<tau>Int 256\<rbrakk> Currency \<heavy_comma>
      \<^bold>v\<^bold>a\<^bold>l account \<Ztypecolon> Address\<close>
  return   \<open>msg \<Ztypecolon> Msg\<heavy_comma>
      balance \<Ztypecolon> ledge: msg.contract msg \<^bold>\<rightarrow> \<bbbS>\<f>\<i>\<e>\<l>\<d> ''balance'' \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (account \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub>[\<^sub>] n \<Znrres> \<fish_eye>\<lbrakk>\<tau>Int 256\<rbrakk> Currency \<heavy_comma>
      \<^bold>v\<^bold>a\<^bold>l balance \<Ztypecolon> \<nat>[256]\<close>
  \<medium_left_bracket>
    op_get_msg_addr[where G=msg.contract]
    op_root_ledge_ref
    op_get_member_ledgeRef[where field=\<open>''balance''\<close>]
    \<open>\<a>\<r>\<g>0\<close> op_get_mapping_ledgeRef
    op_load_ledge
  \<medium_right_bracket>. .

proc transfer:
  premises \<open>balance_alice + amount \<le> Total_Supply\<close>
  argument \<open>msg \<Ztypecolon> Msg\<heavy_comma>
      balance_sender \<Ztypecolon> ledge: msg.contract msg \<^bold>\<rightarrow> \<bbbS>\<f>\<i>\<e>\<l>\<d> ''balance'' \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (msg.sender msg \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub>[\<^sub>] \<fish_eye>\<lbrakk>\<tau>Int 256\<rbrakk> Currency \<heavy_comma>
      balance_alice  \<Ztypecolon> ledge: msg.contract msg \<^bold>\<rightarrow> \<bbbS>\<f>\<i>\<e>\<l>\<d> ''balance'' \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (alice \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub>[\<^sub>] \<fish_eye>\<lbrakk>\<tau>Int 256\<rbrakk> Currency \<heavy_comma>
      \<^bold>v\<^bold>a\<^bold>l alice \<Ztypecolon> Address\<heavy_comma>
      \<^bold>v\<^bold>a\<^bold>l amount \<Ztypecolon> Currency\<close>
  return \<open>msg \<Ztypecolon> Msg\<heavy_comma>
      (if amount \<le> balance_sender then balance_sender - amount else balance_sender)
        \<Ztypecolon> ledge: msg.contract msg \<^bold>\<rightarrow> \<bbbS>\<f>\<i>\<e>\<l>\<d> ''balance'' \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (msg.sender msg \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub>[\<^sub>] \<fish_eye>\<lbrakk>\<tau>Int 256\<rbrakk> Currency \<heavy_comma>
      (if amount \<le> balance_sender then balance_alice + amount else balance_alice)
        \<Ztypecolon> ledge: msg.contract msg \<^bold>\<rightarrow> \<bbbS>\<f>\<i>\<e>\<l>\<d> ''balance'' \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (alice \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub>[\<^sub>] \<fish_eye>\<lbrakk>\<tau>Int 256\<rbrakk> Currency \<heavy_comma>
      \<^bold>v\<^bold>a\<^bold>l amount \<le> balance_sender \<Ztypecolon> \<bool>\<close>
  \<medium_left_bracket>
    \<rightarrow> v_alice, v_amount
  have [useful]: \<open>balance_alice \<le> Total_Supply\<close> \<open>balance_sender \<le> Total_Supply\<close> using \<phi> by simp+ ;;
    op_get_var[where vname=v_amount]
    op_get_msg_addr[where G=msg.contract]
    op_root_ledge_ref
    op_get_member_ledgeRef[where field=\<open>''balance''\<close>]
    op_get_msg_addr[where G=msg.sender]
    op_get_mapping_ledgeRef
    op_load_ledge
    op_le \<rightarrow> ret ;;
    if \<medium_left_bracket> op_get_var[where vname=ret] \<medium_right_bracket>.
  \<medium_left_bracket> op_get_msg_addr[where G=msg.contract]
    op_root_ledge_ref
    op_get_member_ledgeRef[where field=\<open>''balance''\<close>]
    op_get_msg_addr[where G=msg.sender]
    op_get_mapping_ledgeRef
    op_get_msg_addr[where G=msg.contract]
    op_root_ledge_ref
    op_get_member_ledgeRef[where field=\<open>''balance''\<close>]
    op_get_msg_addr[where G=msg.sender]
    op_get_mapping_ledgeRef
    op_load_ledge
    op_get_var[where vname=v_amount]
    op_sub
    op_store_ledge
    op_get_msg_addr[where G=msg.contract]
    op_root_ledge_ref
    op_get_member_ledgeRef[where field=\<open>''balance''\<close>]
    op_get_var[where vname=v_alice]
    op_get_mapping_ledgeRef
    dup
    op_load_ledge
    op_get_var[where vname=v_amount]
    op_add
    op_store_ledge
  \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>.
  ;; op_get_var[where vname=ret]
  \<medium_right_bracket>. .



proc transfer_from:
  premises \<open>balance_bob + amount \<le> Total_Supply\<close>
  argument \<open>msg \<Ztypecolon> Msg\<heavy_comma>
      balance_alice \<Ztypecolon> ledge: msg.contract msg \<^bold>\<rightarrow> \<bbbS>\<f>\<i>\<e>\<l>\<d> ''balance'' \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (alice \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub>[\<^sub>] \<fish_eye>\<lbrakk>\<tau>Int 256\<rbrakk> Currency \<heavy_comma>
      balance_bob   \<Ztypecolon> ledge: msg.contract msg \<^bold>\<rightarrow> \<bbbS>\<f>\<i>\<e>\<l>\<d> ''balance'' \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (bob   \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub>[\<^sub>] \<fish_eye>\<lbrakk>\<tau>Int 256\<rbrakk> Currency \<heavy_comma>
      allowance     \<Ztypecolon> ledge: msg.contract msg \<^bold>\<rightarrow> \<bbbS>\<f>\<i>\<e>\<l>\<d> ''allowance'' \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (alice \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (bob \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub>[\<^sub>] \<fish_eye>\<lbrakk>\<tau>Int 256\<rbrakk> \<nat>[256] \<heavy_comma>
      \<^bold>v\<^bold>a\<^bold>l alice  \<Ztypecolon> Address\<heavy_comma>
      \<^bold>v\<^bold>a\<^bold>l bob    \<Ztypecolon> Address\<heavy_comma>
      \<^bold>v\<^bold>a\<^bold>l amount \<Ztypecolon> Currency\<close>
  return \<open>msg \<Ztypecolon> Msg\<heavy_comma>
      (if amount \<le> balance_alice \<and> amount \<le> allowance then balance_alice - amount else balance_alice)
        \<Ztypecolon> ledge: msg.contract msg \<^bold>\<rightarrow> \<bbbS>\<f>\<i>\<e>\<l>\<d> ''balance'' \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (alice \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub>[\<^sub>] \<fish_eye>\<lbrakk>\<tau>Int 256\<rbrakk> Currency \<heavy_comma>
      (if amount \<le> balance_alice \<and> amount \<le> allowance then balance_bob   + amount else balance_bob)
        \<Ztypecolon> ledge: msg.contract msg \<^bold>\<rightarrow> \<bbbS>\<f>\<i>\<e>\<l>\<d> ''balance'' \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (bob \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub>[\<^sub>] \<fish_eye>\<lbrakk>\<tau>Int 256\<rbrakk> Currency \<heavy_comma>
      (if amount \<le> balance_alice \<and> amount \<le> allowance then allowance - amount else allowance)
        \<Ztypecolon> ledge: msg.contract msg \<^bold>\<rightarrow> \<bbbS>\<f>\<i>\<e>\<l>\<d> ''allowance'' \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (alice \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (bob \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub>[\<^sub>] \<fish_eye>\<lbrakk>\<tau>Int 256\<rbrakk> \<nat>[256] \<heavy_comma>
      \<^bold>v\<^bold>a\<^bold>l amount \<le> balance_alice \<and> amount \<le> allowance \<Ztypecolon> \<bool>\<close>
  \<medium_left_bracket> 
(* if amount \<le> balance_alice \<and> amount \<le> allowance
 *)
    \<rightarrow> v_alice, v_bob, v_amount
  have [useful]: \<open>balance_alice \<le> Total_Supply\<close>
                 \<open>balance_bob \<le> Total_Supply\<close>
                 \<open>allowance \<le> 2 ^ Big 256\<close>
                using \<phi> by simp+ ;;
    op_get_var[where vname=v_amount]
    op_get_msg_addr[where G=msg.contract]
    op_root_ledge_ref
    op_get_member_ledgeRef[where field=\<open>''balance''\<close>]
    op_get_var[where vname=v_alice]
    op_get_mapping_ledgeRef
    op_load_ledge
    op_le
    op_get_var[where vname=v_amount]
    op_get_msg_addr[where G=msg.contract]
    op_root_ledge_ref
    op_get_member_ledgeRef[where field=\<open>''allowance''\<close>]
    op_get_var[where vname=v_alice]
    op_get_mapping_ledgeRef
    op_get_var[where vname=v_bob]
    op_get_mapping_ledgeRef
    op_load_ledge
    op_le
    op_and \<rightarrow> ret
  ;;if \<open>$ret\<close>
  \<medium_left_bracket> 
  (* balance[alice] -= amount;
     balance[bob]   += amount;
     allowance[alice,bob] -= amount;
   *)
    op_get_msg_addr[where G=msg.contract]
    op_root_ledge_ref
    op_get_member_ledgeRef[where field=\<open>''balance''\<close>]
    op_get_var[where vname=v_alice]
    op_get_mapping_ledgeRef
    dup
    op_load_ledge
    op_get_var[where vname=v_amount]
    op_sub
    op_store_ledge
  ;;op_get_msg_addr[where G=msg.contract]
    op_root_ledge_ref
    op_get_member_ledgeRef[where field=\<open>''allowance''\<close>]
    op_get_var[where vname=v_alice]
    op_get_mapping_ledgeRef
    op_get_var[where vname=v_bob]
    op_get_mapping_ledgeRef
    dup
    op_load_ledge
    op_get_var[where vname=v_amount]
    op_sub
    op_store_ledge
  ;;op_get_msg_addr[where G=msg.contract]
    op_root_ledge_ref
    op_get_member_ledgeRef[where field=\<open>''balance''\<close>]
    op_get_var[where vname=v_bob]
    op_get_mapping_ledgeRef
    dup
    op_load_ledge
    op_get_var[where vname=v_amount]
    op_add
    op_store_ledge
  \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>.
  ;; \<open>$ret\<close>
  \<medium_right_bracket>. .


proc approve:
  argument \<open>msg \<Ztypecolon> Msg\<heavy_comma>
      allowance \<Ztypecolon> ledge: msg.contract msg \<^bold>\<rightarrow> \<bbbS>\<f>\<i>\<e>\<l>\<d> ''allowance''
                           \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (msg.sender msg \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (spender \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub>[\<^sub>] \<fish_eye>\<lbrakk>\<tau>Int 256\<rbrakk> \<nat>[256] \<heavy_comma>
      \<^bold>v\<^bold>a\<^bold>l spender \<Ztypecolon> Address\<heavy_comma>
      \<^bold>v\<^bold>a\<^bold>l amount \<Ztypecolon> \<nat>[256]\<close>
  return \<open>msg \<Ztypecolon> Msg\<heavy_comma>
      (if allowance + amount < 2 ^ Big 256 then allowance + amount else allowance)
          \<Ztypecolon> ledge: msg.contract msg \<^bold>\<rightarrow> \<bbbS>\<f>\<i>\<e>\<l>\<d> ''allowance''
                     \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (msg.sender msg \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (spender \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub>[\<^sub>] \<fish_eye>\<lbrakk>\<tau>Int 256\<rbrakk> \<nat>[256] \<heavy_comma>
      \<^bold>v\<^bold>a\<^bold>l allowance + amount < 2 ^ Big 256 \<Ztypecolon> \<bool>\<close>
  \<medium_left_bracket> \<rightarrow> v_spender, v_amount;;
    op_get_msg_addr[where G=msg.contract]
    op_root_ledge_ref
    op_get_member_ledgeRef[where field=\<open>''allowance''\<close>]
    op_get_msg_addr[where G=msg.sender]
    op_get_mapping_ledgeRef
    op_get_var[where vname=v_spender]
    op_get_mapping_ledgeRef
    op_load_ledge \<rightarrow> v_allowance;;
(* check the overflow by: allowance \<le> allowance + amount *)
    op_get_var[where vname=v_allowance]
    op_get_var[where vname=v_allowance]
    op_get_var[where vname=v_amount]
    op_add_mod
    op_le
  have [simp]: \<open>allowance \<le> (allowance + amount) mod 2 ^ Big 256 \<longleftrightarrow> allowance + amount < 2 ^ Big 256\<close>
    using \<phi> mod_if by force
  ;; \<rightarrow> ret
  ;; if \<open>$ret\<close>
  \<medium_left_bracket> op_get_msg_addr[where G=msg.contract]
    op_root_ledge_ref
    op_get_member_ledgeRef[where field=\<open>''allowance''\<close>]
    op_get_msg_addr[where G=msg.sender]
    op_get_mapping_ledgeRef
    op_get_var[where vname=v_spender]
    op_get_mapping_ledgeRef
    op_get_var[where vname=v_allowance]
    op_get_var[where vname=v_amount]
    op_add
    op_store_ledge
  \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. 
  ;; \<open>$ret\<close>
  \<medium_right_bracket>. .


proc allowance:
  argument \<open>msg \<Ztypecolon> Msg\<heavy_comma>
      allowance \<Ztypecolon> ledge: msg.contract msg \<^bold>\<rightarrow> \<bbbS>\<f>\<i>\<e>\<l>\<d> ''allowance''
                           \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (msg.sender msg \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (spender \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub>[\<^sub>] \<fish_eye>\<lbrakk>\<tau>Int 256\<rbrakk> \<nat>[256] \<heavy_comma>
      \<^bold>v\<^bold>a\<^bold>l spender \<Ztypecolon> Address\<close>
  return \<open>msg \<Ztypecolon> Msg\<heavy_comma>
      allowance \<Ztypecolon> ledge: msg.contract msg \<^bold>\<rightarrow> \<bbbS>\<f>\<i>\<e>\<l>\<d> ''allowance''
                           \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (msg.sender msg \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub># \<bbbS>\<m>\<a>\<p> (spender \<Ztypecolon> Address) \<^bold>\<rightarrow>\<^sub>[\<^sub>] \<fish_eye>\<lbrakk>\<tau>Int 256\<rbrakk> \<nat>[256] \<heavy_comma>
      \<^bold>v\<^bold>a\<^bold>l allowance \<Ztypecolon> \<nat>[256]\<close>
  \<medium_left_bracket> op_get_msg_addr[where G=msg.contract]
    op_root_ledge_ref
    op_get_member_ledgeRef[where field=\<open>''allowance''\<close>]
    op_get_msg_addr[where G=msg.sender]
    op_get_mapping_ledgeRef
    \<open>\<a>\<r>\<g>0\<close> op_get_mapping_ledgeRef
    op_load_ledge
  \<medium_right_bracket>. .

end

end