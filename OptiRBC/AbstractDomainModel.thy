theory AbstractDomainModel
  imports HOL.Real
begin

text \<open>This is the abstract domain model used in the Ivy specification\<close>

locale abstract_domain_model =
  fixes broadcaster :: "'p::finite"
    and faulty :: "'p set"
    and opt_quorum_member :: "'opQ \<Rightarrow> 'p \<Rightarrow> bool"
    and maj_quorum_member :: "'vtQ \<Rightarrow> 'p \<Rightarrow> bool"
    and classic_quorum_member :: "'quQ \<Rightarrow> 'p \<Rightarrow> bool"
    and amplification_quorum_member :: "'amQ \<Rightarrow> 'p \<Rightarrow> bool"
    and commit_quorum_member :: "'coQ \<Rightarrow> 'p \<Rightarrow> bool"
  assumes broadcaster_not_in_classic_quorum:
    "\<not> classic_quorum_member quQ broadcaster"
    and broadcaster_not_in_maj_quorum:
    "\<not> maj_quorum_member vtQ broadcaster"
    and broadcaster_not_in_opt_quorum:
    "\<not> opt_quorum_member opQ broadcaster"
    and non_faulty_commit_quorum:
    "\<exists>coQ. \<forall>p. commit_quorum_member coQ p \<longrightarrow> p \<notin> faulty"
    and non_faulty_amplification_quorum:
    "\<exists>amQ. \<forall>p. amplification_quorum_member amQ p \<longrightarrow> p \<notin> faulty"
    and non_faulty_maj_quorum:
    "\<exists>vtQ. \<forall>p. maj_quorum_member vtQ p \<longrightarrow> p \<notin> faulty"
    and non_faulty_classic_quorum:
    "\<exists>quQ. \<forall>p. classic_quorum_member quQ p \<longrightarrow> p \<notin> faulty"
    and opt_quorum_has_nonfaulty_member:
    "\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ p"
    and opt_quorum_intersection:
    "broadcaster \<in> faulty \<longrightarrow> (\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ\<^sub>1 p \<and> opt_quorum_member opQ\<^sub>2 p)"
    and opt_maj_quorum_intersection:
    "broadcaster \<in> faulty \<longrightarrow> (\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ p \<and> maj_quorum_member vtQ p)"
    and opt_quorum_intersects_classic_quorum:
    "broadcaster \<in> faulty \<longrightarrow> (\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ p \<and> classic_quorum_member quQ p)"
    and classic_quorum_intersection:
    "broadcaster \<in> faulty \<longrightarrow> (\<exists>p. p \<notin> faulty \<and> classic_quorum_member quQ\<^sub>1 p \<and> classic_quorum_member quQ\<^sub>2 p)"
    and quorum_not_faulty:
    "\<exists>p. p \<notin> faulty \<and> classic_quorum_member Q p"
    and maj_quorum_has_nonfaulty_member:
    "\<exists>p. p \<notin> faulty \<and> maj_quorum_member vtQ p"
    and amplification_quorum_has_nonfaulty_member:
    "\<exists>p. p \<notin> faulty \<and> amplification_quorum_member amQ p"
    and opt_quorum_contains_maj_quorum:
    "broadcaster \<in> faulty \<longrightarrow> (\<exists>vtQ. \<forall>p. maj_quorum_member vtQ p \<longrightarrow> p \<notin> faulty \<and> opt_quorum_member opQ p)"
    and commit_quorum_contains_non_faulty_amplification_quorum:
    "\<exists>amQ. \<forall>p. amplification_quorum_member amQ p \<longrightarrow> p \<notin> faulty \<and> commit_quorum_member coQ p"

end
