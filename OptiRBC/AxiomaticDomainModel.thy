theory AxiomaticDomainModel
  imports AbstractDomainModel
begin

text \<open>In this theory we define types of quorums corresponding to the various thresholds
used by the optimistic RBC algorithm. This will then allow us to do proof abstractly, just relying
on intersection properties and not on cardinalitites.\<close>

section \<open>The domain model, axiomatically\<close>

typedecl party

axiomatization faulty :: "party set" and broadcaster :: party
  where party_finite: "finite (UNIV :: party set)"

instantiation party :: finite
begin

instance
  by intro_classes (simp add: party_finite)

end

definition n :: nat where
  "n \<equiv> card (UNIV :: party set)"

definition f :: nat where
  "f \<equiv> card faulty"

axiomatization where
  fault_bound: "3*f < n"
  and two_parties: "2 \<le> n"

typedef opt_quorum =
  "{S :: party set. broadcaster \<notin> S \<and> card S >= max 1 \<lceil>real (n + 2 * f - 2) / 2\<rceil>}"
proof -
  text \<open>Proof sketch: @{term "UNIV - {broadcaster}"} excludes @{term broadcaster} and has
    cardinality @{term "n - 1"}. The global inequalities @{thm [source] fault_bound} and
    @{thm [source] two_parties} make this large enough for the optimistic threshold and ensure
    that it is nonempty.\<close>
  let ?S = "UNIV - {broadcaster} :: party set"
  have card_S: "card ?S = n - 1"
    by (simp add: n_def)
  have ge_one: "card ?S >= 1"
  proof -
    have "n - 1 >= 1"
      using two_parties by linarith
    then show ?thesis
      by (simp add: card_S)
  qed
  have thresh: "card ?S >= \<lceil>real (n + 2 * f - 2) / 2\<rceil>"
  proof -
    have "real (n - 1) >= real (n + 2 * f - 2) / 2"
      using fault_bound by linarith
    then have "\<lceil>real (n - 1)\<rceil> >= \<lceil>real (n + 2 * f - 2) / 2\<rceil>"
      by (intro ceiling_mono)
    then have "n - 1 >= \<lceil>real (n + 2 * f - 2) / 2\<rceil>"
      by simp
    then show ?thesis
      by (simp add: card_S)
  qed
  show "\<exists>S :: party set.
      S \<in> {S :: party set. broadcaster \<notin> S \<and> card S >= max 1 \<lceil>real (n + 2 * f - 2) / 2\<rceil>}"
    using ge_one thresh by (intro exI[of _ ?S]) simp
qed

typedef maj_quorum =
  "{S :: party set. broadcaster \<notin> S \<and> card S >= \<lceil>real n / 2\<rceil>}"
proof -
  text \<open>Proof sketch: @{term "UNIV - {broadcaster}"} again provides all non-broadcaster parties.
    The global inequality @{term "2 \<le> n"} ensures that this set reaches the vote threshold.\<close>
  let ?S = "UNIV - {broadcaster} :: party set"
  have card_S: "card ?S = n - 1"
    by (simp add: n_def)
  have thresh: "card ?S >= \<lceil>real n / 2\<rceil>"
  proof -
    have "real (n - 1) >= real n / 2"
      using two_parties by linarith
    then have "\<lceil>real (n - 1)\<rceil> >= \<lceil>real n / 2\<rceil>"
      by (intro ceiling_mono)
    then have "n - 1 >= \<lceil>real n / 2\<rceil>"
      by simp
    then show ?thesis
      by (simp add: card_S)
  qed
  show "\<exists>S :: party set.
      S \<in> {S :: party set. broadcaster \<notin> S \<and> card S >= \<lceil>real n / 2\<rceil>}"
    using thresh by (intro exI[of _ ?S]) simp
qed

typedef classic_quorum =
  "{S :: party set. broadcaster \<notin> S \<and> card S >= \<lceil>real (n + f - 1) / 2\<rceil>}"
proof -
  text \<open>Proof sketch: use @{term "UNIV - {broadcaster}"} once more. The global inequalities
    @{term fault_bound} and @{term "2 \<le> n"} imply that @{term "n - 1"} dominates the quorum
    threshold.\<close>
  let ?S = "UNIV - {broadcaster} :: party set"
  have card_S: "card ?S = n - 1"
    by (simp add: n_def)
  have thresh: "card ?S >= \<lceil>real (n + f - 1) / 2\<rceil>"
  proof -
    have "real (n - 1) >= real (n + f - 1) / 2"
      using fault_bound two_parties by linarith
    then have "\<lceil>real (n - 1)\<rceil> >= \<lceil>real (n + f - 1) / 2\<rceil>"
      by (intro ceiling_mono)
    then have "n - 1 >= \<lceil>real (n + f - 1) / 2\<rceil>"
      by simp
    then show ?thesis
      by (simp add: card_S)
  qed
  show "\<exists>S :: party set.
      S \<in> {S :: party set. broadcaster \<notin> S \<and> card S >= \<lceil>real (n + f - 1) / 2\<rceil>}"
    using thresh by (intro exI[of _ ?S]) simp
qed

typedef amplification_quorum =
  "{S :: party set. card S >= f + 1}"
proof -
  text \<open>Proof sketch: the full universe has cardinality @{term n}, and the global inequality
    @{thm [source] fault_bound} implies @{prop "n >= f + 1"}.\<close>
  have thresh: "card (UNIV :: party set) >= f + 1"
  proof -
    have "n >= f + 1"
      using fault_bound by linarith
    then show ?thesis
      by (simp add: n_def)
  qed
  show "\<exists>S :: party set. S \<in> {S :: party set. card S >= f + 1}"
    using thresh by (intro exI[of _ "UNIV :: party set"]) simp
qed

typedef commit_quorum =
  "{S :: party set. card S >= 2 * f + 1}"
proof -
  text \<open>Proof sketch: the full universe again witnesses nonemptiness because the global inequality
    @{thm [source] fault_bound} implies @{term "n >= 2 * f + 1"}.\<close>
  have thresh: "card (UNIV :: party set) >= 2 * f + 1"
  proof -
    have "n >= 2 * f + 1"
      using fault_bound by linarith
    then show ?thesis
      by (simp add: n_def)
  qed
  show "\<exists>S :: party set. S \<in> {S :: party set. card S >= 2 * f + 1}"
    using thresh by (intro exI[of _ "UNIV :: party set"]) simp
qed

section \<open>Intersection properties\<close>

lemma card_lemma_1:
  assumes "broadcaster \<in> faulty"
    and "broadcaster \<notin> S\<^sub>1"
    and "card S\<^sub>1 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>"
    and "broadcaster \<notin> S\<^sub>2"
    and "card S\<^sub>2 \<ge> \<lceil>real n / 2\<rceil>"
  shows "(S\<^sub>1 \<inter> S\<^sub>2) - faulty \<noteq> {}"
  text \<open>Proof sketch: Since broadcaster is not in @{term S\<^sub>1} or @{term S\<^sub>2}, both are subsets of
    @{term "UNIV - {broadcaster}"} which has cardinality @{term "n - 1::nat"}. By inclusion-exclusion,
    @{term "card (S\<^sub>1 \<inter> S\<^sub>2)"} is at least @{term "f::nat"}.
    Since broadcaster is in faulty but not in @{term "S\<^sub>1 \<inter> S\<^sub>2"}, at most @{term "f - 1::nat"} faulty
    elements can be in the intersection. So @{term "(S\<^sub>1 \<inter> S\<^sub>2) - faulty"} has at least 1 element.\<close>
proof -
  have n_pos: "n \<ge> 1" using fault_bound by (simp add: n_def)
  have f_pos: "f \<ge> 1"
    by (metis One_nat_def \<open>broadcaster \<in> faulty\<close> bot_nat_0.extremum_unique card.remove f_def finite nat.simps(3) not_less_eq_eq)
  have card_U: "card (UNIV - {broadcaster} :: party set) = n - 1"
    using n_pos by (simp add: n_def)
  text \<open>By inclusion-exclusion, the intersection is large enough.\<close>
  have ie: "card (S\<^sub>1 \<inter> S\<^sub>2) + (n - 1) \<ge> card S\<^sub>1 + card S\<^sub>2"
    by (metis Diff_empty Un_iff add.commute add_le_cancel_right \<open>broadcaster \<notin> S\<^sub>1\<close> \<open>broadcaster \<notin> S\<^sub>2\<close> card_U card_Un_Int card_mono finite subset_Diff_insert subset_UNIV)
  text \<open>The sum of cardinalities is at least @{term "n + f - 1::nat"} in int.\<close>
  have sum_bound: "int (card S\<^sub>1) + int (card S\<^sub>2) \<ge> int n + int f - 1"
  proof -
    have "n + 2*f \<ge> 2" using n_pos f_pos by linarith
    hence "real (n + 2*f - 2) / 2 + real n / 2 = real n + real f - 1"
      by (simp add: field_simps)
    thus ?thesis
      using \<open>card S\<^sub>1 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>\<close> \<open>card S\<^sub>2 \<ge> \<lceil>real n / 2\<rceil>\<close>
        le_of_int_ceiling[of "real (n + 2*f - 2) / 2"]
        le_of_int_ceiling[of "real n / 2"]
      by linarith
  qed
  text \<open>So the intersection has at least @{term "f::nat"} elements.\<close>
  have inter_card: "int (card (S\<^sub>1 \<inter> S\<^sub>2)) \<ge> int f"
    using ie sum_bound n_pos by linarith
  text \<open>Broadcaster is in faulty but not in the intersection, so at most @{term "f - 1::nat"}
    faulty elements are in the intersection.\<close>
  have faulty_inter: "card (faulty \<inter> (S\<^sub>1 \<inter> S\<^sub>2)) \<le> f - 1"
    by (metis Int_iff Int_lower1 One_nat_def \<open>broadcaster \<in> faulty\<close> \<open>broadcaster \<notin> S\<^sub>1\<close> bot_nat_0.extremum_unique card.infinite card.remove card_Diff_singleton_if card_seteq f_def f_pos not_less_eq_eq)
  text \<open>Conclude that the intersection minus faulty is nonempty.\<close>
  have "card ((S\<^sub>1 \<inter> S\<^sub>2) - faulty) \<ge> 1"
    by (metis Diff_Diff_Int Diff_empty Int_lower2 One_nat_def card.empty card_seteq dec_greater_eq_self_imp_bot empty_subsetI f_def f_pos faulty_inter finite inter_card not_less_eq_eq of_nat_le_iff)
  thus ?thesis by (metis card.empty not_one_le_zero)
qed

lemma card_lemma_2:
  \<comment> \<open>This follows from @{thm [source] card_lemma_1} because @{term "\<lceil>real (n + f - 1) / 2\<rceil> \<ge> \<lceil>real n / 2\<rceil>"} when @{term "f>0"}.\<close>
  assumes "broadcaster \<in> faulty"
    and "broadcaster \<notin> S\<^sub>1"
    and "card S\<^sub>1 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>"
    and "broadcaster \<notin> S\<^sub>2"
    and "card S\<^sub>2 \<ge> \<lceil>real (n + f - 1) / 2\<rceil>"
  shows "(S\<^sub>1 \<inter> S\<^sub>2) - faulty \<noteq> {}"
  text \<open>Since @{term "f \<ge> 1"}, we have @{term "\<lceil>real (n + f - 1) / 2\<rceil> \<ge> \<lceil>real n / 2\<rceil>"},
    so the assumption on @{term S\<^sub>2} is at least as strong as what @{thm [source] card_lemma_1} requires.
    We apply @{thm [source] card_lemma_1} directly.\<close>
proof -
  have "f \<ge> 1"
    by (metis One_nat_def \<open>broadcaster \<in> faulty\<close> bot_nat_0.extremum_unique card.remove f_def finite nat.simps(3) not_less_eq_eq)
  hence "\<lceil>real (n + f - 1) / 2\<rceil> \<ge> \<lceil>real n / 2\<rceil>"
    by (intro ceiling_mono divide_right_mono) linarith+
  hence "card S\<^sub>2 \<ge> \<lceil>real n / 2\<rceil>"
    using \<open>card S\<^sub>2 \<ge> \<lceil>real (n + f - 1) / 2\<rceil>\<close> by linarith
  thus ?thesis
    using card_lemma_1[OF \<open>broadcaster \<in> faulty\<close> \<open>broadcaster \<notin> S\<^sub>1\<close> \<open>card S\<^sub>1 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>\<close> \<open>broadcaster \<notin> S\<^sub>2\<close>]
    by blast
qed

lemma card_lemma_3:
  \<comment> \<open>This should follows immediately from @{thm [source] card_lemma_1} because @{term "\<lceil>real (n + 2*f - 2) / 2\<rceil> \<ge> \<lceil>real n / 2\<rceil>"} when @{term "f>0"}\<close>
  assumes "broadcaster \<in> faulty"
    and "broadcaster \<notin> S\<^sub>1" 
    and "card S\<^sub>1 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>"
    and "broadcaster \<notin> S\<^sub>2"
    and "card S\<^sub>2 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>"
  shows "((S\<^sub>1 \<inter> S\<^sub>2) - faulty) \<noteq> {}"
  text \<open>Since @{term "f \<ge> 1"}, we have @{term "\<lceil>real (n + 2*f - 2) / 2\<rceil> \<ge> \<lceil>real n / 2\<rceil>"},
    so the assumption on @{term S\<^sub>2} implies the weaker bound needed by @{thm [source] card_lemma_1}.
    We apply @{thm [source] card_lemma_1} directly.\<close>
proof -
  have "f \<ge> 1"
    by (metis One_nat_def \<open>broadcaster \<in> faulty\<close> bot_nat_0.extremum_unique card.remove f_def finite nat.simps(3) not_less_eq_eq)
  hence "\<lceil>real (n + 2*f - 2) / 2\<rceil> \<ge> \<lceil>real n / 2\<rceil>"
    by (intro ceiling_mono divide_right_mono) linarith+
  hence "card S\<^sub>2 \<ge> \<lceil>real n / 2\<rceil>"
    using \<open>card S\<^sub>2 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>\<close> by linarith
  thus ?thesis
    using card_lemma_1[OF \<open>broadcaster \<in> faulty\<close> \<open>broadcaster \<notin> S\<^sub>1\<close> \<open>card S\<^sub>1 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>\<close> \<open>broadcaster \<notin> S\<^sub>2\<close>]
    by blast
qed

lemma card_lemma_4:
  assumes "card S\<^sub>1 \<ge> 2*f +1"
  shows "card (S\<^sub>1 - faulty) \<ge> f +1"
  text \<open>At most @{term f} elements of @{term S\<^sub>1} can be faulty, so removing faulty elements
    leaves at least @{term "2*f + 1 - f"} = @{term "f + (1::nat)"} elements.\<close>
proof -
  have "card (S\<^sub>1 \<inter> faulty) \<le> f"
    by (metis Int_lower2 card_mono f_def finite)
  moreover have "card (S\<^sub>1 - faulty) = card S\<^sub>1 - card (S\<^sub>1 \<inter> faulty)"
    by (metis card_Diff_subset_Int finite)
  ultimately show ?thesis using assms by linarith
qed

lemma card_lemma_5:
  assumes "broadcaster \<in> faulty"
    and "broadcaster \<notin> S\<^sub>1" 
    and "card S\<^sub>1 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>"
  shows "card (S\<^sub>1 - faulty) \<ge> \<lceil>real n / 2\<rceil>"
  text \<open>Since @{term "broadcaster \<in> faulty"} but @{term "broadcaster \<notin> S\<^sub>1"}, at most @{term "f - 1::nat"}
    faulty elements are in @{term S\<^sub>1}. So @{term "card (S\<^sub>1 - faulty)"} is at least
    @{term "\<lceil>real (n + 2*f - 2) / 2\<rceil> - int (f - 1)"}. Since
    @{term "\<lceil>real (n + 2*f - 2) / 2\<rceil> = \<lceil>real n / 2\<rceil> + int f - 1"}, the result follows.\<close>
proof -
  have f_pos: "f \<ge> 1"
    by (metis One_nat_def \<open>broadcaster \<in> faulty\<close> bot_nat_0.extremum_unique card.remove f_def finite nat.simps(3) not_less_eq_eq)
  have "card (S\<^sub>1 \<inter> faulty) \<le> f - 1"
    by (metis Int_iff Int_lower2 assms(1,2) card.remove card_Diff_singleton_if card_seteq f_def finite not_less_eq_eq)
  moreover have "card (S\<^sub>1 - faulty) = card S\<^sub>1 - card (S\<^sub>1 \<inter> faulty)"
    by (metis card_Diff_subset_Int finite)
  moreover have "\<lceil>real (n + 2*f - 2) / 2\<rceil> = \<lceil>real n / 2\<rceil> + int f - 1"
  proof -
    have "n + 2*f \<ge> 2" using f_pos by linarith
    hence "real (n + 2*f - 2) / 2 = real n / 2 + real f - 1"
      by (simp add: field_simps)
    thus ?thesis by linarith
  qed
  moreover have "card (S\<^sub>1 \<inter> faulty) \<le> card S\<^sub>1"
    by (simp add: card_mono)
  ultimately have "int (card (S\<^sub>1 - faulty)) \<ge> int (card S\<^sub>1) - int (f - 1)"
    by (simp add: card_Diff_subset_Int card_mono)
  moreover have "int (card S\<^sub>1) \<ge> \<lceil>real n / 2\<rceil> + int f - 1"
    using assms(3) by linarith
  ultimately show ?thesis using f_pos by linarith
qed

lemma card_lemma_6:
  assumes "card S\<^sub>1 \<ge> \<lceil>real n / 2\<rceil>"
  shows "\<exists> p \<in> S\<^sub>1 . p \<notin> faulty"
  text \<open>Proof sketch: From @{term "3*f < n"} we get @{term "f < \<lceil>real n / 2\<rceil>"}, so
    @{term "card faulty < card S\<^sub>1"}. Hence @{term S\<^sub>1} cannot be a subset of faulty,
    meaning there exists a member of @{term S\<^sub>1} not in faulty.\<close>
proof -
  have "int f < \<lceil>real n / 2\<rceil>"
  proof -
    have "2 * f < n" using fault_bound by linarith
    hence "real (2*f) < real n" by simp
    hence "real f < real n / 2" by simp
    thus ?thesis by linarith
  qed
  hence "int f < int (card S\<^sub>1)" using assms by linarith
  hence "card faulty < card S\<^sub>1" by (simp add: f_def)
  hence "\<not> S\<^sub>1 \<subseteq> faulty"
    by (metis card_mono finite leD)
  thus ?thesis by blast
qed

lemma card_lemma_7:
  assumes "broadcaster \<in> faulty"
    and "broadcaster \<notin> S\<^sub>1"
    and "card S\<^sub>1 \<ge> \<lceil>real (n + f - 1) / 2\<rceil>"
    and "broadcaster \<notin> S\<^sub>2"
    and "card S\<^sub>2 \<ge> \<lceil>real (n + f - 1) / 2\<rceil>"
  shows "(S\<^sub>1 \<inter> S\<^sub>2) - faulty \<noteq> {}"
  text \<open>Proof sketch: Since @{term "broadcaster"} is excluded from @{term S\<^sub>1} and @{term S\<^sub>2},
    both sets lie in @{term "UNIV - {broadcaster}"}, whose cardinality is @{term "n - 1::nat"}.
    Inclusion-exclusion and the lower bounds on @{term "card S\<^sub>1"} and @{term "card S\<^sub>2"}
    yield @{term "card (S\<^sub>1 \<inter> S\<^sub>2) \<ge> f"}. Because @{term "broadcaster \<in> faulty"} but
    @{term "broadcaster \<notin> S\<^sub>1 \<inter> S\<^sub>2"}, at most @{term "f - 1::nat"} faulty parties lie
    in the intersection. Therefore @{term "(S\<^sub>1 \<inter> S\<^sub>2) - faulty"} is nonempty.\<close>
proof -
  have n_pos: "n \<ge> 1"
    using fault_bound by (simp add: n_def)
  have f_pos: "f \<ge> 1"
    by (metis One_nat_def \<open>broadcaster \<in> faulty\<close> bot_nat_0.extremum_unique card.remove f_def finite nat.simps(3) not_less_eq_eq)
  have card_U: "card (UNIV - {broadcaster} :: party set) = n - 1"
    using n_pos by (simp add: n_def)
  have union_bound: "card (S\<^sub>1 \<union> S\<^sub>2) \<le> n - 1"
    by (metis Diff_empty Un_iff assms(2,4) card_U card_mono finite subset_Diff_insert top_greatest)
  have ie: "card (S\<^sub>1 \<inter> S\<^sub>2) + (n - 1) \<ge> card S\<^sub>1 + card S\<^sub>2"
    by (metis add.commute add_le_cancel_right card_Un_Int finite union_bound)
  have sum_bound: "int (card S\<^sub>1) + int (card S\<^sub>2) \<ge> int n + int f - 1"
  proof -
    have "2 * \<lceil>real (n + f - 1) / 2\<rceil> \<ge> int n + int f - 1"
      using le_of_int_ceiling[of "real (n + f - 1) / 2"] by linarith
    thus ?thesis
      using \<open>card S\<^sub>1 \<ge> \<lceil>real (n + f - 1) / 2\<rceil>\<close> \<open>card S\<^sub>2 \<ge> \<lceil>real (n + f - 1) / 2\<rceil>\<close>
      by linarith
  qed
  have inter_card: "card (S\<^sub>1 \<inter> S\<^sub>2) \<ge> f"
    using ie sum_bound n_pos by linarith
  have faulty_inter: "card (faulty \<inter> (S\<^sub>1 \<inter> S\<^sub>2)) \<le> f - 1"
    by (metis Int_iff Int_lower1 One_nat_def assms(1,2) card.infinite card.remove
        card_Diff_singleton_if card_seteq dual_order.refl f_def f_pos not_less_eq_eq)
  show ?thesis
    by (metis Diff_eq_empty_iff Int_absorb1 diff_diff_cancel diff_is_0_eq diff_le_mono2 f_pos faulty_inter inter_card not_one_le_zero)
qed

section "Mapping to the abstract domain model"

definition opt_quorum_member :: "opt_quorum => party => bool" where
  "opt_quorum_member Q p \<equiv> p \<in> Rep_opt_quorum Q"

definition maj_quorum_member :: "maj_quorum => party => bool" where
  "maj_quorum_member Q p \<equiv> p \<in> Rep_maj_quorum Q"

definition classic_quorum_member :: "classic_quorum => party => bool" where
  "classic_quorum_member Q p \<equiv> p \<in> Rep_classic_quorum Q"

definition amplification_quorum_member :: "amplification_quorum => party => bool" where
  "amplification_quorum_member Q p \<equiv> p \<in> Rep_amplification_quorum Q"

definition commit_quorum_member :: "commit_quorum => party => bool" where
  "commit_quorum_member Q p \<equiv> p \<in> Rep_commit_quorum Q"

interpretation axiomatic_abstract_domain_model:
  abstract_domain_model broadcaster faulty opt_quorum_member maj_quorum_member
    classic_quorum_member amplification_quorum_member commit_quorum_member
proof (standard)
  show "\<not> classic_quorum_member quQ broadcaster" for quQ
    using Rep_classic_quorum[of quQ] unfolding classic_quorum_member_def by auto

  show "\<not> maj_quorum_member vtQ broadcaster" for vtQ
    using Rep_maj_quorum[of vtQ] unfolding maj_quorum_member_def by auto

  show "\<not> opt_quorum_member opQ broadcaster" for opQ
    using Rep_opt_quorum[of opQ] unfolding opt_quorum_member_def by auto

  show "\<exists>coQ. \<forall>p. commit_quorum_member coQ p \<longrightarrow> p \<notin> faulty"
  text \<open>Proof sketch: @{term "(UNIV :: party set) - faulty"} has cardinality @{term "n - f"},
    and @{thm [source] fault_bound} implies @{term "n - f \<ge> 2 * f + 1"}. Using this set as
    the carrier of a commit quorum yields a witness whose members are all nonfaulty.\<close>
  proof -
    let ?S = "(UNIV :: party set) - faulty"
    have card_S: "card ?S = n - f"
      by (simp add: n_def f_def Finite_Set.card_Diff_subset)
    have co_carrier: "?S \<in> {S :: party set. card S \<ge> 2 * f + 1}"
    proof
      have "n - f \<ge> 2 * f + 1"
        using fault_bound by linarith
      with card_S show "card ?S \<ge> 2 * f + 1"
        by simp
    qed
    let ?coQ = "Abs_commit_quorum ?S"
    have rep_coQ: "Rep_commit_quorum ?coQ = ?S"
      using co_carrier by (simp add: Abs_commit_quorum_inverse)
    show ?thesis
      using rep_coQ unfolding commit_quorum_member_def by auto
  qed

  show "\<exists>amQ. \<forall>p. amplification_quorum_member amQ p \<longrightarrow> p \<notin> faulty"
  text \<open>Proof sketch: @{term "(UNIV :: party set) - faulty"} also has enough members for the
    amplification threshold because @{thm [source] fault_bound} implies @{term "n - f \<ge> f + 1"}.
    Turning that set into an amplification quorum gives the desired witness.\<close>
  proof -
    let ?S = "(UNIV :: party set) - faulty"
    have card_S: "card ?S = n - f"
      by (simp add: n_def f_def Finite_Set.card_Diff_subset)
    have am_carrier: "?S \<in> {S :: party set. card S \<ge> f + 1}"
    proof
      have "n - f \<ge> f + 1"
        using fault_bound by linarith
      with card_S show "card ?S \<ge> f + 1"
        by simp
    qed
    let ?amQ = "Abs_amplification_quorum ?S"
    have rep_amQ: "Rep_amplification_quorum ?amQ = ?S"
      using am_carrier by (simp add: Abs_amplification_quorum_inverse)
    show ?thesis
      using rep_amQ unfolding amplification_quorum_member_def by auto
  qed

  show "\<exists>vtQ. \<forall>p. maj_quorum_member vtQ p \<longrightarrow> p \<notin> faulty"
  text \<open>Proof sketch: Use the nonfaulty non-broadcaster parties as the carrier. If the broadcaster
    is faulty this is @{term "UNIV - faulty"}; otherwise it is @{term "(UNIV - faulty) - {broadcaster}"}.
    In both cases the resulting set still reaches the majority threshold.\<close>
  proof -
    let ?S = "((UNIV :: party set) - faulty) - {broadcaster}"
    have card_nonfaulty: "card ((UNIV :: party set) - faulty) = n - f"
      by (simp add: n_def f_def Finite_Set.card_Diff_subset)
    have vt_carrier: "?S \<in> {S :: party set. broadcaster \<notin> S \<and> card S \<ge> \<lceil>real n / 2\<rceil>}"
    proof -
      have broadcaster_notin: "broadcaster \<notin> ?S"
        by simp
      have card_bound: "card ?S \<ge> \<lceil>real n / 2\<rceil>"
      proof (cases "broadcaster \<in> faulty")
        case True
        have card_S: "card ?S = n - f"
          using True card_nonfaulty by simp
        have "real (n - f) \<ge> real n / 2"
          using fault_bound by linarith
        then have "\<lceil>real (n - f)\<rceil> \<ge> \<lceil>real n / 2\<rceil>"
          by (intro ceiling_mono)
        with card_S show ?thesis
          by simp
      next
        case False
        have card_S: "card ?S = n - f - 1"
          using False card_nonfaulty by (simp add: Finite_Set.card_Diff_singleton)
        have n_bound: "2 * f + 2 \<le> n"
        proof (cases "f = 0")
          case True
          then show ?thesis using two_parties by simp
        next
          case False
          then have "f \<ge> 1" by simp
          then show ?thesis using fault_bound by linarith
        qed
        have "real (n - f - 1) \<ge> real n / 2"
          using n_bound by linarith
        then have "\<lceil>real (n - f - 1)\<rceil> \<ge> \<lceil>real n / 2\<rceil>"
          by (intro ceiling_mono)
        with card_S show ?thesis
          by simp
      qed
      show ?thesis
        using broadcaster_notin card_bound by simp
    qed
    let ?vtQ = "Abs_maj_quorum ?S"
    have rep_vtQ: "Rep_maj_quorum ?vtQ = ?S"
      using vt_carrier by (simp add: Abs_maj_quorum_inverse)
    show ?thesis
      using rep_vtQ unfolding maj_quorum_member_def by auto
  qed


  show "\<exists>quQ. \<forall>p. classic_quorum_member quQ p \<longrightarrow> p \<notin> faulty"
  text \<open>Proof sketch: Reuse the nonfaulty non-broadcaster parties as the carrier. The same case
    split on whether @{term broadcaster} is faulty shows that this set also meets the classic-quorum
    threshold, so it yields a classic quorum all of whose members are nonfaulty.\<close>
  proof -
    let ?S = "((UNIV :: party set) - faulty) - {broadcaster}"
    have card_nonfaulty: "card ((UNIV :: party set) - faulty) = n - f"
      by (simp add: n_def f_def Finite_Set.card_Diff_subset)
    have qu_carrier: "?S \<in> {S :: party set. broadcaster \<notin> S \<and> card S \<ge> \<lceil>real (n + f - 1) / 2\<rceil>}"
    proof -
      have broadcaster_notin: "broadcaster \<notin> ?S"
        by simp
      have card_bound: "card ?S \<ge> \<lceil>real (n + f - 1) / 2\<rceil>"
      proof (cases "broadcaster \<in> faulty")
        case True
        have card_S: "card ?S = n - f"
          using True card_nonfaulty by simp
        have "real (n - f) \<ge> real (n + f - 1) / 2"
          using fault_bound by linarith
        then have "\<lceil>real (n - f)\<rceil> \<ge> \<lceil>real (n + f - 1) / 2\<rceil>"
          by (intro ceiling_mono)
        with card_S show ?thesis
          by simp
      next
        case False
        have card_S: "card ?S = n - f - 1"
          using False card_nonfaulty by (simp add: Finite_Set.card_Diff_singleton)
        have n_bound: "3 * f + 1 \<le> n"
          using fault_bound by linarith
        have "real (n - f - 1) \<ge> real (n + f - 1) / 2"
          using n_bound by linarith
        then have "\<lceil>real (n - f - 1)\<rceil> \<ge> \<lceil>real (n + f - 1) / 2\<rceil>"
          by (intro ceiling_mono)
        with card_S show ?thesis
          by simp
      qed
      show ?thesis
        using broadcaster_notin card_bound by simp
    qed
    let ?quQ = "Abs_classic_quorum ?S"
    have rep_quQ: "Rep_classic_quorum ?quQ = ?S"
      using qu_carrier by (simp add: Abs_classic_quorum_inverse)
    show ?thesis
      using rep_quQ unfolding classic_quorum_member_def by auto
  qed

  show "\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ p" for opQ
  text \<open>Proof sketch: @{term "Rep_opt_quorum opQ"} is too large to fit inside @{term faulty}.
    The optimistic threshold forces @{term "int f < max 1 \<lceil>real (n + 2 * f - 2) / 2\<rceil>"}, and the
    representing set has at least that many members, so it must contain a nonfaulty party.\<close>
  proof -
    have opQ_card: "max 1 \<lceil>real (n + 2 * f - 2) / 2\<rceil> \<le> int (card (Rep_opt_quorum opQ))"
      using Rep_opt_quorum[of opQ] by auto
    have opt_thresh: "int f < max 1 \<lceil>real (n + 2 * f - 2) / 2\<rceil>"
    proof (cases "f = 0")
      case True
      then show ?thesis by simp
    next
      case False
      then have f_pos: "f \<ge> 1" by simp
      have "4 \<le> n"
        using fault_bound f_pos by linarith
      then have "real f < real (n + 2 * f - 2) / 2"
        by linarith
      then have "int f < \<lceil>real (n + 2 * f - 2) / 2\<rceil>"
        by (simp add: less_ceiling_iff)
      then show ?thesis
        by simp
    qed
    have "int (card faulty) < int (card (Rep_opt_quorum opQ))"
    proof -
      have "int f < int (card (Rep_opt_quorum opQ))"
        using opQ_card opt_thresh by linarith
      then show ?thesis
        by (simp add: f_def)
    qed
    then have "card faulty < card (Rep_opt_quorum opQ)"
      by simp
    then have "\<not> Rep_opt_quorum opQ \<subseteq> faulty"
      by (metis card_mono finite leD)
    then obtain p where "p \<in> Rep_opt_quorum opQ" and "p \<notin> faulty"
      by blast
    then show ?thesis
      unfolding opt_quorum_member_def by blast
  qed

  show "broadcaster \<in> faulty \<longrightarrow> (\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ\<^sub>1 p \<and> opt_quorum_member opQ\<^sub>2 p)" for opQ\<^sub>1 opQ\<^sub>2
  text \<open>Proof sketch: Apply @{thm [source] card_lemma_3} to the representing sets @{term "Rep_opt_quorum opQ\<^sub>1"} and @{term "Rep_opt_quorum opQ\<^sub>2"}. Any witness in their nonfaulty intersection immediately yields the required quorum members.\<close>
  proof
    assume broadcaster_faulty: "broadcaster \<in> faulty"
    have opQ1_props:
      "broadcaster \<notin> Rep_opt_quorum opQ\<^sub>1"
      "card (Rep_opt_quorum opQ\<^sub>1) \<ge> \<lceil>real (n + 2 * f - 2) / 2\<rceil>"
      using Rep_opt_quorum[of opQ\<^sub>1] by auto
    have opQ2_props:
      "broadcaster \<notin> Rep_opt_quorum opQ\<^sub>2"
      "card (Rep_opt_quorum opQ\<^sub>2) \<ge> \<lceil>real (n + 2 * f - 2) / 2\<rceil>"
      using Rep_opt_quorum[of opQ\<^sub>2] by auto
    from card_lemma_3[OF broadcaster_faulty opQ1_props(1) opQ1_props(2) opQ2_props(1) opQ2_props(2)]
    obtain p where "p \<in> (Rep_opt_quorum opQ\<^sub>1 \<inter> Rep_opt_quorum opQ\<^sub>2) - faulty"
      by blast
    then show "\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ\<^sub>1 p \<and> opt_quorum_member opQ\<^sub>2 p"
      unfolding opt_quorum_member_def by blast
  qed

  show "broadcaster \<in> faulty \<longrightarrow> (\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ p \<and> maj_quorum_member vtQ p)" for opQ vtQ
  text \<open>Proof sketch: Apply @{thm [source] card_lemma_1} to @{term "Rep_opt_quorum opQ"} and @{term "Rep_maj_quorum vtQ"}. A witness in the nonfaulty intersection satisfies both membership predicates after unfolding their definitions.\<close>
  proof
    assume broadcaster_faulty: "broadcaster \<in> faulty"
    have opQ_props:
      "broadcaster \<notin> Rep_opt_quorum opQ"
      "card (Rep_opt_quorum opQ) \<ge> \<lceil>real (n + 2 * f - 2) / 2\<rceil>"
      using Rep_opt_quorum[of opQ] by auto
    have vtQ_props:
      "broadcaster \<notin> Rep_maj_quorum vtQ"
      "card (Rep_maj_quorum vtQ) \<ge> \<lceil>real n / 2\<rceil>"
      using Rep_maj_quorum[of vtQ] by auto
    from card_lemma_1[OF broadcaster_faulty opQ_props(1) opQ_props(2) vtQ_props(1) vtQ_props(2)]
    obtain p where "p \<in> (Rep_opt_quorum opQ \<inter> Rep_maj_quorum vtQ) - faulty"
      by blast
    then show "\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ p \<and> maj_quorum_member vtQ p"
      unfolding opt_quorum_member_def maj_quorum_member_def by blast
  qed

  show "broadcaster \<in> faulty \<longrightarrow> (\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ p \<and> classic_quorum_member quQ p)" for opQ quQ
  text \<open>Proof sketch: Use @{thm [source] card_lemma_2} on @{term "Rep_opt_quorum opQ"} and @{term "Rep_classic_quorum quQ"}. The produced witness lies in both representing sets and outside @{term faulty}.\<close>
  proof
    assume broadcaster_faulty: "broadcaster \<in> faulty"
    have opQ_props:
      "broadcaster \<notin> Rep_opt_quorum opQ"
      "card (Rep_opt_quorum opQ) \<ge> \<lceil>real (n + 2 * f - 2) / 2\<rceil>"
      using Rep_opt_quorum[of opQ] by auto
    have quQ_props:
      "broadcaster \<notin> Rep_classic_quorum quQ"
      "card (Rep_classic_quorum quQ) \<ge> \<lceil>real (n + f - 1) / 2\<rceil>"
      using Rep_classic_quorum[of quQ] by auto
    from card_lemma_2[OF broadcaster_faulty opQ_props(1) opQ_props(2) quQ_props(1) quQ_props(2)]
    obtain p where "p \<in> (Rep_opt_quorum opQ \<inter> Rep_classic_quorum quQ) - faulty"
      by blast
    then show "\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ p \<and> classic_quorum_member quQ p"
      unfolding opt_quorum_member_def classic_quorum_member_def by blast
  qed

  show "broadcaster \<in> faulty \<longrightarrow> (\<exists>p. p \<notin> faulty \<and> classic_quorum_member quQ\<^sub>1 p \<and> classic_quorum_member quQ\<^sub>2 p)" for quQ\<^sub>1 quQ\<^sub>2
  text \<open>Proof sketch: Use @{thm [source] card_lemma_7} on @{term "Rep_classic_quorum quQ\<^sub>1"} and @{term "Rep_classic_quorum quQ\<^sub>2"}. The lemma yields a party in both representing sets and outside @{term faulty}, which is exactly the desired witness.\<close>
  proof
    assume broadcaster_faulty: "broadcaster \<in> faulty"
    from card_lemma_7[OF broadcaster_faulty]
    obtain p where "p \<in> (Rep_classic_quorum quQ\<^sub>1 \<inter> Rep_classic_quorum quQ\<^sub>2) - faulty"
      using Rep_classic_quorum[of quQ\<^sub>1] Rep_classic_quorum[of quQ\<^sub>2] by auto
    then show "\<exists>p. p \<notin> faulty \<and> classic_quorum_member quQ\<^sub>1 p \<and> classic_quorum_member quQ\<^sub>2 p"
      unfolding classic_quorum_member_def by blast
  qed

  show "\<exists>p. p \<notin> faulty \<and> classic_quorum_member Q p" for Q
  text \<open>Proof sketch: Every classic quorum is too large to be contained in @{term faulty}. Its
    threshold implies @{term "int f < \<lceil>real (n + f - 1) / 2\<rceil>"}, while the representing set of
    @{term Q} has at least that many members, so it contains a nonfaulty party.\<close>
  proof -
    have Q_card: "\<lceil>real (n + f - 1) / 2\<rceil> \<le> int (card (Rep_classic_quorum Q))"
      using Rep_classic_quorum[of Q] by auto
    have qu_thresh: "int f < \<lceil>real (n + f - 1) / 2\<rceil>"
    proof (cases "f = 0")
      case True
      have "0 < real (n + f - 1) / 2"
        using two_parties True by linarith
      then show ?thesis
        using True by simp
    next
      case False
      then have f_pos: "f \<ge> 1" by simp
      have "f + 1 < n"
        using fault_bound f_pos by linarith
      then have "real f < real (n + f - 1) / 2"
        by linarith
      then show ?thesis
        by (simp add: less_ceiling_iff)
    qed
    have "card faulty < card (Rep_classic_quorum Q)"
      using Q_card qu_thresh by (simp add: f_def)
    then have "\<not> Rep_classic_quorum Q \<subseteq> faulty"
      by (metis card_mono finite leD)
    then obtain p where "p \<in> Rep_classic_quorum Q" and "p \<notin> faulty"
      by blast
    then show ?thesis
      unfolding classic_quorum_member_def by blast
  qed

  show "\<exists>p. p \<notin> faulty \<and> maj_quorum_member vtQ p" for vtQ
  text \<open>Proof sketch: @{thm [source] card_lemma_6} applies directly to @{term "Rep_maj_quorum vtQ"}, whose cardinality is part of the typedef invariant.\<close>
    using Rep_maj_quorum card_lemma_6 maj_quorum_member_def by fastforce

  show "\<exists>p. p \<notin> faulty \<and> amplification_quorum_member amQ p" for amQ
  text \<open>Proof sketch: @{term "Rep_amplification_quorum amQ"} has at least @{term "f + 1"} elements, while @{term faulty} has exactly @{term f}. Therefore the representing set cannot be contained in @{term faulty}.\<close>
  proof -
    have amQ_props: "card (Rep_amplification_quorum amQ) \<ge> f + 1"
      using Rep_amplification_quorum[of amQ] by auto
    have "card faulty < card (Rep_amplification_quorum amQ)"
      using amQ_props by (simp add: f_def)
    then have "\<not> Rep_amplification_quorum amQ \<subseteq> faulty"
      by (metis card_mono finite leD)
    then obtain p where "p \<in> Rep_amplification_quorum amQ" and "p \<notin> faulty"
      by blast
    then show ?thesis
      unfolding amplification_quorum_member_def by blast
  qed

  show "broadcaster \<in> faulty \<longrightarrow> (\<exists>vtQ. \<forall>p. maj_quorum_member vtQ p \<longrightarrow> p \<notin> faulty \<and> opt_quorum_member opQ p)" for opQ
  text \<open>Proof sketch: @{thm [source] card_lemma_5} shows that @{term "Rep_opt_quorum opQ - faulty"} still meets the vote threshold. Build a vote quorum from that set, so every one of its members is both nonfaulty and already in the optimistic quorum.\<close>
  proof
    assume broadcaster_faulty: "broadcaster \<in> faulty"
    let ?S = "Rep_opt_quorum opQ - faulty"
    have opQ_props:
      "broadcaster \<notin> Rep_opt_quorum opQ"
      "card (Rep_opt_quorum opQ) \<ge> \<lceil>real (n + 2 * f - 2) / 2\<rceil>"
      using Rep_opt_quorum[of opQ] by auto
    have vote_carrier: "?S \<in> {S :: party set. broadcaster \<notin> S \<and> card S \<ge> \<lceil>real n / 2\<rceil>}"
      using opQ_props card_lemma_5[OF broadcaster_faulty opQ_props(1) opQ_props(2)]
      by auto
    let ?vtQ = "Abs_maj_quorum ?S"
    have rep_vtQ: "Rep_maj_quorum ?vtQ = ?S"
      using vote_carrier by (simp add: Abs_maj_quorum_inverse)
    show "\<exists>vtQ. \<forall>p. maj_quorum_member vtQ p \<longrightarrow> p \<notin> faulty \<and> opt_quorum_member opQ p"
      using opt_quorum_member_def rep_vtQ maj_quorum_member_def by auto
  qed

  show "\<exists>amQ. \<forall>p. amplification_quorum_member amQ p \<longrightarrow> p \<notin> faulty \<and> commit_quorum_member coQ p" for coQ
  text \<open>Proof sketch: @{thm [source] card_lemma_4} guarantees that @{term "Rep_commit_quorum coQ - faulty"} still has the amplification threshold. Use that set as the representing set of a witness amplification quorum.\<close>
  proof -
    let ?S = "Rep_commit_quorum coQ - faulty"
    have coQ_props: "card (Rep_commit_quorum coQ) \<ge> 2 * f + 1"
      using Rep_commit_quorum[of coQ] by auto
    have am_carrier: "?S \<in> {S :: party set. card S \<ge> f + 1}"
      using card_lemma_4[OF coQ_props] by simp
    let ?amQ = "Abs_amplification_quorum ?S"
    have rep_amQ: "Rep_amplification_quorum ?amQ = ?S"
      using am_carrier by (simp add: Abs_amplification_quorum_inverse)
    show ?thesis
      using amplification_quorum_member_def commit_quorum_member_def rep_amQ by auto
  qed
qed

end