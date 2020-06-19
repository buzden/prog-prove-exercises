theory Chapter4
  imports Main
begin

lemma assumes T: \<open>\<forall>x y. T x y \<or> T y x\<close>
  and A: \<open>\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y\<close>
  and TA: \<open>\<forall>x y. T x y \<longrightarrow> A x y\<close> and \<open>A x y\<close>
  shows \<open>T x y\<close>
proof -
  from T have \<open>T x y \<or> T y x\<close> by blast
  then show ?thesis
  proof
    assume \<open>T x y\<close>
    show \<open>T x y\<close> by (simp add: \<open>T x y\<close>)
  next
    assume \<open>T y x\<close>
    then have \<open>A y x\<close> using TA by blast
    then have \<open>x = y\<close> using A by (simp add: \<open>A x y\<close>)
    then show \<open>T x y\<close> using T by blast
  qed
qed

end