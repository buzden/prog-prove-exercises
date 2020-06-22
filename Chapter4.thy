theory Chapter4
  imports Main
begin

(* Exercise 4.1 *)

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
    then have \<open>A y x\<close> by (simp add: TA)
    then have \<open>x = y\<close> by (simp add: A \<open>A x y\<close>)
    then show \<open>T x y\<close> using T by blast
  qed
qed

(*
(* Slightly shorter and less constructive proof *)
proof cases
  assume \<open>T x y\<close>
  show \<open>T x y\<close> by (simp add: \<open>T x y\<close>)
next
  assume \<open>\<not>T x y\<close>
  have \<open>T y x\<close> using T \<open>\<not> T x y\<close> by blast
  then have \<open>A y x\<close> by (simp add: TA)
  then have \<open>x = y\<close> by (simp add: A \<open>A x y\<close>)
  then show \<open>T x y\<close> using T by blast
qed
*)

(* Exercise 4.2 *)

lemma \<open>\<exists>ys zs. xs = ys @ zs \<and>
               (length ys = length zs \<or> length ys = length zs + 1)\<close>
  (is \<open>\<exists>ys zs. ?p ys zs\<close>)
proof -
  let ?ys = \<open>take ((length xs + 1) div 2) xs\<close>
  let ?zs = \<open>drop ((length xs + 1) div 2) xs\<close>
  have \<open>xs = ?ys @ ?zs \<and> (length ?ys = length ?zs \<or> length ?ys = length ?zs + 1)\<close> by auto
  then show ?thesis by blast
qed

end