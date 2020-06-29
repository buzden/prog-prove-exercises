theory Chapter4
  imports Main Chapter3
begin

(* Exercise 4.1 *)

lemma assumes F: \<open>\<forall>x y. F x y \<or> F y x\<close>
  and A: \<open>\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y\<close>
  and FA: \<open>\<forall>x y. F x y \<longrightarrow> A x y\<close> and \<open>A x y\<close>
  shows \<open>F x y\<close>
proof -
  from F have \<open>F x y \<or> F y x\<close> by blast
  then show ?thesis
  proof
    assume \<open>F x y\<close>
    show \<open>F x y\<close> by (simp add: \<open>F x y\<close>)
  next
    assume \<open>F y x\<close>
    then have \<open>A y x\<close> by (simp add: FA)
    then have \<open>x = y\<close> by (simp add: A \<open>A x y\<close>)
    then show \<open>F x y\<close> using F by blast
  qed
qed

  \<comment> \<open>`T` from the task is replaced with `F` because of clash with imports\<close>

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

(* Section 4.4.6 *)

lemma \<open>\<not> ev (Suc (Suc (Suc 0)))\<close> (is \<open>\<not>?X\<close>)
proof
  assume \<open>?X\<close>
  have \<open>ev (Suc 0)\<close> using \<open>?X\<close> ev.simps by blast
  then show False by cases
qed

lemma \<open>ev (Suc m) \<Longrightarrow> \<not> ev m\<close>
proof (induction "Suc m" arbitrary: m rule: ev.induct)
  case evSS
  then show ?case using ev.simps by blast
qed

  \<comment> \<open>The proof above differs from one in book, does not use
      rule inversion and seems to be much simpler to my mind.\<close>

(* Exercise 4.3 *)

lemma
  assumes a: \<open>ev (Suc (Suc n))\<close>
  shows \<open>ev n\<close>
proof (cases \<open>Suc (Suc n)\<close> rule: ev.induct)
  case ev0
  then show ?case by (simp add: assms)
next
  case evSS
  then show ?thesis using assms ev.simps by blast
qed

(* Exercise 4.4 *)

lemma \<open>\<not> ev (Suc (Suc (Suc 0)))\<close> (is \<open>\<not>?X\<close>)
proof
  assume \<open>?X\<close>
  then show False
  proof cases
    case evSS
    then show False using ev.simps by blast
  qed
qed

(* Exercise 4.5 *)

theorem iter_then_star': \<open>iter r n x y \<Longrightarrow> star r x y\<close>
proof (induction rule: iter.induct)
  case (iterR r x)
  then show ?case by (simp add: star.refl)
next
  case (iterN r x y n z)
  then show ?case by (simp add: star.step)
qed

(* Exercise 4.6 *)

fun elems :: \<open>'a list \<Rightarrow> 'a set\<close> where
  \<open>elems []     = {}\<close>
| \<open>elems (x#xs) = {x} \<union> elems xs\<close>

theorem \<open>x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys\<close>
  (is \<open>?x_in_xs \<Longrightarrow> \<exists> ys zs. ?prop xs ys zs\<close>)
proof (induction xs)
case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case
  proof (cases \<open>x = a\<close>)
    case True
    then show ?thesis by fastforce
  next
    case False
    assume \<open>x \<in> elems (a#as)\<close>
    then have \<open>x \<in> elems as\<close> by (simp add: False)
    then have prev: \<open>\<exists>ys zs. ?prop as ys zs\<close> using Cons.IH by blast
    obtain ys zs where \<open>?prop as ys zs\<close> using prev by blast
    then have \<open>?prop (a#as) (a#ys) zs\<close> by (simp add: False)
    then show ?thesis by blast
  qed
qed

(* Exercise 4.7 *)

fun balanced :: \<open>nat \<Rightarrow> alpha list \<Rightarrow> bool\<close> where
  \<open>balanced 0       []    = True\<close>
| \<open>balanced n       (a#w) = balanced (Suc n) w\<close>
| \<open>balanced (Suc n) (b#w) = balanced n w\<close>
| \<open>balanced _       _     = False\<close>


theorem balanced_thru_replicate:
  \<open>balanced n w = S (replicate n a @ w)\<close>

end