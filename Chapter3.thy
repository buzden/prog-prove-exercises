theory Chapter3
  imports Main
begin

(* Exercise 3.1 *)

datatype 'a tree
  = Tip
  | Node \<open>'a tree\<close> 'a \<open>'a tree\<close>

fun set :: \<open>'a tree \<Rightarrow> 'a set\<close> where
  \<open>set Tip          = {}\<close>
| \<open>set (Node l x r) = {x} \<union> set l \<union> set r\<close>

fun ord :: \<open>int tree \<Rightarrow> bool\<close> where
  \<open>ord Tip          \<longleftrightarrow> True\<close>
| \<open>ord (Node l x r) \<longleftrightarrow> ord l
                      \<and> ord r
                      \<and> (\<forall>c \<in> set l. c \<le> x)
                      \<and> (\<forall>c \<in> set r. c \<ge> x)\<close>

fun ins :: \<open>int \<Rightarrow> int tree \<Rightarrow> int tree\<close> where
  \<open>ins n Tip          = Node Tip n Tip\<close>
| \<open>ins n (Node l x r) = (if n = x
                           then (Node l x r)
                         else if n < x
                           then Node (ins n l) x r
                           else Node l x (ins n r))\<close>

theorem ins_adds[simp]: \<open>set (ins x t) = {x} \<union> set t\<close>
  apply (induction t)
  apply auto
  done

theorem ins_preserves_ord: \<open>ord t \<Longrightarrow> ord (ins i t)\<close>
  apply (induction t)
  apply auto
  done

(* *)

thm conjI[OF refl[of \<open>a\<close>] refl[of \<open>b\<close>]]

(* Examples from section 3.5.1 *)

inductive ev :: \<open>nat \<Rightarrow> bool\<close> where
  ev0:  \<open>ev 0\<close>
| evSS: \<open>ev n \<Longrightarrow> ev (Suc (Suc n))\<close>

thm evSS[OF evSS[OF ev0]]

lemma \<open>ev (Suc (Suc (Suc (Suc 0))))\<close>
  apply (rule evSS)
  apply (rule evSS)
  apply (rule ev0)
  done

fun evn :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>evn 0 = True\<close>
| \<open>evn (Suc 0) = False\<close>
| \<open>evn (Suc (Suc n)) = evn n\<close>

lemma \<open>ev m \<Longrightarrow> evn m\<close>
  apply (induction m rule: ev.induct)
  by simp_all

declare ev.intros[simp, intro]

lemma \<open>evn m \<Longrightarrow> ev m\<close>
  apply (induction rule: evn.induct)
  by simp_all

lemma \<open>\<not>ev m \<Longrightarrow> \<not>evn m\<close>
  apply (induction m rule: evn.induct)
  by auto

lemma \<open>\<not>evn m \<Longrightarrow> \<not>ev m\<close>
  apply (induction rule: evn.induct)
  apply simp_all
  using ev.cases apply blast
  using ev.simps by blast

(* Example from section 3.5.2 *)

inductive star :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close> for r where
  refl: \<open>star r x x\<close>
| step: \<open>r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z\<close>

lemma star_trans: \<open>star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z\<close>
  apply (induction rule: star.induct)
  apply simp
  apply (metis step)
  done

(* Exercise 3.2 *)

inductive palindrome :: \<open>'a list \<Rightarrow> bool\<close> where
  empty : \<open>palindrome []\<close>
| added : \<open>palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])\<close>

theorem rev_of_palindrome: \<open>palindrome xs \<Longrightarrow> rev xs = xs\<close>
  apply (induction rule: palindrome.induct)
  by auto

(* Exercise 3.3 *)

inductive star' :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close> for r where
  refl': \<open>star' r x x\<close>
| step': \<open>star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z\<close>

theorem star'_is_star: \<open>star' r x y \<Longrightarrow> star r x y\<close>
  apply (induction rule: star'.induct)
  apply (simp add: star.refl)
  by (meson star.simps star_trans)

lemma star'_trans: \<open>star' r y z \<Longrightarrow> star' r x y \<Longrightarrow> star' r x z\<close>
  apply (induction rule: star'.induct)
  apply simp
  by (metis step')

theorem star_is_star': \<open>star r x y \<Longrightarrow> star' r x y\<close>
  apply (induction rule: star.induct)
  apply (simp add: refl')
  by (meson refl' step' star'_trans)

(* Exercise 3.4 *)

inductive iter :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  iterR : \<open>iter r 0 x x\<close>
| iterN : \<open>r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z\<close>

theorem iter_then_star: \<open>iter r n x y \<Longrightarrow> star r x y\<close>
  apply (induction rule: iter.induct)
  by (simp_all add: star.refl star.step)

theorem star_then_some_iter: \<open>star r x y \<Longrightarrow> \<exists>n. iter r n x y\<close>
  apply (induction rule: star.induct)
  apply (meson iter.simps)
  apply (meson iterN)
  done

(* Exercise 3.5 *)

datatype alpha = a | b

inductive S :: \<open>alpha list \<Rightarrow> bool\<close> where
  empty : \<open>S []\<close>
| asb   : \<open>S w \<Longrightarrow> S (a # w @ [b])\<close>
| ss    : \<open>S v \<Longrightarrow> S w \<Longrightarrow> S (v@w)\<close>

inductive T :: \<open>alpha list \<Rightarrow> bool\<close> where
  empty : \<open>T []\<close>
| tatb  : \<open>T v \<Longrightarrow> T w \<Longrightarrow> T (v @ [a] @ w @ [b])\<close>

theorem t_to_s: \<open>T w \<Longrightarrow> S w\<close>
  apply (induction rule: T.induct)
  by (simp_all add: S.empty S.asb S.ss)

lemma t_conj: \<open>T v \<Longrightarrow> T w \<Longrightarrow> T (w @ v)\<close>
  apply (induction rule: T.induct)
  apply simp
  by (metis Cons_eq_appendI T.simps append_eq_appendI append_self_conv2)

theorem s_to_t: \<open>S w \<Longrightarrow> T w\<close>
  apply (induction rule: S.induct)
  apply (simp add: T.empty)
  apply (metis T.empty T.simps append.left_neutral append_Cons)
  using t_conj by blast  

theorem s_eq_t: \<open>S w = T w\<close>
  using s_to_t t_to_s by blast

end