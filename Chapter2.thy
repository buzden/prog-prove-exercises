theory Chapter2
  imports Main
begin

(* Exercise 2.1 *)

value \<open>1 + (2::nat)\<close>
value \<open>1 + (2::int)\<close>
value \<open>1 - (2::nat)\<close>
value \<open>1 - (2::int)\<close>

value \<open>1 + 2 :: nat\<close>

(* Exercise 2.2 *)

fun add :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>add 0       n = n\<close> |
  \<open>add (Suc m) n = Suc (add m n)\<close>

theorem add_assoc[simp]: \<open>add n (add m k) = add (add n m) k\<close>
  apply (induction n)
  apply auto
  done

lemma add_z[simp]: \<open>add n 0 = n\<close>
  apply (induction n)
  apply auto
  done

lemma add_succ_right[simp]: \<open>add n (Suc m) = Suc (add n m)\<close>
  apply (induction n)
  apply auto
  done

theorem add_comm: \<open>add n m = add m n\<close>
  apply (induction n)
  apply auto
  done

fun double :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>double 0       = 0\<close> |
  \<open>double (Suc n) = Suc (Suc (double n))\<close>

theorem double_is_add: \<open>double m = add m m\<close>
  apply (induction m)
  apply auto
  done

(* Exercise 2.3 *)

fun count :: \<open>'a \<Rightarrow> 'a list \<Rightarrow> nat\<close> where
  \<open>count _ []       = 0\<close> |
  \<open>count x (y # xs) = (if x = y then Suc (count x xs) else count x xs)\<close>

theorem count_le_length: \<open>count x xs \<le> length xs\<close>
  apply (induction xs)
  apply auto
  done

(* Exercise 2.4 *)

fun snoc :: \<open>'a list \<Rightarrow> 'a \<Rightarrow> 'a list\<close> where
  \<open>snoc []     n = [n]\<close> |
  \<open>snoc (x#xs) n = x # snoc xs n\<close>

fun reverse :: \<open>'a list \<Rightarrow> 'a list\<close> where
  \<open>reverse []     = []\<close> |
  \<open>reverse (x#xs) = snoc (reverse xs) x\<close>

lemma reverse_of_snoc[simp]: \<open>reverse (snoc xs x) = x # reverse xs\<close>
  apply (induction xs)
  apply auto
  done

theorem double_reverse[simp]: \<open>reverse (reverse xs) = xs\<close>
  apply (induction xs)
  apply auto
  done

(* Exercise 2.5 *)

fun sum_upto :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>sum_upto 0       = 0\<close> |
  \<open>sum_upto (Suc n) = Suc n + sum_upto n\<close>

theorem sum_upto_formula: \<open>sum_upto n = n * (n + 1) div 2\<close>
  apply (induction n)
  apply auto
  done

(* Exercise 2.6 *)

datatype 'a tree = Tip
                 | Node \<open>'a tree\<close> 'a \<open>'a tree\<close>

fun contents :: \<open>'a tree \<Rightarrow> 'a list\<close> where
  \<open>contents Tip          = []\<close> |
  \<open>contents (Node l x r) = x # contents l @ contents r\<close>

fun sum_tree :: \<open>nat tree \<Rightarrow> nat\<close> where
  \<open>sum_tree Tip          = 0\<close> |
  \<open>sum_tree (Node l x r) = x + sum_tree l + sum_tree r\<close>

theorem sum_tree_thru_contents: \<open>sum_tree tr = sum_list (contents tr)\<close>
  apply (induction tr)
  apply auto
  done

(* Exercise 2.7 *)

datatype 'a tree2
  = Tip
  | Leaf 'a
  | Node \<open>'a tree2\<close> 'a \<open>'a tree2\<close>

fun mirror :: \<open>'a tree2 \<Rightarrow> 'a tree2\<close> where
  \<open>mirror Tip          = Tip\<close>
| \<open>mirror (Leaf x)     = Leaf x\<close>
| \<open>mirror (Node l x r) = Node (mirror r) x (mirror l)\<close>

lemma mirror_of_mirror: \<open>mirror (mirror tr) = tr\<close>
  apply (induction tr)
  apply auto
  done

fun pre_order :: \<open>'a tree2 \<Rightarrow> 'a list\<close> where
  \<open>pre_order Tip          = []\<close>
| \<open>pre_order (Leaf x)     = [x]\<close>
| \<open>pre_order (Node l x r) = x # pre_order l @ pre_order r\<close>

fun post_order :: \<open>'a tree2 \<Rightarrow> 'a list\<close> where
  \<open>post_order Tip          = []\<close>
| \<open>post_order (Leaf x)     = [x]\<close>
| \<open>post_order (Node l x r) = post_order l @ post_order r @ [x]\<close>

theorem pre_n_post_orders: \<open>pre_order (mirror t) = rev (post_order t)\<close>
  apply (induction t)
  apply auto
  done

(* Exercise 2.8 *)

fun intersperse :: \<open>'a \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>intersperse _ []       = []\<close>
| \<open>intersperse _ [x]      = [x]\<close>
| \<open>intersperse s (x#y#xs) = x # s # intersperse s (y#xs)\<close>

lemma intersperse_n_map_step:
    \<open>map f (intersperse a xs) = intersperse (f a) (map f xs) \<Longrightarrow>
     map f (intersperse a (aa # xs)) = intersperse (f a) (f aa # map f xs)\<close>
  apply (induction xs)
  apply auto
  done

theorem intersperse_n_map:
    \<open>map f (intersperse a xs) = intersperse (f a) (map f xs)\<close>
  apply (induction xs)
  apply (auto simp add: intersperse_n_map_step)
  done

(* Exercise 2.9 *)

fun itadd :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>itadd 0       m = m\<close>
| \<open>itadd (Suc n) m = itadd n (Suc m)\<close>

theorem itadd_is_add: \<open>itadd n m = add n m\<close>
  apply (induction n arbitrary: m)
  apply auto
  done

(* Exercise 2.10 *)

datatype tree0
  = Tip
  | Node tree0 tree0

fun nodes :: \<open>tree0 \<Rightarrow> nat\<close> where
  \<open>nodes Tip = 1\<close>
| \<open>nodes (Node l r) = 1 + nodes l + nodes r\<close>

fun explode :: \<open>nat \<Rightarrow> tree0 \<Rightarrow> tree0\<close> where
  \<open>explode 0       t = t\<close>
| \<open>explode (Suc n) t = explode n (Node t t)\<close>

theorem explode_in_nodes: \<open>nodes (explode n t) = 2^n * nodes t + 2^n - 1\<close>
  apply (induction n arbitrary: t)
  apply (auto simp add: algebra_simps)
  done

(* Exercise 2.11 *)

datatype exp
  = Var
  | Const int
  | Add exp exp
  | Mult exp exp

fun eval :: \<open>exp \<Rightarrow> int \<Rightarrow> int\<close> where
  \<open>eval Var        x = x\<close>
| \<open>eval (Const n)  _ = n\<close>
| \<open>eval (Add l r)  x = eval l x + eval r x\<close>
| \<open>eval (Mult l r) x = eval l x * eval r x\<close>

fun evalp :: \<open>int list \<Rightarrow> int \<Rightarrow> int\<close> where
  \<open>evalp []     _ = 0\<close>
| \<open>evalp (p#ps) x = p + x * evalp ps x\<close>

fun add_cwise :: \<open>int list \<Rightarrow> int list \<Rightarrow> int list\<close> where
  \<open>add_cwise []     r      = r\<close>
| \<open>add_cwise l      []     = l\<close>
| \<open>add_cwise (l#ls) (r#rs) = (l+r) # add_cwise ls rs\<close>

fun mult_regroup :: \<open>int list \<Rightarrow> int list \<Rightarrow> int list\<close> where
  \<open>mult_regroup []     r      = []\<close>
| \<open>mult_regroup l      []     = []\<close>
| \<open>mult_regroup (l#ls) (r#rs) =
    l*r # add_cwise (0 # mult_regroup ls rs)
           (add_cwise (map (\<lambda>x \<Rightarrow> x*l) rs) (map (\<lambda>x \<Rightarrow> x*r) ls))\<close>

fun coeffs :: \<open>exp \<Rightarrow> int list\<close> where
  \<open>coeffs Var        = [0, 1]\<close>
| \<open>coeffs (Const n)  = [n]\<close>
| \<open>coeffs (Add l r)  = add_cwise (coeffs l) (coeffs r)\<close>
| \<open>coeffs (Mult l r) = mult_regroup (coeffs l) (coeffs r)\<close>

lemma evalp_add_lin[simp]: \<open>evalp (add_cwise l r) x = evalp l x + evalp r x\<close>
  apply (induction l r rule: add_cwise.induct)
  apply (auto simp add: algebra_simps)
  done

lemma evalp_map[simp]: \<open>evalp (map (\<lambda>x \<Rightarrow> x*n) ns) x = n * evalp ns x\<close>
  apply (induction ns)
  apply (auto simp add: algebra_simps)
  done

lemma evalp_mul_lin[simp]: \<open>evalp (mult_regroup l r) x = evalp l x * evalp r x\<close>
  apply (induction l r rule: mult_regroup.induct)
  apply auto
  apply (simp add: algebra_simps)
  done

theorem evalp_of_coeffs_is_eval: \<open>evalp (coeffs e) x = eval e x\<close>
  apply (induction e)
  apply auto
  done

end