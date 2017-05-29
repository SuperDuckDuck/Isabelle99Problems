theory P03
imports Main 
begin 

thm notE
lemma "n = 0 \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> n = 3" by (rule notE)
using [[simp_trace_new mode=full]]
proof - 
assume a: "n = 0"
assume b: "n \<noteq> 0"
from a b have False by (simp )
from a and b have "0 \<noteq> 0" by simp

thm simp_thms
fun p03_2 :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option " where
"p03_2 [] _ = None"|
"p03_2 (x#xs) n = (if n = 1 then Some x else  p03_2 xs (n -1))"

value  "p03_2 [1,2,3,4] 3 :: int option"


lemma "p03_2 [] n = None"
proof -
  show ?thesis by (subst p03_2.simps(1); rule refl)
qed
thm subst
lemma "p03_2 [x] 1  = Some x" by simp

thm
lemma " length ls  \<ge> n  \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> p03_2 ls n = Some a"
using [[simp_trace_new mode=full]]
proof (induct ls)
 case Nil
  assume a:"\<not>(n = 0)"
  assume "n \<le> length []"
  with list.size(3) have "n \<le> 0" by (rule subst) 
  with le_0_eq have "n = 0"  by (rule subst)
  with a show "p03_2 [] n = Some a"  by (rule notE)
 next
show "\<And>aa ls. (n \<le> length ls \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> p03_2 ls n = Some a) \<Longrightarrow> n \<le> length (aa # ls) \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> p03_2 (aa # ls) n = Some a" by auto
  fix aa ls
  assume "n \<le> length ls \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> p03_2 ls n = Some a"
  assume " n \<le> length (aa # ls)"
  assume "n \<noteq> 0"
  