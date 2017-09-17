theory P04 
imports Main 
begin 


primrec p04_1 :: "'a list \<Rightarrow> int" where 
"p04_1 [] = 0"|
"p04_1 (x#xs) = 1 + p04_1 xs"


value "p04_1[1,2,3,4,5]"

value "p04_1 []"

lemma "p04_1 [] = 0" by simp
    
lemma "p04_1 ls = int (length ls)"
proof (induct ls)
  case Nil 
  show ?case by simp
 next 
  fix a ls 
  case (Cons a ls)
  assume " p04_1 ls = int (length ls)"
  thus " p04_1 (a # ls) = int (length (a # ls))" by simp
qed
  
lemma "p04_1 (ls @ xs) = p04_1 ls + p04_1 xs" 
  apply (induction ls  arbitrary : xs)
   apply auto
  done
    

lemma " p04_1 ls + 1 = p04_1 (h#ls)" by simp
    
lemma "int(card (set ls)) \<le> p04_1 ls" 
  using [[simp_trace_new mode=full]]
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume hyp:"int (card (set ls)) \<le> p04_1 ls"
  show ?case 
  proof (cases "a \<in> set ls")
    case True
    assume chyp:"a \<in> set ls"
    then have  "set (a # ls) = set ls" by auto
    then have "int (card (set (a # ls))) = int(card (set ls))" using chyp by simp 
    then show ?thesis using hyp by simp
  next
    case False
    assume assm:"a \<notin> set ls"
    from assm have "card (set (a#ls)) = Suc (card (set ls))" by simp
    with hyp show ?thesis by simp
  qed
qed
  
lemma helper :"p04_1 ls \<ge> 0" by (induct ls , simp_all) (* used in p04_2 = p04_1*)    
  
primrec p04_2 :: "'a list \<Rightarrow> nat" where 
  "p04_2 [] = 0"|
  "p04_2 (x#xs) = Suc (p04_2 xs)"

value "p04_2[1,2,3,4,5]"

value "p04_2 []"

lemma "p04_2 [] = 0" by simp
    
lemma "p04_2 ls = length ls" by (induct ls ,simp_all)
    
lemma "p04_2 (ls @ xs) = p04_2 ls + p04_2 xs" by (induct ls, simp_all)
    
lemma " p04_2 ls + 1 = p04_2 (h#ls)" by simp

lemma helper2 : "a \<in> set ls \<Longrightarrow> card (set (a#ls)) = card (set ls)"
proof -
  assume assm:"a \<in> set ls"
  have a:"(card (set (a#ls)) = card (set ls)) = (length (remdups(a#ls)) = length (remdups ls))" by (subst length_remdups_card_conv)+ simp
  from assm have b:"length (remdups(a#ls)) = length (remdups ls)" 
  proof (induct ls)
    case Nil
    then show ?case by simp
  next
    case (Cons aa ls)
    then show ?case by auto 
  qed
  with a show ?thesis by simp
qed
  
    
    
lemma "card (set ls) \<le> p04_2 ls" 
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume hyp:"card (set ls) \<le> p04_2 ls"
  show ?case 
  proof (cases "a \<in> set ls")
    case True
    assume ca:"a \<in> set ls"
    have "(card (set (a # ls)) \<le> p04_2 (a # ls)) = (card (set  ls) \<le> p04_2 (a # ls))"  by (subst helper2, fact, rule refl)
    then show ?thesis using hyp  by simp
  next
    case False
    then show ?thesis using hyp by simp
  qed
qed    
 
lemma "p04_2 ls = nat(p04_1 ls)" 
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume hyp:"p04_2 ls = nat (p04_1 ls)"
  have "p04_2 (a # ls) =  Suc (nat (p04_1 ls))" by (simp add : hyp)
  also have "\<dots> = nat (1 + p04_1 ls)" by (simp add :Suc_nat_eq_nat_zadd1 helper)
  also have "\<dots> = nat (p04_1 (a#ls))" by simp
  finally show ?case by assumption
qed

lemma "(\<Sum>x\<leftarrow>ls. 1)  = p04_2 ls" by (induct ls, simp_all)

lemma "p04_2 (replicate n val) = n" by (induct n , simp_all)
    
definition p04_3 :: "'a list \<Rightarrow> nat" where
  "p04_3 ls = foldl (\<lambda> res  _ . Suc res ) 0 ls"
  
declare p04_3_def[simp] 
  
lemma "p04_3 [] = 0" by simp

lemma helper4 : "foldr (\<lambda> _ res . Suc res) (xs @ ys) 0 = foldr (\<lambda> _ res . Suc res) (xs) 0 + foldr (\<lambda> _ res . Suc res) (ys) 0"  by (induct xs, simp_all)
    
lemma "p04_3 ls = length ls" 
proof -
  have tmp:"p04_3 ls = foldr (\<lambda> val res. Suc res)  (rev ls) 0 " by (simp add : foldl_conv_foldr)
  show ?thesis 
  proof (subst tmp, induct ls)
    case Nil
    then show ?case by simp
  next
    case (Cons a ls)
    assume hyp:"foldr (\<lambda>val. Suc) (rev ls) 0 = length ls"
    have "foldr (\<lambda>val. Suc) (rev (a#ls)) 0 = foldr (\<lambda>val. Suc) (rev ls) 0  + foldr (\<lambda>val. Suc) [a] 0 " by (subst rev.simps(2), subst helper4, rule refl)
    then show ?case using hyp by simp
  qed
qed
  
    
