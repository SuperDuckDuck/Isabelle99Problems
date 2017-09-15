theory P08
  imports Main 
begin 
  
  
fun p08 :: "'a list \<Rightarrow> 'a list" where 
  "p08 [] = []"|
  "p08 [x] = [x]"|
  "p08 (x#y#xs) = (if x= y then p08 (y#xs) else x # p08 (y#xs))"
  
  
  
lemma "length (p08 ls) \<le> length ls" 
  using [[simp_trace_new mode=full]]
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume a:"length (p08 ls) \<le> length ls"
  show ?case 
  proof (cases ls)
    case Nil
    assume "ls = []"
    then show ?thesis by simp
  next
    case (Cons aa list)
    assume b:"ls = aa # list"
    with a show ?thesis by simp 
  qed  
qed
 
lemma "x \<in> \<nat> \<Longrightarrow> x < length ls - 1 \<Longrightarrow>  ls ! x = ls ! (x+1) \<Longrightarrow> length ls \<ge> 2 \<Longrightarrow> length (p08 ls) < length ls" 
proof (cases ls rule : p08.cases)
  case 1
  then show ?thesis 
next
  case (2 x)
  then show ?thesis sorry
next
  case (3 x y xs)
  then show ?thesis sorry
qed 
  
  
lemma "x \<in> \<nat> \<Longrightarrow> x < length ls - 1 \<Longrightarrow>  ls ! x = ls ! (x+1) \<Longrightarrow> length ls \<ge> 2 \<Longrightarrow> length (p08 ls) < length ls" 
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume a:"x \<in> \<nat> \<Longrightarrow> x < length ls - 1 \<Longrightarrow> ls ! x = ls ! (x + 1) \<Longrightarrow> 2 \<le> length ls \<Longrightarrow> length (p08 ls) < length ls"
  assume b:"x \<in> \<nat>"
  assume c:"x < length (a # ls) - 1"
  assume d:"(a # ls) ! x = (a # ls) ! (x + 1)"
  assume e:"2 \<le> length (a # ls)"
  show ?case 
  proof (cases ls)
    case Nil
    with e show ?thesis by simp
  next
    case (Cons aa list)
    assume f:"ls = aa # list"
    show ?thesis 
    proof (cases "aa = a")
      case True
      with f show ?thesis 
    next
      case False
      then show ?thesis sorry
    qed 
  qed
qed
  
    
    
    
    lemma "\<not>(\<exists>x. )"