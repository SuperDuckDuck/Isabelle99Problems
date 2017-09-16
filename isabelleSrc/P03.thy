theory P03
imports Main 
begin 
(*
fun p03_simple :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where 
  "p03_simple [] _ = None"|
  "p03_simple (x#xs) n = (if n = 0 then Some x else p03_simple xs (n - 1))"

lemma "p03_simple [] n = None" by simp
    
  
lemma lm1 :  "p03_simple ls n= None \<Longrightarrow> p03_simple ls (Suc n) = None" 
proof (induct n rule : p03_simple.induct)
  case (1 uu)
  then show ?case by simp
next
  case (2 x xs n)
  assume " n \<noteq> 0 \<Longrightarrow> p03_simple xs (n - 1) = None \<Longrightarrow> p03_simple xs (Suc (n - 1)) = None"
  hence a:" n \<noteq> 0 \<Longrightarrow> p03_simple xs (n - 1) = None \<Longrightarrow> p03_simple xs n  = None" by auto
  assume b:"p03_simple (x # xs) n = None"
  from a and b show ?case 
  proof (cases n)
    case 0
    with b show ?thesis by simp
  next
    case (Suc nat)
    assume asm1:"n = Suc nat"
    hence tmp1:"n \<noteq> 0" by auto
    from a and asm1 have tmp2:" n \<noteq> 0 \<Longrightarrow> p03_simple xs nat = None \<Longrightarrow> p03_simple xs n  = None" by auto
    from b and asm1 have "p03_simple xs nat = None" by auto
    with tmp1 and tmp2 have " p03_simple xs n  = None" by auto
    then show ?thesis by auto
  qed
qed
  
lemma "p03_simple (a#ls) n= None \<Longrightarrow> p03_simple ls n = None" 
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  assume "(p03_simple (a # ls) n = None \<Longrightarrow> p03_simple ls n = None)"
  assume "p03_simple (a # ls) (Suc n) = None"
  thus ?case by (simp add: lm1)
qed
  
lemma "length ls <  n \<Longrightarrow> (p03_simple ls n = p03_simple (h#ls) n)"  
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume a:"length ls < n \<Longrightarrow> p03_simple ls n = p03_simple (h # ls) n"
  assume b:"length (a # ls) < n"
  show ?case 
  proof (cases n)
    case 0
    with a and b  show ?thesis by simp
  next
    case (Suc nat)
    with a and b show ?thesis 
  qed
    
qed
  

 
lemma "length xs > length ys \<Longrightarrow>length xs \<le> n \<Longrightarrow> p03_simple xs n = None \<Longrightarrow> p03_simple ys n = None"
proof (induct xs ys  rule : list_induct2')  
  case 1
  then show ?case by simp
next
  case (2 x xs)
  then show ?case by simp
next
  case (3 y ys)
  then show ?case by simp
next
  case (4 x xs y ys)
  assume a:"length ys < length xs \<Longrightarrow> length xs \<le> n \<Longrightarrow> p03_simple xs n = None \<Longrightarrow> p03_simple ys n = None"
  assume b:"length (y # ys) < length (x # xs)"
  assume c:"length (x # xs) \<le> n"
  assume d:" p03_simple (x # xs) n = None"
  from a b c d show ?case 
 

    


lemma "length ls \<le> n \<Longrightarrow> p03_simple ls n = None " 
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume a:"length ls \<le> n \<Longrightarrow> p03_simple ls n = None"
  assume b:"length (a # ls) \<le> n"
  from a and b show ?case by (simp add : lm1)
qed
  
      
        
 
      
  qed
    
qed
*)  
  
primrec p03_1 ::  "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "p03_1 [] _ defa = defa"|
  "p03_1 (x#xs) n defa = (case n of 0 \<Rightarrow> defa | (Suc 0) \<Rightarrow> x  | _ \<Rightarrow> p03_1 xs (n -1) defa)"
  
value "p03_1 [] 3 5 :: int"
  
value "p03_1 [1] 1 5 :: int"
  
value "p03_1 [1,2,3,4] 3 5:: int"
  
value "p03_1 [1] 0 5 :: int"
  
value "p03_1 [] 0 5 :: int"
  
lemma "p03_1 [] n defa = defa" by simp
    
lemma "p03_1 xs 0 defa = defa" by (induct xs , simp_all)
    
lemma "n \<le> length ls \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> p03_1 ls n defa \<in> set ls"
proof -
  assume hyp1:"n \<le> length ls"
     and hyp2:"n \<noteq> 0"
  thus "p03_1 ls n defa \<in> set ls " 
  proof (induct ls arbitrary : n)
    case Nil
    then show ?case by simp
  next
    case (Cons a ls)
    assume hypa1:"\<And>n . n \<le> length ls \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> p03_1 ls n defa \<in> set ls"
      and hypa2:"n \<le> length (a # ls)"
      and hypa3:"n \<noteq> 0"
    from hypa2 and hypa3  show ?case 
    proof (cases n)
      case 0
      with hypa3 show ?thesis by simp
    next
      case (Suc nat)
      assume nHyp:"n = Suc nat"
      then show ?thesis 
      proof (cases nat)
        case 0
        with nHyp show ?thesis by simp
      next
        case (Suc nat2)
        assume n2Hyp:"nat = Suc nat2"
        with nHyp have tmp:"n = Suc (Suc nat2)" by simp
        with hypa1 and hypa2 and hypa3 show ?thesis by simp
      qed
    qed
  qed
qed
  
lemma "n > length ls \<Longrightarrow> p03_1 ls n defa = defa" 
proof (induct ls arbitrary : n)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume hyp1:"\<And>n. length ls < n \<Longrightarrow> p03_1 ls n defa = defa"
  assume hyp2:"length (a # ls) < n"
  thus ?case 
  proof (induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    assume hypa1:"length (a # ls) < Suc n"
    then show ?case using hyp1 by (induct n , simp_all)
  qed    
qed
    
    
    
fun p03_2 :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where 
  "p03_2 [] _ defa = defa"|
  "p03_2 _ 0 defa = defa"|
  "p03_2 (x#xs) (Suc 0) _ = x"|
  "p03_2 (x#xs) (Suc n) defa = p03_2 xs n defa"

lemma "n \<le> length ls \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> p03_2 ls n defa \<in> set ls"  by (induct ls n defa rule : p03_2.induct, simp_all)
    
lemma ""
 
definition p03_3 :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "p03_3 ls n defa  = (let tmp = drop (n - 1) ls in if List.null tmp then defa else hd tmp)"

lemma "n \<le> length ls \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> p03_3 ls n defa \<in> set ls" 
proof (induct ls arbitrary : n)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume hyp1:"\<And>n . n \<le> length ls \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> p03_3 ls n defa \<in> set ls"
    and hyp2:"n \<le> length (a # ls)"
    and hyp3:"n \<noteq> 0"
  from hyp2 and hyp3  show ?case
  proof (induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then show ?case 
  qed
    
qed
  
  
primrec p03_4 :: 
  
fun p03_5 :: ""
    (*
fun bla :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "bla [] _ defa = defa"|
  "bla _ 0 defa = defa"|
  "bla (x#xs) (Suc 0) _ = x"|
  "bla (x#xs) (Suc n) defa = bla xs n defa"
  
lemma "n \<le> length ls \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> bla ls n defa \<in> set ls" proof (induct ls n defa rule : bla.induct)
  case (1 uu defa)
  then show ?case sorry
next
  case (2 v va defa)
  then show ?case sorry
next
  case (3 x xs uw)
  then show ?case sorry
next
  case (4 x xs v defa)
  then show ?case sorry
qed
  *)
  
  
  (*
declare bla_def[simp]
  thm bla_def
lemma "bla (n::nat) = (0::nat) \<or> bla n = 2 \<or> bla n = 1" 
  using [[simp_trace_new mode=full]]
proof (induct n)
  case 0
    (*have "bla 0 = " *)
  then show ?case by simp
next
  case (Suc n)
  then show ?case sorry
qed
  *)
    
(*
fun p03_1 :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
"p03_1 [] _ = None"|
"p03_1 (x#xs) n = (case n of  0 \<Rightarrow> None| (Suc 0) \<Rightarrow> Some x | Suc val  \<Rightarrow>  p03_1 xs val)"

value "p03_1 [1,2 ,3,4] 4 :: int option"

value "p03_1 [] 4"

value "p03_1 [1,2,3,4] 0"

  
lemma "p03_1 [] n = None" by simp
    
lemma "n = 0 \<Longrightarrow> p03_1 ls n = None" 
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  then show ?case by simp
qed

lemma tmp : "length (val#ls) < n \<Longrightarrow> length ls < n" by auto

lemma "(length ls < n \<Longrightarrow> P) \<Longrightarrow> length (a#ls) < (Suc n2) \<Longrightarrow> n = Suc n2 \<Longrightarrow> P" by simp
 *)   