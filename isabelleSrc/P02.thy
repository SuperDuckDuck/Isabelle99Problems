theory P02 
imports Main 
begin 

fun p02_1 :: "'a list \<Rightarrow> 'a  \<Rightarrow> 'a" where 
"p02_1 [] defa = defa"|
"p02_1 [x] defa = defa"|
"p02_1 [x , y] defa = x"|
"p02_1 (x#xs) defa = p02_1 xs defa"

value "p02_1 [] 5 :: int"

value "(p02_1 [2] 6) :: int"

value "p02_1 [1,2] 3 :: int"
  
lemma "p02_1 [] defa = defa " by simp
    
lemma "p02_1 [val] defa = defa" by simp
    
lemma "p02_1 [val1,val2] defa = val1" by simp 

lemma "p02_1 (xs @ [a , b]) def = a"
proof (induct xs)
  show "p02_1 ([] @ [a, b]) def = a" by simp
 next 
  fix aa xs 
  show "p02_1 (xs @ [a, b]) def = a \<Longrightarrow> p02_1 ((aa # xs) @ [a, b]) def = a "
  proof (cases xs)
    assume "xs = []"
    thus " p02_1 ((aa # xs) @ [a, b]) def = a" by simp
   next
    fix ab list 
    assume a:" p02_1 (xs @ [a, b]) def = a" 
    assume "xs = ab # list"
    from this and a show "p02_1 ((aa # xs) @ [a, b]) def = a " 
    proof (cases list)
      assume " xs = ab # list"
     moreover
      assume " p02_1 (xs @ [a, b]) def = a"
     moreover
      assume "list = []"
     ultimately
      show "p02_1 ((aa # xs) @ [a, b]) def = a" by simp
     next 
      fix ac lista
      assume " xs = ab # list"
     moreover
      assume "p02_1 (xs @ [a, b]) def = a"
     moreover
      assume "list = ac # lista"
     ultimately
      show "p02_1 ((aa # xs) @ [a, b]) def = a" by simp
    qed
  qed
qed

  
lemma "length xs \<ge> 2 \<Longrightarrow> p02_1 xs defa \<in> set xs" 
proof (induct xs defa rule :  p02_1.induct)
  case (1 defa)
  then show ?case by simp
next
  case (2 x defa)
  then show ?case by simp
next
  case (3 x y defa)
  then show ?case by simp
next
  case (4 x v vb vc defa)
  then show ?case by simp
qed

lemma "length xs < 2 \<Longrightarrow> p02_1 xs defa = defa" by (induct xs defa rule : p02_1.induct, simp_all)
    
lemma "\<forall> xs. p02_1 xs defa = defa \<or> p02_1 xs defa \<in> set xs " 
proof -
  {
    assume hyp:"\<not>(\<forall> xs. p02_1 xs defa = defa \<or> p02_1 xs defa \<in> set xs)"
    hence a:"\<exists> xs . (p02_1 xs defa \<noteq> defa) \<and> (p02_1 xs defa \<notin> set xs)" by simp
    {
      fix a 
      assume hyp2:"(p02_1 a defa \<noteq> defa) \<and> (p02_1 a defa \<notin> set a)"
      hence False by (induct a defa  rule : p02_1.induct, simp_all)
    }
    with a have False by (rule exE)
  }
  thus "\<forall> xs. p02_1 xs defa = defa \<or> p02_1 xs defa \<in> set xs" by auto
qed
  
 
fun p02_2 :: "'a list \<Rightarrow> 'a option" where 
"p02_2 [] = None"|
"p02_2 [x] = None"|
"p02_2 [x,y] = Some x"|
"p02_2 (x#xs) = p02_2 xs"