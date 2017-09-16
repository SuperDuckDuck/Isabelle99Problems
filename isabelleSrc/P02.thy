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
  
lemma "length xs \<ge> 2 \<Longrightarrow> p02_1 xs defa = xs ! ((length xs) -2) " by (induct xs defa rule : p02_1.induct, simp_all)
    
lemma "length ys = 2 \<Longrightarrow> p02_1 (xs @ ys) defa = hd ys" by  (induct xs defa rule : p02_1.induct; induct ys defa rule : p02_1.induct, simp_all)

fun p02_2 :: "'a list \<Rightarrow> 'a option" where 
"p02_2 [] = None"|
"p02_2 [x] = None"|
"p02_2 [x,y] = Some x"|
"p02_2 (x#xs) = p02_2 xs"


value "p02_2 [] :: 'a option"
  
value "p02_2 [1] :: int option"
  
value "p02_2 [1,2] :: int option"
  
lemma "p02_2 [] = None" by simp
    
lemma "p02_2 [val] = None" by simp
    
lemma "p02_2 [val1,val2] = Some val1" by simp
    
lemma "p02_2 (xs @ [val1 , val2]) = Some val1" by (induct xs rule : p02_2.induct, simp_all)

lemma "length xs \<ge> 2 \<Longrightarrow> \<exists>x . p02_2 xs = Some x" by (induct xs rule : p02_2.induct, simp_all)    
    
lemma "length xs \<ge> 2 \<Longrightarrow> the (p02_2 xs)  \<in> set xs" by (induct xs rule : p02_2.induct, simp_all)
    
lemma "length xs < 2 \<Longrightarrow> p02_2 xs = None" by (induct xs rule : p02_2.induct, simp_all)    
find_theorems "\<not>(\<forall>x . ?P x)" 
  
lemma "\<forall> xs:: 'a list . (p02_2 xs  = None) \<or> (the (p02_2 xs)  \<in> set xs) " 
proof -
  {
    assume "\<not>(\<forall> xs:: 'a list . p02_2 xs  = None \<or> (the (p02_2 xs)  \<in> set xs ))" 
    hence a:"\<exists> xs . ((p02_2 (xs :: 'a list)  \<noteq> None) \<and> (the (p02_2 xs)  \<notin> set xs)) " by simp 
    {
      fix as
      assume "(p02_2 (as :: 'a list)  \<noteq> None) \<and> (the (p02_2 as)  \<notin> set as)" 
      hence False by (induct as rule : p02_2.induct, simp_all)
    }
    with a have False by (rule exE)     
  }
  thus ?thesis by blast   
qed
    
lemma "length ys = 2 \<Longrightarrow> the (p02_2 (xs @ ys)) = hd ys" by (induct xs rule : p02_2.induct; induct ys rule : p02_2.induct, simp_all)  
  
lemma "length xs \<ge> 2 \<Longrightarrow> the (p02_2 xs) = xs ! ((length xs) - 2)" by (induct xs rule : p02_2.induct, simp_all)
  
lemma "length xs \<ge> 2 \<Longrightarrow> the (p02_2 xs) = p02_1 xs defa" by (induct xs rule : p02_2.induct, simp_all) 