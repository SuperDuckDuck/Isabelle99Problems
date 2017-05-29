theory P01 
imports Main 
begin 



fun p01_1 :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a" where 
"p01_1 [] def = def"|
"p01_1 [x] _ = x"|
"p01_1 (x#xs) def = p01_1 xs def"


value "p01_1 [] 5 :: int"

term p01_1


lemma "p01_1 [] def = def" by simp 

lemma "p01_1 [x] def = x" by simp

lemma "p01_1 (xs @ [x]) def = x"
proof (induct xs)
  case Nil 
  show ?case by simp
 next 
  fix a xs
  show " p01_1 (xs @ [x]) def = x \<Longrightarrow> p01_1 ((a # xs) @ [x]) def = x "
  proof (induct xs)
    case Nil 
    show ?case by simp
   next 
    fix aa xs 
    assume "(p01_1 (xs @ [x]) def = x \<Longrightarrow> p01_1 ((a # xs) @ [x]) def = x)"
    show "p01_1 ((aa # xs) @ [x]) def = x \<Longrightarrow> p01_1 ((a # aa # xs) @ [x]) def = x " by simp
  qed
qed




lemma "length xs \<ge> 1 \<Longrightarrow> p01_1 xs def = last xs"  
proof (induct xs)
  show "1 \<le> length [] \<Longrightarrow> p01_1 [] def = last []" by simp
 next
  fix xs a
  show "(1 \<le> length xs \<Longrightarrow> p01_1 xs def = last xs) \<Longrightarrow> 1 \<le> length (a # xs) \<Longrightarrow> p01_1 (a # xs) def = last (a # xs)"
  proof (cases xs)
  show "(1 \<le> length xs \<Longrightarrow> p01_1 xs def = last xs) \<Longrightarrow> 1 \<le> length (a # xs) \<Longrightarrow> xs = [] \<Longrightarrow> p01_1 (a # xs) def = last (a # xs)" by simp
 next
  fix aa list
  show " (1 \<le> length xs \<Longrightarrow> p01_1 xs def = last xs) \<Longrightarrow> 1 \<le> length (a # xs) \<Longrightarrow> xs = aa # list \<Longrightarrow> p01_1 (a # xs) def = last (a # xs)" by simp
 qed
qed
  

 

lemma "length xs \<ge> 1 \<Longrightarrow> p01_1 xs def = x \<Longrightarrow> x \<in> set xs" 
proof (induct xs) 
  show " 1 \<le> length [] \<Longrightarrow> p01_1 [] def = x \<Longrightarrow> x \<in> set []" by simp
 next 
  fix a xs 
  show "(1 \<le> length xs \<Longrightarrow> p01_1 xs def = x \<Longrightarrow> x \<in> set xs) \<Longrightarrow> 1 \<le> length (a # xs) \<Longrightarrow> p01_1 (a # xs) def = x \<Longrightarrow> x \<in> set (a # xs) "
  proof (cases xs)
  assume "(1 \<le> length xs \<Longrightarrow> p01_1 xs def = x \<Longrightarrow> x \<in> set xs) "
  assume " 1 \<le> length (a # xs)"
  assume a:"xs = []"
  assume " p01_1 (a # xs) def = x"
  from this and a show "x \<in> set (a # xs)" by simp
 next 
  fix aa list 
  assume a:"(1 \<le> length xs \<Longrightarrow> p01_1 xs def = x \<Longrightarrow> x \<in> set xs)"
  assume b:"1 \<le> length (a # xs)"
  assume c:" p01_1 (a # xs) def = x"
  assume " xs = aa # list"
  from this and a and b and c show  "x \<in> set (a # xs)" by simp
 qed
qed




fun p01_2 :: "'a list \<Rightarrow> 'a option " where
"p01_2 [] = None"|
"p01_2 [x] = Some x"|
"p01_2 (x#xs) = p01_2 xs"


value "p01_2 []"

value "p01_2 [1 , 2] :: int option"

lemma "p01_2 [] = None" by simp

lemma "p01_2 [x] = Some x" by simp

lemma "p01_2 (xs @ [a]) = Some a" 
proof (induct xs)
  show " p01_2 ([] @ [a]) = Some a" by simp
 next 
  fix aa xs 
  assume " p01_2 (xs @ [a]) = Some a"
  thus "p01_2 ((aa # xs) @ [a]) = Some a " 
  proof (cases xs)
    assume "p01_2 (xs @ [a]) = Some a"
    assume "xs = []"
    thus " p01_2 ((aa # xs) @ [a]) = Some a" by simp
   next 
    fix ab list 
    assume " p01_2 (xs @ [a]) = Some a"
    moreover
    assume "xs = ab # list"
    ultimately show "p01_2 ((aa # xs) @ [a]) = Some a" by simp
  qed
qed

lemma "p01_2 ls = Some x \<Longrightarrow> last ls = x"
proof (induct ls)
  show "p01_2 [] = Some x \<Longrightarrow> last [] = x" by simp
 next 
  fix a ls
  show " (p01_2 ls = Some x \<Longrightarrow> last ls = x) \<Longrightarrow> p01_2 (a # ls) = Some x \<Longrightarrow> last (a # ls) = x "
  proof (cases ls)
    assume " (p01_2 ls = Some x \<Longrightarrow> last ls = x)"
    assume a:" p01_2 (a # ls) =  Some x"
    assume " ls = []"
    with a show "last (a # ls) = x" by simp
   next 
    fix aa list 
    assume a:"(p01_2 ls = Some x \<Longrightarrow> last ls = x)"
    assume b:"p01_2 (a # ls) = Some x"
    assume " ls = aa # list"
    with a and b show "last (a # ls) = x" by simp
  qed
qed

 