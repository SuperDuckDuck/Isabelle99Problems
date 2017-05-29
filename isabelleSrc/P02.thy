theory P02 
imports Main 
begin 

fun p02_1 :: "'a list \<Rightarrow> 'a  \<Rightarrow> 'a" where 
"p02_1 [] def = def"|
"p02_1 [x] def = def"|
"p02_1 [x , y] def = x"|
"p02_1 (x#xs) def = p02_1 xs def"

value "p02_1 [] 5 :: int"

value "(p02_1 [2] 6) :: int"

value "p02_1 [1,2] 3 :: int"

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




fun p02_2 :: "'a list \<Rightarrow> 'a option" where 
"p02_2 [] = None"|
"p02_2 [x] = None"|
"p02_2 [x,y] = Some x"|
"p02_2 (x#xs) = p02_2 xs"