theory "specification"
  imports Main
begin

(* Definição de uma árvore binária *)
datatype 'a tree = Empty | Node "'a tree" 'a "'a tree"

(* Definição da função cat *)
primrec cat :: "'a list ⇒ 'a list ⇒ 'a list" where
  cat_base: "cat [] l = l" |
  cat_induction: "cat (h # t) l = h # (cat t l)"

(* Definição da função size (tamanho) *)
primrec size :: "'a list ⇒ nat" where
  size_base: "size [] = 0" |
  size_induction: "size (h # t) = 1 + size t"

(* Definição da função numnodes (numnodos) *)
primrec numnodes :: "'a tree ⇒ nat" where
  numnodes_base: "numnodes Empty = 0" |
  numnodes_induction: "numnodes (Node L x R) = 1 + numnodes L + numnodes R"

(* Definição da função mirror (espelho) *)
primrec mirror :: "'a tree ⇒ 'a tree" where
  mirror_base: "mirror Empty = Empty" |
  mirror_induction: "mirror (Node L x R) = Node (mirror R) x (mirror L)"

(* Definição da função content (conteudo) *)
primrec content :: "'a tree ⇒ 'a list" where
  content_base: "content Empty = []" |
  content_induction: "content (Node L x R) = x # (cat (content L) (content R))"

(* Primeiro teorema e lemma a ser reusado na prova do segundo teorema *)
lemma cat_size: "size (cat L1 L2) = size L1 + size L2"
proof (induct L1)
  case Nil
  show ?case
  proof -
    have 1: "cat [] L2 = L2" by (simp only: cat_base)
    also have 2: "size [] = 0" by (simp only: size_base)
    also have 3: "size (cat [] L2) = size L2" by (simp only: 1)
    finally have conclusion: "size (cat [] L2) = size [] + size L2" by (simp only: 2 3)
    thus ?thesis by (simp only: conclusion)
  qed
next
  case (Cons h t)
  assume induction_hypothesis: "size (cat t L2) = size t + size L2"
  show ?case
  proof -
    have 1: "size (cat (h # t) L2) = size (h # (cat t L2))" by (simp only: cat_induction)
    also have 2: "... = 1 + size (cat t L2)" by (simp only: size_induction)
    also have 3: "... = 1 + size t + size L2" by (simp only: induction_hypothesis)
    also have 4: "... = size (h # t) + size L2" by (simp only: size_induction)
    finally have conclusion: "... = size (cat (h # t) L2)" by (simp only: 1 4)
    thus ?thesis by (simp only: conclusion)
  qed
qed

(* Prova do segundo teorema *)
theorem numnodes_equals_size_of_content: "numnodes A = size (content A)"
proof (induct A)
  case Empty
  show ?case
  proof -
    have 1: "numnodes Empty = 0" by (simp only: numnodes_base)
    also have 2: "content Empty = []" by (simp only: content_base)
    also have 3: "size [] = 0" by (simp only: size_base)
    also have 4: "size (content Empty) = 0" by (simp only: 2 3)
    also have conclusion: "numnodes Empty = size (content Empty)" by (simp only: 1 4)
    thus ?thesis by (simp only: conclusion)
  qed
next
  case (Node L x R)
  assume induction_hypothesis_left: "numnodes L = size (content L)"
  assume induction_hypothesis_right: "numnodes R = size (content R)"
  show ?case
  proof -
    have 1: "content (Node L x R) = x # cat (content L) (content R)" by (simp only: content_induction)
    also have 2: "size ... = 1 + size (cat (content L) (content R))" by (simp only: size_induction)
    also have 3: "size (x # cat (content L) (content R)) = 1 + (size (content L) + size (content R))" by (simp only: size_induction cat_size)
    moreover have 4: "... = 1 + numnodes L + numnodes R" by (simp only: induction_hypothesis_left induction_hypothesis_right)
    moreover have 5: "size (x # cat (content L) (content R)) = ..." by (simp only: 3 4)
    moreover have 6: "size (content (Node L x R)) = ..." by (simp only: 5 content_induction)
    moreover have conclusion: "size (content (Node L x R)) = numnodes (Node L x R)" by (simp only: 6 numnodes_induction)
    thus ?thesis by (simp only: conclusion)
  qed
qed

end
