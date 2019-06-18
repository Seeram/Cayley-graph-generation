1   push reached_nodes[], generating_set[]
2
3   foreach len in [ 2, ... , diameter ]
4       foreach variation with repetitions of length len
5           node = gen_set[ var[0] ] x ... x gen_set[ var[len] ]
6           push reached_nodes[], node
7
8   foreach node in cayley_graph[]
9       if any in reached_nodes[] not equal to node
10          return cayley_graph has not given diameter
11
12  return cayley_graph has given diameter
