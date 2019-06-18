1   function find_cycle(generating_set[], girth)
2       foreach variation with len girth
3           node = gen_set[ var[0] x ... x gen_set[ var[len] ]
4           if node equal to eye matrix
5               return found cycle
6
7   if find_cycle(generating_set, grith)  
8       foreach i in [ 3, ... , girth - 1 ]
9           if(find_cycle(generating_set[], i)) 
10              return girth i
11
12      return graph has given girth
